import V185TrunkScan23Chunk0535

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3169035 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5]
def baseStart_3169035 : Nat := 118140960795 + 3169035 * 2 ^ 59
def prefixEnd_3169035 : Nat := 4983230072969 + 3 ^ 40 * 3169035 * 2
def baseEnd_3169035 : Nat := 1627238165921113869688379

theorem tailTrace_3169035 : CollatzResearch.WordTrace tailWord_3169035 prefixEnd_3169035 1627238165921113869688379 := by
  unfold tailWord_3169035
  simp only [CollatzResearch.WordTrace]
  refine ⟨115584202074134897933740559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77056134716089931955827039 115584202074134897933740559)
  ·
    refine ⟨173376303111202346900610839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115584202074134897933740559 173376303111202346900610839)
    ·
      refine ⟨260064454666803520350916259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173376303111202346900610839 260064454666803520350916259)
      ·
        refine ⟨390096682000205280526374389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260064454666803520350916259 390096682000205280526374389)
        ·
          refine ⟨36571563937519245049347599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 390096682000205280526374389 36571563937519245049347599)
          ·
            refine ⟨54857345906278867574021399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36571563937519245049347599 54857345906278867574021399)
            ·
              refine ⟨82286018859418301361032099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54857345906278867574021399 82286018859418301361032099)
              ·
                refine ⟨123429028289127452041548149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82286018859418301361032099 123429028289127452041548149)
                ·
                  refine ⟨11571471402105698628895139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123429028289127452041548149 11571471402105698628895139)
                  ·
                    refine ⟨17357207103158547943342709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11571471402105698628895139 17357207103158547943342709)
                    ·
                      refine ⟨1627238165921113869688379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17357207103158547943342709 1627238165921113869688379)
                      ·
                        rfl

theorem cell23_3169035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_3169035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169035 prefixEnd_3169035 := by exact prefixLift 3169035
  have htrace : WordTrace (prefixWord ++ tailWord_3169035) baseStart_3169035 baseEnd_3169035 := by
    simpa [prefixWord, tailWord_3169035, baseEnd_3169035] using wordTrace_append hprefix tailTrace_3169035
  have hstable : (prefixWord ++ tailWord_3169035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169035).length < 2 ^ (prefixWord ++ tailWord_3169035).sum := by decide
  have hdescent : baseEnd_3169035 < baseStart_3169035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169052 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3169052 : Nat := 118140960795 + 3169052 * 2 ^ 59
def prefixEnd_3169052 : Nat := 4983230072969 + 3 ^ 40 * 3169052 * 2
def baseEnd_3169052 : Nat := 1627246895092240303175801

theorem tailTrace_3169052 : CollatzResearch.WordTrace tailWord_3169052 prefixEnd_3169052 1627246895092240303175801 := by
  unfold tailWord_3169052
  simp only [CollatzResearch.WordTrace]
  refine ⟨57792411057536654918554705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77056548076715539891406273 57792411057536654918554705)
  ·
    refine ⟨43344308293152491188916029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57792411057536654918554705 43344308293152491188916029)
    ·
      refine ⟨16254115609932184195843511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43344308293152491188916029 16254115609932184195843511)
      ·
        refine ⟨24381173414898276293765267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16254115609932184195843511 24381173414898276293765267)
        ·
          refine ⟨36571760122347414440647901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24381173414898276293765267 36571760122347414440647901)
          ·
            refine ⟨13714410045880280415242963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36571760122347414440647901 13714410045880280415242963)
            ·
              refine ⟨20571615068820420622864445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13714410045880280415242963 20571615068820420622864445)
              ·
                refine ⟨7714355650807657733574167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20571615068820420622864445 7714355650807657733574167)
                ·
                  refine ⟨11571533476211486600361251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7714355650807657733574167 11571533476211486600361251)
                  ·
                    refine ⟨17357300214317229900541877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11571533476211486600361251 17357300214317229900541877)
                    ·
                      refine ⟨1627246895092240303175801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17357300214317229900541877 1627246895092240303175801)
                      ·
                        rfl

theorem cell23_3169052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3169052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169052 prefixEnd_3169052 := by exact prefixLift 3169052
  have htrace : WordTrace (prefixWord ++ tailWord_3169052) baseStart_3169052 baseEnd_3169052 := by
    simpa [prefixWord, tailWord_3169052, baseEnd_3169052] using wordTrace_append hprefix tailTrace_3169052
  have hstable : (prefixWord ++ tailWord_3169052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169052).length < 2 ^ (prefixWord ++ tailWord_3169052).sum := by decide
  have hdescent : baseEnd_3169052 < baseStart_3169052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169053 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3169053 : Nat := 118140960795 + 3169053 * 2 ^ 59
def prefixEnd_3169053 : Nat := 4983230072969 + 3 ^ 40 * 3169053 * 2
def baseEnd_3169053 : Nat := 1627247408572894799263297

theorem tailTrace_3169053 : CollatzResearch.WordTrace tailWord_3169053 prefixEnd_3169053 1627247408572894799263297 := by
  unfold tailWord_3169053
  simp only [CollatzResearch.WordTrace]
  refine ⟨115584858588069687007895813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77056572392046458005263875 115584858588069687007895813)
  ·
    refine ⟨21672160985263066313980465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115584858588069687007895813 21672160985263066313980465)
    ·
      refine ⟨16254120738947299735485349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21672160985263066313980465 16254120738947299735485349)
      ·
        refine ⟨3047647638552618700403503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16254120738947299735485349 3047647638552618700403503)
        ·
          refine ⟨4571471457828928050605255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047647638552618700403503 4571471457828928050605255)
          ·
            refine ⟨6857207186743392075907883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571471457828928050605255 6857207186743392075907883)
            ·
              refine ⟨10285810780115088113861825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6857207186743392075907883 10285810780115088113861825)
              ·
                refine ⟨7714358085086316085396369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10285810780115088113861825 7714358085086316085396369)
                ·
                  refine ⟨5785768563814737064047277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7714358085086316085396369 5785768563814737064047277)
                  ·
                    refine ⟨2169663211430526399017729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5785768563814737064047277 2169663211430526399017729)
                    ·
                      refine ⟨1627247408572894799263297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169663211430526399017729 1627247408572894799263297)
                      ·
                        rfl

theorem cell23_3169053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3169053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169053 prefixEnd_3169053 := by exact prefixLift 3169053
  have htrace : WordTrace (prefixWord ++ tailWord_3169053) baseStart_3169053 baseEnd_3169053 := by
    simpa [prefixWord, tailWord_3169053, baseEnd_3169053] using wordTrace_append hprefix tailTrace_3169053
  have hstable : (prefixWord ++ tailWord_3169053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169053).length < 2 ^ (prefixWord ++ tailWord_3169053).sum := by decide
  have hdescent : baseEnd_3169053 < baseStart_3169053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169055 : List Nat := [1, 1, 2, 4, 2, 2, 11]
def baseStart_3169055 : Nat := 118140960795 + 3169055 * 2 ^ 59
def prefixEnd_3169055 : Nat := 4983230072969 + 3 ^ 40 * 3169055 * 2
def baseEnd_3169055 : Nat := 20089486858446960388127

theorem tailTrace_3169055 : CollatzResearch.WordTrace tailWord_3169055 prefixEnd_3169055 20089486858446960388127 := by
  unfold tailWord_3169055
  simp only [CollatzResearch.WordTrace]
  refine ⟨115584931534062441349468619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77056621022708294232979079 115584931534062441349468619)
  ·
    refine ⟨173377397301093662024202929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115584931534062441349468619 173377397301093662024202929)
    ·
      refine ⟨130033047975820246518152197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173377397301093662024202929 130033047975820246518152197)
      ·
        refine ⟨24381196495466296222153537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130033047975820246518152197 24381196495466296222153537)
        ·
          refine ⟨18285897371599722166615153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24381196495466296222153537 18285897371599722166615153)
          ·
            refine ⟨13714423028699791624961365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18285897371599722166615153 13714423028699791624961365)
            ·
              refine ⟨20089486858446960388127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13714423028699791624961365 20089486858446960388127)
              ·
                rfl

theorem cell23_3169055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 11].length) (baseStart_3169055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169055 prefixEnd_3169055 := by exact prefixLift 3169055
  have htrace : WordTrace (prefixWord ++ tailWord_3169055) baseStart_3169055 baseEnd_3169055 := by
    simpa [prefixWord, tailWord_3169055, baseEnd_3169055] using wordTrace_append hprefix tailTrace_3169055
  have hstable : (prefixWord ++ tailWord_3169055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169055).length < 2 ^ (prefixWord ++ tailWord_3169055).sum := by decide
  have hdescent : baseEnd_3169055 < baseStart_3169055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169060 : List Nat := [2, 3, 1, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_3169060 : Nat := 118140960795 + 3169060 * 2 ^ 59
def prefixEnd_3169060 : Nat := 4983230072969 + 3 ^ 40 * 3169060 * 2
def baseEnd_3169060 : Nat := 1627251002937476271875765

theorem tailTrace_3169060 : CollatzResearch.WordTrace tailWord_3169060 prefixEnd_3169060 1627251002937476271875765 := by
  unfold tailWord_3169060
  simp only [CollatzResearch.WordTrace]
  refine ⟨57792556949522163601700317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77056742599362884802267089 57792556949522163601700317)
  ·
    refine ⟨21672208856070811350637619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57792556949522163601700317 21672208856070811350637619)
    ·
      refine ⟨32508313284106217025956429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21672208856070811350637619 32508313284106217025956429)
      ·
        refine ⟨12190617481539831384733661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32508313284106217025956429 12190617481539831384733661)
        ·
          refine ⟨4571481555577436769275123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12190617481539831384733661 4571481555577436769275123)
          ·
            refine ⟨6857222333366155153912685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571481555577436769275123 6857222333366155153912685)
            ·
              refine ⟨2571458375012308182717257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6857222333366155153912685 2571458375012308182717257)
              ·
                refine ⟨1928593781259231137037943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571458375012308182717257 1928593781259231137037943)
                ·
                  refine ⟨2892890671888846705556915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928593781259231137037943 2892890671888846705556915)
                  ·
                    refine ⟨4339336007833270058335373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2892890671888846705556915 4339336007833270058335373)
                    ·
                      refine ⟨1627251002937476271875765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339336007833270058335373 1627251002937476271875765)
                      ·
                        rfl

theorem cell23_3169060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_3169060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169060 prefixEnd_3169060 := by exact prefixLift 3169060
  have htrace : WordTrace (prefixWord ++ tailWord_3169060) baseStart_3169060 baseEnd_3169060 := by
    simpa [prefixWord, tailWord_3169060, baseEnd_3169060] using wordTrace_append hprefix tailTrace_3169060
  have hstable : (prefixWord ++ tailWord_3169060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169060).length < 2 ^ (prefixWord ++ tailWord_3169060).sum := by decide
  have hdescent : baseEnd_3169060 < baseStart_3169060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169086 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3169086 : Nat := 118140960795 + 3169086 * 2 ^ 59
def prefixEnd_3169086 : Nat := 4983230072969 + 3 ^ 40 * 3169086 * 2
def baseEnd_3169086 : Nat := 1627264353434493170150645

theorem tailTrace_3169086 : CollatzResearch.WordTrace tailWord_3169086 prefixEnd_3169086 1627264353434493170150645 := by
  unfold tailWord_3169086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14448257774618766705480889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77057374797966755762564741 14448257774618766705480889)
  ·
    refine ⟨10836193330964075029110667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14448257774618766705480889 10836193330964075029110667)
    ·
      refine ⟨16254289996446112543666001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10836193330964075029110667 16254289996446112543666001)
      ·
        refine ⟨12190717497334584407749501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16254289996446112543666001 12190717497334584407749501)
        ·
          refine ⟨4571519061500469152906063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12190717497334584407749501 4571519061500469152906063)
          ·
            refine ⟨6857278592250703729359095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571519061500469152906063 6857278592250703729359095)
            ·
              refine ⟨10285917888376055594038643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6857278592250703729359095 10285917888376055594038643)
              ·
                refine ⟨15428876832564083391057965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10285917888376055594038643 15428876832564083391057965)
                ·
                  refine ⟨5785828812211531271646737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15428876832564083391057965 5785828812211531271646737)
                  ·
                    refine ⟨4339371609158648453735053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5785828812211531271646737 4339371609158648453735053)
                    ·
                      refine ⟨1627264353434493170150645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339371609158648453735053 1627264353434493170150645)
                      ·
                        rfl

theorem cell23_3169086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3169086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169086 prefixEnd_3169086 := by exact prefixLift 3169086
  have htrace : WordTrace (prefixWord ++ tailWord_3169086) baseStart_3169086 baseEnd_3169086 := by
    simpa [prefixWord, tailWord_3169086, baseEnd_3169086] using wordTrace_append hprefix tailTrace_3169086
  have hstable : (prefixWord ++ tailWord_3169086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169086).length < 2 ^ (prefixWord ++ tailWord_3169086).sum := by decide
  have hdescent : baseEnd_3169086 < baseStart_3169086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169132 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_3169132 : Nat := 118140960795 + 3169132 * 2 ^ 59
def prefixEnd_3169132 : Nat := 4983230072969 + 3 ^ 40 * 3169132 * 2
def baseEnd_3169132 : Nat := 542429324514866663391811

theorem tailTrace_3169132 : CollatzResearch.WordTrace tailWord_3169132 prefixEnd_3169132 542429324514866663391811 := by
  unfold tailWord_3169132
  simp only [CollatzResearch.WordTrace]
  refine ⟨57793869977391741750010825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77058493303188989000014433 57793869977391741750010825)
  ·
    refine ⟨43345402483043806312508119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57793869977391741750010825 43345402483043806312508119)
    ·
      refine ⟨65018103724565709468762179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43345402483043806312508119 65018103724565709468762179)
      ·
        refine ⟨97527155586848564203143269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65018103724565709468762179 97527155586848564203143269)
        ·
          refine ⟨18286341672534105788089363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97527155586848564203143269 18286341672534105788089363)
          ·
            refine ⟨27429512508801158682134045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18286341672534105788089363 27429512508801158682134045)
            ·
              refine ⟨10286067190800434505800267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27429512508801158682134045 10286067190800434505800267)
              ·
                refine ⟨15429100786200651758700401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10286067190800434505800267 15429100786200651758700401)
                ·
                  refine ⟨11571825589650488819025301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15429100786200651758700401 11571825589650488819025301)
                  ·
                    refine ⟨542429324514866663391811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11571825589650488819025301 542429324514866663391811)
                    ·
                      rfl

theorem cell23_3169132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_3169132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169132 prefixEnd_3169132 := by exact prefixLift 3169132
  have htrace : WordTrace (prefixWord ++ tailWord_3169132) baseStart_3169132 baseEnd_3169132 := by
    simpa [prefixWord, tailWord_3169132, baseEnd_3169132] using wordTrace_append hprefix tailTrace_3169132
  have hstable : (prefixWord ++ tailWord_3169132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169132).length < 2 ^ (prefixWord ++ tailWord_3169132).sum := by decide
  have hdescent : baseEnd_3169132 < baseStart_3169132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169139 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 1, 4, 2]
def baseStart_3169139 : Nat := 118140960795 + 3169139 * 2 ^ 59
def prefixEnd_3169139 : Nat := 4983230072969 + 3 ^ 40 * 3169139 * 2
def baseEnd_3169139 : Nat := 1627291567909181462787901

theorem tailTrace_3169139 : CollatzResearch.WordTrace tailWord_3169139 prefixEnd_3169139 1627291567909181462787901 := by
  unfold tailWord_3169139
  simp only [CollatzResearch.WordTrace]
  refine ⟨115587995265758123695526471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77058663510505415797017647 115587995265758123695526471)
  ·
    refine ⟨173381992898637185543289707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115587995265758123695526471 173381992898637185543289707)
    ·
      refine ⟨260072989347955778314934561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173381992898637185543289707 260072989347955778314934561)
      ·
        refine ⟨195054742010966833736200921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260072989347955778314934561 195054742010966833736200921)
        ·
          refine ⟨146291056508225125302150691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195054742010966833736200921 146291056508225125302150691)
          ·
            refine ⟨219436584762337687953226037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146291056508225125302150691 219436584762337687953226037)
            ·
              refine ⟨20572179821469158245614941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219436584762337687953226037 20572179821469158245614941)
              ·
                refine ⟨7714567433050934342105603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20572179821469158245614941 7714567433050934342105603)
                ·
                  refine ⟨11571851149576401513158405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7714567433050934342105603 11571851149576401513158405)
                  ·
                    refine ⟨2169722090545575283717201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11571851149576401513158405 2169722090545575283717201)
                    ·
                      refine ⟨1627291567909181462787901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169722090545575283717201 1627291567909181462787901)
                      ·
                        rfl

theorem cell23_3169139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 4, 2].length) (baseStart_3169139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169139 prefixEnd_3169139 := by exact prefixLift 3169139
  have htrace : WordTrace (prefixWord ++ tailWord_3169139) baseStart_3169139 baseEnd_3169139 := by
    simpa [prefixWord, tailWord_3169139, baseEnd_3169139] using wordTrace_append hprefix tailTrace_3169139
  have hstable : (prefixWord ++ tailWord_3169139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169139).length < 2 ^ (prefixWord ++ tailWord_3169139).sum := by decide
  have hdescent : baseEnd_3169139 < baseStart_3169139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169154 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3169154 : Nat := 118140960795 + 3169154 * 2 ^ 59
def prefixEnd_3169154 : Nat := 4983230072969 + 3 ^ 40 * 3169154 * 2
def baseEnd_3169154 : Nat := 1627299270118998904100333

theorem tailTrace_3169154 : CollatzResearch.WordTrace tailWord_3169154 prefixEnd_3169154 1627299270118998904100333 := by
  unfold tailWord_3169154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28897135590175945314330629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77059028240469187504881677 28897135590175945314330629)
  ·
    refine ⟨5418212923157989746436993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28897135590175945314330629 5418212923157989746436993)
    ·
      refine ⟨4063659692368492309827745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5418212923157989746436993 4063659692368492309827745)
      ·
        refine ⟨3047744769276369232370809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4063659692368492309827745 3047744769276369232370809)
        ·
          refine ⟨2285808576957276924278107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3047744769276369232370809 2285808576957276924278107)
          ·
            refine ⟨3428712865435915386417161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285808576957276924278107 3428712865435915386417161)
            ·
              refine ⟨2571534649076936539812871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428712865435915386417161 2571534649076936539812871)
              ·
                refine ⟨3857301973615404809719307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571534649076936539812871 3857301973615404809719307)
                ·
                  refine ⟨5785952960423107214578961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3857301973615404809719307 5785952960423107214578961)
                  ·
                    refine ⟨4339464720317330410934221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5785952960423107214578961 4339464720317330410934221)
                    ·
                      refine ⟨1627299270118998904100333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339464720317330410934221 1627299270118998904100333)
                      ·
                        rfl

theorem cell23_3169154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3169154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169154 prefixEnd_3169154 := by exact prefixLift 3169154
  have htrace : WordTrace (prefixWord ++ tailWord_3169154) baseStart_3169154 baseEnd_3169154 := by
    simpa [prefixWord, tailWord_3169154, baseEnd_3169154] using wordTrace_append hprefix tailTrace_3169154
  have hstable : (prefixWord ++ tailWord_3169154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169154).length < 2 ^ (prefixWord ++ tailWord_3169154).sum := by decide
  have hdescent : baseEnd_3169154 < baseStart_3169154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169156 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_3169156 : Nat := 118140960795 + 3169156 * 2 ^ 59
def prefixEnd_3169156 : Nat := 4983230072969 + 3 ^ 40 * 3169156 * 2
def baseEnd_3169156 : Nat := 1627300297080307896275323

theorem tailTrace_3169156 : CollatzResearch.WordTrace tailWord_3169156 prefixEnd_3169156 1627300297080307896275323 := by
  unfold tailWord_3169156
  simp only [CollatzResearch.WordTrace]
  refine ⟨57794307653348267799447661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77059076871131023732596881 57794307653348267799447661)
  ·
    refine ⟨21672865370005600424792873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57794307653348267799447661 21672865370005600424792873)
    ·
      refine ⟨16254649027504200318594655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21672865370005600424792873 16254649027504200318594655)
      ·
        refine ⟨24381973541256300477891983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16254649027504200318594655 24381973541256300477891983)
        ·
          refine ⟨36572960311884450716837975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24381973541256300477891983 36572960311884450716837975)
          ·
            refine ⟨54859440467826676075256963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36572960311884450716837975 54859440467826676075256963)
            ·
              refine ⟨82289160701740014112885445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54859440467826676075256963 82289160701740014112885445)
              ·
                refine ⟨15429217631576252646166021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82289160701740014112885445 15429217631576252646166021)
                ·
                  refine ⟨2892978305920547371156129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15429217631576252646166021 2892978305920547371156129)
                  ·
                    refine ⟨2169733729440410528367097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2892978305920547371156129 2169733729440410528367097)
                    ·
                      refine ⟨1627300297080307896275323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169733729440410528367097 1627300297080307896275323)
                      ·
                        rfl

theorem cell23_3169156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_3169156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169156 prefixEnd_3169156 := by exact prefixLift 3169156
  have htrace : WordTrace (prefixWord ++ tailWord_3169156) baseStart_3169156 baseEnd_3169156 := by
    simpa [prefixWord, tailWord_3169156, baseEnd_3169156] using wordTrace_append hprefix tailTrace_3169156
  have hstable : (prefixWord ++ tailWord_3169156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169156).length < 2 ^ (prefixWord ++ tailWord_3169156).sum := by decide
  have hdescent : baseEnd_3169156 < baseStart_3169156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169160 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_3169160 : Nat := 118140960795 + 3169160 * 2 ^ 59
def prefixEnd_3169160 : Nat := 4983230072969 + 3 ^ 40 * 3169160 * 2
def baseEnd_3169160 : Nat := 1627302351002925880625305

theorem tailTrace_3169160 : CollatzResearch.WordTrace tailWord_3169160 prefixEnd_3169160 1627302351002925880625305 := by
  unfold tailWord_3169160
  simp only [CollatzResearch.WordTrace]
  refine ⟨57794380599341022141020467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77059174132454696188027289 57794380599341022141020467)
  ·
    refine ⟨86691570899011533211530701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57794380599341022141020467 86691570899011533211530701)
    ·
      refine ⟨32509339087129324954324013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86691570899011533211530701 32509339087129324954324013)
      ·
        refine ⟨12191002157673496857871505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32509339087129324954324013 12191002157673496857871505)
        ·
          refine ⟨9143251618255122643403629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12191002157673496857871505 9143251618255122643403629)
          ·
            refine ⟨3428719356845670991276361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9143251618255122643403629 3428719356845670991276361)
            ·
              refine ⟨2571539517634253243457271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3428719356845670991276361 2571539517634253243457271)
              ·
                refine ⟨3857309276451379865185907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571539517634253243457271 3857309276451379865185907)
                ·
                  refine ⟨5785963914677069797778861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3857309276451379865185907 5785963914677069797778861)
                  ·
                    refine ⟨2169736468003901174167073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5785963914677069797778861 2169736468003901174167073)
                    ·
                      refine ⟨1627302351002925880625305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169736468003901174167073 1627302351002925880625305)
                      ·
                        rfl

theorem cell23_3169160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_3169160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169160 prefixEnd_3169160 := by exact prefixLift 3169160
  have htrace : WordTrace (prefixWord ++ tailWord_3169160) baseStart_3169160 baseEnd_3169160 := by
    simpa [prefixWord, tailWord_3169160, baseEnd_3169160] using wordTrace_append hprefix tailTrace_3169160
  have hstable : (prefixWord ++ tailWord_3169160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169160).length < 2 ^ (prefixWord ++ tailWord_3169160).sum := by decide
  have hdescent : baseEnd_3169160 < baseStart_3169160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169173 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_3169173 : Nat := 118140960795 + 3169173 * 2 ^ 59
def prefixEnd_3169173 : Nat := 4983230072969 + 3 ^ 40 * 3169173 * 2
def baseEnd_3169173 : Nat := 1627309026251434329762745

theorem tailTrace_3169173 : CollatzResearch.WordTrace tailWord_3169173 prefixEnd_3169173 1627309026251434329762745 := by
  unfold tailWord_3169173
  simp only [CollatzResearch.WordTrace]
  refine ⟨115589235347634947502264173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77059490231756631668176115 115589235347634947502264173)
  ·
    refine ⟨43345963255363105313349065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115589235347634947502264173 43345963255363105313349065)
    ·
      refine ⟨32509472441522328985011799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43345963255363105313349065 32509472441522328985011799)
      ·
        refine ⟨48764208662283493477517699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32509472441522328985011799 48764208662283493477517699)
        ·
          refine ⟨73146312993425240216276549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48764208662283493477517699 73146312993425240216276549)
          ·
            refine ⟨13714933686267232540551853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73146312993425240216276549 13714933686267232540551853)
            ·
              refine ⟨5143100132350212202706945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13714933686267232540551853 5143100132350212202706945)
              ·
                refine ⟨3857325099262659152030209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143100132350212202706945 3857325099262659152030209)
                ·
                  refine ⟨2892993824446994364022657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3857325099262659152030209 2892993824446994364022657)
                  ·
                    refine ⟨2169745368335245773016993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2892993824446994364022657 2169745368335245773016993)
                    ·
                      refine ⟨1627309026251434329762745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169745368335245773016993 1627309026251434329762745)
                      ·
                        rfl

theorem cell23_3169173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_3169173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169173 prefixEnd_3169173 := by exact prefixLift 3169173
  have htrace : WordTrace (prefixWord ++ tailWord_3169173) baseStart_3169173 baseEnd_3169173 := by
    simpa [prefixWord, tailWord_3169173, baseEnd_3169173] using wordTrace_append hprefix tailTrace_3169173
  have hstable : (prefixWord ++ tailWord_3169173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169173).length < 2 ^ (prefixWord ++ tailWord_3169173).sum := by decide
  have hdescent : baseEnd_3169173 < baseStart_3169173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169202 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3169202 : Nat := 118140960795 + 3169202 * 2 ^ 59
def prefixEnd_3169202 : Nat := 4983230072969 + 3 ^ 40 * 3169202 * 2
def baseEnd_3169202 : Nat := 1627323917190414716300111

theorem tailTrace_3169202 : CollatzResearch.WordTrace tailWord_3169202 prefixEnd_3169202 1627323917190414716300111 := by
  unfold tailWord_3169202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28897573266132471363767465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77060195376353256970046573 28897573266132471363767465)
  ·
    refine ⟨21673179949599353522825599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28897573266132471363767465 21673179949599353522825599)
    ·
      refine ⟨32509769924399030284238399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21673179949599353522825599 32509769924399030284238399)
      ·
        refine ⟨48764654886598545426357599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32509769924399030284238399 48764654886598545426357599)
        ·
          refine ⟨73146982329897818139536399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48764654886598545426357599 73146982329897818139536399)
          ·
            refine ⟨109720473494846727209304599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73146982329897818139536399 109720473494846727209304599)
            ·
              refine ⟨164580710242270090813956899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109720473494846727209304599 164580710242270090813956899)
              ·
                refine ⟨246871065363405136220935349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164580710242270090813956899 246871065363405136220935349)
                ·
                  refine ⟨23144162377819231520712689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246871065363405136220935349 23144162377819231520712689)
                  ·
                    refine ⟨17358121783364423640534517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23144162377819231520712689 17358121783364423640534517)
                    ·
                      refine ⟨1627323917190414716300111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17358121783364423640534517 1627323917190414716300111)
                      ·
                        rfl

theorem cell23_3169202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3169202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169202 prefixEnd_3169202 := by exact prefixLift 3169202
  have htrace : WordTrace (prefixWord ++ tailWord_3169202) baseStart_3169202 baseEnd_3169202 := by
    simpa [prefixWord, tailWord_3169202, baseEnd_3169202] using wordTrace_append hprefix tailTrace_3169202
  have hstable : (prefixWord ++ tailWord_3169202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169202).length < 2 ^ (prefixWord ++ tailWord_3169202).sum := by decide
  have hdescent : baseEnd_3169202 < baseStart_3169202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169213 : List Nat := [1, 4, 1, 2, 4, 2, 1, 3, 5]
def baseStart_3169213 : Nat := 118140960795 + 3169213 * 2 ^ 59
def prefixEnd_3169213 : Nat := 4983230072969 + 3 ^ 40 * 3169213 * 2
def baseEnd_3169213 : Nat := 180814396164179352584729

theorem tailTrace_3169213 : CollatzResearch.WordTrace tailWord_3169213 prefixEnd_3169213 180814396164179352584729 := by
  unfold tailWord_3169213
  simp only [CollatzResearch.WordTrace]
  refine ⟨115590694267490034333720293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77060462844993356222480195 115590694267490034333720293)
  ·
    refine ⟨21673255175154381437572555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115590694267490034333720293 21673255175154381437572555)
    ·
      refine ⟨32509882762731572156358833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21673255175154381437572555 32509882762731572156358833)
      ·
        refine ⟨24382412072048679117269125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32509882762731572156358833 24382412072048679117269125)
        ·
          refine ⟨4571702263509127334487961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24382412072048679117269125 4571702263509127334487961)
          ·
            refine ⟨3428776697631845500865971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4571702263509127334487961 3428776697631845500865971)
            ·
              refine ⟨5143165046447768251298957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428776697631845500865971 5143165046447768251298957)
              ·
                refine ⟨1928686892417913094237109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5143165046447768251298957 1928686892417913094237109)
                ·
                  refine ⟨180814396164179352584729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1928686892417913094237109 180814396164179352584729)
                  ·
                    rfl

theorem cell23_3169213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_3169213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169213 prefixEnd_3169213 := by exact prefixLift 3169213
  have htrace : WordTrace (prefixWord ++ tailWord_3169213) baseStart_3169213 baseEnd_3169213 := by
    simpa [prefixWord, tailWord_3169213, baseEnd_3169213] using wordTrace_append hprefix tailTrace_3169213
  have hstable : (prefixWord ++ tailWord_3169213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169213).length < 2 ^ (prefixWord ++ tailWord_3169213).sum := by decide
  have hdescent : baseEnd_3169213 < baseStart_3169213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169239 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 3, 4]
def baseStart_3169239 : Nat := 118140960795 + 3169239 * 2 ^ 59
def prefixEnd_3169239 : Nat := 4983230072969 + 3 ^ 40 * 3169239 * 2
def baseEnd_3169239 : Nat := 542447638658210357179147

theorem tailTrace_3169239 : CollatzResearch.WordTrace tailWord_3169239 prefixEnd_3169239 542447638658210357179147 := by
  unfold tailWord_3169239
  simp only [CollatzResearch.WordTrace]
  refine ⟨115591642565395840774166771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77061095043597227182777847 115591642565395840774166771)
  ·
    refine ⟨173387463848093761161250157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115591642565395840774166771 173387463848093761161250157)
    ·
      refine ⟨65020298943035160435468809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173387463848093761161250157 65020298943035160435468809)
      ·
        refine ⟨48765224207276370326601607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65020298943035160435468809 48765224207276370326601607)
        ·
          refine ⟨73147836310914555489902411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48765224207276370326601607 73147836310914555489902411)
          ·
            refine ⟨109721754466371833234853617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73147836310914555489902411 109721754466371833234853617)
            ·
              refine ⟨82291315849778874926140213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109721754466371833234853617 82291315849778874926140213)
              ·
                refine ⟨7714810860916769524325645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82291315849778874926140213 7714810860916769524325645)
                ·
                  refine ⟨2893054072843788571622117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7714810860916769524325645 2893054072843788571622117)
                  ·
                    refine ⟨542447638658210357179147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893054072843788571622117 542447638658210357179147)
                    ·
                      rfl

theorem cell23_3169239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_3169239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169239 prefixEnd_3169239 := by exact prefixLift 3169239
  have htrace : WordTrace (prefixWord ++ tailWord_3169239) baseStart_3169239 baseEnd_3169239 := by
    simpa [prefixWord, tailWord_3169239, baseEnd_3169239] using wordTrace_append hprefix tailTrace_3169239
  have hstable : (prefixWord ++ tailWord_3169239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169239).length < 2 ^ (prefixWord ++ tailWord_3169239).sum := by decide
  have hdescent : baseEnd_3169239 < baseStart_3169239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169249 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_3169249 : Nat := 118140960795 + 3169249 * 2 ^ 59
def prefixEnd_3169249 : Nat := 4983230072969 + 3 ^ 40 * 3169249 * 2
def baseEnd_3169249 : Nat := 1627348050781176032412395

theorem tailTrace_3169249 : CollatzResearch.WordTrace tailWord_3169249 prefixEnd_3169249 1627348050781176032412395 := by
  unfold tailWord_3169249
  simp only [CollatzResearch.WordTrace]
  refine ⟨115592007295359612482030801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77061338196906408321353867 115592007295359612482030801)
  ·
    refine ⟨86694005471519709361523101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115592007295359612482030801 86694005471519709361523101)
    ·
      refine ⟨32510252051819891010571163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86694005471519709361523101 32510252051819891010571163)
      ·
        refine ⟨48765378077729836515856745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32510252051819891010571163 48765378077729836515856745)
        ·
          refine ⟨36574033558297377386892559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48765378077729836515856745 36574033558297377386892559)
          ·
            refine ⟨54861050337446066080338839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36574033558297377386892559 54861050337446066080338839)
            ·
              refine ⟨82291575506169099120508259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54861050337446066080338839 82291575506169099120508259)
              ·
                refine ⟨123437363259253648680762389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82291575506169099120508259 123437363259253648680762389)
                ·
                  refine ⟨5786126402777514781910737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123437363259253648680762389 5786126402777514781910737)
                  ·
                    refine ⟨4339594802083136086433053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5786126402777514781910737 4339594802083136086433053)
                    ·
                      refine ⟨1627348050781176032412395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339594802083136086433053 1627348050781176032412395)
                      ·
                        rfl

theorem cell23_3169249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_3169249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169249 prefixEnd_3169249 := by exact prefixLift 3169249
  have htrace : WordTrace (prefixWord ++ tailWord_3169249) baseStart_3169249 baseEnd_3169249 := by
    simpa [prefixWord, tailWord_3169249, baseEnd_3169249] using wordTrace_append hprefix tailTrace_3169249
  have hstable : (prefixWord ++ tailWord_3169249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169249).length < 2 ^ (prefixWord ++ tailWord_3169249).sum := by decide
  have hdescent : baseEnd_3169249 < baseStart_3169249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169252 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 10]
def baseStart_3169252 : Nat := 118140960795 + 3169252 * 2 ^ 59
def prefixEnd_3169252 : Nat := 4983230072969 + 3 ^ 40 * 3169252 * 2
def baseEnd_3169252 : Nat := 180816621247015502297209

theorem tailTrace_3169252 : CollatzResearch.WordTrace tailWord_3169252 prefixEnd_3169252 180816621247015502297209 := by
  unfold tailWord_3169252
  simp only [CollatzResearch.WordTrace]
  refine ⟨57796058357174371997195005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77061411142899162662926673 57796058357174371997195005)
  ·
    refine ⟨21673521883940389498948127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57796058357174371997195005 21673521883940389498948127)
    ·
      refine ⟨32510282825910584248422191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21673521883940389498948127 32510282825910584248422191)
      ·
        refine ⟨48765424238865876372633287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32510282825910584248422191 48765424238865876372633287)
        ·
          refine ⟨73148136358298814558949931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48765424238865876372633287 73148136358298814558949931)
          ·
            refine ⟨109722204537448221838424897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73148136358298814558949931 109722204537448221838424897)
            ·
              refine ⟨82291653403086166378818673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109722204537448221838424897 82291653403086166378818673)
              ·
                refine ⟨61718740052314624784114005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82291653403086166378818673 61718740052314624784114005)
                ·
                  refine ⟨180816621247015502297209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 61718740052314624784114005 180816621247015502297209)
                  ·
                    rfl

theorem cell23_3169252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_3169252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169252 prefixEnd_3169252 := by exact prefixLift 3169252
  have htrace : WordTrace (prefixWord ++ tailWord_3169252) baseStart_3169252 baseEnd_3169252 := by
    simpa [prefixWord, tailWord_3169252, baseEnd_3169252] using wordTrace_append hprefix tailTrace_3169252
  have hstable : (prefixWord ++ tailWord_3169252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169252).length < 2 ^ (prefixWord ++ tailWord_3169252).sum := by decide
  have hdescent : baseEnd_3169252 < baseStart_3169252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169272 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3169272 : Nat := 118140960795 + 3169272 * 2 ^ 59
def prefixEnd_3169272 : Nat := 4983230072969 + 3 ^ 40 * 3169272 * 2
def baseEnd_3169272 : Nat := 1627359860836229442424789

theorem tailTrace_3169272 : CollatzResearch.WordTrace tailWord_3169272 prefixEnd_3169272 1627359860836229442424789 := by
  unfold tailWord_3169272
  simp only [CollatzResearch.WordTrace]
  refine ⟨57796423087138143705059035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77061897449517524940078713 57796423087138143705059035)
  ·
    refine ⟨86694634630707215557588553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57796423087138143705059035 86694634630707215557588553)
    ·
      refine ⟨65020975973030411668191415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86694634630707215557588553 65020975973030411668191415)
      ·
        refine ⟨97531463959545617502287123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65020975973030411668191415 97531463959545617502287123)
        ·
          refine ⟨146297195939318426253430685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97531463959545617502287123 146297195939318426253430685)
          ·
            refine ⟨54861448477244409845036507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146297195939318426253430685 54861448477244409845036507)
            ·
              refine ⟨82292172715866614767554761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54861448477244409845036507 82292172715866614767554761)
              ·
                refine ⟨61719129536899961075666071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82292172715866614767554761 61719129536899961075666071)
                ·
                  refine ⟨92578694305349941613499107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61719129536899961075666071 92578694305349941613499107)
                  ·
                    refine ⟨138868041458024912420248661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92578694305349941613499107 138868041458024912420248661)
                    ·
                      refine ⟨1627359860836229442424789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 138868041458024912420248661 1627359860836229442424789)
                      ·
                        rfl

theorem cell23_3169272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3169272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169272 prefixEnd_3169272 := by exact prefixLift 3169272
  have htrace : WordTrace (prefixWord ++ tailWord_3169272) baseStart_3169272 baseEnd_3169272 := by
    simpa [prefixWord, tailWord_3169272, baseEnd_3169272] using wordTrace_append hprefix tailTrace_3169272
  have hstable : (prefixWord ++ tailWord_3169272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169272).length < 2 ^ (prefixWord ++ tailWord_3169272).sum := by decide
  have hdescent : baseEnd_3169272 < baseStart_3169272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169290 : List Nat := [3, 1, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_3169290 : Nat := 118140960795 + 3169290 * 2 ^ 59
def prefixEnd_3169290 : Nat := 4983230072969 + 3 ^ 40 * 3169290 * 2
def baseEnd_3169290 : Nat := 542456367829336790666569

theorem tailTrace_3169290 : CollatzResearch.WordTrace tailWord_3169290 prefixEnd_3169290 542456367829336790666569 := by
  unfold tailWord_3169290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28898375672052769121068331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77062335125474050989515549 28898375672052769121068331)
  ·
    refine ⟨43347563508079153681602497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28898375672052769121068331 43347563508079153681602497)
    ·
      refine ⟨32510672631059365261201873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43347563508079153681602497 32510672631059365261201873)
      ·
        refine ⟨24383004473294523945901405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32510672631059365261201873 24383004473294523945901405)
        ·
          refine ⟨9143626677485446479713027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24383004473294523945901405 9143626677485446479713027)
          ·
            refine ⟨13715440016228169719569541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9143626677485446479713027 13715440016228169719569541)
            ·
              refine ⟨2571645003042781822419289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13715440016228169719569541 2571645003042781822419289)
              ·
                refine ⟨1928733752282086366814467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571645003042781822419289 1928733752282086366814467)
                ·
                  refine ⟨2893100628423129550221701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928733752282086366814467 2893100628423129550221701)
                  ·
                    refine ⟨542456367829336790666569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893100628423129550221701 542456367829336790666569)
                    ·
                      rfl

theorem cell23_3169290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_3169290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169290 prefixEnd_3169290 := by exact prefixLift 3169290
  have htrace : WordTrace (prefixWord ++ tailWord_3169290) baseStart_3169290 baseEnd_3169290 := by
    simpa [prefixWord, tailWord_3169290, baseEnd_3169290] using wordTrace_append hprefix tailTrace_3169290
  have hstable : (prefixWord ++ tailWord_3169290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169290).length < 2 ^ (prefixWord ++ tailWord_3169290).sum := by decide
  have hdescent : baseEnd_3169290 < baseStart_3169290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169306 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2]
def baseStart_3169306 : Nat := 118140960795 + 3169306 * 2 ^ 59
def prefixEnd_3169306 : Nat := 4983230072969 + 3 ^ 40 * 3169306 * 2
def baseEnd_3169306 : Nat := 1627377319178482309399633

theorem tailTrace_3169306 : CollatzResearch.WordTrace tailWord_3169306 prefixEnd_3169306 1627377319178482309399633 := by
  unfold tailWord_3169306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28898521564038277804213943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77062724170768740811237181 28898521564038277804213943)
  ·
    refine ⟨43347782346057416706320915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28898521564038277804213943 43347782346057416706320915)
    ·
      refine ⟨65021673519086125059481373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43347782346057416706320915 65021673519086125059481373)
      ·
        refine ⟨24383127569657296897305515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65021673519086125059481373 24383127569657296897305515)
        ·
          refine ⟨36574691354485945345958273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24383127569657296897305515 36574691354485945345958273)
          ·
            refine ⟨27431018515864459009468705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36574691354485945345958273 27431018515864459009468705)
            ·
              refine ⟨20573263886898344257101529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27431018515864459009468705 20573263886898344257101529)
              ·
                refine ⟨15429947915173758192826147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20573263886898344257101529 15429947915173758192826147)
                ·
                  refine ⟨23144921872760637289239221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15429947915173758192826147 23144921872760637289239221)
                  ·
                    refine ⟨2169836425571309745866177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23144921872760637289239221 2169836425571309745866177)
                    ·
                      refine ⟨1627377319178482309399633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169836425571309745866177 1627377319178482309399633)
                      ·
                        rfl

theorem cell23_3169306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_3169306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169306 prefixEnd_3169306 := by exact prefixLift 3169306
  have htrace : WordTrace (prefixWord ++ tailWord_3169306) baseStart_3169306 baseEnd_3169306 := by
    simpa [prefixWord, tailWord_3169306, baseEnd_3169306] using wordTrace_append hprefix tailTrace_3169306
  have hstable : (prefixWord ++ tailWord_3169306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169306).length < 2 ^ (prefixWord ++ tailWord_3169306).sum := by decide
  have hdescent : baseEnd_3169306 < baseStart_3169306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169313 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_3169313 : Nat := 118140960795 + 3169313 * 2 ^ 59
def prefixEnd_3169313 : Nat := 4983230072969 + 3 ^ 40 * 3169313 * 2
def baseEnd_3169313 : Nat := 1627380913543063782012101

theorem tailTrace_3169313 : CollatzResearch.WordTrace tailWord_3169313 prefixEnd_3169313 1627380913543063782012101 := by
  unfold tailWord_3169313
  simp only [CollatzResearch.WordTrace]
  refine ⟨115594341567127751412360593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77062894378085167608240395 115594341567127751412360593)
  ·
    refine ⟨86695756175345813559270445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115594341567127751412360593 86695756175345813559270445)
    ·
      refine ⟨32510908565754680084726417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86695756175345813559270445 32510908565754680084726417)
      ·
        refine ⟨24383181424316010063544813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32510908565754680084726417 24383181424316010063544813)
        ·
          refine ⟨9143693034118503773829305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24383181424316010063544813 9143693034118503773829305)
          ·
            refine ⟨6857769775588877830371979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9143693034118503773829305 6857769775588877830371979)
            ·
              refine ⟨10286654663383316745557969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6857769775588877830371979 10286654663383316745557969)
              ·
                refine ⟨7714990997537487559168477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10286654663383316745557969 7714990997537487559168477)
                ·
                  refine ⟨2893121624076557834688179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7714990997537487559168477 2893121624076557834688179)
                  ·
                    refine ⟨4339682436114836752032269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2893121624076557834688179 4339682436114836752032269)
                    ·
                      refine ⟨1627380913543063782012101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339682436114836752032269 1627380913543063782012101)
                      ·
                        rfl

theorem cell23_3169313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_3169313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169313 prefixEnd_3169313 := by exact prefixLift 3169313
  have htrace : WordTrace (prefixWord ++ tailWord_3169313) baseStart_3169313 baseEnd_3169313 := by
    simpa [prefixWord, tailWord_3169313, baseEnd_3169313] using wordTrace_append hprefix tailTrace_3169313
  have hstable : (prefixWord ++ tailWord_3169313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169313).length < 2 ^ (prefixWord ++ tailWord_3169313).sum := by decide
  have hdescent : baseEnd_3169313 < baseStart_3169313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169316 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_3169316 : Nat := 118140960795 + 3169316 * 2 ^ 59
def prefixEnd_3169316 : Nat := 4983230072969 + 3 ^ 40 * 3169316 * 2
def baseEnd_3169316 : Nat := 542460817995009090091529

theorem tailTrace_3169316 : CollatzResearch.WordTrace tailWord_3169316 prefixEnd_3169316 542460817995009090091529 := by
  unfold tailWord_3169316
  simp only [CollatzResearch.WordTrace]
  refine ⟨57797225493058441462359901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77062967324077921949813201 57797225493058441462359901)
  ·
    refine ⟨21673959559896915548384963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57797225493058441462359901 21673959559896915548384963)
    ·
      refine ⟨32510939339845373322577445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21673959559896915548384963 32510939339845373322577445)
      ·
        refine ⟨6095801126221007497983271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32510939339845373322577445 6095801126221007497983271)
        ·
          refine ⟨9143701689331511246974907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6095801126221007497983271 9143701689331511246974907)
          ·
            refine ⟨13715552533997266870462361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9143701689331511246974907 13715552533997266870462361)
            ·
              refine ⟨10286664400497950152846771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13715552533997266870462361 10286664400497950152846771)
              ·
                refine ⟨15429996600746925229270157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10286664400497950152846771 15429996600746925229270157)
                ·
                  refine ⟨5786248725280096960976309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15429996600746925229270157 5786248725280096960976309)
                  ·
                    refine ⟨542460817995009090091529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5786248725280096960976309 542460817995009090091529)
                    ·
                      rfl

theorem cell23_3169316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_3169316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169316 prefixEnd_3169316 := by exact prefixLift 3169316
  have htrace : WordTrace (prefixWord ++ tailWord_3169316) baseStart_3169316 baseEnd_3169316 := by
    simpa [prefixWord, tailWord_3169316, baseEnd_3169316] using wordTrace_append hprefix tailTrace_3169316
  have hstable : (prefixWord ++ tailWord_3169316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169316).length < 2 ^ (prefixWord ++ tailWord_3169316).sum := by decide
  have hdescent : baseEnd_3169316 < baseStart_3169316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169329 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 1, 6]
def baseStart_3169329 : Nat := 118140960795 + 3169329 * 2 ^ 59
def prefixEnd_3169329 : Nat := 4983230072969 + 3 ^ 40 * 3169329 * 2
def baseEnd_3169329 : Nat := 542463043077845239804009

theorem tailTrace_3169329 : CollatzResearch.WordTrace tailWord_3169329 prefixEnd_3169329 542463043077845239804009 := by
  unfold tailWord_3169329
  simp only [CollatzResearch.WordTrace]
  refine ⟨115594925135069786144943041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77063283423379857429962027 115594925135069786144943041)
  ·
    refine ⟨86696193851302339608707281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115594925135069786144943041 86696193851302339608707281)
    ·
      refine ⟨65022145388476754706530461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86696193851302339608707281 65022145388476754706530461)
      ·
        refine ⟨24383304520678783014948923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65022145388476754706530461 24383304520678783014948923)
        ·
          refine ⟨36574956781018174522423385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24383304520678783014948923 36574956781018174522423385)
          ·
            refine ⟨27431217585763630891817539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36574956781018174522423385 27431217585763630891817539)
            ·
              refine ⟨41146826378645446337726309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27431217585763630891817539 41146826378645446337726309)
              ·
                refine ⟨7715029945996021188323683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41146826378645446337726309 7715029945996021188323683)
                ·
                  refine ⟨11572544918994031782485525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715029945996021188323683 11572544918994031782485525)
                  ·
                    refine ⟨542463043077845239804009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11572544918994031782485525 542463043077845239804009)
                    ·
                      rfl

theorem cell23_3169329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_3169329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169329 prefixEnd_3169329 := by exact prefixLift 3169329
  have htrace : WordTrace (prefixWord ++ tailWord_3169329) baseStart_3169329 baseEnd_3169329 := by
    simpa [prefixWord, tailWord_3169329, baseEnd_3169329] using wordTrace_append hprefix tailTrace_3169329
  have hstable : (prefixWord ++ tailWord_3169329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169329).length < 2 ^ (prefixWord ++ tailWord_3169329).sum := by decide
  have hdescent : baseEnd_3169329 < baseStart_3169329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169330 : List Nat := [3, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3]
def baseStart_3169330 : Nat := 118140960795 + 3169330 * 2 ^ 59
def prefixEnd_3169330 : Nat := 4983230072969 + 3 ^ 40 * 3169330 * 2
def baseEnd_3169330 : Nat := 1627389642714190215499523

theorem tailTrace_3169330 : CollatzResearch.WordTrace tailWord_3169330 prefixEnd_3169330 1627389642714190215499523 := by
  unfold tailWord_3169330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28898740402016540828932361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77063307738710775543819629 28898740402016540828932361)
  ·
    refine ⟨21674055301512405621699271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28898740402016540828932361 21674055301512405621699271)
    ·
      refine ⟨32511082952268608432548907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21674055301512405621699271 32511082952268608432548907)
      ·
        refine ⟨48766624428402912648823361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32511082952268608432548907 48766624428402912648823361)
        ·
          refine ⟨36574968321302184486617521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48766624428402912648823361 36574968321302184486617521)
          ·
            refine ⟨27431226240976638364963141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36574968321302184486617521 27431226240976638364963141)
            ·
              refine ⟨5143354920183119693430589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27431226240976638364963141 5143354920183119693430589)
              ·
                refine ⟨1928758095068669885036471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5143354920183119693430589 1928758095068669885036471)
                ·
                  refine ⟨2893137142603004827554707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928758095068669885036471 2893137142603004827554707)
                  ·
                    refine ⟨4339705713904507241332061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2893137142603004827554707 4339705713904507241332061)
                    ·
                      refine ⟨1627389642714190215499523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4339705713904507241332061 1627389642714190215499523)
                      ·
                        rfl

theorem cell23_3169330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_3169330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169330 prefixEnd_3169330 := by exact prefixLift 3169330
  have htrace : WordTrace (prefixWord ++ tailWord_3169330) baseStart_3169330 baseEnd_3169330 := by
    simpa [prefixWord, tailWord_3169330, baseEnd_3169330] using wordTrace_append hprefix tailTrace_3169330
  have hstable : (prefixWord ++ tailWord_3169330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169330).length < 2 ^ (prefixWord ++ tailWord_3169330).sum := by decide
  have hdescent : baseEnd_3169330 < baseStart_3169330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169349 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_3169349 : Nat := 118140960795 + 3169349 * 2 ^ 59
def prefixEnd_3169349 : Nat := 4983230072969 + 3 ^ 40 * 3169349 * 2
def baseEnd_3169349 : Nat := 1627399398846625641161935

theorem tailTrace_3169349 : CollatzResearch.WordTrace tailWord_3169349 prefixEnd_3169349 1627399398846625641161935 := by
  unfold tailWord_3169349
  simp only [CollatzResearch.WordTrace]
  refine ⟨115595654594997329560671101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77063769729998219707114067 115595654594997329560671101)
  ·
    refine ⟨43348370473123998585251663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115595654594997329560671101 43348370473123998585251663)
    ·
      refine ⟨65022555709685997877877495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43348370473123998585251663 65022555709685997877877495)
      ·
        refine ⟨97533833564528996816816243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65022555709685997877877495 97533833564528996816816243)
        ·
          refine ⟨146300750346793495225224365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97533833564528996816816243 146300750346793495225224365)
          ·
            refine ⟨54862781380047560709459137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146300750346793495225224365 54862781380047560709459137)
            ·
              refine ⟨41147086035035670532094353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54862781380047560709459137 41147086035035670532094353)
              ·
                refine ⟨30860314526276752899070765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41147086035035670532094353 30860314526276752899070765)
                ·
                  refine ⟨11572617947353782337151537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30860314526276752899070765 11572617947353782337151537)
                  ·
                    refine ⟨8679463460515336752863653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11572617947353782337151537 8679463460515336752863653)
                    ·
                      refine ⟨1627399398846625641161935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8679463460515336752863653 1627399398846625641161935)
                      ·
                        rfl

theorem cell23_3169349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_3169349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169349 prefixEnd_3169349 := by exact prefixLift 3169349
  have htrace : WordTrace (prefixWord ++ tailWord_3169349) baseStart_3169349 baseEnd_3169349 := by
    simpa [prefixWord, tailWord_3169349, baseEnd_3169349] using wordTrace_append hprefix tailTrace_3169349
  have hstable : (prefixWord ++ tailWord_3169349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169349).length < 2 ^ (prefixWord ++ tailWord_3169349).sum := by decide
  have hdescent : baseEnd_3169349 < baseStart_3169349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169399 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_3169399 : Nat := 118140960795 + 3169399 * 2 ^ 59
def prefixEnd_3169399 : Nat := 4983230072969 + 3 ^ 40 * 3169399 * 2
def baseEnd_3169399 : Nat := 1627425072879350445536705

theorem tailTrace_3169399 : CollatzResearch.WordTrace tailWord_3169399 prefixEnd_3169399 1627425072879350445536705 := by
  unfold tailWord_3169399
  simp only [CollatzResearch.WordTrace]
  refine ⟨115597478244816188099991251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77064985496544125399994167 115597478244816188099991251)
  ·
    refine ⟨173396217367224282149986877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115597478244816188099991251 173396217367224282149986877)
    ·
      refine ⟨65023581512709105806245079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173396217367224282149986877 65023581512709105806245079)
      ·
        refine ⟨97535372269063658709367619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65023581512709105806245079 97535372269063658709367619)
        ·
          refine ⟨146303058403595488064051429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97535372269063658709367619 146303058403595488064051429)
          ·
            refine ⟨27431823450674154012009643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146303058403595488064051429 27431823450674154012009643)
            ·
              refine ⟨41147735176011231018014465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27431823450674154012009643 41147735176011231018014465)
              ·
                refine ⟨30860801382008423263510849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41147735176011231018014465 30860801382008423263510849)
                ·
                  refine ⟨23145601036506317447633137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30860801382008423263510849 23145601036506317447633137)
                  ·
                    refine ⟨17359200777379738085724853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23145601036506317447633137 17359200777379738085724853)
                    ·
                      refine ⟨1627425072879350445536705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17359200777379738085724853 1627425072879350445536705)
                      ·
                        rfl

theorem cell23_3169399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_3169399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169399 prefixEnd_3169399 := by exact prefixLift 3169399
  have htrace : WordTrace (prefixWord ++ tailWord_3169399) baseStart_3169399 baseEnd_3169399 := by
    simpa [prefixWord, tailWord_3169399, baseEnd_3169399] using wordTrace_append hprefix tailTrace_3169399
  have hstable : (prefixWord ++ tailWord_3169399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169399).length < 2 ^ (prefixWord ++ tailWord_3169399).sum := by decide
  have hdescent : baseEnd_3169399 < baseStart_3169399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169419 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 2, 6]
def baseStart_3169419 : Nat := 118140960795 + 3169419 * 2 ^ 59
def prefixEnd_3169419 : Nat := 4983230072969 + 3 ^ 40 * 3169419 * 2
def baseEnd_3169419 : Nat := 542478447497480122428871

theorem tailTrace_3169419 : CollatzResearch.WordTrace tailWord_3169419 prefixEnd_3169419 542478447497480122428871 := by
  unfold tailWord_3169419
  simp only [CollatzResearch.WordTrace]
  refine ⟨115598207704743731515719311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77065471803162487677146207 115598207704743731515719311)
  ·
    refine ⟨173397311557115597273578967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115598207704743731515719311 173397311557115597273578967)
    ·
      refine ⟨260095967335673395910368451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173397311557115597273578967 260095967335673395910368451)
      ·
        refine ⟨390143951003510093865552677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260095967335673395910368451 390143951003510093865552677)
        ·
          refine ⟨73151990813158142599791127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390143951003510093865552677 73151990813158142599791127)
          ·
            refine ⟨109727986219737213899686691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73151990813158142599791127 109727986219737213899686691)
            ·
              refine ⟨164591979329605820849530037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109727986219737213899686691 164591979329605820849530037)
              ·
                refine ⟨15430498062150545704643441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164591979329605820849530037 15430498062150545704643441)
                ·
                  refine ⟨11572873546612909278482581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15430498062150545704643441 11572873546612909278482581)
                  ·
                    refine ⟨542478447497480122428871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11572873546612909278482581 542478447497480122428871)
                    ·
                      rfl

theorem cell23_3169419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 6].length) (baseStart_3169419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169419 prefixEnd_3169419 := by exact prefixLift 3169419
  have htrace : WordTrace (prefixWord ++ tailWord_3169419) baseStart_3169419 baseEnd_3169419 := by
    simpa [prefixWord, tailWord_3169419, baseEnd_3169419] using wordTrace_append hprefix tailTrace_3169419
  have hstable : (prefixWord ++ tailWord_3169419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169419).length < 2 ^ (prefixWord ++ tailWord_3169419).sum := by decide
  have hdescent : baseEnd_3169419 < baseStart_3169419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169443 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 6, 2, 2]
def baseStart_3169443 : Nat := 118140960795 + 3169443 * 2 ^ 59
def prefixEnd_3169443 : Nat := 4983230072969 + 3 ^ 40 * 3169443 * 2
def baseEnd_3169443 : Nat := 1627447666028148273386503

theorem tailTrace_3169443 : CollatzResearch.WordTrace tailWord_3169443 prefixEnd_3169443 1627447666028148273386503 := by
  unfold tailWord_3169443
  simp only [CollatzResearch.WordTrace]
  refine ⟨115599083056656783614592983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77066055371104522409728655 115599083056656783614592983)
  ·
    refine ⟨173398624584985175421889475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115599083056656783614592983 173398624584985175421889475)
    ·
      refine ⟨260097936877477763132834213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173398624584985175421889475 260097936877477763132834213)
      ·
        refine ⟨48768363164527080587406415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260097936877477763132834213 48768363164527080587406415)
        ·
          refine ⟨73152544746790620881109623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48768363164527080587406415 73152544746790620881109623)
          ·
            refine ⟨109728817120185931321664435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73152544746790620881109623 109728817120185931321664435)
            ·
              refine ⟨164593225680278896982496653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109728817120185931321664435 164593225680278896982496653)
              ·
                refine ⟨61722459630104586368436245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164593225680278896982496653 61722459630104586368436245)
                ·
                  refine ⟨2893240295161152486020449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61722459630104586368436245 2893240295161152486020449)
                  ·
                    refine ⟨2169930221370864364515337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2893240295161152486020449 2169930221370864364515337)
                    ·
                      refine ⟨1627447666028148273386503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169930221370864364515337 1627447666028148273386503)
                      ·
                        rfl

theorem cell23_3169443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_3169443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169443 prefixEnd_3169443 := by exact prefixLift 3169443
  have htrace : WordTrace (prefixWord ++ tailWord_3169443) baseStart_3169443 baseEnd_3169443 := by
    simpa [prefixWord, tailWord_3169443, baseEnd_3169443] using wordTrace_append hprefix tailTrace_3169443
  have hstable : (prefixWord ++ tailWord_3169443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169443).length < 2 ^ (prefixWord ++ tailWord_3169443).sum := by decide
  have hdescent : baseEnd_3169443 < baseStart_3169443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169459 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7]
def baseStart_3169459 : Nat := 118140960795 + 3169459 * 2 ^ 59
def prefixEnd_3169459 : Nat := 4983230072969 + 3 ^ 40 * 3169459 * 2
def baseEnd_3169459 : Nat := 1627455881718620210786429

theorem tailTrace_3169459 : CollatzResearch.WordTrace tailWord_3169459 prefixEnd_3169459 1627455881718620210786429 := by
  unfold tailWord_3169459
  simp only [CollatzResearch.WordTrace]
  refine ⟨115599666624598818347175431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77066444416399212231450287 115599666624598818347175431)
  ·
    refine ⟨173399499936898227520763147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115599666624598818347175431 173399499936898227520763147)
    ·
      refine ⟨260099249905347341281144721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173399499936898227520763147 260099249905347341281144721)
      ·
        refine ⟨195074437429010505960858541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260099249905347341281144721 195074437429010505960858541)
        ·
          refine ⟨73152914035878939735321953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195074437429010505960858541 73152914035878939735321953)
          ·
            refine ⟨54864685526909204801491465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73152914035878939735321953 54864685526909204801491465)
            ·
              refine ⟨41148514145181903601118599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54864685526909204801491465 41148514145181903601118599)
              ·
                refine ⟨61722771217772855401677899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41148514145181903601118599 61722771217772855401677899)
                ·
                  refine ⟨92584156826659283102516849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61722771217772855401677899 92584156826659283102516849)
                  ·
                    refine ⟨69438117619994462326887637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92584156826659283102516849 69438117619994462326887637)
                    ·
                      refine ⟨1627455881718620210786429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69438117619994462326887637 1627455881718620210786429)
                      ·
                        rfl

theorem cell23_3169459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_3169459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169459 prefixEnd_3169459 := by exact prefixLift 3169459
  have htrace : WordTrace (prefixWord ++ tailWord_3169459) baseStart_3169459 baseEnd_3169459 := by
    simpa [prefixWord, tailWord_3169459, baseEnd_3169459] using wordTrace_append hprefix tailTrace_3169459
  have hstable : (prefixWord ++ tailWord_3169459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169459).length < 2 ^ (prefixWord ++ tailWord_3169459).sum := by decide
  have hdescent : baseEnd_3169459 < baseStart_3169459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169473 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3169473 : Nat := 118140960795 + 3169473 * 2 ^ 59
def prefixEnd_3169473 : Nat := 4983230072969 + 3 ^ 40 * 3169473 * 2
def baseEnd_3169473 : Nat := 1627463070447783156011365

theorem tailTrace_3169473 : CollatzResearch.WordTrace tailWord_3169473 prefixEnd_3169473 1627463070447783156011365 := by
  unfold tailWord_3169473
  simp only [CollatzResearch.WordTrace]
  refine ⟨115600177246548098738185073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77066784831032065825456715 115600177246548098738185073)
  ·
    refine ⟨86700132934911074053638805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115600177246548098738185073 86700132934911074053638805)
    ·
      refine ⟨4064068731323956596264319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86700132934911074053638805 4064068731323956596264319)
      ·
        refine ⟨6096103096985934894396479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064068731323956596264319 6096103096985934894396479)
        ·
          refine ⟨9144154645478902341594719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6096103096985934894396479 9144154645478902341594719)
          ·
            refine ⟨13716231968218353512392079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9144154645478902341594719 13716231968218353512392079)
            ·
              refine ⟨20574347952327530268588119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13716231968218353512392079 20574347952327530268588119)
              ·
                refine ⟨30861521928491295402882179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20574347952327530268588119 30861521928491295402882179)
                ·
                  refine ⟨46292282892736943104323269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30861521928491295402882179 46292282892736943104323269)
                  ·
                    refine ⟨8679803042388176832060613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46292282892736943104323269 8679803042388176832060613)
                    ·
                      refine ⟨1627463070447783156011365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8679803042388176832060613 1627463070447783156011365)
                      ·
                        rfl

theorem cell23_3169473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3169473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169473 prefixEnd_3169473 := by exact prefixLift 3169473
  have htrace : WordTrace (prefixWord ++ tailWord_3169473) baseStart_3169473 baseEnd_3169473 := by
    simpa [prefixWord, tailWord_3169473, baseEnd_3169473] using wordTrace_append hprefix tailTrace_3169473
  have hstable : (prefixWord ++ tailWord_3169473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169473).length < 2 ^ (prefixWord ++ tailWord_3169473).sum := by decide
  have hdescent : baseEnd_3169473 < baseStart_3169473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8]
def baseStart_3169499 : Nat := 118140960795 + 3169499 * 2 ^ 59
def prefixEnd_3169499 : Nat := 4983230072969 + 3 ^ 40 * 3169499 * 2
def baseEnd_3169499 : Nat := 1627476420944800054286245

theorem tailTrace_3169499 : CollatzResearch.WordTrace tailWord_3169499 prefixEnd_3169499 1627476420944800054286245 := by
  unfold tailWord_3169499
  simp only [CollatzResearch.WordTrace]
  refine ⟨115601125544453905178631551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77067417029635936785754367 115601125544453905178631551)
  ·
    refine ⟨173401688316680857767947327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115601125544453905178631551 173401688316680857767947327)
    ·
      refine ⟨260102532475021286651920991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173401688316680857767947327 260102532475021286651920991)
      ·
        refine ⟨390153798712531929977881487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260102532475021286651920991 390153798712531929977881487)
        ·
          refine ⟨585230698068797894966822231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390153798712531929977881487 585230698068797894966822231)
          ·
            refine ⟨877846047103196842450233347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585230698068797894966822231 877846047103196842450233347)
            ·
              refine ⟨1316769070654795263675350021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877846047103196842450233347 1316769070654795263675350021)
              ·
                refine ⟨246894200747774111939128129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1316769070654795263675350021 246894200747774111939128129)
                ·
                  refine ⟨185170650560830583954346097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246894200747774111939128129 185170650560830583954346097)
                  ·
                    refine ⟨138877987920622937965759573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185170650560830583954346097 138877987920622937965759573)
                    ·
                      refine ⟨1627476420944800054286245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 138877987920622937965759573 1627476420944800054286245)
                      ·
                        rfl

theorem cell23_3169499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_3169499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169499 prefixEnd_3169499 := by exact prefixLift 3169499
  have htrace : WordTrace (prefixWord ++ tailWord_3169499) baseStart_3169499 baseEnd_3169499 := by
    simpa [prefixWord, tailWord_3169499, baseEnd_3169499] using wordTrace_append hprefix tailTrace_3169499
  have hstable : (prefixWord ++ tailWord_3169499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169499).length < 2 ^ (prefixWord ++ tailWord_3169499).sum := by decide
  have hdescent : baseEnd_3169499 < baseStart_3169499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169511 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3169511 : Nat := 118140960795 + 3169511 * 2 ^ 59
def prefixEnd_3169511 : Nat := 4983230072969 + 3 ^ 40 * 3169511 * 2
def baseEnd_3169511 : Nat := 1627482582712654007336191

theorem tailTrace_3169511 : CollatzResearch.WordTrace tailWord_3169511 prefixEnd_3169511 1627482582712654007336191 := by
  unfold tailWord_3169511
  simp only [CollatzResearch.WordTrace]
  refine ⟨115601563220410431228068387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77067708813606954152045591 115601563220410431228068387)
  ·
    refine ⟨173402344830615646842102581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115601563220410431228068387 173402344830615646842102581)
    ·
      refine ⟨16256469827870216891447117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173402344830615646842102581 16256469827870216891447117)
      ·
        refine ⟨6096176185451331334292669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16256469827870216891447117 6096176185451331334292669)
        ·
          refine ⟨2286066069544249250359751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6096176185451331334292669 2286066069544249250359751)
          ·
            refine ⟨3429099104316373875539627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286066069544249250359751 3429099104316373875539627)
            ·
              refine ⟨5143648656474560813309441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429099104316373875539627 5143648656474560813309441)
              ·
                refine ⟨3857736492355920609982081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143648656474560813309441 3857736492355920609982081)
                ·
                  refine ⟨2893302369266940457486561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3857736492355920609982081 2893302369266940457486561)
                  ·
                    refine ⟨2169976776950205343114921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2893302369266940457486561 2169976776950205343114921)
                    ·
                      refine ⟨1627482582712654007336191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2169976776950205343114921 1627482582712654007336191)
                      ·
                        rfl

theorem cell23_3169511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3169511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169511 prefixEnd_3169511 := by exact prefixLift 3169511
  have htrace : WordTrace (prefixWord ++ tailWord_3169511) baseStart_3169511 baseEnd_3169511 := by
    simpa [prefixWord, tailWord_3169511, baseEnd_3169511] using wordTrace_append hprefix tailTrace_3169511
  have hstable : (prefixWord ++ tailWord_3169511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169511).length < 2 ^ (prefixWord ++ tailWord_3169511).sum := by decide
  have hdescent : baseEnd_3169511 < baseStart_3169511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169546 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3169546 : Nat := 118140960795 + 3169546 * 2 ^ 59
def prefixEnd_3169546 : Nat := 4983230072969 + 3 ^ 40 * 3169546 * 2
def baseEnd_3169546 : Nat := 1627500554535561370398529

theorem tailTrace_3169546 : CollatzResearch.WordTrace tailWord_3169546 prefixEnd_3169546 1627500554535561370398529 := by
  unfold tailWord_3169546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28900709943820908051398123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77068559850189088137061661 28900709943820908051398123)
  ·
    refine ⟨43351064915731362077097185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28900709943820908051398123 43351064915731362077097185)
    ·
      refine ⟨32513298686798521557822889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43351064915731362077097185 32513298686798521557822889)
      ·
        refine ⟨24384974015098891168367167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32513298686798521557822889 24384974015098891168367167)
        ·
          refine ⟨36577461022648336752550751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24384974015098891168367167 36577461022648336752550751)
          ·
            refine ⟨54866191533972505128826127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36577461022648336752550751 54866191533972505128826127)
            ·
              refine ⟨82299287300958757693239191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54866191533972505128826127 82299287300958757693239191)
              ·
                refine ⟨123448930951438136539858787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82299287300958757693239191 123448930951438136539858787)
                ·
                  refine ⟨185173396427157204809788181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123448930951438136539858787 185173396427157204809788181)
                  ·
                    refine ⟨8680002957522993975458821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 185173396427157204809788181 8680002957522993975458821)
                    ·
                      refine ⟨1627500554535561370398529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8680002957522993975458821 1627500554535561370398529)
                      ·
                        rfl

theorem cell23_3169546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3169546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169546 prefixEnd_3169546 := by exact prefixLift 3169546
  have htrace : WordTrace (prefixWord ++ tailWord_3169546) baseStart_3169546 baseEnd_3169546 := by
    simpa [prefixWord, tailWord_3169546, baseEnd_3169546] using wordTrace_append hprefix tailTrace_3169546
  have hstable : (prefixWord ++ tailWord_3169546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169546).length < 2 ^ (prefixWord ++ tailWord_3169546).sum := by decide
  have hdescent : baseEnd_3169546 < baseStart_3169546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169553 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_3169553 : Nat := 118140960795 + 3169553 * 2 ^ 59
def prefixEnd_3169553 : Nat := 4983230072969 + 3 ^ 40 * 3169553 * 2
def baseEnd_3169553 : Nat := 1627504148900142843010997

theorem tailTrace_3169553 : CollatzResearch.WordTrace tailWord_3169553 prefixEnd_3169553 1627504148900142843010997 := by
  unfold tailWord_3169553
  simp only [CollatzResearch.WordTrace]
  refine ⟨115603095086258272401097313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77068730057505514934064875 115603095086258272401097313)
  ·
    refine ⟨86702321314693704300822985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115603095086258272401097313 86702321314693704300822985)
    ·
      refine ⟨65026740986020278225617239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86702321314693704300822985 65026740986020278225617239)
      ·
        refine ⟨97540111479030417338425859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65026740986020278225617239 97540111479030417338425859)
        ·
          refine ⟨146310167218545626007638789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97540111479030417338425859 146310167218545626007638789)
          ·
            refine ⟨27433156353477304876432273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146310167218545626007638789 27433156353477304876432273)
            ·
              refine ⟨20574867265107978657324205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27433156353477304876432273 20574867265107978657324205)
              ·
                refine ⟨7715575224415491996496577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20574867265107978657324205 7715575224415491996496577)
                ·
                  refine ⟨5786681418311618997372433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7715575224415491996496577 5786681418311618997372433)
                  ·
                    refine ⟨4340011063733714248029325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5786681418311618997372433 4340011063733714248029325)
                    ·
                      refine ⟨1627504148900142843010997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4340011063733714248029325 1627504148900142843010997)
                      ·
                        rfl

theorem cell23_3169553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_3169553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169553 prefixEnd_3169553 := by exact prefixLift 3169553
  have htrace : WordTrace (prefixWord ++ tailWord_3169553) baseStart_3169553 baseEnd_3169553 := by
    simpa [prefixWord, tailWord_3169553, baseEnd_3169553] using wordTrace_append hprefix tailTrace_3169553
  have hstable : (prefixWord ++ tailWord_3169553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169553).length < 2 ^ (prefixWord ++ tailWord_3169553).sum := by decide
  have hdescent : baseEnd_3169553 < baseStart_3169553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169617 : List Nat := [1, 2, 2, 1, 4, 1, 2, 5, 1, 1, 3]
def baseStart_3169617 : Nat := 118140960795 + 3169617 * 2 ^ 59
def prefixEnd_3169617 : Nat := 4983230072969 + 3 ^ 40 * 3169617 * 2
def baseEnd_3169617 : Nat := 1627537011662030592610703

theorem tailTrace_3169617 : CollatzResearch.WordTrace tailWord_3169617 prefixEnd_3169617 1627537011662030592610703 := by
  unfold tailWord_3169617
  simp only [CollatzResearch.WordTrace]
  refine ⟨115605429358026411331427105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77070286238684274220951403 115605429358026411331427105)
  ·
    refine ⟨86704072018519808498570329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115605429358026411331427105 86704072018519808498570329)
    ·
      refine ⟨65028054013889856373927747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86704072018519808498570329 65028054013889856373927747)
      ·
        refine ⟨97542081020834784560891621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65028054013889856373927747 97542081020834784560891621)
        ·
          refine ⟨18289140191406522105167179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97542081020834784560891621 18289140191406522105167179)
          ·
            refine ⟨27433710287109783157750769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18289140191406522105167179 27433710287109783157750769)
            ·
              refine ⟨20575282715332337368313077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27433710287109783157750769 20575282715332337368313077)
              ·
                refine ⟨1928932754562406628279351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20575282715332337368313077 1928932754562406628279351)
                ·
                  refine ⟨2893399131843609942419027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928932754562406628279351 2893399131843609942419027)
                  ·
                    refine ⟨4340098697765414913628541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2893399131843609942419027 4340098697765414913628541)
                    ·
                      refine ⟨1627537011662030592610703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4340098697765414913628541 1627537011662030592610703)
                      ·
                        rfl

theorem cell23_3169617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_3169617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169617 prefixEnd_3169617 := by exact prefixLift 3169617
  have htrace : WordTrace (prefixWord ++ tailWord_3169617) baseStart_3169617 baseEnd_3169617 := by
    simpa [prefixWord, tailWord_3169617, baseEnd_3169617] using wordTrace_append hprefix tailTrace_3169617
  have hstable : (prefixWord ++ tailWord_3169617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169617).length < 2 ^ (prefixWord ++ tailWord_3169617).sum := by decide
  have hdescent : baseEnd_3169617 < baseStart_3169617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169633 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 4, 4]
def baseStart_3169633 : Nat := 118140960795 + 3169633 * 2 ^ 59
def prefixEnd_3169633 : Nat := 4983230072969 + 3 ^ 40 * 3169633 * 2
def baseEnd_3169633 : Nat := 542515075784167510003543

theorem tailTrace_3169633 : CollatzResearch.WordTrace tailWord_3169633 prefixEnd_3169633 542515075784167510003543 := by
  unfold tailWord_3169633
  simp only [CollatzResearch.WordTrace]
  refine ⟨115606012925968446064009553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77070675283978964042673035 115606012925968446064009553)
  ·
    refine ⟨86704509694476334548007165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115606012925968446064009553 86704509694476334548007165)
    ·
      refine ⟨32514191135428625455502687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86704509694476334548007165 32514191135428625455502687)
      ·
        refine ⟨48771286703142938183254031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32514191135428625455502687 48771286703142938183254031)
        ·
          refine ⟨73156930054714407274881047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48771286703142938183254031 73156930054714407274881047)
          ·
            refine ⟨109735395082071610912321571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73156930054714407274881047 109735395082071610912321571)
            ·
              refine ⟨164603092623107416368482357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109735395082071610912321571 164603092623107416368482357)
              ·
                refine ⟨15431539933416320284545221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164603092623107416368482357 15431539933416320284545221)
                ·
                  refine ⟨2893413737515560053352229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15431539933416320284545221 2893413737515560053352229)
                  ·
                    refine ⟨542515075784167510003543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893413737515560053352229 542515075784167510003543)
                    ·
                      rfl

theorem cell23_3169633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_3169633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169633 prefixEnd_3169633 := by exact prefixLift 3169633
  have htrace : WordTrace (prefixWord ++ tailWord_3169633) baseStart_3169633 baseEnd_3169633 := by
    simpa [prefixWord, tailWord_3169633, baseEnd_3169633] using wordTrace_append hprefix tailTrace_3169633
  have hstable : (prefixWord ++ tailWord_3169633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169633).length < 2 ^ (prefixWord ++ tailWord_3169633).sum := by decide
  have hdescent : baseEnd_3169633 < baseStart_3169633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169634 : List Nat := [3, 3, 2, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3169634 : Nat := 118140960795 + 3169634 * 2 ^ 59
def prefixEnd_3169634 : Nat := 4983230072969 + 3 ^ 40 * 3169634 * 2
def baseEnd_3169634 : Nat := 1627545740833157026098125

theorem tailTrace_3169634 : CollatzResearch.WordTrace tailWord_3169634 prefixEnd_3169634 1627545740833157026098125 := by
  unfold tailWord_3169634
  simp only [CollatzResearch.WordTrace]
  refine ⟨28901512349741205808698989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77070699599309882156530637 28901512349741205808698989)
  ·
    refine ⟨10838067131152952178262121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28901512349741205808698989 10838067131152952178262121)
    ·
      refine ⟨8128550348364714133696591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10838067131152952178262121 8128550348364714133696591)
      ·
        refine ⟨12192825522547071200544887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8128550348364714133696591 12192825522547071200544887)
        ·
          refine ⟨18289238283820606800817331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12192825522547071200544887 18289238283820606800817331)
          ·
            refine ⟨27433857425730910201225997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18289238283820606800817331 27433857425730910201225997)
            ·
              refine ⟨10287696534649091325459749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27433857425730910201225997 10287696534649091325459749)
              ·
                refine ⟨1928943100246704623523703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10287696534649091325459749 1928943100246704623523703)
                ·
                  refine ⟨2893414650370056935285555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928943100246704623523703 2893414650370056935285555)
                  ·
                    refine ⟨4340121975555085402928333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2893414650370056935285555 4340121975555085402928333)
                    ·
                      refine ⟨1627545740833157026098125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4340121975555085402928333 1627545740833157026098125)
                      ·
                        rfl

theorem cell23_3169634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3169634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169634 prefixEnd_3169634 := by exact prefixLift 3169634
  have htrace : WordTrace (prefixWord ++ tailWord_3169634) baseStart_3169634 baseEnd_3169634 := by
    simpa [prefixWord, tailWord_3169634, baseEnd_3169634] using wordTrace_append hprefix tailTrace_3169634
  have hstable : (prefixWord ++ tailWord_3169634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169634).length < 2 ^ (prefixWord ++ tailWord_3169634).sum := by decide
  have hdescent : baseEnd_3169634 < baseStart_3169634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169650 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3169650 : Nat := 118140960795 + 3169650 * 2 ^ 59
def prefixEnd_3169650 : Nat := 4983230072969 + 3 ^ 40 * 3169650 * 2
def baseEnd_3169650 : Nat := 542517985507876321166017

theorem tailTrace_3169650 : CollatzResearch.WordTrace tailWord_3169650 prefixEnd_3169650 542517985507876321166017 := by
  unfold tailWord_3169650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28901658241726714491844601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77071088644604571978252269 28901658241726714491844601)
  ·
    refine ⟨21676243681295035868883451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28901658241726714491844601 21676243681295035868883451)
    ·
      refine ⟨32514365521942553803325177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21676243681295035868883451 32514365521942553803325177)
      ·
        refine ⟨24385774141456915352493883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32514365521942553803325177 24385774141456915352493883)
        ·
          refine ⟨36578661212185373028740825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24385774141456915352493883 36578661212185373028740825)
          ·
            refine ⟨27433995909139029771555619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36578661212185373028740825 27433995909139029771555619)
            ·
              refine ⟨41150993863708544657333429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27433995909139029771555619 41150993863708544657333429)
              ·
                refine ⟨3857905674722676061625009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41150993863708544657333429 3857905674722676061625009)
                ·
                  refine ⟨2893429256042007046218757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3857905674722676061625009 2893429256042007046218757)
                  ·
                    refine ⟨542517985507876321166017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893429256042007046218757 542517985507876321166017)
                    ·
                      rfl

theorem cell23_3169650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3169650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169650 prefixEnd_3169650 := by exact prefixLift 3169650
  have htrace : WordTrace (prefixWord ++ tailWord_3169650) baseStart_3169650 baseEnd_3169650 := by
    simpa [prefixWord, tailWord_3169650, baseEnd_3169650] using wordTrace_append hprefix tailTrace_3169650
  have hstable : (prefixWord ++ tailWord_3169650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169650).length < 2 ^ (prefixWord ++ tailWord_3169650).sum := by decide
  have hdescent : baseEnd_3169650 < baseStart_3169650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169656 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3169656 : Nat := 118140960795 + 3169656 * 2 ^ 59
def prefixEnd_3169656 : Nat := 4983230072969 + 3 ^ 40 * 3169656 * 2
def baseEnd_3169656 : Nat := 1627557037407555940023023

theorem tailTrace_3169656 : CollatzResearch.WordTrace tailWord_3169656 prefixEnd_3169656 1627557037407555940023023 := by
  unfold tailWord_3169656
  simp only [CollatzResearch.WordTrace]
  refine ⟨57803425902442560496048411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77071234536590080661397881 57803425902442560496048411)
  ·
    refine ⟨86705138853663840744072617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57803425902442560496048411 86705138853663840744072617)
    ·
      refine ⟨65028854140247880558054463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86705138853663840744072617 65028854140247880558054463)
      ·
        refine ⟨97543281210371820837081695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65028854140247880558054463 97543281210371820837081695)
        ·
          refine ⟨146314921815557731255622543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97543281210371820837081695 146314921815557731255622543)
          ·
            refine ⟨219472382723336596883433815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146314921815557731255622543 219472382723336596883433815)
            ·
              refine ⟨329208574085004895325150723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219472382723336596883433815 329208574085004895325150723)
              ·
                refine ⟨493812861127507342987726085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329208574085004895325150723 493812861127507342987726085)
                ·
                  refine ⟨92589911461407626810198641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493812861127507342987726085 92589911461407626810198641)
                  ·
                    refine ⟨69442433596055720107648981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92589911461407626810198641 69442433596055720107648981)
                    ·
                      refine ⟨1627557037407555940023023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69442433596055720107648981 1627557037407555940023023)
                      ·
                        rfl

theorem cell23_3169656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3169656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169656 prefixEnd_3169656 := by exact prefixLift 3169656
  have htrace : WordTrace (prefixWord ++ tailWord_3169656) baseStart_3169656 baseEnd_3169656 := by
    simpa [prefixWord, tailWord_3169656, baseEnd_3169656] using wordTrace_append hprefix tailTrace_3169656
  have hstable : (prefixWord ++ tailWord_3169656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169656).length < 2 ^ (prefixWord ++ tailWord_3169656).sum := by decide
  have hdescent : baseEnd_3169656 < baseStart_3169656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169660 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_3169660 : Nat := 118140960795 + 3169660 * 2 ^ 59
def prefixEnd_3169660 : Nat := 4983230072969 + 3 ^ 40 * 3169660 * 2
def baseEnd_3169660 : Nat := 1627559091330173924373005

theorem tailTrace_3169660 : CollatzResearch.WordTrace tailWord_3169660 prefixEnd_3169660 1627559091330173924373005 := by
  unfold tailWord_3169660
  simp only [CollatzResearch.WordTrace]
  refine ⟨57803498848435314837621217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77071331797913753116828289 57803498848435314837621217)
  ·
    refine ⟨43352624136326486128215913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57803498848435314837621217 43352624136326486128215913)
    ·
      refine ⟨32514468102244864596161935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43352624136326486128215913 32514468102244864596161935)
      ·
        refine ⟨48771702153367296894242903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32514468102244864596161935 48771702153367296894242903)
        ·
          refine ⟨73157553230050945341364355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48771702153367296894242903 73157553230050945341364355)
          ·
            refine ⟨109736329845076418012046533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73157553230050945341364355 109736329845076418012046533)
            ·
              refine ⟨20575561845951828377258725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109736329845076418012046533 20575561845951828377258725)
              ·
                refine ⟨3857917846115967820736011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20575561845951828377258725 3857917846115967820736011)
                ·
                  refine ⟨5786876769173951731104017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3857917846115967820736011 5786876769173951731104017)
                  ·
                    refine ⟨4340157576880463798328013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5786876769173951731104017 4340157576880463798328013)
                    ·
                      refine ⟨1627559091330173924373005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4340157576880463798328013 1627559091330173924373005)
                      ·
                        rfl

theorem cell23_3169660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_3169660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169660 prefixEnd_3169660 := by exact prefixLift 3169660
  have htrace : WordTrace (prefixWord ++ tailWord_3169660) baseStart_3169660 baseEnd_3169660 := by
    simpa [prefixWord, tailWord_3169660, baseEnd_3169660] using wordTrace_append hprefix tailTrace_3169660
  have hstable : (prefixWord ++ tailWord_3169660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169660).length < 2 ^ (prefixWord ++ tailWord_3169660).sum := by decide
  have hdescent : baseEnd_3169660 < baseStart_3169660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169684 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3169684 : Nat := 118140960795 + 3169684 * 2 ^ 59
def prefixEnd_3169684 : Nat := 4983230072969 + 3 ^ 40 * 3169684 * 2
def baseEnd_3169684 : Nat := 542523804955293943490965

theorem tailTrace_3169684 : CollatzResearch.WordTrace tailWord_3169684 prefixEnd_3169684 542523804955293943490965 := by
  unfold tailWord_3169684
  simp only [CollatzResearch.WordTrace]
  refine ⟨57803936524391840887058053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77071915365855787849410737 57803936524391840887058053)
  ·
    refine ⟨10838238098323470166323385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57803936524391840887058053 10838238098323470166323385)
    ·
      refine ⟨8128678573742602624742539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10838238098323470166323385 8128678573742602624742539)
      ·
        refine ⟨12193017860613903937113809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8128678573742602624742539 12193017860613903937113809)
        ·
          refine ⟨9144763395460427952835357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12193017860613903937113809 9144763395460427952835357)
          ·
            refine ⟨3429286273297660482313259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9144763395460427952835357 3429286273297660482313259)
            ·
              refine ⟨5143929409946490723469889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429286273297660482313259 5143929409946490723469889)
              ·
                refine ⟨3857947057459868042602417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143929409946490723469889 3857947057459868042602417)
                ·
                  refine ⟨2893460293094901031951813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3857947057459868042602417 2893460293094901031951813)
                  ·
                    refine ⟨542523804955293943490965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893460293094901031951813 542523804955293943490965)
                    ·
                      rfl

theorem cell23_3169684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3169684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169684 prefixEnd_3169684 := by exact prefixLift 3169684
  have htrace : WordTrace (prefixWord ++ tailWord_3169684) baseStart_3169684 baseEnd_3169684 := by
    simpa [prefixWord, tailWord_3169684, baseEnd_3169684] using wordTrace_append hprefix tailTrace_3169684
  have hstable : (prefixWord ++ tailWord_3169684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169684).length < 2 ^ (prefixWord ++ tailWord_3169684).sum := by decide
  have hdescent : baseEnd_3169684 < baseStart_3169684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169704 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3169704 : Nat := 118140960795 + 3169704 * 2 ^ 59
def prefixEnd_3169704 : Nat := 4983230072969 + 3 ^ 40 * 3169704 * 2
def baseEnd_3169704 : Nat := 1627581684478971752222803

theorem tailTrace_3169704 : CollatzResearch.WordTrace tailWord_3169704 prefixEnd_3169704 1627581684478971752222803 := by
  unfold tailWord_3169704
  simp only [CollatzResearch.WordTrace]
  refine ⟨57804301254355612594922083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77072401672474150126562777 57804301254355612594922083)
  ·
    refine ⟨86706451881533418892383125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57804301254355612594922083 86706451881533418892383125)
    ·
      refine ⟨4064364931946879010580459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86706451881533418892383125 4064364931946879010580459)
      ·
        refine ⟨6096547397920318515870689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064364931946879010580459 6096547397920318515870689)
        ·
          refine ⟨4572410548440238886903017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6096547397920318515870689 4572410548440238886903017)
          ·
            refine ⟨3429307911330179165177263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4572410548440238886903017 3429307911330179165177263)
            ·
              refine ⟨5143961866995268747765895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429307911330179165177263 5143961866995268747765895)
              ·
                refine ⟨7715942800492903121648843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143961866995268747765895 7715942800492903121648843)
                ·
                  refine ⟨11573914200739354682473265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7715942800492903121648843 11573914200739354682473265)
                  ·
                    refine ⟨8680435650554516011854949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11573914200739354682473265 8680435650554516011854949)
                    ·
                      refine ⟨1627581684478971752222803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8680435650554516011854949 1627581684478971752222803)
                      ·
                        rfl

theorem cell23_3169704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3169704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169704 prefixEnd_3169704 := by exact prefixLift 3169704
  have htrace : WordTrace (prefixWord ++ tailWord_3169704) baseStart_3169704 baseEnd_3169704 := by
    simpa [prefixWord, tailWord_3169704, baseEnd_3169704] using wordTrace_append hprefix tailTrace_3169704
  have hstable : (prefixWord ++ tailWord_3169704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169704).length < 2 ^ (prefixWord ++ tailWord_3169704).sum := by decide
  have hdescent : baseEnd_3169704 < baseStart_3169704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169743 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_3169743 : Nat := 118140960795 + 3169743 * 2 ^ 59
def prefixEnd_3169743 : Nat := 4983230072969 + 3 ^ 40 * 3169743 * 2
def baseEnd_3169743 : Nat := 1627601710224497099635123

theorem tailTrace_3169743 : CollatzResearch.WordTrace tailWord_3169743 prefixEnd_3169743 1627601710224497099635123 := by
  unfold tailWord_3169743
  simp only [CollatzResearch.WordTrace]
  refine ⟨115610024955569934850513883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77073349970379956567009255 115610024955569934850513883)
  ·
    refine ⟨173415037433354902275770825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115610024955569934850513883 173415037433354902275770825)
    ·
      refine ⟨130061278075016176706828119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173415037433354902275770825 130061278075016176706828119)
      ·
        refine ⟨195091917112524265060242179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130061278075016176706828119 195091917112524265060242179)
        ·
          refine ⟨292637875668786397590363269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195091917112524265060242179 292637875668786397590363269)
          ·
            refine ⟨54869601687897449548193113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292637875668786397590363269 54869601687897449548193113)
            ·
              refine ⟨41152201265923087161144835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54869601687897449548193113 41152201265923087161144835)
              ·
                refine ⟨61728301898884630741717253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41152201265923087161144835 61728301898884630741717253)
                ·
                  refine ⟨11574056606040868264071985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61728301898884630741717253 11574056606040868264071985)
                  ·
                    refine ⟨8680542454530651198053989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11574056606040868264071985 8680542454530651198053989)
                    ·
                      refine ⟨1627601710224497099635123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8680542454530651198053989 1627601710224497099635123)
                      ·
                        rfl

theorem cell23_3169743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_3169743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169743 prefixEnd_3169743 := by exact prefixLift 3169743
  have htrace : WordTrace (prefixWord ++ tailWord_3169743) baseStart_3169743 baseEnd_3169743 := by
    simpa [prefixWord, tailWord_3169743, baseEnd_3169743] using wordTrace_append hprefix tailTrace_3169743
  have hstable : (prefixWord ++ tailWord_3169743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169743).length < 2 ^ (prefixWord ++ tailWord_3169743).sum := by decide
  have hdescent : baseEnd_3169743 < baseStart_3169743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169800 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 2, 5]
def baseStart_3169800 : Nat := 118140960795 + 3169800 * 2 ^ 59
def prefixEnd_3169800 : Nat := 4983230072969 + 3 ^ 40 * 3169800 * 2
def baseEnd_3169800 : Nat := 542543659540601125540787

theorem tailTrace_3169800 : CollatzResearch.WordTrace tailWord_3169800 prefixEnd_3169800 542543659540601125540787 := by
  unfold tailWord_3169800
  simp only [CollatzResearch.WordTrace]
  refine ⟨57806051958181716792669427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77074735944242289056892569 57806051958181716792669427)
  ·
    refine ⟨86709077937272575189004141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57806051958181716792669427 86709077937272575189004141)
    ·
      refine ⟨32515904226477215695876553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86709077937272575189004141 32515904226477215695876553)
      ·
        refine ⟨24386928169857911771907415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32515904226477215695876553 24386928169857911771907415)
        ·
          refine ⟨36580392254786867657861123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24386928169857911771907415 36580392254786867657861123)
          ·
            refine ⟨54870588382180301486791685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36580392254786867657861123 54870588382180301486791685)
            ·
              refine ⟨10288235321658806528773441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54870588382180301486791685 10288235321658806528773441)
              ·
                refine ⟨7716176491244104896580081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10288235321658806528773441 7716176491244104896580081)
                ·
                  refine ⟨5787132368433078672435061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7716176491244104896580081 5787132368433078672435061)
                  ·
                    refine ⟨542543659540601125540787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5787132368433078672435061 542543659540601125540787)
                    ·
                      rfl

theorem cell23_3169800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_3169800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169800 prefixEnd_3169800 := by exact prefixLift 3169800
  have htrace : WordTrace (prefixWord ++ tailWord_3169800) baseStart_3169800 baseEnd_3169800 := by
    simpa [prefixWord, tailWord_3169800, baseEnd_3169800] using wordTrace_append hprefix tailTrace_3169800
  have hstable : (prefixWord ++ tailWord_3169800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169800).length < 2 ^ (prefixWord ++ tailWord_3169800).sum := by decide
  have hdescent : baseEnd_3169800 < baseStart_3169800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169820 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3169820 : Nat := 118140960795 + 3169820 * 2 ^ 59
def prefixEnd_3169820 : Nat := 4983230072969 + 3 ^ 40 * 3169820 * 2
def baseEnd_3169820 : Nat := 1627641248234893298372269

theorem tailTrace_3169820 : CollatzResearch.WordTrace tailWord_3169820 prefixEnd_3169820 1627641248234893298372269 := by
  unfold tailWord_3169820
  simp only [CollatzResearch.WordTrace]
  refine ⟨57806416688145488500533457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77075222250860651334044609 57806416688145488500533457)
  ·
    refine ⟨43354812516109116375400093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57806416688145488500533457 43354812516109116375400093)
    ·
      refine ⟨16258054693540918640775035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43354812516109116375400093 16258054693540918640775035)
      ·
        refine ⟨24387082040311377961162553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16258054693540918640775035 24387082040311377961162553)
        ·
          refine ⟨18290311530233533470871915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24387082040311377961162553 18290311530233533470871915)
          ·
            refine ⟨27435467295350300206307873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18290311530233533470871915 27435467295350300206307873)
            ·
              refine ⟨20576600471512725154730905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27435467295350300206307873 20576600471512725154730905)
              ·
                refine ⟨15432450353634543866048179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20576600471512725154730905 15432450353634543866048179)
                ·
                  refine ⟨23148675530451815799072269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15432450353634543866048179 23148675530451815799072269)
                  ·
                    refine ⟨8680753323919430924652101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23148675530451815799072269 8680753323919430924652101)
                    ·
                      refine ⟨1627641248234893298372269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8680753323919430924652101 1627641248234893298372269)
                      ·
                        rfl

theorem cell23_3169820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3169820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169820 prefixEnd_3169820 := by exact prefixLift 3169820
  have htrace : WordTrace (prefixWord ++ tailWord_3169820) baseStart_3169820 baseEnd_3169820 := by
    simpa [prefixWord, tailWord_3169820, baseEnd_3169820] using wordTrace_append hprefix tailTrace_3169820
  have hstable : (prefixWord ++ tailWord_3169820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169820).length < 2 ^ (prefixWord ++ tailWord_3169820).sum := by decide
  have hdescent : baseEnd_3169820 < baseStart_3169820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169857 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3169857 : Nat := 118140960795 + 3169857 * 2 ^ 59
def prefixEnd_3169857 : Nat := 4983230072969 + 3 ^ 40 * 3169857 * 2
def baseEnd_3169857 : Nat := 1627660247019109653609599

theorem tailTrace_3169857 : CollatzResearch.WordTrace tailWord_3169857 prefixEnd_3169857 1627660247019109653609599 := by
  unfold tailWord_3169857
  simp only [CollatzResearch.WordTrace]
  refine ⟨115614182877156932320163825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77076121918104621546775883 115614182877156932320163825)
  ·
    refine ⟨86710637157867699240122869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115614182877156932320163825 86710637157867699240122869)
    ·
      refine ⟨8129122233550096803761519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86710637157867699240122869 8129122233550096803761519)
      ·
        refine ⟨12193683350325145205642279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8129122233550096803761519 12193683350325145205642279)
        ·
          refine ⟨18290525025487717808463419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12193683350325145205642279 18290525025487717808463419)
          ·
            refine ⟨27435787538231576712695129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18290525025487717808463419 27435787538231576712695129)
            ·
              refine ⟨20576840653673682534521347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27435787538231576712695129 20576840653673682534521347)
              ·
                refine ⟨30865260980510523801782021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20576840653673682534521347 30865260980510523801782021)
                ·
                  refine ⟨5787236433845723212834129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30865260980510523801782021 5787236433845723212834129)
                  ·
                    refine ⟨4340427325384292409625597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5787236433845723212834129 4340427325384292409625597)
                    ·
                      refine ⟨1627660247019109653609599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4340427325384292409625597 1627660247019109653609599)
                      ·
                        rfl

theorem cell23_3169857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3169857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169857 prefixEnd_3169857 := by exact prefixLift 3169857
  have htrace : WordTrace (prefixWord ++ tailWord_3169857) baseStart_3169857 baseEnd_3169857 := by
    simpa [prefixWord, tailWord_3169857, baseEnd_3169857] using wordTrace_append hprefix tailTrace_3169857
  have hstable : (prefixWord ++ tailWord_3169857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169857).length < 2 ^ (prefixWord ++ tailWord_3169857).sum := by decide
  have hdescent : baseEnd_3169857 < baseStart_3169857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169897 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 1, 5, 2]
def baseStart_3169897 : Nat := 118140960795 + 3169897 * 2 ^ 59
def prefixEnd_3169897 : Nat := 4983230072969 + 3 ^ 40 * 3169897 * 2
def baseEnd_3169897 : Nat := 1627680786245289497109415

theorem tailTrace_3169897 : CollatzResearch.WordTrace tailWord_3169897 prefixEnd_3169897 1627680786245289497109415 := by
  unfold tailWord_3169897
  simp only [CollatzResearch.WordTrace]
  refine ⟨115615641797012019151619945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77077094531341346101079963 115615641797012019151619945)
  ·
    refine ⟨86711731347759014363714959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115615641797012019151619945 86711731347759014363714959)
    ·
      refine ⟨130067597021638521545572439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86711731347759014363714959 130067597021638521545572439)
      ·
        refine ⟨195101395532457782318358659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130067597021638521545572439 195101395532457782318358659)
        ·
          refine ⟨292652093298686673477537989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195101395532457782318358659 292652093298686673477537989)
          ·
            refine ⟨54872267493503751277038373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292652093298686673477537989 54872267493503751277038373)
            ·
              refine ⟨10288550155031953364444695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54872267493503751277038373 10288550155031953364444695)
              ·
                refine ⟨15432825232547930046667043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10288550155031953364444695 15432825232547930046667043)
                ·
                  refine ⟨23149237848821895070000565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15432825232547930046667043 23149237848821895070000565)
                  ·
                    refine ⟨2170241048327052662812553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23149237848821895070000565 2170241048327052662812553)
                    ·
                      refine ⟨1627680786245289497109415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170241048327052662812553 1627680786245289497109415)
                      ·
                        rfl

theorem cell23_3169897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 5, 2].length) (baseStart_3169897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169897 prefixEnd_3169897 := by exact prefixLift 3169897
  have htrace : WordTrace (prefixWord ++ tailWord_3169897) baseStart_3169897 baseEnd_3169897 := by
    simpa [prefixWord, tailWord_3169897, baseEnd_3169897] using wordTrace_append hprefix tailTrace_3169897
  have hstable : (prefixWord ++ tailWord_3169897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169897).length < 2 ^ (prefixWord ++ tailWord_3169897).sum := by decide
  have hdescent : baseEnd_3169897 < baseStart_3169897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169921 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3169921 : Nat := 118140960795 + 3169921 * 2 ^ 59
def prefixEnd_3169921 : Nat := 4983230072969 + 3 ^ 40 * 3169921 * 2
def baseEnd_3169921 : Nat := 1627693109780997403209305

theorem tailTrace_3169921 : CollatzResearch.WordTrace tailWord_3169921 prefixEnd_3169921 1627693109780997403209305 := by
  unfold tailWord_3169921
  simp only [CollatzResearch.WordTrace]
  refine ⟨115616517148925071250493617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77077678099283380833662411 115616517148925071250493617)
  ·
    refine ⟨86712387861693803437870213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115616517148925071250493617 86712387861693803437870213)
    ·
      refine ⟨16258572724067588144600665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86712387861693803437870213 16258572724067588144600665)
      ·
        refine ⟨12193929543050691108450499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16258572724067588144600665 12193929543050691108450499)
        ·
          refine ⟨18290894314576036662675749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12193929543050691108450499 18290894314576036662675749)
          ·
            refine ⟨3429542683983006874251703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18290894314576036662675749 3429542683983006874251703)
            ·
              refine ⟨5144314025974510311377555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429542683983006874251703 5144314025974510311377555)
              ·
                refine ⟨7716471038961765467066333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144314025974510311377555 7716471038961765467066333)
                ·
                  refine ⟨2893676639610662050149875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7716471038961765467066333 2893676639610662050149875)
                  ·
                    refine ⟨4340514959415993075224813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2893676639610662050149875 4340514959415993075224813)
                    ·
                      refine ⟨1627693109780997403209305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4340514959415993075224813 1627693109780997403209305)
                      ·
                        rfl

theorem cell23_3169921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3169921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169921 prefixEnd_3169921 := by exact prefixLift 3169921
  have htrace : WordTrace (prefixWord ++ tailWord_3169921) baseStart_3169921 baseEnd_3169921 := by
    simpa [prefixWord, tailWord_3169921, baseEnd_3169921] using wordTrace_append hprefix tailTrace_3169921
  have hstable : (prefixWord ++ tailWord_3169921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169921).length < 2 ^ (prefixWord ++ tailWord_3169921).sum := by decide
  have hdescent : baseEnd_3169921 < baseStart_3169921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169928 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 6]
def baseStart_3169928 : Nat := 118140960795 + 3169928 * 2 ^ 59
def prefixEnd_3169928 : Nat := 4983230072969 + 3 ^ 40 * 3169928 * 2
def baseEnd_3169928 : Nat := 180855189349508763980197

theorem tailTrace_3169928 : CollatzResearch.WordTrace tailWord_3169928 prefixEnd_3169928 180855189349508763980197 := by
  unfold tailWord_3169928
  simp only [CollatzResearch.WordTrace]
  refine ⟨57808386229949855722999219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77077848306599807630665625 57808386229949855722999219)
  ·
    refine ⟨86712579344924783584498829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57808386229949855722999219 86712579344924783584498829)
    ·
      refine ⟨32517217254346793844187061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86712579344924783584498829 32517217254346793844187061)
      ·
        refine ⟨3048489117595011922892537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32517217254346793844187061 3048489117595011922892537)
        ·
          refine ⟨2286366838196258942169403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048489117595011922892537 2286366838196258942169403)
          ·
            refine ⟨3429550257294388413254105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286366838196258942169403 3429550257294388413254105)
            ·
              refine ⟨2572162692970791309940579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429550257294388413254105 2572162692970791309940579)
              ·
                refine ⟨3858244039456186964910869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572162692970791309940579 3858244039456186964910869)
                ·
                  refine ⟨180855189349508763980197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3858244039456186964910869 180855189349508763980197)
                  ·
                    rfl

theorem cell23_3169928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 6].length) (baseStart_3169928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169928 prefixEnd_3169928 := by exact prefixLift 3169928
  have htrace : WordTrace (prefixWord ++ tailWord_3169928) baseStart_3169928 baseEnd_3169928 := by
    simpa [prefixWord, tailWord_3169928, baseEnd_3169928] using wordTrace_append hprefix tailTrace_3169928
  have hstable : (prefixWord ++ tailWord_3169928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169928).length < 2 ^ (prefixWord ++ tailWord_3169928).sum := by decide
  have hdescent : baseEnd_3169928 < baseStart_3169928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169944 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3169944 : Nat := 118140960795 + 3169944 * 2 ^ 59
def prefixEnd_3169944 : Nat := 4983230072969 + 3 ^ 40 * 3169944 * 2
def baseEnd_3169944 : Nat := 1627704919836050813221699

theorem tailTrace_3169944 : CollatzResearch.WordTrace tailWord_3169944 prefixEnd_3169944 1627704919836050813221699 := by
  unfold tailWord_3169944
  simp only [CollatzResearch.WordTrace]
  refine ⟨57808678013920873089290443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77078237351894497452387257 57808678013920873089290443)
  ·
    refine ⟨86713017020881309633935665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57808678013920873089290443 86713017020881309633935665)
    ·
      refine ⟨65034762765660982225451749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86713017020881309633935665 65034762765660982225451749)
      ·
        refine ⟨12194018018561434167272203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65034762765660982225451749 12194018018561434167272203)
        ·
          refine ⟨18291027027842151250908305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194018018561434167272203 18291027027842151250908305)
          ·
            refine ⟨13718270270881613438181229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18291027027842151250908305 13718270270881613438181229)
            ·
              refine ⟨5144351351580605039317961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13718270270881613438181229 5144351351580605039317961)
              ·
                refine ⟨3858263513685453779488471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5144351351580605039317961 3858263513685453779488471)
                ·
                  refine ⟨5787395270528180669232707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858263513685453779488471 5787395270528180669232707)
                  ·
                    refine ⟨8681092905792271003849061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5787395270528180669232707 8681092905792271003849061)
                    ·
                      refine ⟨1627704919836050813221699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8681092905792271003849061 1627704919836050813221699)
                      ·
                        rfl

theorem cell23_3169944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3169944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169944 prefixEnd_3169944 := by exact prefixLift 3169944
  have htrace : WordTrace (prefixWord ++ tailWord_3169944) baseStart_3169944 baseEnd_3169944 := by
    simpa [prefixWord, tailWord_3169944, baseEnd_3169944] using wordTrace_append hprefix tailTrace_3169944
  have hstable : (prefixWord ++ tailWord_3169944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169944).length < 2 ^ (prefixWord ++ tailWord_3169944).sum := by decide
  have hdescent : baseEnd_3169944 < baseStart_3169944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3169978 : List Nat := [3, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2]
def baseStart_3169978 : Nat := 118140960795 + 3169978 * 2 ^ 59
def prefixEnd_3169978 : Nat := 4983230072969 + 3 ^ 40 * 3169978 * 2
def baseEnd_3169978 : Nat := 1627722378178303680196543

theorem tailTrace_3169978 : CollatzResearch.WordTrace tailWord_3169978 prefixEnd_3169978 1627722378178303680196543 := by
  unfold tailWord_3169978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28904649027429642496329647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77079064073145713323545725 28904649027429642496329647)
  ·
    refine ⟨43356973541144463744494471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28904649027429642496329647 43356973541144463744494471)
    ·
      refine ⟨65035460311716695616741707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43356973541144463744494471 65035460311716695616741707)
      ·
        refine ⟨97553190467575043425112561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65035460311716695616741707 97553190467575043425112561)
        ·
          refine ⟨73164892850681282568834421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97553190467575043425112561 73164892850681282568834421)
          ·
            refine ⟨6859208704751370240828227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73164892850681282568834421 6859208704751370240828227)
            ·
              refine ⟨10288813057127055361242341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859208704751370240828227 10288813057127055361242341)
              ·
                refine ⟨1929152448211322880232939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10288813057127055361242341 1929152448211322880232939)
                ·
                  refine ⟨2893728672316984320349409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929152448211322880232939 2893728672316984320349409)
                  ·
                    refine ⟨2170296504237738240262057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2893728672316984320349409 2170296504237738240262057)
                    ·
                      refine ⟨1627722378178303680196543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170296504237738240262057 1627722378178303680196543)
                      ·
                        rfl

theorem cell23_3169978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_3169978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3169978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3169978 prefixEnd_3169978 := by exact prefixLift 3169978
  have htrace : WordTrace (prefixWord ++ tailWord_3169978) baseStart_3169978 baseEnd_3169978 := by
    simpa [prefixWord, tailWord_3169978, baseEnd_3169978] using wordTrace_append hprefix tailTrace_3169978
  have hstable : (prefixWord ++ tailWord_3169978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3169978).length < 2 ^ (prefixWord ++ tailWord_3169978).sum := by decide
  have hdescent : baseEnd_3169978 < baseStart_3169978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3169978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170012 : List Nat := [2, 2, 5, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3170012 : Nat := 118140960795 + 3170012 * 2 ^ 59
def prefixEnd_3170012 : Nat := 4983230072969 + 3 ^ 40 * 3170012 * 2
def baseEnd_3170012 : Nat := 1627739836520556547171387

theorem tailTrace_3170012 : CollatzResearch.WordTrace tailWord_3170012 prefixEnd_3170012 1627739836520556547171387 := by
  unfold tailWord_3170012
  simp only [CollatzResearch.WordTrace]
  refine ⟨57809918095797696896028145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77079890794396929194704193 57809918095797696896028145)
  ·
    refine ⟨43357438571848272672021109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57809918095797696896028145 43357438571848272672021109)
    ·
      refine ⟨4064759866110775563001979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43357438571848272672021109 4064759866110775563001979)
      ·
        refine ⟨6097139799166163344502969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064759866110775563001979 6097139799166163344502969)
        ·
          refine ⟨4572854849374622508377227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097139799166163344502969 4572854849374622508377227)
          ·
            refine ⟨6859282274061933762565841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4572854849374622508377227 6859282274061933762565841)
            ·
              refine ⟨5144461705546450321924381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6859282274061933762565841 5144461705546450321924381)
              ·
                refine ⟨1929173139579918870721643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5144461705546450321924381 1929173139579918870721643)
                ·
                  refine ⟨2893759709369878306082465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929173139579918870721643 2893759709369878306082465)
                  ·
                    refine ⟨2170319782027408729561849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2893759709369878306082465 2170319782027408729561849)
                    ·
                      refine ⟨1627739836520556547171387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170319782027408729561849 1627739836520556547171387)
                      ·
                        rfl

theorem cell23_3170012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3170012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170012 prefixEnd_3170012 := by exact prefixLift 3170012
  have htrace : WordTrace (prefixWord ++ tailWord_3170012) baseStart_3170012 baseEnd_3170012 := by
    simpa [prefixWord, tailWord_3170012, baseEnd_3170012] using wordTrace_append hprefix tailTrace_3170012
  have hstable : (prefixWord ++ tailWord_3170012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170012).length < 2 ^ (prefixWord ++ tailWord_3170012).sum := by decide
  have hdescent : baseEnd_3170012 < baseStart_3170012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170021 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 1, 3, 2]
def baseStart_3170021 : Nat := 118140960795 + 3170021 * 2 ^ 59
def prefixEnd_3170021 : Nat := 4983230072969 + 3 ^ 40 * 3170021 * 2
def baseEnd_3170021 : Nat := 1627744457846447011958845

theorem tailTrace_3170021 : CollatzResearch.WordTrace tailWord_3170021 prefixEnd_3170021 1627744457846447011958845 := by
  unfold tailWord_3170021
  simp only [CollatzResearch.WordTrace]
  refine ⟨115620164448562788329133917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77080109632375192219422611 115620164448562788329133917)
  ·
    refine ⟨43357561668211045623425219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115620164448562788329133917 43357561668211045623425219)
    ·
      refine ⟨65036342502316568435137829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43357561668211045623425219 65036342502316568435137829)
      ·
        refine ⟨12194314219184356581588343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65036342502316568435137829 12194314219184356581588343)
        ·
          refine ⟨18291471328776534872382515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194314219184356581588343 18291471328776534872382515)
          ·
            refine ⟨27437206993164802308573773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18291471328776534872382515 27437206993164802308573773)
            ·
              refine ⟨10288952622436800865715165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27437206993164802308573773 10288952622436800865715165)
              ·
                refine ⟨3858357233413800324643187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10288952622436800865715165 3858357233413800324643187)
                ·
                  refine ⟨5787535850120700486964781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858357233413800324643187 5787535850120700486964781)
                  ·
                    refine ⟨2170325943795262682611793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5787535850120700486964781 2170325943795262682611793)
                    ·
                      refine ⟨1627744457846447011958845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170325943795262682611793 1627744457846447011958845)
                      ·
                        rfl

theorem cell23_3170021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_3170021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170021 prefixEnd_3170021 := by exact prefixLift 3170021
  have htrace : WordTrace (prefixWord ++ tailWord_3170021) baseStart_3170021 baseEnd_3170021 := by
    simpa [prefixWord, tailWord_3170021, baseEnd_3170021] using wordTrace_append hprefix tailTrace_3170021
  have hstable : (prefixWord ++ tailWord_3170021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170021).length < 2 ^ (prefixWord ++ tailWord_3170021).sum := by decide
  have hdescent : baseEnd_3170021 < baseStart_3170021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170047 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_3170047 : Nat := 118140960795 + 3170047 * 2 ^ 59
def prefixEnd_3170047 : Nat := 4983230072969 + 3 ^ 40 * 3170047 * 2
def baseEnd_3170047 : Nat := 1627757808343463910233725

theorem tailTrace_3170047 : CollatzResearch.WordTrace tailWord_3170047 prefixEnd_3170047 1627757808343463910233725 := by
  unfold tailWord_3170047
  simp only [CollatzResearch.WordTrace]
  refine ⟨115621112746468594769580395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77080741830979063179720263 115621112746468594769580395)
  ·
    refine ⟨173431669119702892154370593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115621112746468594769580395 173431669119702892154370593)
    ·
      refine ⟨130073751839777169115777945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173431669119702892154370593 130073751839777169115777945)
      ·
        refine ⟨97555313879832876836833459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130073751839777169115777945 97555313879832876836833459)
        ·
          refine ⟨146332970819749315255250189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97555313879832876836833459 146332970819749315255250189)
          ·
            refine ⟨54874864057405993220718821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146332970819749315255250189 54874864057405993220718821)
            ·
              refine ⟨10289037010763623728884779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54874864057405993220718821 10289037010763623728884779)
              ·
                refine ⟨15433555516145435593327169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289037010763623728884779 15433555516145435593327169)
                ·
                  refine ⟨11575166637109076694995377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15433555516145435593327169 11575166637109076694995377)
                  ·
                    refine ⟨8681374977831807521246533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11575166637109076694995377 8681374977831807521246533)
                    ·
                      refine ⟨1627757808343463910233725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8681374977831807521246533 1627757808343463910233725)
                      ·
                        rfl

theorem cell23_3170047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_3170047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170047 prefixEnd_3170047 := by exact prefixLift 3170047
  have htrace : WordTrace (prefixWord ++ tailWord_3170047) baseStart_3170047 baseEnd_3170047 := by
    simpa [prefixWord, tailWord_3170047, baseEnd_3170047] using wordTrace_append hprefix tailTrace_3170047
  have hstable : (prefixWord ++ tailWord_3170047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170047).length < 2 ^ (prefixWord ++ tailWord_3170047).sum := by decide
  have hdescent : baseEnd_3170047 < baseStart_3170047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170051 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 2, 2, 2]
def baseStart_3170051 : Nat := 118140960795 + 3170051 * 2 ^ 59
def prefixEnd_3170051 : Nat := 4983230072969 + 3 ^ 40 * 3170051 * 2
def baseEnd_3170051 : Nat := 1627759862266081894583707

theorem tailTrace_3170051 : CollatzResearch.WordTrace tailWord_3170051 prefixEnd_3170051 1627759862266081894583707 := by
  unfold tailWord_3170051
  simp only [CollatzResearch.WordTrace]
  refine ⟨115621258638454103452726007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77080839092302735635150671 115621258638454103452726007)
  ·
    refine ⟨173431887957681155179089011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115621258638454103452726007 173431887957681155179089011)
    ·
      refine ⟨260147831936521732768633517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173431887957681155179089011 260147831936521732768633517)
      ·
        refine ⟨97555436976195649788237569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260147831936521732768633517 97555436976195649788237569)
        ·
          refine ⟨73166577732146737341178177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97555436976195649788237569 73166577732146737341178177)
          ·
            refine ⟨54874933299110053005883633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73166577732146737341178177 54874933299110053005883633)
            ·
              refine ⟨41156199974332539754412725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54874933299110053005883633 41156199974332539754412725)
              ·
                refine ⟨3858393747593675601976193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41156199974332539754412725 3858393747593675601976193)
                ·
                  refine ⟨2893795310695256701482145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3858393747593675601976193 2893795310695256701482145)
                  ·
                    refine ⟨2170346483021442526111609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2893795310695256701482145 2170346483021442526111609)
                    ·
                      refine ⟨1627759862266081894583707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170346483021442526111609 1627759862266081894583707)
                      ·
                        rfl

theorem cell23_3170051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_3170051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170051 prefixEnd_3170051 := by exact prefixLift 3170051
  have htrace : WordTrace (prefixWord ++ tailWord_3170051) baseStart_3170051 baseEnd_3170051 := by
    simpa [prefixWord, tailWord_3170051, baseEnd_3170051] using wordTrace_append hprefix tailTrace_3170051
  have hstable : (prefixWord ++ tailWord_3170051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170051).length < 2 ^ (prefixWord ++ tailWord_3170051).sum := by decide
  have hdescent : baseEnd_3170051 < baseStart_3170051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170067 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 3]
def baseStart_3170067 : Nat := 118140960795 + 3170067 * 2 ^ 59
def prefixEnd_3170067 : Nat := 4983230072969 + 3 ^ 40 * 3170067 * 2
def baseEnd_3170067 : Nat := 1627768077956553831983633

theorem tailTrace_3170067 : CollatzResearch.WordTrace tailWord_3170067 prefixEnd_3170067 1627768077956553831983633 := by
  unfold tailWord_3170067
  simp only [CollatzResearch.WordTrace]
  refine ⟨115621842206396138185308455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77081228137597425456872303 115621842206396138185308455)
  ·
    refine ⟨173432763309594207277962683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115621842206396138185308455 173432763309594207277962683)
    ·
      refine ⟨260149144964391310916944025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173432763309594207277962683 260149144964391310916944025)
      ·
        refine ⟨195111858723293483187708019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260149144964391310916944025 195111858723293483187708019)
        ·
          refine ⟨292667788084940224781562029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195111858723293483187708019 292667788084940224781562029)
          ·
            refine ⟨109750420531852584293085761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292667788084940224781562029 109750420531852584293085761)
            ·
              refine ⟨82312815398889438219814321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109750420531852584293085761 82312815398889438219814321)
              ·
                refine ⟨61734611549167078664860741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82312815398889438219814321 61734611549167078664860741)
                ·
                  refine ⟨11575239665468827249661389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61734611549167078664860741 11575239665468827249661389)
                  ·
                    refine ⟨4340714874550810218623021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11575239665468827249661389 4340714874550810218623021)
                    ·
                      refine ⟨1627768077956553831983633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4340714874550810218623021 1627768077956553831983633)
                      ·
                        rfl

theorem cell23_3170067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_3170067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170067 prefixEnd_3170067 := by exact prefixLift 3170067
  have htrace : WordTrace (prefixWord ++ tailWord_3170067) baseStart_3170067 baseEnd_3170067 := by
    simpa [prefixWord, tailWord_3170067, baseEnd_3170067] using wordTrace_append hprefix tailTrace_3170067
  have hstable : (prefixWord ++ tailWord_3170067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170067).length < 2 ^ (prefixWord ++ tailWord_3170067).sum := by decide
  have hdescent : baseEnd_3170067 < baseStart_3170067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170097 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3170097 : Nat := 118140960795 + 3170097 * 2 ^ 59
def prefixEnd_3170097 : Nat := 4983230072969 + 3 ^ 40 * 3170097 * 2
def baseEnd_3170097 : Nat := 1627783482376188714608495

theorem tailTrace_3170097 : CollatzResearch.WordTrace tailWord_3170097 prefixEnd_3170097 1627783482376188714608495 := by
  unfold tailWord_3170097
  simp only [CollatzResearch.WordTrace]
  refine ⟨115622936396287453308900545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77081957597524968872600363 115622936396287453308900545)
  ·
    refine ⟨86717202297215589981675409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115622936396287453308900545 86717202297215589981675409)
    ·
      refine ⟨65037901722911692486256557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86717202297215589981675409 65037901722911692486256557)
      ·
        refine ⟨24389213146091884682346209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65037901722911692486256557 24389213146091884682346209)
        ·
          refine ⟨18291909859568913511759657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24389213146091884682346209 18291909859568913511759657)
          ·
            refine ⟨13718932394676685133819743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18291909859568913511759657 13718932394676685133819743)
            ·
              refine ⟨20578398592015027700729615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13718932394676685133819743 20578398592015027700729615)
              ·
                refine ⟨30867597888022541551094423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20578398592015027700729615 30867597888022541551094423)
                ·
                  refine ⟨46301396832033812326641635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30867597888022541551094423 46301396832033812326641635)
                  ·
                    refine ⟨69452095248050718489962453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46301396832033812326641635 69452095248050718489962453)
                    ·
                      refine ⟨1627783482376188714608495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69452095248050718489962453 1627783482376188714608495)
                      ·
                        rfl

theorem cell23_3170097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3170097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170097 prefixEnd_3170097 := by exact prefixLift 3170097
  have htrace : WordTrace (prefixWord ++ tailWord_3170097) baseStart_3170097 baseEnd_3170097 := by
    simpa [prefixWord, tailWord_3170097, baseEnd_3170097] using wordTrace_append hprefix tailTrace_3170097
  have hstable : (prefixWord ++ tailWord_3170097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170097).length < 2 ^ (prefixWord ++ tailWord_3170097).sum := by decide
  have hdescent : baseEnd_3170097 < baseStart_3170097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170102 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3170102 : Nat := 118140960795 + 3170102 * 2 ^ 59
def prefixEnd_3170102 : Nat := 4983230072969 + 3 ^ 40 * 3170102 * 2
def baseEnd_3170102 : Nat := 1627786049779461195045973

theorem tailTrace_3170102 : CollatzResearch.WordTrace tailWord_3170102 prefixEnd_3170102 1627786049779461195045973 := by
  unfold tailWord_3170102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226444922579333697677035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77082079174179559441888373 7226444922579333697677035)
  ·
    refine ⟨10839667383869000546515553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7226444922579333697677035 10839667383869000546515553)
    ·
      refine ⟨8129750537901750409886665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10839667383869000546515553 8129750537901750409886665)
      ·
        refine ⟨6097312903426312807414999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8129750537901750409886665 6097312903426312807414999)
        ·
          refine ⟨9145969355139469211122499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6097312903426312807414999 9145969355139469211122499)
          ·
            refine ⟨13718954032709203816683749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9145969355139469211122499 13718954032709203816683749)
            ·
              refine ⟨2572303881132975715628203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13718954032709203816683749 2572303881132975715628203)
              ·
                refine ⟨3858455821699463573442305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572303881132975715628203 3858455821699463573442305)
                ·
                  refine ⟨2893841866274597680081729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3858455821699463573442305 2893841866274597680081729)
                  ·
                    refine ⟨2170381399705948260061297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2893841866274597680081729 2170381399705948260061297)
                    ·
                      refine ⟨1627786049779461195045973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170381399705948260061297 1627786049779461195045973)
                      ·
                        rfl

theorem cell23_3170102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3170102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170102 prefixEnd_3170102 := by exact prefixLift 3170102
  have htrace : WordTrace (prefixWord ++ tailWord_3170102) baseStart_3170102 baseEnd_3170102 := by
    simpa [prefixWord, tailWord_3170102, baseEnd_3170102] using wordTrace_append hprefix tailTrace_3170102
  have hstable : (prefixWord ++ tailWord_3170102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170102).length < 2 ^ (prefixWord ++ tailWord_3170102).sum := by decide
  have hdescent : baseEnd_3170102 < baseStart_3170102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170137 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3170137 : Nat := 118140960795 + 3170137 * 2 ^ 59
def prefixEnd_3170137 : Nat := 4983230072969 + 3 ^ 40 * 3170137 * 2
def baseEnd_3170137 : Nat := 1627804021602368558108311

theorem tailTrace_3170137 : CollatzResearch.WordTrace tailWord_3170137 prefixEnd_3170137 1627804021602368558108311 := by
  unfold tailWord_3170137
  simp only [CollatzResearch.WordTrace]
  refine ⟨115624395316142540140356665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77082930210761693426904443 115624395316142540140356665)
  ·
    refine ⟨86718296487106905105267499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115624395316142540140356665 86718296487106905105267499)
    ·
      refine ⟨130077444730660357657901249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86718296487106905105267499 130077444730660357657901249)
      ·
        refine ⟨97558083547995268243425937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130077444730660357657901249 97558083547995268243425937)
        ·
          refine ⟨73168562660996451182569453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97558083547995268243425937 73168562660996451182569453)
          ·
            refine ⟨27438210997873669193463545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73168562660996451182569453 27438210997873669193463545)
            ·
              refine ⟨20578658248405251895097659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27438210997873669193463545 20578658248405251895097659)
              ·
                refine ⟨30867987372607877842646489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20578658248405251895097659 30867987372607877842646489)
                ·
                  refine ⟨23150990529455908381984867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30867987372607877842646489 23150990529455908381984867)
                  ·
                    refine ⟨34726485794183862572977301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23150990529455908381984867 34726485794183862572977301)
                    ·
                      refine ⟨1627804021602368558108311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34726485794183862572977301 1627804021602368558108311)
                      ·
                        rfl

theorem cell23_3170137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3170137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170137 prefixEnd_3170137 := by exact prefixLift 3170137
  have htrace : WordTrace (prefixWord ++ tailWord_3170137) baseStart_3170137 baseEnd_3170137 := by
    simpa [prefixWord, tailWord_3170137, baseEnd_3170137] using wordTrace_append hprefix tailTrace_3170137
  have hstable : (prefixWord ++ tailWord_3170137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170137).length < 2 ^ (prefixWord ++ tailWord_3170137).sum := by decide
  have hdescent : baseEnd_3170137 < baseStart_3170137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170158 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_3170158 : Nat := 118140960795 + 3170158 * 2 ^ 59
def prefixEnd_3170158 : Nat := 4983230072969 + 3 ^ 40 * 3170158 * 2
def baseEnd_3170158 : Nat := 1627814804696112975945715

theorem tailTrace_3170158 : CollatzResearch.WordTrace tailWord_3170158 prefixEnd_3170158 1627814804696112975945715 := by
  unfold tailWord_3170158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453145156133307590858891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77083440832710973817914085 14453145156133307590858891)
  ·
    refine ⟨21679717734199961386288337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14453145156133307590858891 21679717734199961386288337)
    ·
      refine ⟨16259788300649971039716253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21679717734199961386288337 16259788300649971039716253)
      ·
        refine ⟨6097420612743739139893595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16259788300649971039716253 6097420612743739139893595)
        ·
          refine ⟨9146130919115608709840393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6097420612743739139893595 9146130919115608709840393)
          ·
            refine ⟨6859598189336706532380295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9146130919115608709840393 6859598189336706532380295)
            ·
              refine ⟨10289397284005059798570443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859598189336706532380295 10289397284005059798570443)
              ·
                refine ⟨15434095926007589697855665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289397284005059798570443 15434095926007589697855665)
                ·
                  refine ⟨11575571944505692273391749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15434095926007589697855665 11575571944505692273391749)
                  ·
                    refine ⟨2170419739594817301260953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11575571944505692273391749 2170419739594817301260953)
                    ·
                      refine ⟨1627814804696112975945715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170419739594817301260953 1627814804696112975945715)
                      ·
                        rfl

theorem cell23_3170158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_3170158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170158 prefixEnd_3170158 := by exact prefixLift 3170158
  have htrace : WordTrace (prefixWord ++ tailWord_3170158) baseStart_3170158 baseEnd_3170158 := by
    simpa [prefixWord, tailWord_3170158, baseEnd_3170158] using wordTrace_append hprefix tailTrace_3170158
  have hstable : (prefixWord ++ tailWord_3170158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170158).length < 2 ^ (prefixWord ++ tailWord_3170158).sum := by decide
  have hdescent : baseEnd_3170158 < baseStart_3170158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170187 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5]
def baseStart_3170187 : Nat := 118140960795 + 3170187 * 2 ^ 59
def prefixEnd_3170187 : Nat := 4983230072969 + 3 ^ 40 * 3170187 * 2
def baseEnd_3170187 : Nat := 1627829695635093362483081

theorem tailTrace_3170187 : CollatzResearch.WordTrace tailWord_3170187 prefixEnd_3170187 1627829695635093362483081 := by
  unfold tailWord_3170187
  simp only [CollatzResearch.WordTrace]
  refine ⟨115626218965961398679676815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77084145977307599119784543 115626218965961398679676815)
  ·
    refine ⟨173439328448942098019515223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115626218965961398679676815 173439328448942098019515223)
    ·
      refine ⟨260158992673413147029272835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173439328448942098019515223 260158992673413147029272835)
      ·
        refine ⟨390238489010119720543909253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260158992673413147029272835 390238489010119720543909253)
        ·
          refine ⟨73169716689397447601982985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390238489010119720543909253 73169716689397447601982985)
          ·
            refine ⟨54877287517048085701487239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73169716689397447601982985 54877287517048085701487239)
            ·
              refine ⟨82315931275572128552230859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54877287517048085701487239 82315931275572128552230859)
              ·
                refine ⟨123473896913358192828346289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82315931275572128552230859 123473896913358192828346289)
                ·
                  refine ⟨92605422685018644621259717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123473896913358192828346289 92605422685018644621259717)
                  ·
                    refine ⟨17363516753440995866486197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92605422685018644621259717 17363516753440995866486197)
                    ·
                      refine ⟨1627829695635093362483081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17363516753440995866486197 1627829695635093362483081)
                      ·
                        rfl

theorem cell23_3170187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_3170187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170187 prefixEnd_3170187 := by exact prefixLift 3170187
  have htrace : WordTrace (prefixWord ++ tailWord_3170187) baseStart_3170187 baseEnd_3170187 := by
    simpa [prefixWord, tailWord_3170187, baseEnd_3170187] using wordTrace_append hprefix tailTrace_3170187
  have hstable : (prefixWord ++ tailWord_3170187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170187).length < 2 ^ (prefixWord ++ tailWord_3170187).sum := by decide
  have hdescent : baseEnd_3170187 < baseStart_3170187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170201 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 2, 3, 2]
def baseStart_3170201 : Nat := 118140960795 + 3170201 * 2 ^ 59
def prefixEnd_3170201 : Nat := 4983230072969 + 3 ^ 40 * 3170201 * 2
def baseEnd_3170201 : Nat := 1627836884364256307708017

theorem tailTrace_3170201 : CollatzResearch.WordTrace tailWord_3170201 prefixEnd_3170201 1627836884364256307708017 := by
  unfold tailWord_3170201
  simp only [CollatzResearch.WordTrace]
  refine ⟨115626729587910679070686457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77084486391940452713790971 115626729587910679070686457)
  ·
    refine ⟨86720047190933009303014843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115626729587910679070686457 86720047190933009303014843)
    ·
      refine ⟨130080070786399513954522265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86720047190933009303014843 130080070786399513954522265)
      ·
        refine ⟨97560053089799635465891699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130080070786399513954522265 97560053089799635465891699)
        ·
          refine ⟨146340079634699453198837549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97560053089799635465891699 146340079634699453198837549)
          ·
            refine ⟨54877529863012294949564081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146340079634699453198837549 54877529863012294949564081)
            ·
              refine ⟨41158147397259221212173061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54877529863012294949564081 41158147397259221212173061)
              ·
                refine ⟨7717152636986103977282449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41158147397259221212173061 7717152636986103977282449)
                ·
                  refine ⟨5787864477739577982961837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717152636986103977282449 5787864477739577982961837)
                  ·
                    refine ⟨2170449179152341743610689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5787864477739577982961837 2170449179152341743610689)
                    ·
                      refine ⟨1627836884364256307708017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170449179152341743610689 1627836884364256307708017)
                      ·
                        rfl

theorem cell23_3170201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_3170201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170201 prefixEnd_3170201 := by exact prefixLift 3170201
  have htrace : WordTrace (prefixWord ++ tailWord_3170201) baseStart_3170201 baseEnd_3170201 := by
    simpa [prefixWord, tailWord_3170201, baseEnd_3170201] using wordTrace_append hprefix tailTrace_3170201
  have hstable : (prefixWord ++ tailWord_3170201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170201).length < 2 ^ (prefixWord ++ tailWord_3170201).sum := by decide
  have hdescent : baseEnd_3170201 < baseStart_3170201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170251 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 3]
def baseStart_3170251 : Nat := 118140960795 + 3170251 * 2 ^ 59
def prefixEnd_3170251 : Nat := 4983230072969 + 3 ^ 40 * 3170251 * 2
def baseEnd_3170251 : Nat := 1627862558396981112082787

theorem tailTrace_3170251 : CollatzResearch.WordTrace tailWord_3170251 prefixEnd_3170251 1627862558396981112082787 := by
  unfold tailWord_3170251
  simp only [CollatzResearch.WordTrace]
  refine ⟨115628553237729537610006607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77085702158486358406671071 115628553237729537610006607)
  ·
    refine ⟨173442829856594306415009911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115628553237729537610006607 173442829856594306415009911)
    ·
      refine ⟨260164244784891459622514867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173442829856594306415009911 260164244784891459622514867)
      ·
        refine ⟨390246367177337189433772301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260164244784891459622514867 390246367177337189433772301)
        ·
          refine ⟨146342387691501446037664613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390246367177337189433772301 146342387691501446037664613)
          ·
            refine ⟨27439197692156521132062115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146342387691501446037664613 27439197692156521132062115)
            ·
              refine ⟨41158796538234781698093173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27439197692156521132062115 41158796538234781698093173)
              ·
                refine ⟨3858637175459510784196235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41158796538234781698093173 3858637175459510784196235)
                ·
                  refine ⟨5787955763189266176294353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858637175459510784196235 5787955763189266176294353)
                  ·
                    refine ⟨4340966822391949632220765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5787955763189266176294353 4340966822391949632220765)
                    ·
                      refine ⟨1627862558396981112082787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4340966822391949632220765 1627862558396981112082787)
                      ·
                        rfl

theorem cell23_3170251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 2, 3].length) (baseStart_3170251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170251 prefixEnd_3170251 := by exact prefixLift 3170251
  have htrace : WordTrace (prefixWord ++ tailWord_3170251) baseStart_3170251 baseEnd_3170251 := by
    simpa [prefixWord, tailWord_3170251, baseEnd_3170251] using wordTrace_append hprefix tailTrace_3170251
  have hstable : (prefixWord ++ tailWord_3170251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170251).length < 2 ^ (prefixWord ++ tailWord_3170251).sum := by decide
  have hdescent : baseEnd_3170251 < baseStart_3170251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170275 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 2, 4]
def baseStart_3170275 : Nat := 118140960795 + 3170275 * 2 ^ 59
def prefixEnd_3170275 : Nat := 4983230072969 + 3 ^ 40 * 3170275 * 2
def baseEnd_3170275 : Nat := 542624960644229672727559

theorem tailTrace_3170275 : CollatzResearch.WordTrace tailWord_3170275 prefixEnd_3170275 542624960644229672727559 := by
  unfold tailWord_3170275
  simp only [CollatzResearch.WordTrace]
  refine ⟨115629428589642589708880279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77086285726428393139253519 115629428589642589708880279)
  ·
    refine ⟨173444142884463884563320419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115629428589642589708880279 173444142884463884563320419)
    ·
      refine ⟨260166214326695826844980629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173444142884463884563320419 260166214326695826844980629)
      ·
        refine ⟨12195291296563866883358467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 260166214326695826844980629 12195291296563866883358467)
        ·
          refine ⟨18292936944845800325037701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12195291296563866883358467 18292936944845800325037701)
          ·
            refine ⟨3429925677158587560944569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18292936944845800325037701 3429925677158587560944569)
            ·
              refine ⟨2572444257868940670708427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429925677158587560944569 2572444257868940670708427)
              ·
                refine ⟨3858666386803411006062641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572444257868940670708427 3858666386803411006062641)
                ·
                  refine ⟨2893999790102558254546981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3858666386803411006062641 2893999790102558254546981)
                  ·
                    refine ⟨542624960644229672727559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893999790102558254546981 542624960644229672727559)
                    ·
                      rfl

theorem cell23_3170275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 2, 4].length) (baseStart_3170275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170275 prefixEnd_3170275 := by exact prefixLift 3170275
  have htrace : WordTrace (prefixWord ++ tailWord_3170275) baseStart_3170275 baseEnd_3170275 := by
    simpa [prefixWord, tailWord_3170275, baseEnd_3170275] using wordTrace_append hprefix tailTrace_3170275
  have hstable : (prefixWord ++ tailWord_3170275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170275).length < 2 ^ (prefixWord ++ tailWord_3170275).sum := by decide
  have hdescent : baseEnd_3170275 < baseStart_3170275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170285 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3170285 : Nat := 118140960795 + 3170285 * 2 ^ 59
def prefixEnd_3170285 : Nat := 4983230072969 + 3 ^ 40 * 3170285 * 2
def baseEnd_3170285 : Nat := 1627880016739233979057631

theorem tailTrace_3170285 : CollatzResearch.WordTrace tailWord_3170285 prefixEnd_3170285 1627880016739233979057631 := by
  unfold tailWord_3170285
  simp only [CollatzResearch.WordTrace]
  refine ⟨115629793319606361416744309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77086528879737574277829539 115629793319606361416744309)
  ·
    refine ⟨10840293123713096382819779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115629793319606361416744309 10840293123713096382819779)
    ·
      refine ⟨16260439685569644574229669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10840293123713096382819779 16260439685569644574229669)
      ·
        refine ⟨3048832441044308357668063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16260439685569644574229669 3048832441044308357668063)
        ·
          refine ⟨4573248661566462536502095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3048832441044308357668063 4573248661566462536502095)
          ·
            refine ⟨6859872992349693804753143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573248661566462536502095 6859872992349693804753143)
            ·
              refine ⟨10289809488524540707129715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859872992349693804753143 10289809488524540707129715)
              ·
                refine ⟨15434714232786811060694573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289809488524540707129715 15434714232786811060694573)
                ·
                  refine ⟨5788017837295054147760465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15434714232786811060694573 5788017837295054147760465)
                  ·
                    refine ⟨4341013377971290610820349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5788017837295054147760465 4341013377971290610820349)
                    ·
                      refine ⟨1627880016739233979057631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4341013377971290610820349 1627880016739233979057631)
                      ·
                        rfl

theorem cell23_3170285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3170285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170285 prefixEnd_3170285 := by exact prefixLift 3170285
  have htrace : WordTrace (prefixWord ++ tailWord_3170285) baseStart_3170285 baseEnd_3170285 := by
    simpa [prefixWord, tailWord_3170285, baseEnd_3170285] using wordTrace_append hprefix tailTrace_3170285
  have hstable : (prefixWord ++ tailWord_3170285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170285).length < 2 ^ (prefixWord ++ tailWord_3170285).sum := by decide
  have hdescent : baseEnd_3170285 < baseStart_3170285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170302 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3170302 : Nat := 118140960795 + 3170302 * 2 ^ 59
def prefixEnd_3170302 : Nat := 4983230072969 + 3 ^ 40 * 3170302 * 2
def baseEnd_3170302 : Nat := 1627888745910360412545053

theorem tailTrace_3170302 : CollatzResearch.WordTrace tailWord_3170302 prefixEnd_3170302 1627888745910360412545053 := by
  unfold tailWord_3170302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453801670068096665014145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77086942240363182213408773 14453801670068096665014145)
  ·
    refine ⟨10840351252551072498760609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14453801670068096665014145 10840351252551072498760609)
    ·
      refine ⟨8130263439413304374070457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10840351252551072498760609 8130263439413304374070457)
      ·
        refine ⟨6097697579559978280552843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8130263439413304374070457 6097697579559978280552843)
        ·
          refine ⟨9146546369339967420829265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6097697579559978280552843 9146546369339967420829265)
          ·
            refine ⟨6859909777004975565621949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9146546369339967420829265 6859909777004975565621949)
            ·
              refine ⟨2572466166376865837108231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6859909777004975565621949 2572466166376865837108231)
              ·
                refine ⟨3858699249565298755662347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572466166376865837108231 3858699249565298755662347)
                ·
                  refine ⟨5788048874347948133493521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858699249565298755662347 5788048874347948133493521)
                  ·
                    refine ⟨4341036655760961100120141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5788048874347948133493521 4341036655760961100120141)
                    ·
                      refine ⟨1627888745910360412545053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4341036655760961100120141 1627888745910360412545053)
                      ·
                        rfl

theorem cell23_3170302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3170302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170302 prefixEnd_3170302 := by exact prefixLift 3170302
  have htrace : WordTrace (prefixWord ++ tailWord_3170302) baseStart_3170302 baseEnd_3170302 := by
    simpa [prefixWord, tailWord_3170302, baseEnd_3170302] using wordTrace_append hprefix tailTrace_3170302
  have hstable : (prefixWord ++ tailWord_3170302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170302).length < 2 ^ (prefixWord ++ tailWord_3170302).sum := by decide
  have hdescent : baseEnd_3170302 < baseStart_3170302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170310 : List Nat := [6, 2, 1, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3170310 : Nat := 118140960795 + 3170310 * 2 ^ 59
def prefixEnd_3170310 : Nat := 4983230072969 + 3 ^ 40 * 3170310 * 2
def baseEnd_3170310 : Nat := 1627892853755596381245017

theorem tailTrace_3170310 : CollatzResearch.WordTrace tailWord_3170310 prefixEnd_3170310 1627892853755596381245017 := by
  unfold tailWord_3170310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613459535766118458950137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77087136763010527124269589 3613459535766118458950137)
  ·
    refine ⟨2710094651824588844212603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3613459535766118458950137 2710094651824588844212603)
    ·
      refine ⟨4065141977736883266318905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710094651824588844212603 4065141977736883266318905)
      ·
        refine ⟨3048856483302662449739179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4065141977736883266318905 3048856483302662449739179)
        ·
          refine ⟨4573284724953993674608769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3048856483302662449739179 4573284724953993674608769)
          ·
            refine ⟨3429963543715495255956577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4573284724953993674608769 3429963543715495255956577)
            ·
              refine ⟨2572472657786621441967433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429963543715495255956577 2572472657786621441967433)
              ·
                refine ⟨1929354493339966081475575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572472657786621441967433 1929354493339966081475575)
                ·
                  refine ⟨2894031740009949122213363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929354493339966081475575 2894031740009949122213363)
                  ·
                    refine ⟨4341047610014923683320045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2894031740009949122213363 4341047610014923683320045)
                    ·
                      refine ⟨1627892853755596381245017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4341047610014923683320045 1627892853755596381245017)
                      ·
                        rfl

theorem cell23_3170310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3170310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170310 prefixEnd_3170310 := by exact prefixLift 3170310
  have htrace : WordTrace (prefixWord ++ tailWord_3170310) baseStart_3170310 baseEnd_3170310 := by
    simpa [prefixWord, tailWord_3170310, baseEnd_3170310] using wordTrace_append hprefix tailTrace_3170310
  have hstable : (prefixWord ++ tailWord_3170310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170310).length < 2 ^ (prefixWord ++ tailWord_3170310).sum := by decide
  have hdescent : baseEnd_3170310 < baseStart_3170310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170428 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_3170428 : Nat := 118140960795 + 3170428 * 2 ^ 59
def prefixEnd_3170428 : Nat := 4983230072969 + 3 ^ 40 * 3170428 * 2
def baseEnd_3170428 : Nat := 1627953444472826919569473

theorem tailTrace_3170428 : CollatzResearch.WordTrace tailWord_3170428 prefixEnd_3170428 1627953444472826919569473 := by
  unfold tailWord_3170428
  simp only [CollatzResearch.WordTrace]
  refine ⟨57817504479044148419599969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77090005972058864559466625 57817504479044148419599969)
  ·
    refine ⟨43363128359283111314699977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57817504479044148419599969 43363128359283111314699977)
    ·
      refine ⟨32522346269462333486024983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43363128359283111314699977 32522346269462333486024983)
      ·
        refine ⟨48783519404193500229037475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32522346269462333486024983 48783519404193500229037475)
        ·
          refine ⟨73175279106290250343556213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48783519404193500229037475 73175279106290250343556213)
          ·
            refine ⟨6860182416214710969708395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73175279106290250343556213 6860182416214710969708395)
            ·
              refine ⟨10290273624322066454562593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6860182416214710969708395 10290273624322066454562593)
              ·
                refine ⟨7717705218241549840921945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10290273624322066454562593 7717705218241549840921945)
                ·
                  refine ⟨5788278913681162380691459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717705218241549840921945 5788278913681162380691459)
                  ·
                    refine ⟨8682418370521743571037189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788278913681162380691459 8682418370521743571037189)
                    ·
                      refine ⟨1627953444472826919569473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8682418370521743571037189 1627953444472826919569473)
                      ·
                        rfl

theorem cell23_3170428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_3170428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170428 prefixEnd_3170428 := by exact prefixLift 3170428
  have htrace : WordTrace (prefixWord ++ tailWord_3170428) baseStart_3170428 baseEnd_3170428 := by
    simpa [prefixWord, tailWord_3170428, baseEnd_3170428] using wordTrace_append hprefix tailTrace_3170428
  have hstable : (prefixWord ++ tailWord_3170428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170428).length < 2 ^ (prefixWord ++ tailWord_3170428).sum := by decide
  have hdescent : baseEnd_3170428 < baseStart_3170428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170462 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3170462 : Nat := 118140960795 + 3170462 * 2 ^ 59
def prefixEnd_3170462 : Nat := 4983230072969 + 3 ^ 40 * 3170462 * 2
def baseEnd_3170462 : Nat := 1627970902815079786544317

theorem tailTrace_3170462 : CollatzResearch.WordTrace tailWord_3170462 prefixEnd_3170462 1627970902815079786544317 := by
  unfold tailWord_3170462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454531129995640080742205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77090832693310080430625093 14454531129995640080742205)
  ·
    refine ⟨5420449173748365030278327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14454531129995640080742205 5420449173748365030278327)
    ·
      refine ⟨8130673760622547545417491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420449173748365030278327 8130673760622547545417491)
      ·
        refine ⟨12196010640933821318126237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130673760622547545417491 12196010640933821318126237)
        ·
          refine ⟨4573503990350182994297339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12196010640933821318126237 4573503990350182994297339)
          ·
            refine ⟨6860255985525274491446009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573503990350182994297339 6860255985525274491446009)
            ·
              refine ⟨5145191989143955868584507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860255985525274491446009 5145191989143955868584507)
              ·
                refine ⟨7717787983715933802876761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145191989143955868584507 7717787983715933802876761)
                ·
                  refine ⟨5788340987786950352157571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717787983715933802876761 5788340987786950352157571)
                  ·
                    refine ⟨8682511481680425528236357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788340987786950352157571 8682511481680425528236357)
                    ·
                      refine ⟨1627970902815079786544317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8682511481680425528236357 1627970902815079786544317)
                      ·
                        rfl

theorem cell23_3170462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3170462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170462 prefixEnd_3170462 := by exact prefixLift 3170462
  have htrace : WordTrace (prefixWord ++ tailWord_3170462) baseStart_3170462 baseEnd_3170462 := by
    simpa [prefixWord, tailWord_3170462, baseEnd_3170462] using wordTrace_append hprefix tailTrace_3170462
  have hstable : (prefixWord ++ tailWord_3170462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170462).length < 2 ^ (prefixWord ++ tailWord_3170462).sum := by decide
  have hdescent : baseEnd_3170462 < baseStart_3170462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170465 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3170465 : Nat := 118140960795 + 3170465 * 2 ^ 59
def prefixEnd_3170465 : Nat := 4983230072969 + 3 ^ 40 * 3170465 * 2
def baseEnd_3170465 : Nat := 1627972443257043274806803

theorem tailTrace_3170465 : CollatzResearch.WordTrace tailWord_3170465 prefixEnd_3170465 1627972443257043274806803 := by
  unfold tailWord_3170465
  simp only [CollatzResearch.WordTrace]
  refine ⟨115636358458954252158296849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77090905639302834772197899 115636358458954252158296849)
  ·
    refine ⟨86727268844215689118722637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115636358458954252158296849 86727268844215689118722637)
    ·
      refine ⟨32522725816580883419520989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86727268844215689118722637 32522725816580883419520989)
      ·
        refine ⟨12196022181217831282320371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32522725816580883419520989 12196022181217831282320371)
        ·
          refine ⟨18294033271826746923480557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196022181217831282320371 18294033271826746923480557)
          ·
            refine ⟨6860262476935030096305209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18294033271826746923480557 6860262476935030096305209)
            ·
              refine ⟨5145196857701272572228907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6860262476935030096305209 5145196857701272572228907)
              ·
                refine ⟨7717795286551908858343361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145196857701272572228907 7717795286551908858343361)
                ·
                  refine ⟨5788346464913931643757521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7717795286551908858343361 5788346464913931643757521)
                  ·
                    refine ⟨4341259848685448732818141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5788346464913931643757521 4341259848685448732818141)
                    ·
                      refine ⟨1627972443257043274806803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4341259848685448732818141 1627972443257043274806803)
                      ·
                        rfl

theorem cell23_3170465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3170465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170465 prefixEnd_3170465 := by exact prefixLift 3170465
  have htrace : WordTrace (prefixWord ++ tailWord_3170465) baseStart_3170465 baseEnd_3170465 := by
    simpa [prefixWord, tailWord_3170465, baseEnd_3170465] using wordTrace_append hprefix tailTrace_3170465
  have hstable : (prefixWord ++ tailWord_3170465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170465).length < 2 ^ (prefixWord ++ tailWord_3170465).sum := by decide
  have hdescent : baseEnd_3170465 < baseStart_3170465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170528 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 4, 4]
def baseStart_3170528 : Nat := 118140960795 + 3170528 * 2 ^ 59
def prefixEnd_3170528 : Nat := 4983230072969 + 3 ^ 40 * 3170528 * 2
def baseEnd_3170528 : Nat := 542668264179425509439671

theorem tailTrace_3170528 : CollatzResearch.WordTrace tailWord_3170528 prefixEnd_3170528 542668264179425509439671 := by
  unfold tailWord_3170528
  simp only [CollatzResearch.WordTrace]
  refine ⟨57819328128863006958920119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77092437505150675945226825 57819328128863006958920119)
  ·
    refine ⟨86728992193294510438380179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57819328128863006958920119 86728992193294510438380179)
    ·
      refine ⟨130093488289941765657570269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86728992193294510438380179 130093488289941765657570269)
      ·
        refine ⟨48785058108728162121588851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130093488289941765657570269 48785058108728162121588851)
        ·
          refine ⟨73177587163092243182383277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48785058108728162121588851 73177587163092243182383277)
          ·
            refine ⟨27441595186159591193393729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73177587163092243182383277 27441595186159591193393729)
            ·
              refine ⟨20581196389619693395045297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27441595186159591193393729 20581196389619693395045297)
              ·
                refine ⟨15435897292214770046283973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20581196389619693395045297 15435897292214770046283973)
                ·
                  refine ⟨2894230742290269383678245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15435897292214770046283973 2894230742290269383678245)
                  ·
                    refine ⟨542668264179425509439671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2894230742290269383678245 542668264179425509439671)
                    ·
                      rfl

theorem cell23_3170528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_3170528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170528 prefixEnd_3170528 := by exact prefixLift 3170528
  have htrace : WordTrace (prefixWord ++ tailWord_3170528) baseStart_3170528 baseEnd_3170528 := by
    simpa [prefixWord, tailWord_3170528, baseEnd_3170528] using wordTrace_append hprefix tailTrace_3170528
  have hstable : (prefixWord ++ tailWord_3170528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170528).length < 2 ^ (prefixWord ++ tailWord_3170528).sum := by decide
  have hdescent : baseEnd_3170528 < baseStart_3170528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170538 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3170538 : Nat := 118140960795 + 3170538 * 2 ^ 59
def prefixEnd_3170538 : Nat := 4983230072969 + 3 ^ 40 * 3170538 * 2
def baseEnd_3170538 : Nat := 1628009927344821489193967

theorem tailTrace_3170538 : CollatzResearch.WordTrace tailWord_3170538 prefixEnd_3170538 1628009927344821489193967 := by
  unfold tailWord_3170538
  simp only [CollatzResearch.WordTrace]
  refine ⟨28909755246922446406426067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77092680658459857083802845 28909755246922446406426067)
  ·
    refine ⟨43364632870383669609639101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28909755246922446406426067 43364632870383669609639101)
    ·
      refine ⟨16261737326393876103614663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43364632870383669609639101 16261737326393876103614663)
      ·
        refine ⟨24392605989590814155421995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16261737326393876103614663 24392605989590814155421995)
        ·
          refine ⟨36588908984386221233132993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24392605989590814155421995 36588908984386221233132993)
          ·
            refine ⟨27441681738289665924849745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36588908984386221233132993 27441681738289665924849745)
            ·
              refine ⟨20581261303717249443637309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27441681738289665924849745 20581261303717249443637309)
              ·
                refine ⟨7717972988893968541363991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20581261303717249443637309 7717972988893968541363991)
                ·
                  refine ⟨11576959483340952812045987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7717972988893968541363991 11576959483340952812045987)
                  ·
                    refine ⟨17365439225011429218068981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11576959483340952812045987 17365439225011429218068981)
                    ·
                      refine ⟨1628009927344821489193967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17365439225011429218068981 1628009927344821489193967)
                      ·
                        rfl

theorem cell23_3170538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3170538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170538 prefixEnd_3170538 := by exact prefixLift 3170538
  have htrace : WordTrace (prefixWord ++ tailWord_3170538) baseStart_3170538 baseEnd_3170538 := by
    simpa [prefixWord, tailWord_3170538, baseEnd_3170538] using wordTrace_append hprefix tailTrace_3170538
  have hstable : (prefixWord ++ tailWord_3170538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170538).length < 2 ^ (prefixWord ++ tailWord_3170538).sum := by decide
  have hdescent : baseEnd_3170538 < baseStart_3170538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170545 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 2, 4]
def baseStart_3170545 : Nat := 118140960795 + 3170545 * 2 ^ 59
def prefixEnd_3170545 : Nat := 4983230072969 + 3 ^ 40 * 3170545 * 2
def baseEnd_3170545 : Nat := 542671173903134320602145

theorem tailTrace_3170545 : CollatzResearch.WordTrace tailWord_3170545 prefixEnd_3170545 542671173903134320602145 := by
  unfold tailWord_3170545
  simp only [CollatzResearch.WordTrace]
  refine ⟨115639276298664425821209089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77092850865776283880806059 115639276298664425821209089)
  ·
    refine ⟨86729457223998319365906817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115639276298664425821209089 86729457223998319365906817)
    ·
      refine ⟨65047092917998739524430113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86729457223998319365906817 65047092917998739524430113)
      ·
        refine ⟨48785319688499054643322585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65047092917998739524430113 48785319688499054643322585)
        ·
          refine ⟨36588989766374290982491939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48785319688499054643322585 36588989766374290982491939)
          ·
            refine ⟨54883484649561436473737909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36588989766374290982491939 54883484649561436473737909)
            ·
              refine ⟨5145326685896384669412929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54883484649561436473737909 5145326685896384669412929)
              ·
                refine ⟨3858995014422288502059697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145326685896384669412929 3858995014422288502059697)
                ·
                  refine ⟨2894246260816716376544773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3858995014422288502059697 2894246260816716376544773)
                  ·
                    refine ⟨542671173903134320602145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2894246260816716376544773 542671173903134320602145)
                    ·
                      rfl

theorem cell23_3170545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_3170545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170545 prefixEnd_3170545 := by exact prefixLift 3170545
  have htrace : WordTrace (prefixWord ++ tailWord_3170545) baseStart_3170545 baseEnd_3170545 := by
    simpa [prefixWord, tailWord_3170545, baseEnd_3170545] using wordTrace_append hprefix tailTrace_3170545
  have hstable : (prefixWord ++ tailWord_3170545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170545).length < 2 ^ (prefixWord ++ tailWord_3170545).sum := by decide
  have hdescent : baseEnd_3170545 < baseStart_3170545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170558 : List Nat := [4, 2, 2, 1, 1, 1, 2, 10]
def baseStart_3170558 : Nat := 118140960795 + 3170558 * 2 ^ 59
def prefixEnd_3170558 : Nat := 4983230072969 + 3 ^ 40 * 3170558 * 2
def baseEnd_3170558 : Nat := 60297044331774496701625

theorem tailTrace_3170558 : CollatzResearch.WordTrace tailWord_3170558 prefixEnd_3170558 60297044331774496701625 := by
  unfold tailWord_3170558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454968805952166130179041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77093166965078219360954885 14454968805952166130179041)
  ·
    refine ⟨10841226604464124597634281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14454968805952166130179041 10841226604464124597634281)
    ·
      refine ⟨8130919953348093448225711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10841226604464124597634281 8130919953348093448225711)
      ·
        refine ⟨12196379930022140172338567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130919953348093448225711 12196379930022140172338567)
        ·
          refine ⟨18294569895033210258507851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196379930022140172338567 18294569895033210258507851)
          ·
            refine ⟨27441854842549815387761777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18294569895033210258507851 27441854842549815387761777)
            ·
              refine ⟨20581391131912361540821333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27441854842549815387761777 20581391131912361540821333)
              ·
                refine ⟨60297044331774496701625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20581391131912361540821333 60297044331774496701625)
                ·
                  rfl

theorem cell23_3170558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_3170558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170558 prefixEnd_3170558 := by exact prefixLift 3170558
  have htrace : WordTrace (prefixWord ++ tailWord_3170558) baseStart_3170558 baseEnd_3170558 := by
    simpa [prefixWord, tailWord_3170558, baseEnd_3170558] using wordTrace_append hprefix tailTrace_3170558
  have hstable : (prefixWord ++ tailWord_3170558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170558).length < 2 ^ (prefixWord ++ tailWord_3170558).sum := by decide
  have hdescent : baseEnd_3170558 < baseStart_3170558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170562 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3170562 : Nat := 118140960795 + 3170562 * 2 ^ 59
def prefixEnd_3170562 : Nat := 4983230072969 + 3 ^ 40 * 3170562 * 2
def baseEnd_3170562 : Nat := 542674083626843131764619

theorem tailTrace_3170562 : CollatzResearch.WordTrace tailWord_3170562 prefixEnd_3170562 542674083626843131764619 := by
  unfold tailWord_3170562
  simp only [CollatzResearch.WordTrace]
  refine ⟨28909974084900709431144485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77093264226401891816385293 28909974084900709431144485)
  ·
    refine ⟨5420620140918883018339591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28909974084900709431144485 5420620140918883018339591)
    ·
      refine ⟨8130930211378324527509387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420620140918883018339591 8130930211378324527509387)
      ·
        refine ⟨12196395317067486791264081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130930211378324527509387 12196395317067486791264081)
        ·
          refine ⟨9147296487800615093448061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12196395317067486791264081 9147296487800615093448061)
          ·
            refine ⟨3430236182925230660043023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9147296487800615093448061 3430236182925230660043023)
            ·
              refine ⟨5145354274387845990064535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430236182925230660043023 5145354274387845990064535)
              ·
                refine ⟨7718031411581768985096803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5145354274387845990064535 7718031411581768985096803)
                ·
                  refine ⟨11577047117372653477645205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7718031411581768985096803 11577047117372653477645205)
                  ·
                    refine ⟨542674083626843131764619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11577047117372653477645205 542674083626843131764619)
                    ·
                      rfl

theorem cell23_3170562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3170562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170562 prefixEnd_3170562 := by exact prefixLift 3170562
  have htrace : WordTrace (prefixWord ++ tailWord_3170562) baseStart_3170562 baseEnd_3170562 := by
    simpa [prefixWord, tailWord_3170562, baseEnd_3170562] using wordTrace_append hprefix tailTrace_3170562
  have hstable : (prefixWord ++ tailWord_3170562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170562).length < 2 ^ (prefixWord ++ tailWord_3170562).sum := by decide
  have hdescent : baseEnd_3170562 < baseStart_3170562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170638 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3170638 : Nat := 118140960795 + 3170638 * 2 ^ 59
def prefixEnd_3170638 : Nat := 4983230072969 + 3 ^ 40 * 3170638 * 2
def baseEnd_3170638 : Nat := 1628061275410271097943507

theorem tailTrace_3170638 : CollatzResearch.WordTrace tailWord_3170638 prefixEnd_3170638 1628061275410271097943507 := by
  unfold tailWord_3170638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455333535915937838043071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77095112191551668469563045 14455333535915937838043071)
  ·
    refine ⟨21683000303873906757064607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14455333535915937838043071 21683000303873906757064607)
    ·
      refine ⟨32524500455810860135596911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21683000303873906757064607 32524500455810860135596911)
      ·
        refine ⟨48786750683716290203395367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32524500455810860135596911 48786750683716290203395367)
        ·
          refine ⟨73180126025574435305093051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48786750683716290203395367 73180126025574435305093051)
          ·
            refine ⟨109770189038361652957639577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73180126025574435305093051 109770189038361652957639577)
            ·
              refine ⟨82327641778771239718229683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109770189038361652957639577 82327641778771239718229683)
              ·
                refine ⟨123491462668156859577344525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82327641778771239718229683 123491462668156859577344525)
                ·
                  refine ⟨46309298500558822341504197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123491462668156859577344525 46309298500558822341504197)
                  ·
                    refine ⟨8682993468854779189032037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46309298500558822341504197 8682993468854779189032037)
                    ·
                      refine ⟨1628061275410271097943507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8682993468854779189032037 1628061275410271097943507)
                      ·
                        rfl

theorem cell23_3170638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3170638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170638 prefixEnd_3170638 := by exact prefixLift 3170638
  have htrace : WordTrace (prefixWord ++ tailWord_3170638) baseStart_3170638 baseEnd_3170638 := by
    simpa [prefixWord, tailWord_3170638, baseEnd_3170638] using wordTrace_append hprefix tailTrace_3170638
  have hstable : (prefixWord ++ tailWord_3170638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170638).length < 2 ^ (prefixWord ++ tailWord_3170638).sum := by decide
  have hdescent : baseEnd_3170638 < baseStart_3170638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170642 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_3170642 : Nat := 118140960795 + 3170642 * 2 ^ 59
def prefixEnd_3170642 : Nat := 4983230072969 + 3 ^ 40 * 3170642 * 2
def baseEnd_3170642 : Nat := 1628063329332889082293489

theorem tailTrace_3170642 : CollatzResearch.WordTrace tailWord_3170642 prefixEnd_3170642 1628063329332889082293489 := by
  unfold tailWord_3170642
  simp only [CollatzResearch.WordTrace]
  refine ⟨28910703544828252846872545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77095209452875340924993453 28910703544828252846872545)
  ·
    refine ⟨21683027658621189635154409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28910703544828252846872545 21683027658621189635154409)
    ·
      refine ⟨16262270743965892226365807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21683027658621189635154409 16262270743965892226365807)
      ·
        refine ⟨24393406115948838339548711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16262270743965892226365807 24393406115948838339548711)
        ·
          refine ⟨36590109173923257509323067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24393406115948838339548711 36590109173923257509323067)
          ·
            refine ⟨54885163760884886263984601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36590109173923257509323067 54885163760884886263984601)
            ·
              refine ⟨41163872820663664697988451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54885163760884886263984601 41163872820663664697988451)
              ·
                refine ⟨61745809230995497046982677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41163872820663664697988451 61745809230995497046982677)
                ·
                  refine ⟨2894334807702913924077313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61745809230995497046982677 2894334807702913924077313)
                  ·
                    refine ⟨2170751105777185443057985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894334807702913924077313 2170751105777185443057985)
                    ·
                      refine ⟨1628063329332889082293489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170751105777185443057985 1628063329332889082293489)
                      ·
                        rfl

theorem cell23_3170642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_3170642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170642 prefixEnd_3170642 := by exact prefixLift 3170642
  have htrace : WordTrace (prefixWord ++ tailWord_3170642) baseStart_3170642 baseEnd_3170642 := by
    simpa [prefixWord, tailWord_3170642, baseEnd_3170642] using wordTrace_append hprefix tailTrace_3170642
  have hstable : (prefixWord ++ tailWord_3170642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170642).length < 2 ^ (prefixWord ++ tailWord_3170642).sum := by decide
  have hdescent : baseEnd_3170642 < baseStart_3170642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170659 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 2, 2, 2]
def baseStart_3170659 : Nat := 118140960795 + 3170659 * 2 ^ 59
def prefixEnd_3170659 : Nat := 4983230072969 + 3 ^ 40 * 3170659 * 2
def baseEnd_3170659 : Nat := 1628072058504015515780911

theorem tailTrace_3170659 : CollatzResearch.WordTrace tailWord_3170659 prefixEnd_3170659 1628072058504015515780911 := by
  unfold tailWord_3170659
  simp only [CollatzResearch.WordTrace]
  refine ⟨115643434220251423290859031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77095622813500948860572687 115643434220251423290859031)
  ·
    refine ⟨173465151330377134936288547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115643434220251423290859031 173465151330377134936288547)
    ·
      refine ⟨260197726995565702404432821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173465151330377134936288547 260197726995565702404432821)
      ·
        refine ⟨24393536905834284600415577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260197726995565702404432821 24393536905834284600415577)
        ·
          refine ⟨18295152679375713450311683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24393536905834284600415577 18295152679375713450311683)
          ·
            refine ⟨27442729019063570175467525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18295152679375713450311683 27442729019063570175467525)
            ·
              refine ⟨5145511691074419407900161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27442729019063570175467525 5145511691074419407900161)
              ·
                refine ⟨3859133768305814555925121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145511691074419407900161 3859133768305814555925121)
                ·
                  refine ⟨2894350326229360916943841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3859133768305814555925121 2894350326229360916943841)
                  ·
                    refine ⟨2170762744672020687707881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894350326229360916943841 2170762744672020687707881)
                    ·
                      refine ⟨1628072058504015515780911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170762744672020687707881 1628072058504015515780911)
                      ·
                        rfl

theorem cell23_3170659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_3170659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170659 prefixEnd_3170659 := by exact prefixLift 3170659
  have htrace : WordTrace (prefixWord ++ tailWord_3170659) baseStart_3170659 baseEnd_3170659 := by
    simpa [prefixWord, tailWord_3170659, baseEnd_3170659] using wordTrace_append hprefix tailTrace_3170659
  have hstable : (prefixWord ++ tailWord_3170659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170659).length < 2 ^ (prefixWord ++ tailWord_3170659).sum := by decide
  have hdescent : baseEnd_3170659 < baseStart_3170659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170665 : List Nat := [1, 2, 1, 1, 1, 3, 5, 4, 5]
def baseStart_3170665 : Nat := 118140960795 + 3170665 * 2 ^ 59
def prefixEnd_3170665 : Nat := 4983230072969 + 3 ^ 40 * 3170665 * 2
def baseEnd_3170665 : Nat := 180897237709771388033987

theorem tailTrace_3170665 : CollatzResearch.WordTrace tailWord_3170665 prefixEnd_3170665 180897237709771388033987 := by
  unfold tailWord_3170665
  simp only [CollatzResearch.WordTrace]
  refine ⟨115643653058229686315577449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77095768705486457543718299 115643653058229686315577449)
  ·
    refine ⟨86732739793672264736683087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115643653058229686315577449 86732739793672264736683087)
    ·
      refine ⟨130099109690508397105024631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86732739793672264736683087 130099109690508397105024631)
      ·
        refine ⟨195148664535762595657536947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130099109690508397105024631 195148664535762595657536947)
        ·
          refine ⟨292722996803643893486305421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195148664535762595657536947 292722996803643893486305421)
          ·
            refine ⟨109771123801366460057364533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292722996803643893486305421 109771123801366460057364533)
            ·
              refine ⟨10291042856378105630377925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109771123801366460057364533 10291042856378105630377925)
              ·
                refine ⟨1929570535570894805695861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10291042856378105630377925 1929570535570894805695861)
                ·
                  refine ⟨180897237709771388033987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1929570535570894805695861 180897237709771388033987)
                  ·
                    rfl

theorem cell23_3170665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 5].length) (baseStart_3170665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170665 prefixEnd_3170665 := by exact prefixLift 3170665
  have htrace : WordTrace (prefixWord ++ tailWord_3170665) baseStart_3170665 baseEnd_3170665 := by
    simpa [prefixWord, tailWord_3170665, baseEnd_3170665] using wordTrace_append hprefix tailTrace_3170665
  have hstable : (prefixWord ++ tailWord_3170665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170665).length < 2 ^ (prefixWord ++ tailWord_3170665).sum := by decide
  have hdescent : baseEnd_3170665 < baseStart_3170665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170710 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3170710 : Nat := 118140960795 + 3170710 * 2 ^ 59
def prefixEnd_3170710 : Nat := 4983230072969 + 3 ^ 40 * 3170710 * 2
def baseEnd_3170710 : Nat := 1628098246017394816243177

theorem tailTrace_3170710 : CollatzResearch.WordTrace tailWord_3170710 prefixEnd_3170710 1628098246017394816243177 := by
  unfold tailWord_3170710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7227830896441666187560349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77096862895377772667310389 7227830896441666187560349)
  ·
    refine ⟨2710436586165624820335131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7227830896441666187560349 2710436586165624820335131)
    ·
      refine ⟨4065654879248437230502697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710436586165624820335131 4065654879248437230502697)
      ·
        refine ⟨3049241159436327922877023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4065654879248437230502697 3049241159436327922877023)
        ·
          refine ⟨4573861739154491884315535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049241159436327922877023 4573861739154491884315535)
          ·
            refine ⟨6860792608731737826473303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573861739154491884315535 6860792608731737826473303)
            ·
              refine ⟨10291188913097606739709955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6860792608731737826473303 10291188913097606739709955)
              ·
                refine ⟨15436783369646410109564933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10291188913097606739709955 15436783369646410109564933)
                ·
                  refine ⟨2894396881808701895543425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15436783369646410109564933 2894396881808701895543425)
                  ·
                    refine ⟨2170797661356526421657569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894396881808701895543425 2170797661356526421657569)
                    ·
                      refine ⟨1628098246017394816243177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170797661356526421657569 1628098246017394816243177)
                      ·
                        rfl

theorem cell23_3170710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3170710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170710 prefixEnd_3170710 := by exact prefixLift 3170710
  have htrace : WordTrace (prefixWord ++ tailWord_3170710) baseStart_3170710 baseEnd_3170710 := by
    simpa [prefixWord, tailWord_3170710, baseEnd_3170710] using wordTrace_append hprefix tailTrace_3170710
  have hstable : (prefixWord ++ tailWord_3170710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170710).length < 2 ^ (prefixWord ++ tailWord_3170710).sum := by decide
  have hdescent : baseEnd_3170710 < baseStart_3170710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170759 : List Nat := [1, 1, 4, 1, 1, 4, 3, 3, 1, 4]
def baseStart_3170759 : Nat := 118140960795 + 3170759 * 2 ^ 59
def prefixEnd_3170759 : Nat := 4983230072969 + 3 ^ 40 * 3170759 * 2
def baseEnd_3170759 : Nat := 542707802189821708176817

theorem tailTrace_3170759 : CollatzResearch.WordTrace tailWord_3170759 prefixEnd_3170759 542707802189821708176817 := by
  unfold tailWord_3170759
  simp only [CollatzResearch.WordTrace]
  refine ⟨115647081519889140369499331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77098054346592760246332887 115647081519889140369499331)
  ·
    refine ⟨173470622279833710554248997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115647081519889140369499331 173470622279833710554248997)
    ·
      refine ⟨32525741677468820728921687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173470622279833710554248997 32525741677468820728921687)
      ·
        refine ⟨48788612516203231093382531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32525741677468820728921687 48788612516203231093382531)
        ·
          refine ⟨73182918774304846640073797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48788612516203231093382531 73182918774304846640073797)
          ·
            refine ⟨13721797270182158745013837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73182918774304846640073797 13721797270182158745013837)
            ·
              refine ⟨5145673976318309529380189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13721797270182158745013837 5145673976318309529380189)
              ·
                refine ⟨1929627741119366073517571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5145673976318309529380189 1929627741119366073517571)
                ·
                  refine ⟨2894441611679049110276357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929627741119366073517571 2894441611679049110276357)
                  ·
                    refine ⟨542707802189821708176817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2894441611679049110276357 542707802189821708176817)
                    ·
                      rfl

theorem cell23_3170759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_3170759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170759 prefixEnd_3170759 := by exact prefixLift 3170759
  have htrace : WordTrace (prefixWord ++ tailWord_3170759) baseStart_3170759 baseEnd_3170759 := by
    simpa [prefixWord, tailWord_3170759, baseEnd_3170759] using wordTrace_append hprefix tailTrace_3170759
  have hstable : (prefixWord ++ tailWord_3170759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170759).length < 2 ^ (prefixWord ++ tailWord_3170759).sum := by decide
  have hdescent : baseEnd_3170759 < baseStart_3170759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170785 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 3, 5]
def baseStart_3170785 : Nat := 118140960795 + 3170785 * 2 ^ 59
def prefixEnd_3170785 : Nat := 4983230072969 + 3 ^ 40 * 3170785 * 2
def baseEnd_3170785 : Nat := 542712252355494007601777

theorem tailTrace_3170785 : CollatzResearch.WordTrace tailWord_3170785 prefixEnd_3170785 542712252355494007601777 := by
  unfold tailWord_3170785
  simp only [CollatzResearch.WordTrace]
  refine ⟨115648029817794946809945809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77098686545196631206630539 115648029817794946809945809)
  ·
    refine ⟨86736022363346210107459357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115648029817794946809945809 86736022363346210107459357)
    ·
      refine ⟨32526008386254828790297259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86736022363346210107459357 32526008386254828790297259)
      ·
        refine ⟨48789012579382243185445889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32526008386254828790297259 48789012579382243185445889)
        ·
          refine ⟨36591759434536682389084417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48789012579382243185445889 36591759434536682389084417)
          ·
            refine ⟨27443819575902511791813313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36591759434536682389084417 27443819575902511791813313)
            ·
              refine ⟨20582864681926883843859985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27443819575902511791813313 20582864681926883843859985)
              ·
                refine ⟨15437148511445162882894989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20582864681926883843859985 15437148511445162882894989)
                ·
                  refine ⟨5788930691791936081085621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15437148511445162882894989 5788930691791936081085621)
                  ·
                    refine ⟨542712252355494007601777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5788930691791936081085621 542712252355494007601777)
                    ·
                      rfl

theorem cell23_3170785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_3170785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170785 prefixEnd_3170785 := by exact prefixLift 3170785
  have htrace : WordTrace (prefixWord ++ tailWord_3170785) baseStart_3170785 baseEnd_3170785 := by
    simpa [prefixWord, tailWord_3170785, baseEnd_3170785] using wordTrace_append hprefix tailTrace_3170785
  have hstable : (prefixWord ++ tailWord_3170785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170785).length < 2 ^ (prefixWord ++ tailWord_3170785).sum := by decide
  have hdescent : baseEnd_3170785 < baseStart_3170785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170815 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 1, 6]
def baseStart_3170815 : Nat := 118140960795 + 3170815 * 2 ^ 59
def prefixEnd_3170815 : Nat := 4983230072969 + 3 ^ 40 * 3170815 * 2
def baseEnd_3170815 : Nat := 542717387162038968476731

theorem tailTrace_3170815 : CollatzResearch.WordTrace tailWord_3170815 prefixEnd_3170815 542717387162038968476731 := by
  unfold tailWord_3170815
  simp only [CollatzResearch.WordTrace]
  refine ⟨115649124007686261933537899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77099416005124174622358599 115649124007686261933537899)
  ·
    refine ⟨173473686011529392900306849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115649124007686261933537899 173473686011529392900306849)
    ·
      refine ⟨130105264508647044675230137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173473686011529392900306849 130105264508647044675230137)
      ·
        refine ⟨97578948381485283506422603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130105264508647044675230137 97578948381485283506422603)
        ·
          refine ⟨146368422572227925259633905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97578948381485283506422603 146368422572227925259633905)
          ·
            refine ⟨109776316929170943944725429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146368422572227925259633905 109776316929170943944725429)
            ·
              refine ⟨10291529712109775994818009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109776316929170943944725429 10291529712109775994818009)
              ·
                refine ⟨7718647284082331996113507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10291529712109775994818009 7718647284082331996113507)
                ·
                  refine ⟨11577970926123497994170261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7718647284082331996113507 11577970926123497994170261)
                  ·
                    refine ⟨542717387162038968476731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11577970926123497994170261 542717387162038968476731)
                    ·
                      rfl

theorem cell23_3170815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_3170815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170815 prefixEnd_3170815 := by exact prefixLift 3170815
  have htrace : WordTrace (prefixWord ++ tailWord_3170815) baseStart_3170815 baseEnd_3170815 := by
    simpa [prefixWord, tailWord_3170815, baseEnd_3170815] using wordTrace_append hprefix tailTrace_3170815
  have hstable : (prefixWord ++ tailWord_3170815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170815).length < 2 ^ (prefixWord ++ tailWord_3170815).sum := by decide
  have hdescent : baseEnd_3170815 < baseStart_3170815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170825 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_3170825 : Nat := 118140960795 + 3170825 * 2 ^ 59
def prefixEnd_3170825 : Nat := 4983230072969 + 3 ^ 40 * 3170825 * 2
def baseEnd_3170825 : Nat := 1628157296292661866305147

theorem tailTrace_3170825 : CollatzResearch.WordTrace tailWord_3170825 prefixEnd_3170825 1628157296292661866305147 := by
  unfold tailWord_3170825
  simp only [CollatzResearch.WordTrace]
  refine ⟨115649488737650033641401929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77099659158433355760934619 115649488737650033641401929)
  ·
    refine ⟨86737116553237525231051447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115649488737650033641401929 86737116553237525231051447)
    ·
      refine ⟨130105674829856287846577171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86737116553237525231051447 130105674829856287846577171)
      ·
        refine ⟨195158512244784431769865757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130105674829856287846577171 195158512244784431769865757)
        ·
          refine ⟨73184442091794161913699659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195158512244784431769865757 73184442091794161913699659)
          ·
            refine ⟨109776663137691242870549489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73184442091794161913699659 109776663137691242870549489)
            ·
              refine ⟨82332497353268432152912117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109776663137691242870549489 82332497353268432152912117)
              ·
                refine ⟨7718671626868915514335511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82332497353268432152912117 7718671626868915514335511)
                ·
                  refine ⟨11578007440303373271503267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7718671626868915514335511 11578007440303373271503267)
                  ·
                    refine ⟨17367011160455059907254901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11578007440303373271503267 17367011160455059907254901)
                    ·
                      refine ⟨1628157296292661866305147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17367011160455059907254901 1628157296292661866305147)
                      ·
                        rfl

theorem cell23_3170825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_3170825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170825 prefixEnd_3170825 := by exact prefixLift 3170825
  have htrace : WordTrace (prefixWord ++ tailWord_3170825) baseStart_3170825 baseEnd_3170825 := by
    simpa [prefixWord, tailWord_3170825, baseEnd_3170825] using wordTrace_append hprefix tailTrace_3170825
  have hstable : (prefixWord ++ tailWord_3170825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170825).length < 2 ^ (prefixWord ++ tailWord_3170825).sum := by decide
  have hdescent : baseEnd_3170825 < baseStart_3170825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170835 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4]
def baseStart_3170835 : Nat := 118140960795 + 3170835 * 2 ^ 59
def prefixEnd_3170835 : Nat := 4983230072969 + 3 ^ 40 * 3170835 * 2
def baseEnd_3170835 : Nat := 1628162431099206827180101

theorem tailTrace_3170835 : CollatzResearch.WordTrace tailWord_3170835 prefixEnd_3170835 1628162431099206827180101 := by
  unfold tailWord_3170835
  simp only [CollatzResearch.WordTrace]
  refine ⟨115649853467613805349265959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77099902311742536899510639 115649853467613805349265959)
  ·
    refine ⟨173474780201420708023898939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115649853467613805349265959 173474780201420708023898939)
    ·
      refine ⟨260212170302131062035848409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173474780201420708023898939 260212170302131062035848409)
      ·
        refine ⟨195159127726598296526886307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260212170302131062035848409 195159127726598296526886307)
        ·
          refine ⟨292738691589897444790329461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195159127726598296526886307 292738691589897444790329461)
          ·
            refine ⟨27444252336552885449093387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 292738691589897444790329461 27444252336552885449093387)
            ·
              refine ⟨41166378504829328173640081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27444252336552885449093387 41166378504829328173640081)
              ·
                refine ⟨30874783878621996130230061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41166378504829328173640081 30874783878621996130230061)
                ·
                  refine ⟨11578043954483248548836273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30874783878621996130230061 11578043954483248548836273)
                  ·
                    refine ⟨8683532965862436411627205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11578043954483248548836273 8683532965862436411627205)
                    ·
                      refine ⟨1628162431099206827180101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8683532965862436411627205 1628162431099206827180101)
                      ·
                        rfl

theorem cell23_3170835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_3170835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170835 prefixEnd_3170835 := by exact prefixLift 3170835
  have htrace : WordTrace (prefixWord ++ tailWord_3170835) baseStart_3170835 baseEnd_3170835 := by
    simpa [prefixWord, tailWord_3170835, baseEnd_3170835] using wordTrace_append hprefix tailTrace_3170835
  have hstable : (prefixWord ++ tailWord_3170835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170835).length < 2 ^ (prefixWord ++ tailWord_3170835).sum := by decide
  have hdescent : baseEnd_3170835 < baseStart_3170835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170842 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_3170842 : Nat := 118140960795 + 3170842 * 2 ^ 59
def prefixEnd_3170842 : Nat := 4983230072969 + 3 ^ 40 * 3170842 * 2
def baseEnd_3170842 : Nat := 1628166025463788299792569

theorem tailTrace_3170842 : CollatzResearch.WordTrace tailWord_3170842 prefixEnd_3170842 1628166025463788299792569 := by
  unfold tailWord_3170842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28912527194647111386192695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77100072519058963696513853 28912527194647111386192695)
  ·
    refine ⟨43368790791970667079289043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28912527194647111386192695 43368790791970667079289043)
    ·
      refine ⟨65053186187956000618933565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43368790791970667079289043 65053186187956000618933565)
      ·
        refine ⟨24394944820483500232100087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65053186187956000618933565 24394944820483500232100087)
        ·
          refine ⟨36592417230725250348150131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24394944820483500232100087 36592417230725250348150131)
          ·
            refine ⟨54888625846087875522225197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36592417230725250348150131 54888625846087875522225197)
            ·
              refine ⟨20583234692282953320834449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54888625846087875522225197 20583234692282953320834449)
              ·
                refine ⟨15437426019212214990625837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20583234692282953320834449 15437426019212214990625837)
                ·
                  refine ⟨5789034757204580621484689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15437426019212214990625837 5789034757204580621484689)
                  ·
                    refine ⟨4341776067903435466113517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5789034757204580621484689 4341776067903435466113517)
                    ·
                      refine ⟨1628166025463788299792569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4341776067903435466113517 1628166025463788299792569)
                      ·
                        rfl

theorem cell23_3170842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_3170842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170842 prefixEnd_3170842 := by exact prefixLift 3170842
  have htrace : WordTrace (prefixWord ++ tailWord_3170842) baseStart_3170842 baseEnd_3170842 := by
    simpa [prefixWord, tailWord_3170842, baseEnd_3170842] using wordTrace_append hprefix tailTrace_3170842
  have hstable : (prefixWord ++ tailWord_3170842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170842).length < 2 ^ (prefixWord ++ tailWord_3170842).sum := by decide
  have hdescent : baseEnd_3170842 < baseStart_3170842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170856 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3170856 : Nat := 118140960795 + 3170856 * 2 ^ 59
def prefixEnd_3170856 : Nat := 4983230072969 + 3 ^ 40 * 3170856 * 2
def baseEnd_3170856 : Nat := 1628173214192951245017505

theorem tailTrace_3170856 : CollatzResearch.WordTrace tailWord_3170856 prefixEnd_3170856 1628173214192951245017505 := by
  unfold tailWord_3170856
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825309700268862967890211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77100412933691817290520281 57825309700268862967890211)
  ·
    refine ⟨86737964550403294451835317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57825309700268862967890211 86737964550403294451835317)
    ·
      refine ⟨8131684176600308854859561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86737964550403294451835317 8131684176600308854859561)
      ·
        refine ⟨6098763132450231641144671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8131684176600308854859561 6098763132450231641144671)
        ·
          refine ⟨9148144698675347461717007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6098763132450231641144671 9148144698675347461717007)
          ·
            refine ⟨13722217048013021192575511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9148144698675347461717007 13722217048013021192575511)
            ·
              refine ⟨20583325572019531788863267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13722217048013021192575511 20583325572019531788863267)
              ·
                refine ⟨30874988358029297683294901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20583325572019531788863267 30874988358029297683294901)
                ·
                  refine ⟨2894530158565246657808897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30874988358029297683294901 2894530158565246657808897)
                  ·
                    refine ⟨2170897618923934993356673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894530158565246657808897 2170897618923934993356673)
                    ·
                      refine ⟨1628173214192951245017505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170897618923934993356673 1628173214192951245017505)
                      ·
                        rfl

theorem cell23_3170856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3170856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170856 prefixEnd_3170856 := by exact prefixLift 3170856
  have htrace : WordTrace (prefixWord ++ tailWord_3170856) baseStart_3170856 baseEnd_3170856 := by
    simpa [prefixWord, tailWord_3170856, baseEnd_3170856] using wordTrace_append hprefix tailTrace_3170856
  have hstable : (prefixWord ++ tailWord_3170856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170856).length < 2 ^ (prefixWord ++ tailWord_3170856).sum := by decide
  have hdescent : baseEnd_3170856 < baseStart_3170856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170872 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_3170872 : Nat := 118140960795 + 3170872 * 2 ^ 59
def prefixEnd_3170872 : Nat := 4983230072969 + 3 ^ 40 * 3170872 * 2
def baseEnd_3170872 : Nat := 1628181429883423182417431

theorem tailTrace_3170872 : CollatzResearch.WordTrace tailWord_3170872 prefixEnd_3170872 1628181429883423182417431 := by
  unfold tailWord_3170872
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825601484239880334181435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77100801978986507112241913 57825601484239880334181435)
  ·
    refine ⟨86738402226359820501272153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57825601484239880334181435 86738402226359820501272153)
    ·
      refine ⟨65053801669769865375954115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86738402226359820501272153 65053801669769865375954115)
      ·
        refine ⟨97580702504654798063931173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65053801669769865375954115 97580702504654798063931173)
        ·
          refine ⟨18296381719622774636987095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97580702504654798063931173 18296381719622774636987095)
          ·
            refine ⟨27444572579434161955480643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18296381719622774636987095 27444572579434161955480643)
            ·
              refine ⟨41166858869151242933220965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27444572579434161955480643 41166858869151242933220965)
              ·
                refine ⟨7718786037965858049978931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41166858869151242933220965 7718786037965858049978931)
                ·
                  refine ⟨11578179056948787074968397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7718786037965858049978931 11578179056948787074968397)
                  ·
                    refine ⟨4341817146355795153113149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11578179056948787074968397 4341817146355795153113149)
                    ·
                      refine ⟨1628181429883423182417431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4341817146355795153113149 1628181429883423182417431)
                      ·
                        rfl

theorem cell23_3170872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_3170872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170872 prefixEnd_3170872 := by exact prefixLift 3170872
  have htrace : WordTrace (prefixWord ++ tailWord_3170872) baseStart_3170872 baseEnd_3170872 := by
    simpa [prefixWord, tailWord_3170872, baseEnd_3170872] using wordTrace_append hprefix tailTrace_3170872
  have hstable : (prefixWord ++ tailWord_3170872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170872).length < 2 ^ (prefixWord ++ tailWord_3170872).sum := by decide
  have hdescent : baseEnd_3170872 < baseStart_3170872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170873 : List Nat := [1, 2, 1, 5, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3170873 : Nat := 118140960795 + 3170873 * 2 ^ 59
def prefixEnd_3170873 : Nat := 4983230072969 + 3 ^ 40 * 3170873 * 2
def baseEnd_3170873 : Nat := 1628181943364077678504927

theorem tailTrace_3170873 : CollatzResearch.WordTrace tailWord_3170873 prefixEnd_3170873 1628181943364077678504927 := by
  unfold tailWord_3170873
  simp only [CollatzResearch.WordTrace]
  refine ⟨115651239441476137839149273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77100826294317425226099515 115651239441476137839149273)
  ·
    refine ⟨86738429581107103379361955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115651239441476137839149273 86738429581107103379361955)
    ·
      refine ⟨130107644371660655069042933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86738429581107103379361955 130107644371660655069042933)
      ·
        refine ⟨12197591659843186412722775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130107644371660655069042933 12197591659843186412722775)
        ·
          refine ⟨18296387489764779619084163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12197591659843186412722775 18296387489764779619084163)
          ·
            refine ⟨27444581234647169428626245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18296387489764779619084163 27444581234647169428626245)
            ·
              refine ⟨5145858981496344267867421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27444581234647169428626245 5145858981496344267867421)
              ·
                refine ⟨1929697118061129100450283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5145858981496344267867421 1929697118061129100450283)
                ·
                  refine ⟨2894545677091693650675425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929697118061129100450283 2894545677091693650675425)
                  ·
                    refine ⟨2170909257818770238006569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894545677091693650675425 2170909257818770238006569)
                    ·
                      refine ⟨1628181943364077678504927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170909257818770238006569 1628181943364077678504927)
                      ·
                        rfl

theorem cell23_3170873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3170873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170873 prefixEnd_3170873 := by exact prefixLift 3170873
  have htrace : WordTrace (prefixWord ++ tailWord_3170873) baseStart_3170873 baseEnd_3170873 := by
    simpa [prefixWord, tailWord_3170873, baseEnd_3170873] using wordTrace_append hprefix tailTrace_3170873
  have hstable : (prefixWord ++ tailWord_3170873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170873).length < 2 ^ (prefixWord ++ tailWord_3170873).sum := by decide
  have hdescent : baseEnd_3170873 < baseStart_3170873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170876 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_3170876 : Nat := 118140960795 + 3170876 * 2 ^ 59
def prefixEnd_3170876 : Nat := 4983230072969 + 3 ^ 40 * 3170876 * 2
def baseEnd_3170876 : Nat := 1628183483806041166767413

theorem tailTrace_3170876 : CollatzResearch.WordTrace tailWord_3170876 prefixEnd_3170876 1628183483806041166767413 := by
  unfold tailWord_3170876
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825674430232634675754241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77100899240310179567672321 57825674430232634675754241)
  ·
    refine ⟨43369255822674476006815681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57825674430232634675754241 43369255822674476006815681)
    ·
      refine ⟨32526941867005857005111761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43369255822674476006815681 32526941867005857005111761)
      ·
        refine ⟨24395206400254392753833821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32526941867005857005111761 24395206400254392753833821)
        ·
          refine ⟨9148202400095397282687683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24395206400254392753833821 9148202400095397282687683)
          ·
            refine ⟨13722303600143095924031525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9148202400095397282687683 13722303600143095924031525)
            ·
              refine ⟨2572931925026830485755911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13722303600143095924031525 2572931925026830485755911)
              ·
                refine ⟨3859397887540245728633867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572931925026830485755911 3859397887540245728633867)
                ·
                  refine ⟨5789096831310368592950801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859397887540245728633867 5789096831310368592950801)
                  ·
                    refine ⟨4341822623482776444713101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5789096831310368592950801 4341822623482776444713101)
                    ·
                      refine ⟨1628183483806041166767413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4341822623482776444713101 1628183483806041166767413)
                      ·
                        rfl

theorem cell23_3170876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_3170876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170876 prefixEnd_3170876 := by exact prefixLift 3170876
  have htrace : WordTrace (prefixWord ++ tailWord_3170876) baseStart_3170876 baseEnd_3170876 := by
    simpa [prefixWord, tailWord_3170876, baseEnd_3170876] using wordTrace_append hprefix tailTrace_3170876
  have hstable : (prefixWord ++ tailWord_3170876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170876).length < 2 ^ (prefixWord ++ tailWord_3170876).sum := by decide
  have hdescent : baseEnd_3170876 < baseStart_3170876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170895 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_3170895 : Nat := 118140960795 + 3170895 * 2 ^ 59
def prefixEnd_3170895 : Nat := 4983230072969 + 3 ^ 40 * 3170895 * 2
def baseEnd_3170895 : Nat := 1628193239938476592429825

theorem tailTrace_3170895 : CollatzResearch.WordTrace tailWord_3170895 prefixEnd_3170895 1628193239938476592429825 := by
  unfold tailWord_3170895
  simp only [CollatzResearch.WordTrace]
  refine ⟨115652041847396435596450139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77101361231597623730966759 115652041847396435596450139)
  ·
    refine ⟨173478062771094653394675209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115652041847396435596450139 173478062771094653394675209)
    ·
      refine ⟨130108547078320990046006407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173478062771094653394675209 130108547078320990046006407)
      ·
        refine ⟨195162820617481485069009611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130108547078320990046006407 195162820617481485069009611)
        ·
          refine ⟨292744230926222227603514417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195162820617481485069009611 292744230926222227603514417)
          ·
            refine ⟨219558173194666670702635813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292744230926222227603514417 219558173194666670702635813)
            ·
              refine ⟨41167157474000000756744215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219558173194666670702635813 41167157474000000756744215)
              ·
                refine ⟨61750736211000001135116323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41167157474000000756744215 61750736211000001135116323)
                ·
                  refine ⟨92626104316500001702674485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61750736211000001135116323 92626104316500001702674485)
                  ·
                    refine ⟨8683697279671875159625733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92626104316500001702674485 8683697279671875159625733)
                    ·
                      refine ⟨1628193239938476592429825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8683697279671875159625733 1628193239938476592429825)
                      ·
                        rfl

theorem cell23_3170895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_3170895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170895 prefixEnd_3170895 := by exact prefixLift 3170895
  have htrace : WordTrace (prefixWord ++ tailWord_3170895) baseStart_3170895 baseEnd_3170895 := by
    simpa [prefixWord, tailWord_3170895, baseEnd_3170895] using wordTrace_append hprefix tailTrace_3170895
  have hstable : (prefixWord ++ tailWord_3170895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170895).length < 2 ^ (prefixWord ++ tailWord_3170895).sum := by decide
  have hdescent : baseEnd_3170895 < baseStart_3170895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170916 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_3170916 : Nat := 118140960795 + 3170916 * 2 ^ 59
def prefixEnd_3170916 : Nat := 4983230072969 + 3 ^ 40 * 3170916 * 2
def baseEnd_3170916 : Nat := 1628204023032221010267229

theorem tailTrace_3170916 : CollatzResearch.WordTrace tailWord_3170916 prefixEnd_3170916 1628204023032221010267229 := by
  unfold tailWord_3170916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57826403890160178091482301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77101871853546904121976401 57826403890160178091482301)
  ·
    refine ⟨21684901458810066784305863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57826403890160178091482301 21684901458810066784305863)
    ·
      refine ⟨32527352188215100176458795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21684901458810066784305863 32527352188215100176458795)
      ·
        refine ⟨48791028282322650264688193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32527352188215100176458795 48791028282322650264688193)
        ·
          refine ⟨36593271211741987698516145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48791028282322650264688193 36593271211741987698516145)
          ·
            refine ⟨27444953408806490773887109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36593271211741987698516145 27444953408806490773887109)
            ·
              refine ⟨5145928764151217020103833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27444953408806490773887109 5145928764151217020103833)
              ·
                refine ⟨3859446573113412765077875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5145928764151217020103833 3859446573113412765077875)
                ·
                  refine ⟨5789169859670119147616813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859446573113412765077875 5789169859670119147616813)
                  ·
                    refine ⟨2170938697376294680356305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5789169859670119147616813 2170938697376294680356305)
                    ·
                      refine ⟨1628204023032221010267229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2170938697376294680356305 1628204023032221010267229)
                      ·
                        rfl

theorem cell23_3170916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_3170916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170916 prefixEnd_3170916 := by exact prefixLift 3170916
  have htrace : WordTrace (prefixWord ++ tailWord_3170916) baseStart_3170916 baseEnd_3170916 := by
    simpa [prefixWord, tailWord_3170916, baseEnd_3170916] using wordTrace_append hprefix tailTrace_3170916
  have hstable : (prefixWord ++ tailWord_3170916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170916).length < 2 ^ (prefixWord ++ tailWord_3170916).sum := by decide
  have hdescent : baseEnd_3170916 < baseStart_3170916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170935 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 9]
def baseStart_3170935 : Nat := 118140960795 + 3170935 * 2 ^ 59
def prefixEnd_3170935 : Nat := 4983230072969 + 3 ^ 40 * 3170935 * 2
def baseEnd_3170935 : Nat := 180912642129406270658849

theorem tailTrace_3170935 : CollatzResearch.WordTrace tailWord_3170935 prefixEnd_3170935 180912642129406270658849 := by
  unfold tailWord_3170935
  simp only [CollatzResearch.WordTrace]
  refine ⟨115653500767251522427906259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77102333844834348285270839 115653500767251522427906259)
  ·
    refine ⟨173480251150877283641859389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115653500767251522427906259 173480251150877283641859389)
    ·
      refine ⟨65055094181578981365697271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173480251150877283641859389 65055094181578981365697271)
      ·
        refine ⟨97582641272368472048545907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65055094181578981365697271 97582641272368472048545907)
        ·
          refine ⟨146373961908552708072818861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97582641272368472048545907 146373961908552708072818861)
          ·
            refine ⟨54890235715707265527307073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146373961908552708072818861 54890235715707265527307073)
            ·
              refine ⟨41167676786780449145480305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54890235715707265527307073 41167676786780449145480305)
              ·
                refine ⟨30875757590085336859110229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41167676786780449145480305 30875757590085336859110229)
                ·
                  refine ⟨180912642129406270658849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30875757590085336859110229 180912642129406270658849)
                  ·
                    rfl

theorem cell23_3170935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 9].length) (baseStart_3170935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170935 prefixEnd_3170935 := by exact prefixLift 3170935
  have htrace : WordTrace (prefixWord ++ tailWord_3170935) baseStart_3170935 baseEnd_3170935 := by
    simpa [prefixWord, tailWord_3170935, baseEnd_3170935] using wordTrace_append hprefix tailTrace_3170935
  have hstable : (prefixWord ++ tailWord_3170935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170935).length < 2 ^ (prefixWord ++ tailWord_3170935).sum := by decide
  have hdescent : baseEnd_3170935 < baseStart_3170935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3170955 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8]
def baseStart_3170955 : Nat := 118140960795 + 3170955 * 2 ^ 59
def prefixEnd_3170955 : Nat := 4983230072969 + 3 ^ 40 * 3170955 * 2
def baseEnd_3170955 : Nat := 1628224048777746357679549

theorem tailTrace_3170955 : CollatzResearch.WordTrace tailWord_3170955 prefixEnd_3170955 1628224048777746357679549 := by
  unfold tailWord_3170955
  simp only [CollatzResearch.WordTrace]
  refine ⟨115654230227179065843634319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77102820151452710562422879 115654230227179065843634319)
  ·
    refine ⟨173481345340768598765451479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115654230227179065843634319 173481345340768598765451479)
    ·
      refine ⟨260222018011152898148177219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173481345340768598765451479 260222018011152898148177219)
      ·
        refine ⟨390333027016729347222265829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260222018011152898148177219 390333027016729347222265829)
        ·
          refine ⟨73187442565636752604174843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390333027016729347222265829 73187442565636752604174843)
          ·
            refine ⟨109781163848455128906262265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73187442565636752604174843 109781163848455128906262265)
            ·
              refine ⟨82335872886341346679696699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109781163848455128906262265 82335872886341346679696699)
              ·
                refine ⟨123503809329512020019545049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82335872886341346679696699 123503809329512020019545049)
                ·
                  refine ⟨92627856997134015014658787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123503809329512020019545049 92627856997134015014658787)
                  ·
                    refine ⟨138941785495701022521988181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92627856997134015014658787 138941785495701022521988181)
                    ·
                      refine ⟨1628224048777746357679549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 138941785495701022521988181 1628224048777746357679549)
                      ·
                        rfl

theorem cell23_3170955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_3170955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3170955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3170955 prefixEnd_3170955 := by exact prefixLift 3170955
  have htrace : WordTrace (prefixWord ++ tailWord_3170955) baseStart_3170955 baseEnd_3170955 := by
    simpa [prefixWord, tailWord_3170955, baseEnd_3170955] using wordTrace_append hprefix tailTrace_3170955
  have hstable : (prefixWord ++ tailWord_3170955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3170955).length < 2 ^ (prefixWord ++ tailWord_3170955).sum := by decide
  have hdescent : baseEnd_3170955 < baseStart_3170955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3170955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171036 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3171036 : Nat := 118140960795 + 3171036 * 2 ^ 59
def prefixEnd_3171036 : Nat := 4983230072969 + 3 ^ 40 * 3171036 * 2
def baseEnd_3171036 : Nat := 1628265640710760540766677

theorem tailTrace_3171036 : CollatzResearch.WordTrace tailWord_3171036 prefixEnd_3171036 1628265640710760540766677 := by
  unfold tailWord_3171036
  simp only [CollatzResearch.WordTrace]
  refine ⟨57828592269942808338666481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77104789693257077784888641 57828592269942808338666481)
  ·
    refine ⟨43371444202457106253999861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57828592269942808338666481 43371444202457106253999861)
    ·
      refine ⟨4066072893980353711312487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43371444202457106253999861 4066072893980353711312487)
      ·
        refine ⟨6099109340970530566968731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066072893980353711312487 6099109340970530566968731)
        ·
          refine ⟨9148664011455795850453097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099109340970530566968731 9148664011455795850453097)
          ·
            refine ⟨6861498008591846887839823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9148664011455795850453097 6861498008591846887839823)
            ·
              refine ⟨10292247012887770331759735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6861498008591846887839823 10292247012887770331759735)
              ·
                refine ⟨15438370519331655497639603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10292247012887770331759735 15438370519331655497639603)
                ·
                  refine ⟨23157555778997483246459405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15438370519331655497639603 23157555778997483246459405)
                  ·
                    refine ⟨8684083417124056217422277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23157555778997483246459405 8684083417124056217422277)
                    ·
                      refine ⟨1628265640710760540766677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8684083417124056217422277 1628265640710760540766677)
                      ·
                        rfl

theorem cell23_3171036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3171036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171036 prefixEnd_3171036 := by exact prefixLift 3171036
  have htrace : WordTrace (prefixWord ++ tailWord_3171036) baseStart_3171036 baseEnd_3171036 := by
    simpa [prefixWord, tailWord_3171036, baseEnd_3171036] using wordTrace_append hprefix tailTrace_3171036
  have hstable : (prefixWord ++ tailWord_3171036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171036).length < 2 ^ (prefixWord ++ tailWord_3171036).sum := by decide
  have hdescent : baseEnd_3171036 < baseStart_3171036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171039 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 3]
def baseStart_3171039 : Nat := 118140960795 + 3171039 * 2 ^ 59
def prefixEnd_3171039 : Nat := 4983230072969 + 3 ^ 40 * 3171039 * 2
def baseEnd_3171039 : Nat := 1628267181152724029029163

theorem tailTrace_3171039 : CollatzResearch.WordTrace tailWord_3171039 prefixEnd_3171039 1628267181152724029029163 := by
  unfold tailWord_3171039
  simp only [CollatzResearch.WordTrace]
  refine ⟨115657293958874748189692171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77104862639249832126461447 115657293958874748189692171)
  ·
    refine ⟨173485940938312122284538257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115657293958874748189692171 173485940938312122284538257)
    ·
      refine ⟨130114455703734091713403693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173485940938312122284538257 130114455703734091713403693)
      ·
        refine ⟨48792920888900284392526385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130114455703734091713403693 48792920888900284392526385)
        ·
          refine ⟨36594690666675213294394789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48792920888900284392526385 36594690666675213294394789)
          ·
            refine ⟨6861504500001602492699023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36594690666675213294394789 6861504500001602492699023)
            ·
              refine ⟨10292256750002403739048535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6861504500001602492699023 10292256750002403739048535)
              ·
                refine ⟨15438385125003605608572803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10292256750002403739048535 15438385125003605608572803)
                ·
                  refine ⟨23157577687505408412859205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15438385125003605608572803 23157577687505408412859205)
                  ·
                    refine ⟨4342045816407264077411101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23157577687505408412859205 4342045816407264077411101)
                    ·
                      refine ⟨1628267181152724029029163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4342045816407264077411101 1628267181152724029029163)
                      ·
                        rfl

theorem cell23_3171039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_3171039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171039 prefixEnd_3171039 := by exact prefixLift 3171039
  have htrace : WordTrace (prefixWord ++ tailWord_3171039) baseStart_3171039 baseEnd_3171039 := by
    simpa [prefixWord, tailWord_3171039, baseEnd_3171039] using wordTrace_append hprefix tailTrace_3171039
  have hstable : (prefixWord ++ tailWord_3171039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171039).length < 2 ^ (prefixWord ++ tailWord_3171039).sum := by decide
  have hdescent : baseEnd_3171039 < baseStart_3171039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171076 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 6]
def baseStart_3171076 : Nat := 118140960795 + 3171076 * 2 ^ 59
def prefixEnd_3171076 : Nat := 4983230072969 + 3 ^ 40 * 3171076 * 2
def baseEnd_3171076 : Nat := 180920686659660042696277

theorem tailTrace_3171076 : CollatzResearch.WordTrace tailWord_3171076 prefixEnd_3171076 180920686659660042696277 := by
  unfold tailWord_3171076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57829321729870351754394541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77105762306493802339192721 57829321729870351754394541)
  ·
    refine ⟨21685995648701381907897953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57829321729870351754394541 21685995648701381907897953)
    ·
      refine ⟨16264496736526036430923465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21685995648701381907897953 16264496736526036430923465)
      ·
        refine ⟨12198372552394527323192599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16264496736526036430923465 12198372552394527323192599)
        ·
          refine ⟨18297558828591790984788899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12198372552394527323192599 18297558828591790984788899)
          ·
            refine ⟨27446338242887686477183349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18297558828591790984788899 27446338242887686477183349)
            ·
              refine ⟨2573094210270720607235939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27446338242887686477183349 2573094210270720607235939)
              ·
                refine ⟨3859641315406080910853909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2573094210270720607235939 3859641315406080910853909)
                ·
                  refine ⟨180920686659660042696277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3859641315406080910853909 180920686659660042696277)
                  ·
                    rfl

theorem cell23_3171076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_3171076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171076 prefixEnd_3171076 := by exact prefixLift 3171076
  have htrace : WordTrace (prefixWord ++ tailWord_3171076) baseStart_3171076 baseEnd_3171076 := by
    simpa [prefixWord, tailWord_3171076, baseEnd_3171076] using wordTrace_append hprefix tailTrace_3171076
  have hstable : (prefixWord ++ tailWord_3171076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171076).length < 2 ^ (prefixWord ++ tailWord_3171076).sum := by decide
  have hdescent : baseEnd_3171076 < baseStart_3171076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171089 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 1, 5]
def baseStart_3171089 : Nat := 118140960795 + 3171089 * 2 ^ 59
def prefixEnd_3171089 : Nat := 4983230072969 + 3 ^ 40 * 3171089 * 2
def baseEnd_3171089 : Nat := 542764285061816277801311

theorem tailTrace_3171089 : CollatzResearch.WordTrace tailWord_3171089 prefixEnd_3171089 542764285061816277801311 := by
  unfold tailWord_3171089
  simp only [CollatzResearch.WordTrace]
  refine ⟨115659117608693606729012321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77106078405795737819341547 115659117608693606729012321)
  ·
    refine ⟨86744338206520205046759241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115659117608693606729012321 86744338206520205046759241)
    ·
      refine ⟨65058253654890153785069431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86744338206520205046759241 65058253654890153785069431)
      ·
        refine ⟨97587380482335230677604147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65058253654890153785069431 97587380482335230677604147)
        ·
          refine ⟨146381070723502846016406221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97587380482335230677604147 146381070723502846016406221)
          ·
            refine ⟨54892901521313567256152333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146381070723502846016406221 54892901521313567256152333)
            ·
              refine ⟨20584838070492587721057125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54892901521313567256152333 20584838070492587721057125)
              ·
                refine ⟨3859657138217360197698211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20584838070492587721057125 3859657138217360197698211)
                ·
                  refine ⟨5789485707326040296547317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859657138217360197698211 5789485707326040296547317)
                  ·
                    refine ⟨542764285061816277801311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5789485707326040296547317 542764285061816277801311)
                    ·
                      rfl

theorem cell23_3171089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_3171089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171089 prefixEnd_3171089 := by exact prefixLift 3171089
  have htrace : WordTrace (prefixWord ++ tailWord_3171089) baseStart_3171089 baseEnd_3171089 := by
    simpa [prefixWord, tailWord_3171089, baseEnd_3171089] using wordTrace_append hprefix tailTrace_3171089
  have hstable : (prefixWord ++ tailWord_3171089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171089).length < 2 ^ (prefixWord ++ tailWord_3171089).sum := by decide
  have hdescent : baseEnd_3171089 < baseStart_3171089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171096 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 2, 3, 2]
def baseStart_3171096 : Nat := 118140960795 + 3171096 * 2 ^ 59
def prefixEnd_3171096 : Nat := 4983230072969 + 3 ^ 40 * 3171096 * 2
def baseEnd_3171096 : Nat := 1628296449550030306016401

theorem tailTrace_3171096 : CollatzResearch.WordTrace tailWord_3171096 prefixEnd_3171096 1628296449550030306016401 := by
  unfold tailWord_3171096
  simp only [CollatzResearch.WordTrace]
  refine ⟨57829686459834123462258571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77106248613112164616344761 57829686459834123462258571)
  ·
    refine ⟨86744529689751185193387857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57829686459834123462258571 86744529689751185193387857)
    ·
      refine ⟨65058397267313388895040893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86744529689751185193387857 65058397267313388895040893)
      ·
        refine ⟨24396898975242520835640335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65058397267313388895040893 24396898975242520835640335)
        ·
          refine ⟨36595348462863781253460503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24396898975242520835640335 36595348462863781253460503)
          ·
            refine ⟨54893022694295671880190755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36595348462863781253460503 54893022694295671880190755)
            ·
              refine ⟨82339534041443507820286133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54893022694295671880190755 82339534041443507820286133)
              ·
                refine ⟨7719331316385328858151825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82339534041443507820286133 7719331316385328858151825)
                ·
                  refine ⟨5789498487288996643613869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7719331316385328858151825 5789498487288996643613869)
                  ·
                    refine ⟨2171061932733373741355201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5789498487288996643613869 2171061932733373741355201)
                    ·
                      refine ⟨1628296449550030306016401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171061932733373741355201 1628296449550030306016401)
                      ·
                        rfl

theorem cell23_3171096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_3171096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171096 prefixEnd_3171096 := by exact prefixLift 3171096
  have htrace : WordTrace (prefixWord ++ tailWord_3171096) baseStart_3171096 baseEnd_3171096 := by
    simpa [prefixWord, tailWord_3171096, baseEnd_3171096] using wordTrace_append hprefix tailTrace_3171096
  have hstable : (prefixWord ++ tailWord_3171096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171096).length < 2 ^ (prefixWord ++ tailWord_3171096).sum := by decide
  have hdescent : baseEnd_3171096 < baseStart_3171096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171106 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3171106 : Nat := 118140960795 + 3171106 * 2 ^ 59
def prefixEnd_3171106 : Nat := 4983230072969 + 3 ^ 40 * 3171106 * 2
def baseEnd_3171106 : Nat := 542767194785525088963785

theorem tailTrace_3171106 : CollatzResearch.WordTrace tailWord_3171106 prefixEnd_3171106 542767194785525088963785 := by
  unfold tailWord_3171106
  simp only [CollatzResearch.WordTrace]
  refine ⟨28914934412408004658095293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77106491766421345754920781 28914934412408004658095293)
  ·
    refine ⟨10843100404653001746785735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28914934412408004658095293 10843100404653001746785735)
    ·
      refine ⟨16264650606979502620178603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10843100404653001746785735 16264650606979502620178603)
      ·
        refine ⟨24396975910469253930267905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16264650606979502620178603 24396975910469253930267905)
        ·
          refine ⟨18297731932851940447700929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24396975910469253930267905 18297731932851940447700929)
          ·
            refine ⟨13723298949638955335775697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18297731932851940447700929 13723298949638955335775697)
            ·
              refine ⟨10292474212229216501831773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13723298949638955335775697 10292474212229216501831773)
              ·
                refine ⟨3859677829585956188186915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10292474212229216501831773 3859677829585956188186915)
                ·
                  refine ⟨5789516744378934282280373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859677829585956188186915 5789516744378934282280373)
                  ·
                    refine ⟨542767194785525088963785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5789516744378934282280373 542767194785525088963785)
                    ·
                      rfl

theorem cell23_3171106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3171106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171106 prefixEnd_3171106 := by exact prefixLift 3171106
  have htrace : WordTrace (prefixWord ++ tailWord_3171106) baseStart_3171106 baseEnd_3171106 := by
    simpa [prefixWord, tailWord_3171106, baseEnd_3171106] using wordTrace_append hprefix tailTrace_3171106
  have hstable : (prefixWord ++ tailWord_3171106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171106).length < 2 ^ (prefixWord ++ tailWord_3171106).sum := by decide
  have hdescent : baseEnd_3171106 < baseStart_3171106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171139 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4]
def baseStart_3171139 : Nat := 118140960795 + 3171139 * 2 ^ 59
def prefixEnd_3171139 : Nat := 4983230072969 + 3 ^ 40 * 3171139 * 2
def baseEnd_3171139 : Nat := 1628318529218173637778703

theorem tailTrace_3171139 : CollatzResearch.WordTrace tailWord_3171139 prefixEnd_3171139 1628318529218173637778703 := by
  unfold tailWord_3171139
  simp only [CollatzResearch.WordTrace]
  refine ⟨115660941258512465268332471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77107294172341643512221647 115660941258512465268332471)
  ·
    refine ⟨173491411887768697902498707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115660941258512465268332471 173491411887768697902498707)
    ·
      refine ⟨260237117831653046853748061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173491411887768697902498707 260237117831653046853748061)
      ·
        refine ⟨97588919186869892570155523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260237117831653046853748061 97588919186869892570155523)
        ·
          refine ⟨146383378780304838855233285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97588919186869892570155523 146383378780304838855233285)
          ·
            refine ⟨27446883521307157285356241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146383378780304838855233285 27446883521307157285356241)
            ·
              refine ⟨20585162640980367964017181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27446883521307157285356241 20585162640980367964017181)
              ·
                refine ⟨7719435990367637986506443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20585162640980367964017181 7719435990367637986506443)
                ·
                  refine ⟨11579153985551456979759665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7719435990367637986506443 11579153985551456979759665)
                  ·
                    refine ⟨8684365489163592734819749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11579153985551456979759665 8684365489163592734819749)
                    ·
                      refine ⟨1628318529218173637778703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8684365489163592734819749 1628318529218173637778703)
                      ·
                        rfl

theorem cell23_3171139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_3171139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171139 prefixEnd_3171139 := by exact prefixLift 3171139
  have htrace : WordTrace (prefixWord ++ tailWord_3171139) baseStart_3171139 baseEnd_3171139 := by
    simpa [prefixWord, tailWord_3171139, baseEnd_3171139] using wordTrace_append hprefix tailTrace_3171139
  have hstable : (prefixWord ++ tailWord_3171139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171139).length < 2 ^ (prefixWord ++ tailWord_3171139).sum := by decide
  have hdescent : baseEnd_3171139 < baseStart_3171139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171146 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_3171146 : Nat := 118140960795 + 3171146 * 2 ^ 59
def prefixEnd_3171146 : Nat := 4983230072969 + 3 ^ 40 * 3171146 * 2
def baseEnd_3171146 : Nat := 1628322123582755110391171

theorem tailTrace_3171146 : CollatzResearch.WordTrace tailWord_3171146 prefixEnd_3171146 1628322123582755110391171 := by
  unfold tailWord_3171146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28915299142371776365959323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77107464379658070309224861 28915299142371776365959323)
  ·
    refine ⟨43372948713557664548938985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28915299142371776365959323 43372948713557664548938985)
    ·
      refine ⟨32529711535168248411704239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43372948713557664548938985 32529711535168248411704239)
      ·
        refine ⟨48794567302752372617556359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32529711535168248411704239 48794567302752372617556359)
        ·
          refine ⟨73191850954128558926334539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48794567302752372617556359 73191850954128558926334539)
          ·
            refine ⟨109787776431192838389501809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73191850954128558926334539 109787776431192838389501809)
            ·
              refine ⟨82340832323394628792126357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109787776431192838389501809 82340832323394628792126357)
              ·
                refine ⟨3859726515159123224630923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82340832323394628792126357 3859726515159123224630923)
                ·
                  refine ⟨5789589772738684836946385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859726515159123224630923 5789589772738684836946385)
                  ·
                    refine ⟨4342192329554013627709789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5789589772738684836946385 4342192329554013627709789)
                    ·
                      refine ⟨1628322123582755110391171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4342192329554013627709789 1628322123582755110391171)
                      ·
                        rfl

theorem cell23_3171146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_3171146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171146 prefixEnd_3171146 := by exact prefixLift 3171146
  have htrace : WordTrace (prefixWord ++ tailWord_3171146) baseStart_3171146 baseEnd_3171146 := by
    simpa [prefixWord, tailWord_3171146, baseEnd_3171146] using wordTrace_append hprefix tailTrace_3171146
  have hstable : (prefixWord ++ tailWord_3171146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171146).length < 2 ^ (prefixWord ++ tailWord_3171146).sum := by decide
  have hdescent : baseEnd_3171146 < baseStart_3171146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171170 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3171170 : Nat := 118140960795 + 3171170 * 2 ^ 59
def prefixEnd_3171170 : Nat := 4983230072969 + 3 ^ 40 * 3171170 * 2
def baseEnd_3171170 : Nat := 542778149039487672163687

theorem tailTrace_3171170 : CollatzResearch.WordTrace tailWord_3171170 prefixEnd_3171170 542778149039487672163687 := by
  unfold tailWord_3171170
  simp only [CollatzResearch.WordTrace]
  refine ⟨28915517980350039390677741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77108047947600105041807309 28915517980350039390677741)
  ·
    refine ⟨10843319242631264771504153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28915517980350039390677741 10843319242631264771504153)
    ·
      refine ⟨8132489431973448578628115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10843319242631264771504153 8132489431973448578628115)
      ·
        refine ⟨12198734147960172867942173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8132489431973448578628115 12198734147960172867942173)
        ·
          refine ⟨4574525305485064825478315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12198734147960172867942173 4574525305485064825478315)
          ·
            refine ⟨6861787958227597238217473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4574525305485064825478315 6861787958227597238217473)
            ·
              refine ⟨5146340968670697928663105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6861787958227597238217473 5146340968670697928663105)
              ·
                refine ⟨3859755726503023446497329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5146340968670697928663105 3859755726503023446497329)
                ·
                  refine ⟨2894816794877267584872997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3859755726503023446497329 2894816794877267584872997)
                  ·
                    refine ⟨542778149039487672163687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2894816794877267584872997 542778149039487672163687)
                    ·
                      rfl

theorem cell23_3171170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3171170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171170 prefixEnd_3171170 := by exact prefixLift 3171170
  have htrace : WordTrace (prefixWord ++ tailWord_3171170) baseStart_3171170 baseEnd_3171170 := by
    simpa [prefixWord, tailWord_3171170, baseEnd_3171170] using wordTrace_append hprefix tailTrace_3171170
  have hstable : (prefixWord ++ tailWord_3171170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171170).length < 2 ^ (prefixWord ++ tailWord_3171170).sum := by decide
  have hdescent : baseEnd_3171170 < baseStart_3171170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171193 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 3]
def baseStart_3171193 : Nat := 118140960795 + 3171193 * 2 ^ 59
def prefixEnd_3171193 : Nat := 4983230072969 + 3 ^ 40 * 3171193 * 2
def baseEnd_3171193 : Nat := 1628346257173516426503455

theorem tailTrace_3171193 : CollatzResearch.WordTrace tailWord_3171193 prefixEnd_3171193 1628346257173516426503455 := by
  unfold tailWord_3171193
  simp only [CollatzResearch.WordTrace]
  refine ⟨115662910800316832490798233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77108607200211221660532155 115662910800316832490798233)
  ·
    refine ⟨86747183100237624368098675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115662910800316832490798233 86747183100237624368098675)
    ·
      refine ⟨130120774650356436552148013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86747183100237624368098675 130120774650356436552148013)
      ·
        refine ⟨48795290493883663707055505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130120774650356436552148013 48795290493883663707055505)
        ·
          refine ⟨36596467870412747780291629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48795290493883663707055505 36596467870412747780291629)
          ·
            refine ⟨13723675451404780417609361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36596467870412747780291629 13723675451404780417609361)
            ·
              refine ⟨10292756588553585313207021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13723675451404780417609361 10292756588553585313207021)
              ·
                refine ⟨3859783720707594492452633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10292756588553585313207021 3859783720707594492452633)
                ·
                  refine ⟨2894837790530695869339475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3859783720707594492452633 2894837790530695869339475)
                  ·
                    refine ⟨4342256685796043804009213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2894837790530695869339475 4342256685796043804009213)
                    ·
                      refine ⟨1628346257173516426503455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4342256685796043804009213 1628346257173516426503455)
                      ·
                        rfl

theorem cell23_3171193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_3171193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171193 prefixEnd_3171193 := by exact prefixLift 3171193
  have htrace : WordTrace (prefixWord ++ tailWord_3171193) baseStart_3171193 baseEnd_3171193 := by
    simpa [prefixWord, tailWord_3171193, baseEnd_3171193] using wordTrace_append hprefix tailTrace_3171193
  have hstable : (prefixWord ++ tailWord_3171193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171193).length < 2 ^ (prefixWord ++ tailWord_3171193).sum := by decide
  have hdescent : baseEnd_3171193 < baseStart_3171193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171203 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 1, 3, 2]
def baseStart_3171203 : Nat := 118140960795 + 3171203 * 2 ^ 59
def prefixEnd_3171203 : Nat := 4983230072969 + 3 ^ 40 * 3171203 * 2
def baseEnd_3171203 : Nat := 1628351391980061387378409

theorem tailTrace_3171203 : CollatzResearch.WordTrace tailWord_3171203 prefixEnd_3171203 1628351391980061387378409 := by
  unfold tailWord_3171203
  simp only [CollatzResearch.WordTrace]
  refine ⟨115663275530280604198662263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77108850353520402799108175 115663275530280604198662263)
  ·
    refine ⟨173494913295420906297993395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115663275530280604198662263 173494913295420906297993395)
    ·
      refine ⟨260242369943131359446990093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173494913295420906297993395 260242369943131359446990093)
      ·
        refine ⟨97590888728674259792621285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260242369943131359446990093 97590888728674259792621285)
        ·
          refine ⟨18298291636626423711116491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97590888728674259792621285 18298291636626423711116491)
          ·
            refine ⟨27447437454939635566674737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18298291636626423711116491 27447437454939635566674737)
            ·
              refine ⟨20585578091204726675006053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27447437454939635566674737 20585578091204726675006053)
              ·
                refine ⟨3859795892100886251563635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20585578091204726675006053 3859795892100886251563635)
                ·
                  refine ⟨5789693838151329377345453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859795892100886251563635 5789693838151329377345453)
                  ·
                    refine ⟨2171135189306748516504545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5789693838151329377345453 2171135189306748516504545)
                    ·
                      refine ⟨1628351391980061387378409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171135189306748516504545 1628351391980061387378409)
                      ·
                        rfl

theorem cell23_3171203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_3171203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171203 prefixEnd_3171203 := by exact prefixLift 3171203
  have htrace : WordTrace (prefixWord ++ tailWord_3171203) baseStart_3171203 baseEnd_3171203 := by
    simpa [prefixWord, tailWord_3171203, baseEnd_3171203] using wordTrace_append hprefix tailTrace_3171203
  have hstable : (prefixWord ++ tailWord_3171203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171203).length < 2 ^ (prefixWord ++ tailWord_3171203).sum := by decide
  have hdescent : baseEnd_3171203 < baseStart_3171203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171219 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 3]
def baseStart_3171219 : Nat := 118140960795 + 3171219 * 2 ^ 59
def prefixEnd_3171219 : Nat := 4983230072969 + 3 ^ 40 * 3171219 * 2
def baseEnd_3171219 : Nat := 1628359607670533324778335

theorem tailTrace_3171219 : CollatzResearch.WordTrace tailWord_3171219 prefixEnd_3171219 1628359607670533324778335 := by
  unfold tailWord_3171219
  simp only [CollatzResearch.WordTrace]
  refine ⟨115663859098222638931244711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77109239398815092620829807 115663859098222638931244711)
  ·
    refine ⟨173495788647333958396867067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115663859098222638931244711 173495788647333958396867067)
    ·
      refine ⟨260243682971000937595300601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173495788647333958396867067 260243682971000937595300601)
      ·
        refine ⟨195182762228250703196475451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260243682971000937595300601 195182762228250703196475451)
        ·
          refine ⟨292774143342376054794713177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195182762228250703196475451 292774143342376054794713177)
          ·
            refine ⟨219580607506782041096034883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292774143342376054794713177 219580607506782041096034883)
            ·
              refine ⟨329370911260173061644052325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219580607506782041096034883 329370911260173061644052325)
              ·
                refine ⟨61757045861282449058259811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329370911260173061644052325 61757045861282449058259811)
                ·
                  refine ⟨92635568791923673587389717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61757045861282449058259811 92635568791923673587389717)
                  ·
                    refine ⟨4342292287121422199408893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92635568791923673587389717 4342292287121422199408893)
                    ·
                      refine ⟨1628359607670533324778335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4342292287121422199408893 1628359607670533324778335)
                      ·
                        rfl

theorem cell23_3171219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_3171219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171219 prefixEnd_3171219 := by exact prefixLift 3171219
  have htrace : WordTrace (prefixWord ++ tailWord_3171219) baseStart_3171219 baseEnd_3171219 := by
    simpa [prefixWord, tailWord_3171219, baseEnd_3171219] using wordTrace_append hprefix tailTrace_3171219
  have hstable : (prefixWord ++ tailWord_3171219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171219).length < 2 ^ (prefixWord ++ tailWord_3171219).sum := by decide
  have hdescent : baseEnd_3171219 < baseStart_3171219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171220 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_3171220 : Nat := 118140960795 + 3171220 * 2 ^ 59
def prefixEnd_3171220 : Nat := 4983230072969 + 3 ^ 40 * 3171220 * 2
def baseEnd_3171220 : Nat := 1628360121151187820865831

theorem tailTrace_3171220 : CollatzResearch.WordTrace tailWord_3171220 prefixEnd_3171220 1628360121151187820865831 := by
  unfold tailWord_3171220
  simp only [CollatzResearch.WordTrace]
  refine ⟨57831947785609508051015557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77109263714146010734687409 57831947785609508051015557)
  ·
    refine ⟨10843490209801782759565417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57831947785609508051015557 10843490209801782759565417)
    ·
      refine ⟨8132617657351337069674063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10843490209801782759565417 8132617657351337069674063)
      ·
        refine ⟨12198926486027005604511095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8132617657351337069674063 12198926486027005604511095)
        ·
          refine ⟨18298389729040508406766643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12198926486027005604511095 18298389729040508406766643)
          ·
            refine ⟨27447584593560762610149965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18298389729040508406766643 27447584593560762610149965)
            ·
              refine ⟨10292844222585285978806237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27447584593560762610149965 10292844222585285978806237)
              ·
                refine ⟨3859816583469482242052339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10292844222585285978806237 3859816583469482242052339)
                ·
                  refine ⟨5789724875204223363078509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859816583469482242052339 5789724875204223363078509)
                  ·
                    refine ⟨2171146828201583761154441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5789724875204223363078509 2171146828201583761154441)
                    ·
                      refine ⟨1628360121151187820865831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171146828201583761154441 1628360121151187820865831)
                      ·
                        rfl

theorem cell23_3171220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_3171220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171220 prefixEnd_3171220 := by exact prefixLift 3171220
  have htrace : WordTrace (prefixWord ++ tailWord_3171220) baseStart_3171220 baseEnd_3171220 := by
    simpa [prefixWord, tailWord_3171220, baseEnd_3171220] using wordTrace_append hprefix tailTrace_3171220
  have hstable : (prefixWord ++ tailWord_3171220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171220).length < 2 ^ (prefixWord ++ tailWord_3171220).sum := by decide
  have hdescent : baseEnd_3171220 < baseStart_3171220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171290 : List Nat := [3, 1, 1, 2, 4, 2, 3, 2, 5]
def baseStart_3171290 : Nat := 118140960795 + 3171290 * 2 ^ 59
def prefixEnd_3171290 : Nat := 4983230072969 + 3 ^ 40 * 3171290 * 2
def baseEnd_3171290 : Nat := 180932896088555838554501

theorem tailTrace_3171290 : CollatzResearch.WordTrace tailWord_3171290 prefixEnd_3171290 180932896088555838554501 := by
  unfold tailWord_3171290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28916612170241354514269831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77110965787310278704719549 28916612170241354514269831)
  ·
    refine ⟨43374918255362031771404747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28916612170241354514269831 43374918255362031771404747)
    ·
      refine ⟨65062377383043047657107121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43374918255362031771404747 65062377383043047657107121)
      ·
        refine ⟨48796783037282285742830341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65062377383043047657107121 48796783037282285742830341)
        ·
          refine ⟨9149396819490428576780689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48796783037282285742830341 9149396819490428576780689)
          ·
            refine ⟨6862047614617821432585517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9149396819490428576780689 6862047614617821432585517)
            ·
              refine ⟨2573267855481683037219569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6862047614617821432585517 2573267855481683037219569)
              ·
                refine ⟨1929950891611262277914677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573267855481683037219569 1929950891611262277914677)
                ·
                  refine ⟨180932896088555838554501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1929950891611262277914677 180932896088555838554501)
                  ·
                    rfl

theorem cell23_3171290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_3171290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171290 prefixEnd_3171290 := by exact prefixLift 3171290
  have htrace : WordTrace (prefixWord ++ tailWord_3171290) baseStart_3171290 baseEnd_3171290 := by
    simpa [prefixWord, tailWord_3171290, baseEnd_3171290] using wordTrace_append hprefix tailTrace_3171290
  have hstable : (prefixWord ++ tailWord_3171290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171290).length < 2 ^ (prefixWord ++ tailWord_3171290).sum := by decide
  have hdescent : baseEnd_3171290 < baseStart_3171290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171301 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3171301 : Nat := 118140960795 + 3171301 * 2 ^ 59
def prefixEnd_3171301 : Nat := 4983230072969 + 3 ^ 40 * 3171301 * 2
def baseEnd_3171301 : Nat := 1628401713084202003952959

theorem tailTrace_3171301 : CollatzResearch.WordTrace tailWord_3171301 prefixEnd_3171301 1628401713084202003952959 := by
  unfold tailWord_3171301
  simp only [CollatzResearch.WordTrace]
  refine ⟨115666849883925566935729757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77111233255950377957153171 115666849883925566935729757)
  ·
    refine ⟨43375068706472087600898659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115666849883925566935729757 43375068706472087600898659)
    ·
      refine ⟨65062603059708131401347989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43375068706472087600898659 65062603059708131401347989)
      ·
        refine ⟨3049809518423818659438187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65062603059708131401347989 3049809518423818659438187)
        ·
          refine ⟨4574714277635727989157281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049809518423818659438187 4574714277635727989157281)
          ·
            refine ⟨3431035708226795991867961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4574714277635727989157281 3431035708226795991867961)
            ·
              refine ⟨2573276781170096993900971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431035708226795991867961 2573276781170096993900971)
              ·
                refine ⟨3859915171755145490851457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2573276781170096993900971 3859915171755145490851457)
                ·
                  refine ⟨2894936378816359118138593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3859915171755145490851457 2894936378816359118138593)
                  ·
                    refine ⟨2171202284112269338603945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894936378816359118138593 2171202284112269338603945)
                    ·
                      refine ⟨1628401713084202003952959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171202284112269338603945 1628401713084202003952959)
                      ·
                        rfl

theorem cell23_3171301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3171301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171301 prefixEnd_3171301 := by exact prefixLift 3171301
  have htrace : WordTrace (prefixWord ++ tailWord_3171301) baseStart_3171301 baseEnd_3171301 := by
    simpa [prefixWord, tailWord_3171301, baseEnd_3171301] using wordTrace_append hprefix tailTrace_3171301
  have hstable : (prefixWord ++ tailWord_3171301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171301).length < 2 ^ (prefixWord ++ tailWord_3171301).sum := by decide
  have hdescent : baseEnd_3171301 < baseStart_3171301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171376 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 3, 5]
def baseStart_3171376 : Nat := 118140960795 + 3171376 * 2 ^ 59
def prefixEnd_3171376 : Nat := 4983230072969 + 3 ^ 40 * 3171376 * 2
def baseEnd_3171376 : Nat := 542813408044429736838371

theorem tailTrace_3171376 : CollatzResearch.WordTrace tailWord_3171376 prefixEnd_3171376 542813408044429736838371 := by
  unfold tailWord_3171376
  simp only [CollatzResearch.WordTrace]
  refine ⟨57834792679326927372354991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77113056905769236496473321 57834792679326927372354991)
  ·
    refine ⟨86752189018990391058532487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57834792679326927372354991 86752189018990391058532487)
    ·
      refine ⟨130128283528485586587798731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86752189018990391058532487 130128283528485586587798731)
      ·
        refine ⟨195192425292728379881698097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130128283528485586587798731 195192425292728379881698097)
        ·
          refine ⟨146394318969546284911273573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195192425292728379881698097 146394318969546284911273573)
          ·
            refine ⟨27448934806789928420863795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146394318969546284911273573 27448934806789928420863795)
            ·
              refine ⟨41173402210184892631295693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27448934806789928420863795 41173402210184892631295693)
              ·
                refine ⟨15440025828819334736735885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41173402210184892631295693 15440025828819334736735885)
                ·
                  refine ⟨5790009685807250526275957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15440025828819334736735885 5790009685807250526275957)
                  ·
                    refine ⟨542813408044429736838371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5790009685807250526275957 542813408044429736838371)
                    ·
                      rfl

theorem cell23_3171376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_3171376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171376 prefixEnd_3171376 := by exact prefixLift 3171376
  have htrace : WordTrace (prefixWord ++ tailWord_3171376) baseStart_3171376 baseEnd_3171376 := by
    simpa [prefixWord, tailWord_3171376, baseEnd_3171376] using wordTrace_append hprefix tailTrace_3171376
  have hstable : (prefixWord ++ tailWord_3171376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171376).length < 2 ^ (prefixWord ++ tailWord_3171376).sum := by decide
  have hdescent : baseEnd_3171376 < baseStart_3171376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171414 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3171414 : Nat := 118140960795 + 3171414 * 2 ^ 59
def prefixEnd_3171414 : Nat := 4983230072969 + 3 ^ 40 * 3171414 * 2
def baseEnd_3171414 : Nat := 180939970710906673537771

theorem tailTrace_3171414 : CollatzResearch.WordTrace tailWord_3171414 prefixEnd_3171414 180939970710906673537771 := by
  unfold tailWord_3171414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7229435708282261702162081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77113980888344124823062197 7229435708282261702162081)
  ·
    refine ⟨5422076781211696276621561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7229435708282261702162081 5422076781211696276621561)
    ·
      refine ⟨4066557585908772207466171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5422076781211696276621561 4066557585908772207466171)
      ·
        refine ⟨6099836378863158311199257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066557585908772207466171 6099836378863158311199257)
        ·
          refine ⟨4574877284147368733399443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6099836378863158311199257 4574877284147368733399443)
          ·
            refine ⟨6862315926221053100099165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4574877284147368733399443 6862315926221053100099165)
            ·
              refine ⟨2573368472332894912537187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6862315926221053100099165 2573368472332894912537187)
              ·
                refine ⟨3860052708499342368805781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2573368472332894912537187 3860052708499342368805781)
                ·
                  refine ⟨180939970710906673537771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3860052708499342368805781 180939970710906673537771)
                  ·
                    rfl

theorem cell23_3171414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3171414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171414 prefixEnd_3171414 := by exact prefixLift 3171414
  have htrace : WordTrace (prefixWord ++ tailWord_3171414) baseStart_3171414 baseEnd_3171414 := by
    simpa [prefixWord, tailWord_3171414, baseEnd_3171414] using wordTrace_append hprefix tailTrace_3171414
  have hstable : (prefixWord ++ tailWord_3171414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171414).length < 2 ^ (prefixWord ++ tailWord_3171414).sum := by decide
  have hdescent : baseEnd_3171414 < baseStart_3171414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171436 : List Nat := [2, 2, 1, 1, 3, 2, 3, 9]
def baseStart_3171436 : Nat := 118140960795 + 3171436 * 2 ^ 59
def prefixEnd_3171436 : Nat := 4983230072969 + 3 ^ 40 * 3171436 * 2
def baseEnd_3171436 : Nat := 60313741961946628732031

theorem tailTrace_3171436 : CollatzResearch.WordTrace tailWord_3171436 prefixEnd_3171436 60313741961946628732031 := by
  unfold tailWord_3171436
  simp only [CollatzResearch.WordTrace]
  refine ⟨57835886869218242495947081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77114515825624323327929441 57835886869218242495947081)
  ·
    refine ⟨43376915151913681871960311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57835886869218242495947081 43376915151913681871960311)
    ·
      refine ⟨65065372727870522807940467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43376915151913681871960311 65065372727870522807940467)
      ·
        refine ⟨97598059091805784211910701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65065372727870522807940467 97598059091805784211910701)
        ·
          refine ⟨36599272159427169079466513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97598059091805784211910701 36599272159427169079466513)
          ·
            refine ⟨27449454119570376809599885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36599272159427169079466513 27449454119570376809599885)
            ·
              refine ⟨10293545294838891303599957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27449454119570376809599885 10293545294838891303599957)
              ·
                refine ⟨60313741961946628732031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10293545294838891303599957 60313741961946628732031)
                ·
                  rfl

theorem cell23_3171436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 9].length) (baseStart_3171436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171436 prefixEnd_3171436 := by exact prefixLift 3171436
  have htrace : WordTrace (prefixWord ++ tailWord_3171436) baseStart_3171436 baseEnd_3171436 := by
    simpa [prefixWord, tailWord_3171436, baseEnd_3171436] using wordTrace_append hprefix tailTrace_3171436
  have hstable : (prefixWord ++ tailWord_3171436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171436).length < 2 ^ (prefixWord ++ tailWord_3171436).sum := by decide
  have hdescent : baseEnd_3171436 < baseStart_3171436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171474 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3171474 : Nat := 118140960795 + 3171474 * 2 ^ 59
def prefixEnd_3171474 : Nat := 4983230072969 + 3 ^ 40 * 3171474 * 2
def baseEnd_3171474 : Nat := 542830181745809942363221

theorem tailTrace_3171474 : CollatzResearch.WordTrace tailWord_3171474 prefixEnd_3171474 542830181745809942363221 := by
  unfold tailWord_3171474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28918289928074704370444369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77115439808199211654518317 28918289928074704370444369)
  ·
    refine ⟨21688717446056028277833277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28918289928074704370444369 21688717446056028277833277)
    ·
      refine ⟨8133269042271010604187479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21688717446056028277833277 8133269042271010604187479)
      ·
        refine ⟨12199903563406515906281219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8133269042271010604187479 12199903563406515906281219)
        ·
          refine ⟨18299855345109773859421829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12199903563406515906281219 18299855345109773859421829)
          ·
            refine ⟨3431222877208082598641593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18299855345109773859421829 3431222877208082598641593)
            ·
              refine ⟨2573417157906061948981195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431222877208082598641593 2573417157906061948981195)
              ·
                refine ⟨3860125736859092923471793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2573417157906061948981195 3860125736859092923471793)
                ·
                  refine ⟨2895094302644319692603845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3860125736859092923471793 2895094302644319692603845)
                  ·
                    refine ⟨542830181745809942363221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895094302644319692603845 542830181745809942363221)
                    ·
                      rfl

theorem cell23_3171474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3171474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171474 prefixEnd_3171474 := by exact prefixLift 3171474
  have htrace : WordTrace (prefixWord ++ tailWord_3171474) baseStart_3171474 baseEnd_3171474 := by
    simpa [prefixWord, tailWord_3171474, baseEnd_3171474] using wordTrace_append hprefix tailTrace_3171474
  have hstable : (prefixWord ++ tailWord_3171474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171474).length < 2 ^ (prefixWord ++ tailWord_3171474).sum := by decide
  have hdescent : baseEnd_3171474 < baseStart_3171474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171593 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_3171593 : Nat := 118140960795 + 3171593 * 2 ^ 59
def prefixEnd_3171593 : Nat := 4983230072969 + 3 ^ 40 * 3171593 * 2
def baseEnd_3171593 : Nat := 1628551649435314861501615

theorem tailTrace_3171593 : CollatzResearch.WordTrace tailWord_3171593 prefixEnd_3171593 1628551649435314861501615 := by
  unfold tailWord_3171593
  simp only [CollatzResearch.WordTrace]
  refine ⟨115677499998867700805359433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77118333332578467203572955 115677499998867700805359433)
  ·
    refine ⟨86758124999150775604019575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115677499998867700805359433 86758124999150775604019575)
    ·
      refine ⟨130137187498726163406029363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86758124999150775604019575 130137187498726163406029363)
      ·
        refine ⟨195205781248089245109044045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130137187498726163406029363 195205781248089245109044045)
        ·
          refine ⟨73202167968033466915891517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195205781248089245109044045 73202167968033466915891517)
          ·
            refine ⟨27450812988012550093459319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73202167968033466915891517 27450812988012550093459319)
            ·
              refine ⟨41176219482018825140188979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27450812988012550093459319 41176219482018825140188979)
              ·
                refine ⟨61764329223028237710283469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41176219482018825140188979 61764329223028237710283469)
                ·
                  refine ⟨23161623458635589141356301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61764329223028237710283469 23161623458635589141356301)
                  ·
                    refine ⟨8685608796988345928008613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23161623458635589141356301 8685608796988345928008613)
                    ·
                      refine ⟨1628551649435314861501615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8685608796988345928008613 1628551649435314861501615)
                      ·
                        rfl

theorem cell23_3171593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_3171593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171593 prefixEnd_3171593 := by exact prefixLift 3171593
  have htrace : WordTrace (prefixWord ++ tailWord_3171593) baseStart_3171593 baseEnd_3171593 := by
    simpa [prefixWord, tailWord_3171593, baseEnd_3171593] using wordTrace_append hprefix tailTrace_3171593
  have hstable : (prefixWord ++ tailWord_3171593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171593).length < 2 ^ (prefixWord ++ tailWord_3171593).sum := by decide
  have hdescent : baseEnd_3171593 < baseStart_3171593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171610 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3171610 : Nat := 118140960795 + 3171610 * 2 ^ 59
def prefixEnd_3171610 : Nat := 4983230072969 + 3 ^ 40 * 3171610 * 2
def baseEnd_3171610 : Nat := 1628560378606441294989037

theorem tailTrace_3171610 : CollatzResearch.WordTrace tailWord_3171610 prefixEnd_3171610 1628560378606441294989037 := by
  unfold tailWord_3171610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28919530009951528177182071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77118746693204075139152189 28919530009951528177182071)
  ·
    refine ⟨43379295014927292265773107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28919530009951528177182071 43379295014927292265773107)
    ·
      refine ⟨65068942522390938398659661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43379295014927292265773107 65068942522390938398659661)
      ·
        refine ⟨24400853445896601899497373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65068942522390938398659661 24400853445896601899497373)
        ·
          refine ⟨9150320042211225712311515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24400853445896601899497373 9150320042211225712311515)
          ·
            refine ⟨13725480063316838568467273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150320042211225712311515 13725480063316838568467273)
            ·
              refine ⟨10294110047487628926350455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13725480063316838568467273 10294110047487628926350455)
              ·
                refine ⟨15441165071231443389525683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10294110047487628926350455 15441165071231443389525683)
                ·
                  refine ⟨23161747606847165084288525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15441165071231443389525683 23161747606847165084288525)
                  ·
                    refine ⟨8685655352567686906608197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23161747606847165084288525 8685655352567686906608197)
                    ·
                      refine ⟨1628560378606441294989037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8685655352567686906608197 1628560378606441294989037)
                      ·
                        rfl

theorem cell23_3171610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3171610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171610 prefixEnd_3171610 := by exact prefixLift 3171610
  have htrace : WordTrace (prefixWord ++ tailWord_3171610) baseStart_3171610 baseEnd_3171610 := by
    simpa [prefixWord, tailWord_3171610, baseEnd_3171610] using wordTrace_append hprefix tailTrace_3171610
  have hstable : (prefixWord ++ tailWord_3171610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171610).length < 2 ^ (prefixWord ++ tailWord_3171610).sum := by decide
  have hdescent : baseEnd_3171610 < baseStart_3171610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171637 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_3171637 : Nat := 118140960795 + 3171637 * 2 ^ 59
def prefixEnd_3171637 : Nat := 4983230072969 + 3 ^ 40 * 3171637 * 2
def baseEnd_3171637 : Nat := 542858080861370896450471

theorem tailTrace_3171637 : CollatzResearch.WordTrace tailWord_3171637 prefixEnd_3171637 542858080861370896450471 := by
  unfold tailWord_3171637
  simp only [CollatzResearch.WordTrace]
  refine ⟨115679104810708296319961165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77119403207138864213307443 115679104810708296319961165)
  ·
    refine ⟨43379664304015611119985437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115679104810708296319961165 43379664304015611119985437)
    ·
      refine ⟨16267374114005854169994539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43379664304015611119985437 16267374114005854169994539)
      ·
        refine ⟨24401061171008781254991809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16267374114005854169994539 24401061171008781254991809)
        ·
          refine ⟨18300795878256585941243857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24401061171008781254991809 18300795878256585941243857)
          ·
            refine ⟨13725596908692439455932893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18300795878256585941243857 13725596908692439455932893)
            ·
              refine ⟨5147098840759664795974835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13725596908692439455932893 5147098840759664795974835)
              ·
                refine ⟨7720648261139497193962253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147098840759664795974835 7720648261139497193962253)
                ·
                  refine ⟨2895243097927311447735845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7720648261139497193962253 2895243097927311447735845)
                  ·
                    refine ⟨542858080861370896450471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895243097927311447735845 542858080861370896450471)
                    ·
                      rfl

theorem cell23_3171637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_3171637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171637 prefixEnd_3171637 := by exact prefixLift 3171637
  have htrace : WordTrace (prefixWord ++ tailWord_3171637) baseStart_3171637 baseEnd_3171637 := by
    simpa [prefixWord, tailWord_3171637, baseEnd_3171637] using wordTrace_append hprefix tailTrace_3171637
  have hstable : (prefixWord ++ tailWord_3171637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171637).length < 2 ^ (prefixWord ++ tailWord_3171637).sum := by decide
  have hdescent : baseEnd_3171637 < baseStart_3171637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171653 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_3171653 : Nat := 118140960795 + 3171653 * 2 ^ 59
def prefixEnd_3171653 : Nat := 4983230072969 + 3 ^ 40 * 3171653 * 2
def baseEnd_3171653 : Nat := 1628582458274584626751339

theorem tailTrace_3171653 : CollatzResearch.WordTrace tailWord_3171653 prefixEnd_3171653 1628582458274584626751339 := by
  unfold tailWord_3171653
  simp only [CollatzResearch.WordTrace]
  refine ⟨115679688378650331052543613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77119792252433554035029075 115679688378650331052543613)
  ·
    refine ⟨43379883141993874144703855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115679688378650331052543613 43379883141993874144703855)
    ·
      refine ⟨65069824712990811217055783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43379883141993874144703855 65069824712990811217055783)
      ·
        refine ⟨97604737069486216825583675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65069824712990811217055783 97604737069486216825583675)
        ·
          refine ⟨146407105604229325238375513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97604737069486216825583675 146407105604229325238375513)
          ·
            refine ⟨109805329203171993928781635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146407105604229325238375513 109805329203171993928781635)
            ·
              refine ⟨164707993804757990893172453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109805329203171993928781635 164707993804757990893172453)
              ·
                refine ⟨30882748838392123292469835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164707993804757990893172453 30882748838392123292469835)
                ·
                  refine ⟨46324123257588184938704753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30882748838392123292469835 46324123257588184938704753)
                  ·
                    refine ⟨34743092443191138704028565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46324123257588184938704753 34743092443191138704028565)
                    ·
                      refine ⟨1628582458274584626751339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34743092443191138704028565 1628582458274584626751339)
                      ·
                        rfl

theorem cell23_3171653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_3171653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171653 prefixEnd_3171653 := by exact prefixLift 3171653
  have htrace : WordTrace (prefixWord ++ tailWord_3171653) baseStart_3171653 baseEnd_3171653 := by
    simpa [prefixWord, tailWord_3171653, baseEnd_3171653] using wordTrace_append hprefix tailTrace_3171653
  have hstable : (prefixWord ++ tailWord_3171653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171653).length < 2 ^ (prefixWord ++ tailWord_3171653).sum := by decide
  have hdescent : baseEnd_3171653 < baseStart_3171653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171661 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3171661 : Nat := 118140960795 + 3171661 * 2 ^ 59
def prefixEnd_3171661 : Nat := 4983230072969 + 3 ^ 40 * 3171661 * 2
def baseEnd_3171661 : Nat := 1628586566119820595451303

theorem tailTrace_3171661 : CollatzResearch.WordTrace tailWord_3171661 prefixEnd_3171661 1628586566119820595451303 := by
  unfold tailWord_3171661
  simp only [CollatzResearch.WordTrace]
  refine ⟨115679980162621348418834837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77119986775080898945889891 115679980162621348418834837)
  ·
    refine ⟨5422499070122875707132883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115679980162621348418834837 5422499070122875707132883)
    ·
      refine ⟨8133748605184313560699325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5422499070122875707132883 8133748605184313560699325)
      ·
        refine ⟨3050155726944117585262247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8133748605184313560699325 3050155726944117585262247)
        ·
          refine ⟨4575233590416176377893371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050155726944117585262247 4575233590416176377893371)
          ·
            refine ⟨6862850385624264566840057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575233590416176377893371 6862850385624264566840057)
            ·
              refine ⟨5147137789218198425130043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6862850385624264566840057 5147137789218198425130043)
              ·
                refine ⟨7720706683827297637695065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147137789218198425130043 7720706683827297637695065)
                ·
                  refine ⟨5790530012870473228271299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7720706683827297637695065 5790530012870473228271299)
                  ·
                    refine ⟨8685795019305709842406949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5790530012870473228271299 8685795019305709842406949)
                    ·
                      refine ⟨1628586566119820595451303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8685795019305709842406949 1628586566119820595451303)
                      ·
                        rfl

theorem cell23_3171661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3171661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171661 prefixEnd_3171661 := by exact prefixLift 3171661
  have htrace : WordTrace (prefixWord ++ tailWord_3171661) baseStart_3171661 baseEnd_3171661 := by
    simpa [prefixWord, tailWord_3171661, baseEnd_3171661] using wordTrace_append hprefix tailTrace_3171661
  have hstable : (prefixWord ++ tailWord_3171661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171661).length < 2 ^ (prefixWord ++ tailWord_3171661).sum := by decide
  have hdescent : baseEnd_3171661 < baseStart_3171661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171688 : List Nat := [2, 1, 4, 2, 3, 2, 2, 2, 1, 4]
def baseStart_3171688 : Nat := 118140960795 + 3171688 * 2 ^ 59
def prefixEnd_3171688 : Nat := 4983230072969 + 3 ^ 40 * 3171688 * 2
def baseEnd_3171688 : Nat := 542866810032497329937893

theorem tailTrace_3171688 : CollatzResearch.WordTrace tailWord_3171688 prefixEnd_3171688 542866810032497329937893 := by
  unfold tailWord_3171688
  simp only [CollatzResearch.WordTrace]
  refine ⟨57840482466761766015033859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77120643289015688020045145 57840482466761766015033859)
  ·
    refine ⟨86760723700142649022550789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57840482466761766015033859 86760723700142649022550789)
    ·
      refine ⟨16267635693776746691728273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86760723700142649022550789 16267635693776746691728273)
      ·
        refine ⟨12200726770332560018796205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16267635693776746691728273 12200726770332560018796205)
        ·
          refine ⟨4575272538874710007048577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12200726770332560018796205 4575272538874710007048577)
          ·
            refine ⟨3431454404156032505286433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4575272538874710007048577 3431454404156032505286433)
            ·
              refine ⟨2573590803117024378964825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431454404156032505286433 2573590803117024378964825)
              ·
                refine ⟨1930193102337768284223619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573590803117024378964825 1930193102337768284223619)
                ·
                  refine ⟨2895289653506652426335429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930193102337768284223619 2895289653506652426335429)
                  ·
                    refine ⟨542866810032497329937893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895289653506652426335429 542866810032497329937893)
                    ·
                      rfl

theorem cell23_3171688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_3171688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171688 prefixEnd_3171688 := by exact prefixLift 3171688
  have htrace : WordTrace (prefixWord ++ tailWord_3171688) baseStart_3171688 baseEnd_3171688 := by
    simpa [prefixWord, tailWord_3171688, baseEnd_3171688] using wordTrace_append hprefix tailTrace_3171688
  have hstable : (prefixWord ++ tailWord_3171688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171688).length < 2 ^ (prefixWord ++ tailWord_3171688).sum := by decide
  have hdescent : baseEnd_3171688 < baseStart_3171688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171714 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3171714 : Nat := 118140960795 + 3171714 * 2 ^ 59
def prefixEnd_3171714 : Nat := 4983230072969 + 3 ^ 40 * 3171714 * 2
def baseEnd_3171714 : Nat := 542871260198169629362853

theorem tailTrace_3171714 : CollatzResearch.WordTrace tailWord_3171714 prefixEnd_3171714 542871260198169629362853 := by
  unfold tailWord_3171714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28920478307857334617628549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77121275487619558980342797 28920478307857334617628549)
  ·
    refine ⟨5422589682723250240805353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28920478307857334617628549 5422589682723250240805353)
    ·
      refine ⟨4066942262042437680604015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5422589682723250240805353 4066942262042437680604015)
      ·
        refine ⟨6100413393063656520906023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066942262042437680604015 6100413393063656520906023)
        ·
          refine ⟨9150620089595484781359035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100413393063656520906023 9150620089595484781359035)
          ·
            refine ⟨13725930134393227172038553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150620089595484781359035 13725930134393227172038553)
            ·
              refine ⟨10294447600794920379028915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13725930134393227172038553 10294447600794920379028915)
              ·
                refine ⟨15441671401192380568543373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10294447600794920379028915 15441671401192380568543373)
                ·
                  refine ⟨5790626775447142713203765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15441671401192380568543373 5790626775447142713203765)
                  ·
                    refine ⟨542871260198169629362853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5790626775447142713203765 542871260198169629362853)
                    ·
                      rfl

theorem cell23_3171714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3171714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171714 prefixEnd_3171714 := by exact prefixLift 3171714
  have htrace : WordTrace (prefixWord ++ tailWord_3171714) baseStart_3171714 baseEnd_3171714 := by
    simpa [prefixWord, tailWord_3171714, baseEnd_3171714] using wordTrace_append hprefix tailTrace_3171714
  have hstable : (prefixWord ++ tailWord_3171714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171714).length < 2 ^ (prefixWord ++ tailWord_3171714).sum := by decide
  have hdescent : baseEnd_3171714 < baseStart_3171714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171721 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 2, 3, 2]
def baseStart_3171721 : Nat := 118140960795 + 3171721 * 2 ^ 59
def prefixEnd_3171721 : Nat := 4983230072969 + 3 ^ 40 * 3171721 * 2
def baseEnd_3171721 : Nat := 1628617374959090360701027

theorem tailTrace_3171721 : CollatzResearch.WordTrace tailWord_3171721 prefixEnd_3171721 1628617374959090360701027 := by
  unfold tailWord_3171721
  simp only [CollatzResearch.WordTrace]
  refine ⟨115682168542403978666019017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77121445694935985777346011 115682168542403978666019017)
  ·
    refine ⟨86761626406802983999514263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115682168542403978666019017 86761626406802983999514263)
    ·
      refine ⟨130142439610204475999271395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86761626406802983999514263 130142439610204475999271395)
      ·
        refine ⟨195213659415306713998907093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130142439610204475999271395 195213659415306713998907093)
        ·
          refine ⟨4575320142546251109349385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 195213659415306713998907093 4575320142546251109349385)
          ·
            refine ⟨3431490106909688332012039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4575320142546251109349385 3431490106909688332012039)
            ·
              refine ⟨5147235160364532498018059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3431490106909688332012039 5147235160364532498018059)
              ·
                refine ⟨7720852740546798747027089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147235160364532498018059 7720852740546798747027089)
                ·
                  refine ⟨5790639555410099060270317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7720852740546798747027089 5790639555410099060270317)
                  ·
                    refine ⟨2171489833278787147601369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5790639555410099060270317 2171489833278787147601369)
                    ·
                      refine ⟨1628617374959090360701027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171489833278787147601369 1628617374959090360701027)
                      ·
                        rfl

theorem cell23_3171721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 3, 2].length) (baseStart_3171721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171721 prefixEnd_3171721 := by exact prefixLift 3171721
  have htrace : WordTrace (prefixWord ++ tailWord_3171721) baseStart_3171721 baseEnd_3171721 := by
    simpa [prefixWord, tailWord_3171721, baseEnd_3171721] using wordTrace_append hprefix tailTrace_3171721
  have hstable : (prefixWord ++ tailWord_3171721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171721).length < 2 ^ (prefixWord ++ tailWord_3171721).sum := by decide
  have hdescent : baseEnd_3171721 < baseStart_3171721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171751 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_3171751 : Nat := 118140960795 + 3171751 * 2 ^ 59
def prefixEnd_3171751 : Nat := 4983230072969 + 3 ^ 40 * 3171751 * 2
def baseEnd_3171751 : Nat := 1628632779378725243325889

theorem tailTrace_3171751 : CollatzResearch.WordTrace tailWord_3171751 prefixEnd_3171751 1628632779378725243325889 := by
  unfold tailWord_3171751
  simp only [CollatzResearch.WordTrace]
  refine ⟨115683262732295293789611107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77122175154863529193074071 115683262732295293789611107)
  ·
    refine ⟨173524894098442940684416661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115683262732295293789611107 173524894098442940684416661)
    ·
      refine ⟨8133979410864512844582031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173524894098442940684416661 8133979410864512844582031)
      ·
        refine ⟨12200969116296769266873047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8133979410864512844582031 12200969116296769266873047)
        ·
          refine ⟨18301453674445153900309571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12200969116296769266873047 18301453674445153900309571)
          ·
            refine ⟨27452180511667730850464357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18301453674445153900309571 27452180511667730850464357)
            ·
              refine ⟨5147283845937699534462067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27452180511667730850464357 5147283845937699534462067)
              ·
                refine ⟨7720925768906549301693101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147283845937699534462067 7720925768906549301693101)
                ·
                  refine ⟨2895347163339955988134913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7720925768906549301693101 2895347163339955988134913)
                  ·
                    refine ⟨2171510372504966991101185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2895347163339955988134913 2171510372504966991101185)
                    ·
                      refine ⟨1628632779378725243325889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171510372504966991101185 1628632779378725243325889)
                      ·
                        rfl

theorem cell23_3171751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_3171751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171751 prefixEnd_3171751 := by exact prefixLift 3171751
  have htrace : WordTrace (prefixWord ++ tailWord_3171751) baseStart_3171751 baseEnd_3171751 := by
    simpa [prefixWord, tailWord_3171751, baseEnd_3171751] using wordTrace_append hprefix tailTrace_3171751
  have hstable : (prefixWord ++ tailWord_3171751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171751).length < 2 ^ (prefixWord ++ tailWord_3171751).sum := by decide
  have hdescent : baseEnd_3171751 < baseStart_3171751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171800 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 4, 6]
def baseStart_3171800 : Nat := 118140960795 + 3171800 * 2 ^ 59
def prefixEnd_3171800 : Nat := 4983230072969 + 3 ^ 40 * 3171800 * 2
def baseEnd_3171800 : Nat := 542885979976931850537721

theorem tailTrace_3171800 : CollatzResearch.WordTrace tailWord_3171800 prefixEnd_3171800 542885979976931850537721 := by
  unfold tailWord_3171800
  simp only [CollatzResearch.WordTrace]
  refine ⟨57842524954558887579072427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77123366606078516772096569 57842524954558887579072427)
  ·
    refine ⟨86763787431838331368608641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57842524954558887579072427 86763787431838331368608641)
    ·
      refine ⟨65072840573878748526456481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86763787431838331368608641 65072840573878748526456481)
      ·
        refine ⟨48804630430409061394842361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65072840573878748526456481 48804630430409061394842361)
        ·
          refine ⟨36603472822806796046131771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48804630430409061394842361 36603472822806796046131771)
          ·
            refine ⟨54905209234210194069197657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36603472822806796046131771 54905209234210194069197657)
            ·
              refine ⟨41178906925657645551898243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54905209234210194069197657 41178906925657645551898243)
              ·
                refine ⟨61768360388486468327847365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41178906925657645551898243 61768360388486468327847365)
                ·
                  refine ⟨11581567572841212811471381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61768360388486468327847365 11581567572841212811471381)
                  ·
                    refine ⟨542885979976931850537721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11581567572841212811471381 542885979976931850537721)
                    ·
                      rfl

theorem cell23_3171800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_3171800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171800 prefixEnd_3171800 := by exact prefixLift 3171800
  have htrace : WordTrace (prefixWord ++ tailWord_3171800) baseStart_3171800 baseEnd_3171800 := by
    simpa [prefixWord, tailWord_3171800, baseEnd_3171800] using wordTrace_append hprefix tailTrace_3171800
  have hstable : (prefixWord ++ tailWord_3171800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171800).length < 2 ^ (prefixWord ++ tailWord_3171800).sum := by decide
  have hdescent : baseEnd_3171800 < baseStart_3171800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171841 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_3171841 : Nat := 118140960795 + 3171841 * 2 ^ 59
def prefixEnd_3171841 : Nat := 4983230072969 + 3 ^ 40 * 3171841 * 2
def baseEnd_3171841 : Nat := 1628678992637629891200475

theorem tailTrace_3171841 : CollatzResearch.WordTrace tailWord_3171841 prefixEnd_3171841 1628678992637629891200475 := by
  unfold tailWord_3171841
  simp only [CollatzResearch.WordTrace]
  refine ⟨115686545301969239160387377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77124363534646159440258251 115686545301969239160387377)
  ·
    refine ⟨86764908976476929370290533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115686545301969239160387377 86764908976476929370290533)
    ·
      refine ⟨16268420433089424256929475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86764908976476929370290533 16268420433089424256929475)
      ·
        refine ⟨24402630649634136385394213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16268420433089424256929475 24402630649634136385394213)
        ·
          refine ⟨4575493246806400572261415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24402630649634136385394213 4575493246806400572261415)
          ·
            refine ⟨6863239870209600858392123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575493246806400572261415 6863239870209600858392123)
            ·
              refine ⟨10294859805314401287588185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863239870209600858392123 10294859805314401287588185)
              ·
                refine ⟨7721144853985800965691139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10294859805314401287588185 7721144853985800965691139)
                ·
                  refine ⟨11581717280978701448536709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7721144853985800965691139 11581717280978701448536709)
                  ·
                    refine ⟨2171571990183506521600633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11581717280978701448536709 2171571990183506521600633)
                    ·
                      refine ⟨1628678992637629891200475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171571990183506521600633 1628678992637629891200475)
                      ·
                        rfl

theorem cell23_3171841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_3171841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171841 prefixEnd_3171841 := by exact prefixLift 3171841
  have htrace : WordTrace (prefixWord ++ tailWord_3171841) baseStart_3171841 baseEnd_3171841 := by
    simpa [prefixWord, tailWord_3171841, baseEnd_3171841] using wordTrace_append hprefix tailTrace_3171841
  have hstable : (prefixWord ++ tailWord_3171841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171841).length < 2 ^ (prefixWord ++ tailWord_3171841).sum := by decide
  have hdescent : baseEnd_3171841 < baseStart_3171841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171857 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_3171857 : Nat := 118140960795 + 3171857 * 2 ^ 59
def prefixEnd_3171857 : Nat := 4983230072969 + 3 ^ 40 * 3171857 * 2
def baseEnd_3171857 : Nat := 1628687208328101828600401

theorem tailTrace_3171857 : CollatzResearch.WordTrace tailWord_3171857 prefixEnd_3171857 1628687208328101828600401 := by
  unfold tailWord_3171857
  simp only [CollatzResearch.WordTrace]
  refine ⟨115687128869911273892969825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77124752579940849261979883 115687128869911273892969825)
  ·
    refine ⟨86765346652433455419727369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115687128869911273892969825 86765346652433455419727369)
    ·
      refine ⟨65074009989325091564795527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86765346652433455419727369 65074009989325091564795527)
      ·
        refine ⟨97611014983987637347193291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65074009989325091564795527 97611014983987637347193291)
        ·
          refine ⟨146416522475981456020789937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97611014983987637347193291 146416522475981456020789937)
          ·
            refine ⟨109812391856986092015592453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146416522475981456020789937 109812391856986092015592453)
            ·
              refine ⟨20589823473184892252923585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109812391856986092015592453 20589823473184892252923585)
              ·
                refine ⟨15442367604888669189692689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20589823473184892252923585 15442367604888669189692689)
                ·
                  refine ⟨11581775703666501892269517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15442367604888669189692689 11581775703666501892269517)
                  ·
                    refine ⟨4343165888874938209601069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11581775703666501892269517 4343165888874938209601069)
                    ·
                      refine ⟨1628687208328101828600401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4343165888874938209601069 1628687208328101828600401)
                      ·
                        rfl

theorem cell23_3171857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_3171857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171857 prefixEnd_3171857 := by exact prefixLift 3171857
  have htrace : WordTrace (prefixWord ++ tailWord_3171857) baseStart_3171857 baseEnd_3171857 := by
    simpa [prefixWord, tailWord_3171857, baseEnd_3171857] using wordTrace_append hprefix tailTrace_3171857
  have hstable : (prefixWord ++ tailWord_3171857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171857).length < 2 ^ (prefixWord ++ tailWord_3171857).sum := by decide
  have hdescent : baseEnd_3171857 < baseStart_3171857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3171914 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2]
def baseStart_3171914 : Nat := 118140960795 + 3171914 * 2 ^ 59
def prefixEnd_3171914 : Nat := 4983230072969 + 3 ^ 40 * 3171914 * 2
def baseEnd_3171914 : Nat := 1628716476725408105587639

theorem tailTrace_3171914 : CollatzResearch.WordTrace tailWord_3171914 prefixEnd_3171914 1628716476725408105587639 := by
  unfold tailWord_3171914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28922301957676193156948699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77126138553803181751863197 28922301957676193156948699)
  ·
    refine ⟨43383452936514289735423049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28922301957676193156948699 43383452936514289735423049)
    ·
      refine ⟨32537589702385717301567287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43383452936514289735423049 32537589702385717301567287)
      ·
        refine ⟨48806384553578575952350931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32537589702385717301567287 48806384553578575952350931)
        ·
          refine ⟨73209576830367863928526397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48806384553578575952350931 73209576830367863928526397)
          ·
            refine ⟨27453591311387948973197399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73209576830367863928526397 27453591311387948973197399)
            ·
              refine ⟨41180386967081923459796099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27453591311387948973197399 41180386967081923459796099)
              ·
                refine ⟨61770580450622885189694149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41180386967081923459796099 61770580450622885189694149)
                ·
                  refine ⟨11581983834491790973067653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61770580450622885189694149 11581983834491790973067653)
                  ·
                    refine ⟨2171621968967210807450185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11581983834491790973067653 2171621968967210807450185)
                    ·
                      refine ⟨1628716476725408105587639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171621968967210807450185 1628716476725408105587639)
                      ·
                        rfl

theorem cell23_3171914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_3171914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3171914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3171914 prefixEnd_3171914 := by exact prefixLift 3171914
  have htrace : WordTrace (prefixWord ++ tailWord_3171914) baseStart_3171914 baseEnd_3171914 := by
    simpa [prefixWord, tailWord_3171914, baseEnd_3171914] using wordTrace_append hprefix tailTrace_3171914
  have hstable : (prefixWord ++ tailWord_3171914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3171914).length < 2 ^ (prefixWord ++ tailWord_3171914).sum := by decide
  have hdescent : baseEnd_3171914 < baseStart_3171914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3171914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172001 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 1, 5]
def baseStart_3172001 : Nat := 118140960795 + 3172001 * 2 ^ 59
def prefixEnd_3172001 : Nat := 4983230072969 + 3 ^ 40 * 3172001 * 2
def baseEnd_3172001 : Nat := 542920383180783088399913

theorem tailTrace_3172001 : CollatzResearch.WordTrace tailWord_3172001 prefixEnd_3172001 542920383180783088399913 := by
  unfold tailWord_3172001
  simp only [CollatzResearch.WordTrace]
  refine ⟨115692380981389586486211857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77128253987593057657474571 115692380981389586486211857)
  ·
    refine ⟨86769285736042189864658893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115692380981389586486211857 86769285736042189864658893)
    ·
      refine ⟨32538482151015821199247085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86769285736042189864658893 32538482151015821199247085)
      ·
        refine ⟨12201930806630932949717657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32538482151015821199247085 12201930806630932949717657)
        ·
          refine ⟨9151448104973199712288243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12201930806630932949717657 9151448104973199712288243)
          ·
            refine ⟨13727172157459799568432365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151448104973199712288243 13727172157459799568432365)
            ·
              refine ⟨5147689559047424838162137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13727172157459799568432365 5147689559047424838162137)
              ·
                refine ⟨3860767169285568628621603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5147689559047424838162137 3860767169285568628621603)
                ·
                  refine ⟨5791150753928352942932405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860767169285568628621603 5791150753928352942932405)
                  ·
                    refine ⟨542920383180783088399913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5791150753928352942932405 542920383180783088399913)
                    ·
                      rfl

theorem cell23_3172001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_3172001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172001 prefixEnd_3172001 := by exact prefixLift 3172001
  have htrace : WordTrace (prefixWord ++ tailWord_3172001) baseStart_3172001 baseEnd_3172001 := by
    simpa [prefixWord, tailWord_3172001, baseEnd_3172001] using wordTrace_append hprefix tailTrace_3172001
  have hstable : (prefixWord ++ tailWord_3172001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172001).length < 2 ^ (prefixWord ++ tailWord_3172001).sum := by decide
  have hdescent : baseEnd_3172001 < baseStart_3172001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172031 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 2, 4]
def baseStart_3172031 : Nat := 118140960795 + 3172031 * 2 ^ 59
def prefixEnd_3172031 : Nat := 4983230072969 + 3 ^ 40 * 3172031 * 2
def baseEnd_3172031 : Nat := 542925517987328049274867

theorem tailTrace_3172031 : CollatzResearch.WordTrace tailWord_3172031 prefixEnd_3172031 542925517987328049274867 := by
  unfold tailWord_3172031
  simp only [CollatzResearch.WordTrace]
  refine ⟨115693475171280901609803947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77128983447520601073202631 115693475171280901609803947)
  ·
    refine ⟨173540212756921352414705921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115693475171280901609803947 173540212756921352414705921)
    ·
      refine ⟨130155159567691014311029441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173540212756921352414705921 130155159567691014311029441)
      ·
        refine ⟨97616369675768260733272081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130155159567691014311029441 97616369675768260733272081)
        ·
          refine ⟨73212277256826195549954061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97616369675768260733272081 73212277256826195549954061)
          ·
            refine ⟨27454603971309823331232773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73212277256826195549954061 27454603971309823331232773)
            ·
              refine ⟨5147738244620591874606145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27454603971309823331232773 5147738244620591874606145)
              ·
                refine ⟨3860803683465443905954609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5147738244620591874606145 3860803683465443905954609)
                ·
                  refine ⟨2895602762599082929465957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3860803683465443905954609 2895602762599082929465957)
                  ·
                    refine ⟨542925517987328049274867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895602762599082929465957 542925517987328049274867)
                    ·
                      rfl

theorem cell23_3172031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_3172031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172031 prefixEnd_3172031 := by exact prefixLift 3172031
  have htrace : WordTrace (prefixWord ++ tailWord_3172031) baseStart_3172031 baseEnd_3172031 := by
    simpa [prefixWord, tailWord_3172031, baseEnd_3172031] using wordTrace_append hprefix tailTrace_3172031
  have hstable : (prefixWord ++ tailWord_3172031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172031).length < 2 ^ (prefixWord ++ tailWord_3172031).sum := by decide
  have hdescent : baseEnd_3172031 < baseStart_3172031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172047 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_3172047 : Nat := 118140960795 + 3172047 * 2 ^ 59
def prefixEnd_3172047 : Nat := 4983230072969 + 3 ^ 40 * 3172047 * 2
def baseEnd_3172047 : Nat := 1628784769652456085224527

theorem tailTrace_3172047 : CollatzResearch.WordTrace tailWord_3172047 prefixEnd_3172047 1628784769652456085224527 := by
  unfold tailWord_3172047
  simp only [CollatzResearch.WordTrace]
  refine ⟨115694058739222936342386395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77129372492815290894924263 115694058739222936342386395)
  ·
    refine ⟨173541088108834404513579593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115694058739222936342386395 173541088108834404513579593)
    ·
      refine ⟨130155816081625803385184695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173541088108834404513579593 130155816081625803385184695)
      ·
        refine ⟨195233724122438705077777043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130155816081625803385184695 195233724122438705077777043)
        ·
          refine ⟨292850586183658057616665565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195233724122438705077777043 292850586183658057616665565)
          ·
            refine ⟨109818969818871771606249587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292850586183658057616665565 109818969818871771606249587)
            ·
              refine ⟨164728454728307657409374381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109818969818871771606249587 164728454728307657409374381)
              ·
                refine ⟨61773170523115371528515393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164728454728307657409374381 61773170523115371528515393)
                ·
                  refine ⟨46329877892336528646386545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61773170523115371528515393 46329877892336528646386545)
                  ·
                    refine ⟨34747408419252396484789909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46329877892336528646386545 34747408419252396484789909)
                    ·
                      refine ⟨1628784769652456085224527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34747408419252396484789909 1628784769652456085224527)
                      ·
                        rfl

theorem cell23_3172047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_3172047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172047 prefixEnd_3172047 := by exact prefixLift 3172047
  have htrace : WordTrace (prefixWord ++ tailWord_3172047) baseStart_3172047 baseEnd_3172047 := by
    simpa [prefixWord, tailWord_3172047, baseEnd_3172047] using wordTrace_append hprefix tailTrace_3172047
  have hstable : (prefixWord ++ tailWord_3172047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172047).length < 2 ^ (prefixWord ++ tailWord_3172047).sum := by decide
  have hdescent : baseEnd_3172047 < baseStart_3172047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172072 : List Nat := [2, 1, 4, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_3172072 : Nat := 118140960795 + 3172072 * 2 ^ 59
def prefixEnd_3172072 : Nat := 4983230072969 + 3 ^ 40 * 3172072 * 2
def baseEnd_3172072 : Nat := 1628797606668818487411913

theorem tailTrace_3172072 : CollatzResearch.WordTrace tailWord_3172072 prefixEnd_3172072 1628797606668818487411913 := by
  unfold tailWord_3172072
  simp only [CollatzResearch.WordTrace]
  refine ⟨57847485282066182806023235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77129980376088243741364313 57847485282066182806023235)
  ·
    refine ⟨86771227923099274209034853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57847485282066182806023235 86771227923099274209034853)
    ·
      refine ⟨16269605235581113914194035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86771227923099274209034853 16269605235581113914194035)
      ·
        refine ⟨24404407853371670871291053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16269605235581113914194035 24404407853371670871291053)
        ·
          refine ⟨9151652945014376576734145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24404407853371670871291053 9151652945014376576734145)
          ·
            refine ⟨6863739708760782432550609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9151652945014376576734145 6863739708760782432550609)
            ·
              refine ⟨5147804781570586824412957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6863739708760782432550609 5147804781570586824412957)
              ·
                refine ⟨1930426793088970059154859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5147804781570586824412957 1930426793088970059154859)
                ·
                  refine ⟨2895640189633455088732289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930426793088970059154859 2895640189633455088732289)
                  ·
                    refine ⟨2171730142225091316549217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2895640189633455088732289 2171730142225091316549217)
                    ·
                      refine ⟨1628797606668818487411913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171730142225091316549217 1628797606668818487411913)
                      ·
                        rfl

theorem cell23_3172072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_3172072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172072 prefixEnd_3172072 := by exact prefixLift 3172072
  have htrace : WordTrace (prefixWord ++ tailWord_3172072) baseStart_3172072 baseEnd_3172072 := by
    simpa [prefixWord, tailWord_3172072, baseEnd_3172072] using wordTrace_append hprefix tailTrace_3172072
  have hstable : (prefixWord ++ tailWord_3172072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172072).length < 2 ^ (prefixWord ++ tailWord_3172072).sum := by decide
  have hdescent : baseEnd_3172072 < baseStart_3172072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172104 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 2, 6]
def baseStart_3172104 : Nat := 118140960795 + 3172104 * 2 ^ 59
def prefixEnd_3172104 : Nat := 4983230072969 + 3 ^ 40 * 3172104 * 2
def baseEnd_3172104 : Nat := 542938012683254120737255

theorem tailTrace_3172104 : CollatzResearch.WordTrace tailWord_3172104 prefixEnd_3172104 542938012683254120737255 := by
  unfold tailWord_3172104
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848068850008217538605683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77130758466677623384807577 57848068850008217538605683)
  ·
    refine ⟨86772103275012326307908525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57848068850008217538605683 86772103275012326307908525)
    ·
      refine ⟨32539538728129622365465697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86772103275012326307908525 32539538728129622365465697)
      ·
        refine ⟨24404654046097216774099273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32539538728129622365465697 24404654046097216774099273)
        ·
          refine ⟨18303490534572912580574455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24404654046097216774099273 18303490534572912580574455)
          ·
            refine ⟨27455235801859368870861683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18303490534572912580574455 27455235801859368870861683)
            ·
              refine ⟨41182853702789053306292525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27455235801859368870861683 41182853702789053306292525)
              ·
                refine ⟨15443570138545894989859697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41182853702789053306292525 15443570138545894989859697)
                ·
                  refine ⟨11582677603909421242394773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15443570138545894989859697 11582677603909421242394773)
                  ·
                    refine ⟨542938012683254120737255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11582677603909421242394773 542938012683254120737255)
                    ·
                      rfl

theorem cell23_3172104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_3172104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172104 prefixEnd_3172104 := by exact prefixLift 3172104
  have htrace : WordTrace (prefixWord ++ tailWord_3172104) baseStart_3172104 baseEnd_3172104 := by
    simpa [prefixWord, tailWord_3172104, baseEnd_3172104] using wordTrace_append hprefix tailTrace_3172104
  have hstable : (prefixWord ++ tailWord_3172104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172104).length < 2 ^ (prefixWord ++ tailWord_3172104).sum := by decide
  have hdescent : baseEnd_3172104 < baseStart_3172104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172111 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 1, 4, 2]
def baseStart_3172111 : Nat := 118140960795 + 3172111 * 2 ^ 59
def prefixEnd_3172111 : Nat := 4983230072969 + 3 ^ 40 * 3172111 * 2
def baseEnd_3172111 : Nat := 1628817632414343834824233

theorem tailTrace_3172111 : CollatzResearch.WordTrace tailWord_3172111 prefixEnd_3172111 1628817632414343834824233 := by
  unfold tailWord_3172111
  simp only [CollatzResearch.WordTrace]
  refine ⟨115696393010991075272716187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77130928673994050181810791 115696393010991075272716187)
  ·
    refine ⟨173544589516486612909074281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115696393010991075272716187 173544589516486612909074281)
    ·
      refine ⟨130158442137364959681805711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173544589516486612909074281 130158442137364959681805711)
      ·
        refine ⟨195237663206047439522708567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130158442137364959681805711 195237663206047439522708567)
        ·
          refine ⟨292856494809071159284062851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195237663206047439522708567 292856494809071159284062851)
          ·
            refine ⟨439284742213606738926094277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292856494809071159284062851 439284742213606738926094277)
            ·
              refine ⟨82365889165051263548642677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439284742213606738926094277 82365889165051263548642677)
              ·
                refine ⟨7721802109223555957685251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82365889165051263548642677 7721802109223555957685251)
                ·
                  refine ⟨11582703163835333936527877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7721802109223555957685251 11582703163835333936527877)
                  ·
                    refine ⟨2171756843219125113098977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11582703163835333936527877 2171756843219125113098977)
                    ·
                      refine ⟨1628817632414343834824233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171756843219125113098977 1628817632414343834824233)
                      ·
                        rfl

theorem cell23_3172111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4, 2].length) (baseStart_3172111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172111 prefixEnd_3172111 := by exact prefixLift 3172111
  have htrace : WordTrace (prefixWord ++ tailWord_3172111) baseStart_3172111 baseEnd_3172111 := by
    simpa [prefixWord, tailWord_3172111, baseEnd_3172111] using wordTrace_append hprefix tailTrace_3172111
  have hstable : (prefixWord ++ tailWord_3172111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172111).length < 2 ^ (prefixWord ++ tailWord_3172111).sum := by decide
  have hdescent : baseEnd_3172111 < baseStart_3172111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172128 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 6, 2, 2]
def baseStart_3172128 : Nat := 118140960795 + 3172128 * 2 ^ 59
def prefixEnd_3172128 : Nat := 4983230072969 + 3 ^ 40 * 3172128 * 2
def baseEnd_3172128 : Nat := 1628826361585470268311655

theorem tailTrace_3172128 : CollatzResearch.WordTrace tailWord_3172128 prefixEnd_3172128 1628826361585470268311655 := by
  unfold tailWord_3172128
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848506525964743588042519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77131342034619658117390025 57848506525964743588042519)
  ·
    refine ⟨86772759788947115382063779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57848506525964743588042519 86772759788947115382063779)
    ·
      refine ⟨130159139683420673073095669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86772759788947115382063779 130159139683420673073095669)
      ·
        refine ⟨12202419345320688100602719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130159139683420673073095669 12202419345320688100602719)
        ·
          refine ⟨18303629017981032150904079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12202419345320688100602719 18303629017981032150904079)
          ·
            refine ⟨27455443526971548226356119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18303629017981032150904079 27455443526971548226356119)
            ·
              refine ⟨41183165290457322339534179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27455443526971548226356119 41183165290457322339534179)
              ·
                refine ⟨61774747935685983509301269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41183165290457322339534179 61774747935685983509301269)
                ·
                  refine ⟨2895691309485280476998497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61774747935685983509301269 2895691309485280476998497)
                  ·
                    refine ⟨2171768482113960357748873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2895691309485280476998497 2171768482113960357748873)
                    ·
                      refine ⟨1628826361585470268311655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171768482113960357748873 1628826361585470268311655)
                      ·
                        rfl

theorem cell23_3172128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_3172128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172128 prefixEnd_3172128 := by exact prefixLift 3172128
  have htrace : WordTrace (prefixWord ++ tailWord_3172128) baseStart_3172128 baseEnd_3172128 := by
    simpa [prefixWord, tailWord_3172128, baseEnd_3172128] using wordTrace_append hprefix tailTrace_3172128
  have hstable : (prefixWord ++ tailWord_3172128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172128).length < 2 ^ (prefixWord ++ tailWord_3172128).sum := by decide
  have hdescent : baseEnd_3172128 < baseStart_3172128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172181 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_3172181 : Nat := 118140960795 + 3172181 * 2 ^ 59
def prefixEnd_3172181 : Nat := 4983230072969 + 3 ^ 40 * 3172181 * 2
def baseEnd_3172181 : Nat := 542951192020052853649637

theorem tailTrace_3172181 : CollatzResearch.WordTrace tailWord_3172181 prefixEnd_3172181 542951192020052853649637 := by
  unfold tailWord_3172181
  simp only [CollatzResearch.WordTrace]
  refine ⟨115698946120737477227764397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77132630747158318151842931 115698946120737477227764397)
  ·
    refine ⟨43387104795276553960411649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115698946120737477227764397 43387104795276553960411649)
    ·
      refine ⟨32540328596457415470308737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43387104795276553960411649 32540328596457415470308737)
      ·
        refine ⟨24405246447343061602731553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32540328596457415470308737 24405246447343061602731553)
        ·
          refine ⟨18303934835507296202048665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24405246447343061602731553 18303934835507296202048665)
          ·
            refine ⟨13727951126630472151536499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18303934835507296202048665 13727951126630472151536499)
            ·
              refine ⟨20591926689945708227304749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13727951126630472151536499 20591926689945708227304749)
              ·
                refine ⟨7721972508729640585239281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20591926689945708227304749 7721972508729640585239281)
                ·
                  refine ⟨5791479381547230438929461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7721972508729640585239281 5791479381547230438929461)
                  ·
                    refine ⟨542951192020052853649637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5791479381547230438929461 542951192020052853649637)
                    ·
                      rfl

theorem cell23_3172181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_3172181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172181 prefixEnd_3172181 := by exact prefixLift 3172181
  have htrace : WordTrace (prefixWord ++ tailWord_3172181) baseStart_3172181 baseEnd_3172181 := by
    simpa [prefixWord, tailWord_3172181, baseEnd_3172181] using wordTrace_append hprefix tailTrace_3172181
  have hstable : (prefixWord ++ tailWord_3172181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172181).length < 2 ^ (prefixWord ++ tailWord_3172181).sum := by decide
  have hdescent : baseEnd_3172181 < baseStart_3172181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172201 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 3, 6, 2]
def baseStart_3172201 : Nat := 118140960795 + 3172201 * 2 ^ 59
def prefixEnd_3172201 : Nat := 4983230072969 + 3 ^ 40 * 3172201 * 2
def baseEnd_3172201 : Nat := 1628863845673248482698819

theorem tailTrace_3172201 : CollatzResearch.WordTrace tailWord_3172201 prefixEnd_3172201 1628863845673248482698819 := by
  unfold tailWord_3172201
  simp only [CollatzResearch.WordTrace]
  refine ⟨115699675580665020643492457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77133117053776680428994971 115699675580665020643492457)
  ·
    refine ⟨86774756685498765482619343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115699675580665020643492457 86774756685498765482619343)
    ·
      refine ⟨130162135028248148223929015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86774756685498765482619343 130162135028248148223929015)
      ·
        refine ⟨195243202542372222335893523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130162135028248148223929015 195243202542372222335893523)
        ·
          refine ⟨292864803813558333503840285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195243202542372222335893523 292864803813558333503840285)
          ·
            refine ⟨109824301430084375063940107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292864803813558333503840285 109824301430084375063940107)
            ·
              refine ⟨164736452145126562595910161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109824301430084375063940107 164736452145126562595910161)
              ·
                refine ⟨123552339108844921946932621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164736452145126562595910161 123552339108844921946932621)
                ·
                  refine ⟨46332127165816845730099733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123552339108844921946932621 46332127165816845730099733)
                  ·
                    refine ⟨2171818460897664643598425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46332127165816845730099733 2171818460897664643598425)
                    ·
                      refine ⟨1628863845673248482698819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171818460897664643598425 1628863845673248482698819)
                      ·
                        rfl

theorem cell23_3172201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 6, 2].length) (baseStart_3172201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172201 prefixEnd_3172201 := by exact prefixLift 3172201
  have htrace : WordTrace (prefixWord ++ tailWord_3172201) baseStart_3172201 baseEnd_3172201 := by
    simpa [prefixWord, tailWord_3172201, baseEnd_3172201] using wordTrace_append hprefix tailTrace_3172201
  have hstable : (prefixWord ++ tailWord_3172201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172201).length < 2 ^ (prefixWord ++ tailWord_3172201).sum := by decide
  have hdescent : baseEnd_3172201 < baseStart_3172201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172211 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 3, 4]
def baseStart_3172211 : Nat := 118140960795 + 3172211 * 2 ^ 59
def prefixEnd_3172211 : Nat := 4983230072969 + 3 ^ 40 * 3172211 * 2
def baseEnd_3172211 : Nat := 542956326826597814524591

theorem tailTrace_3172211 : CollatzResearch.WordTrace tailWord_3172211 prefixEnd_3172211 542956326826597814524591 := by
  unfold tailWord_3172211
  simp only [CollatzResearch.WordTrace]
  refine ⟨115700040310628792351356487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77133360207085861567570991 115700040310628792351356487)
  ·
    refine ⟨173550060465943188527034731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115700040310628792351356487 173550060465943188527034731)
    ·
      refine ⟨260325090698914782790552097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173550060465943188527034731 260325090698914782790552097)
      ·
        refine ⟨195243818024186087092914073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260325090698914782790552097 195243818024186087092914073)
        ·
          refine ⟨146432863518139565319685555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195243818024186087092914073 146432863518139565319685555)
          ·
            refine ⟨219649295277209347979528333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146432863518139565319685555 219649295277209347979528333)
            ·
              refine ⟨82368485728953505492323125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219649295277209347979528333 82368485728953505492323125)
              ·
                refine ⟨7722045537089391139905293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82368485728953505492323125 7722045537089391139905293)
                ·
                  refine ⟨2895767076408521677464485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7722045537089391139905293 2895767076408521677464485)
                  ·
                    refine ⟨542956326826597814524591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895767076408521677464485 542956326826597814524591)
                    ·
                      rfl

theorem cell23_3172211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 4].length) (baseStart_3172211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172211 prefixEnd_3172211 := by exact prefixLift 3172211
  have htrace : WordTrace (prefixWord ++ tailWord_3172211) baseStart_3172211 baseEnd_3172211 := by
    simpa [prefixWord, tailWord_3172211, baseEnd_3172211] using wordTrace_append hprefix tailTrace_3172211
  have hstable : (prefixWord ++ tailWord_3172211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172211).length < 2 ^ (prefixWord ++ tailWord_3172211).sum := by decide
  have hdescent : baseEnd_3172211 < baseStart_3172211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172221 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_3172221 : Nat := 118140960795 + 3172221 * 2 ^ 59
def prefixEnd_3172221 : Nat := 4983230072969 + 3 ^ 40 * 3172221 * 2
def baseEnd_3172221 : Nat := 1628874115286338404448727

theorem tailTrace_3172221 : CollatzResearch.WordTrace tailWord_3172221 prefixEnd_3172221 1628874115286338404448727 := by
  unfold tailWord_3172221
  simp only [CollatzResearch.WordTrace]
  refine ⟨115700405040592564059220517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77133603360395042706147011 115700405040592564059220517)
  ·
    refine ⟨21693825945111105761103847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115700405040592564059220517 21693825945111105761103847)
    ·
      refine ⟨32540738917666658641655771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21693825945111105761103847 32540738917666658641655771)
      ·
        refine ⟨48811108376499987962483657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32540738917666658641655771 48811108376499987962483657)
        ·
          refine ⟨36608331282374990971862743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48811108376499987962483657 36608331282374990971862743)
          ·
            refine ⟨54912496923562486457794115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36608331282374990971862743 54912496923562486457794115)
            ·
              refine ⟨82368745385343729686691173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54912496923562486457794115 82368745385343729686691173)
              ·
                refine ⟨15444139759751949316254595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82368745385343729686691173 15444139759751949316254595)
                ·
                  refine ⟨23166209639627923974381893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15444139759751949316254595 23166209639627923974381893)
                  ·
                    refine ⟨4343664307430235745196605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23166209639627923974381893 4343664307430235745196605)
                    ·
                      refine ⟨1628874115286338404448727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4343664307430235745196605 1628874115286338404448727)
                      ·
                        rfl

theorem cell23_3172221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_3172221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172221 prefixEnd_3172221 := by exact prefixLift 3172221
  have htrace : WordTrace (prefixWord ++ tailWord_3172221) baseStart_3172221 baseEnd_3172221 := by
    simpa [prefixWord, tailWord_3172221, baseEnd_3172221] using wordTrace_append hprefix tailTrace_3172221
  have hstable : (prefixWord ++ tailWord_3172221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172221).length < 2 ^ (prefixWord ++ tailWord_3172221).sum := by decide
  have hdescent : baseEnd_3172221 < baseStart_3172221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172245 : List Nat := [1, 3, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_3172245 : Nat := 118140960795 + 3172245 * 2 ^ 59
def prefixEnd_3172245 : Nat := 4983230072969 + 3 ^ 40 * 3172245 * 2
def baseEnd_3172245 : Nat := 542962146274015436849539

theorem tailTrace_3172245 : CollatzResearch.WordTrace tailWord_3172245 prefixEnd_3172245 542962146274015436849539 := by
  unfold tailWord_3172245
  simp only [CollatzResearch.WordTrace]
  refine ⟨115701280392505616158094189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77134186928337077438729459 115701280392505616158094189)
  ·
    refine ⟨43387980147189606059285321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115701280392505616158094189 43387980147189606059285321)
    ·
      refine ⟨32540985110392204544463991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43387980147189606059285321 32540985110392204544463991)
      ·
        refine ⟨48811477665588306816695987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32540985110392204544463991 48811477665588306816695987)
        ·
          refine ⟨73217216498382460225043981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48811477665588306816695987 73217216498382460225043981)
          ·
            refine ⟨27456456186893422584391493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73217216498382460225043981 27456456186893422584391493)
            ·
              refine ⟨5148085535042516734573405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27456456186893422584391493 5148085535042516734573405)
              ·
                refine ⟨1930532075640943775465027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5148085535042516734573405 1930532075640943775465027)
                ·
                  refine ⟨2895798113461415663197541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930532075640943775465027 2895798113461415663197541)
                  ·
                    refine ⟨542962146274015436849539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2895798113461415663197541 542962146274015436849539)
                    ·
                      rfl

theorem cell23_3172245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_3172245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172245 prefixEnd_3172245 := by exact prefixLift 3172245
  have htrace : WordTrace (prefixWord ++ tailWord_3172245) baseStart_3172245 baseEnd_3172245 := by
    simpa [prefixWord, tailWord_3172245, baseEnd_3172245] using wordTrace_append hprefix tailTrace_3172245
  have hstable : (prefixWord ++ tailWord_3172245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172245).length < 2 ^ (prefixWord ++ tailWord_3172245).sum := by decide
  have hdescent : baseEnd_3172245 < baseStart_3172245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172258 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3172258 : Nat := 118140960795 + 3172258 * 2 ^ 59
def prefixEnd_3172258 : Nat := 4983230072969 + 3 ^ 40 * 3172258 * 2
def baseEnd_3172258 : Nat := 180988123785617195520673

theorem tailTrace_3172258 : CollatzResearch.WordTrace tailWord_3172258 prefixEnd_3172258 180988123785617195520673 := by
  unfold tailWord_3172258
  simp only [CollatzResearch.WordTrace]
  refine ⟨28925438635364629844579357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77134503027639012918878285 28925438635364629844579357)
  ·
    refine ⟨10847039488261736191717259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28925438635364629844579357 10847039488261736191717259)
    ·
      refine ⟨16270559232392604287575889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10847039488261736191717259 16270559232392604287575889)
      ·
        refine ⟨12202919424294453215681917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16270559232392604287575889 12202919424294453215681917)
        ·
          refine ⟨4576094784110419955880719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12202919424294453215681917 4576094784110419955880719)
          ·
            refine ⟨6864142176165629933821079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576094784110419955880719 6864142176165629933821079)
            ·
              refine ⟨10296213264248444900731619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864142176165629933821079 10296213264248444900731619)
              ·
                refine ⟨15444319896372667351097429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10296213264248444900731619 15444319896372667351097429)
                ·
                  refine ⟨180988123785617195520673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15444319896372667351097429 180988123785617195520673)
                  ·
                    rfl

theorem cell23_3172258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3172258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172258 prefixEnd_3172258 := by exact prefixLift 3172258
  have htrace : WordTrace (prefixWord ++ tailWord_3172258) baseStart_3172258 baseEnd_3172258 := by
    simpa [prefixWord, tailWord_3172258, baseEnd_3172258] using wordTrace_append hprefix tailTrace_3172258
  have hstable : (prefixWord ++ tailWord_3172258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172258).length < 2 ^ (prefixWord ++ tailWord_3172258).sum := by decide
  have hdescent : baseEnd_3172258 < baseStart_3172258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172285 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_3172285 : Nat := 118140960795 + 3172285 * 2 ^ 59
def prefixEnd_3172285 : Nat := 4983230072969 + 3 ^ 40 * 3172285 * 2
def baseEnd_3172285 : Nat := 1628906978048226154048433

theorem tailTrace_3172285 : CollatzResearch.WordTrace tailWord_3172285 prefixEnd_3172285 1628906978048226154048433 := by
  unfold tailWord_3172285
  simp only [CollatzResearch.WordTrace]
  refine ⟨115702739312360702989550309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77135159541573801993033539 115702739312360702989550309)
  ·
    refine ⟨21694263621067631810540683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115702739312360702989550309 21694263621067631810540683)
    ·
      refine ⟨32541395431601447715811025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21694263621067631810540683 32541395431601447715811025)
      ·
        refine ⟨24406046573701085786858269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32541395431601447715811025 24406046573701085786858269)
        ·
          refine ⟨9152267465137907170071851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24406046573701085786858269 9152267465137907170071851)
          ·
            refine ⟨13728401197706860755107777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9152267465137907170071851 13728401197706860755107777)
            ·
              refine ⟨10296300898280145566330833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13728401197706860755107777 10296300898280145566330833)
              ·
                refine ⟨7722225673710109174748125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10296300898280145566330833 7722225673710109174748125)
                ·
                  refine ⟨2895834627641290940530547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7722225673710109174748125 2895834627641290940530547)
                  ·
                    refine ⟨4343751941461936410795821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2895834627641290940530547 4343751941461936410795821)
                    ·
                      refine ⟨1628906978048226154048433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4343751941461936410795821 1628906978048226154048433)
                      ·
                        rfl

theorem cell23_3172285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_3172285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172285 prefixEnd_3172285 := by exact prefixLift 3172285
  have htrace : WordTrace (prefixWord ++ tailWord_3172285) baseStart_3172285 baseEnd_3172285 := by
    simpa [prefixWord, tailWord_3172285, baseEnd_3172285] using wordTrace_append hprefix tailTrace_3172285
  have hstable : (prefixWord ++ tailWord_3172285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172285).length < 2 ^ (prefixWord ++ tailWord_3172285).sum := by decide
  have hdescent : baseEnd_3172285 < baseStart_3172285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172288 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 1, 5]
def baseStart_3172288 : Nat := 118140960795 + 3172288 * 2 ^ 59
def prefixEnd_3172288 : Nat := 4983230072969 + 3 ^ 40 * 3172288 * 2
def baseEnd_3172288 : Nat := 542969506163396547436973

theorem tailTrace_3172288 : CollatzResearch.WordTrace tailWord_3172288 prefixEnd_3172288 542969506163396547436973 := by
  unfold tailWord_3172288
  simp only [CollatzResearch.WordTrace]
  refine ⟨57851424365674917250954759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77135232487566556334606345 57851424365674917250954759)
  ·
    refine ⟨86777136548512375876432139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57851424365674917250954759 86777136548512375876432139)
    ·
      refine ⟨130165704822768563814648209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86777136548512375876432139 130165704822768563814648209)
      ·
        refine ⟨97624278617076422860986157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130165704822768563814648209 97624278617076422860986157)
        ·
          refine ⟨36609104481403658572869809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97624278617076422860986157 36609104481403658572869809)
          ·
            refine ⟨27456828361052743929652357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36609104481403658572869809 27456828361052743929652357)
            ·
              refine ⟨5148155317697389486809817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27456828361052743929652357 5148155317697389486809817)
              ·
                refine ⟨3861116488273042115107363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5148155317697389486809817 3861116488273042115107363)
                ·
                  refine ⟨5791674732409563172661045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861116488273042115107363 5791674732409563172661045)
                  ·
                    refine ⟨542969506163396547436973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5791674732409563172661045 542969506163396547436973)
                    ·
                      rfl

theorem cell23_3172288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_3172288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172288 prefixEnd_3172288 := by exact prefixLift 3172288
  have htrace : WordTrace (prefixWord ++ tailWord_3172288) baseStart_3172288 baseEnd_3172288 := by
    simpa [prefixWord, tailWord_3172288, baseEnd_3172288] using wordTrace_append hprefix tailTrace_3172288
  have hstable : (prefixWord ++ tailWord_3172288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172288).length < 2 ^ (prefixWord ++ tailWord_3172288).sum := by decide
  have hdescent : baseEnd_3172288 < baseStart_3172288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172319 : List Nat := [1, 1, 2, 3, 4, 2, 3, 2, 1, 1, 3]
def baseStart_3172319 : Nat := 118140960795 + 3172319 * 2 ^ 59
def prefixEnd_3172319 : Nat := 4983230072969 + 3 ^ 40 * 3172319 * 2
def baseEnd_3172319 : Nat := 1628924436390479021023277

theorem tailTrace_3172319 : CollatzResearch.WordTrace tailWord_3172319 prefixEnd_3172319 1628924436390479021023277 := by
  unfold tailWord_3172319
  simp only [CollatzResearch.WordTrace]
  refine ⟨115703979394237526796288011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77135986262825017864192007 115703979394237526796288011)
  ·
    refine ⟨173555969091356290194432017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115703979394237526796288011 173555969091356290194432017)
    ·
      refine ⟨130166976818517217645824013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173555969091356290194432017 130166976818517217645824013)
      ·
        refine ⟨48812616306943956617184005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130166976818517217645824013 48812616306943956617184005)
        ·
          refine ⟨9152365557551991865722001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48812616306943956617184005 9152365557551991865722001)
          ·
            refine ⟨6864274168163993899291501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9152365557551991865722001 6864274168163993899291501)
            ·
              refine ⟨2574102813061497712234313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6864274168163993899291501 2574102813061497712234313)
              ·
                refine ⟨1930577109796123284175735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574102813061497712234313 1930577109796123284175735)
                ·
                  refine ⟨2895865664694184926263603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930577109796123284175735 2895865664694184926263603)
                  ·
                    refine ⟨4343798497041277389395405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2895865664694184926263603 4343798497041277389395405)
                    ·
                      refine ⟨1628924436390479021023277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4343798497041277389395405 1628924436390479021023277)
                      ·
                        rfl

theorem cell23_3172319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_3172319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172319 prefixEnd_3172319 := by exact prefixLift 3172319
  have htrace : WordTrace (prefixWord ++ tailWord_3172319) baseStart_3172319 baseEnd_3172319 := by
    simpa [prefixWord, tailWord_3172319, baseEnd_3172319] using wordTrace_append hprefix tailTrace_3172319
  have hstable : (prefixWord ++ tailWord_3172319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172319).length < 2 ^ (prefixWord ++ tailWord_3172319).sum := by decide
  have hdescent : baseEnd_3172319 < baseStart_3172319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172321 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_3172321 : Nat := 118140960795 + 3172321 * 2 ^ 59
def prefixEnd_3172321 : Nat := 4983230072969 + 3 ^ 40 * 3172321 * 2
def baseEnd_3172321 : Nat := 1628925463351788013198267

theorem tailTrace_3172321 : CollatzResearch.WordTrace tailWord_3172321 prefixEnd_3172321 1628925463351788013198267 := by
  unfold tailWord_3172321
  simp only [CollatzResearch.WordTrace]
  refine ⟨115704052340230281137860817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77136034893486854091907211 115704052340230281137860817)
  ·
    refine ⟨86778039255172710853395613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115704052340230281137860817 86778039255172710853395613)
    ·
      refine ⟨32541764720689766570023355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86778039255172710853395613 32541764720689766570023355)
      ·
        refine ⟨48812647081034649855035033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32541764720689766570023355 48812647081034649855035033)
        ·
          refine ⟨36609485310775987391276275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48812647081034649855035033 36609485310775987391276275)
          ·
            refine ⟨54914227966163981086914413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36609485310775987391276275 54914227966163981086914413)
            ·
              refine ⟨20592835487311492907592905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54914227966163981086914413 20592835487311492907592905)
              ·
                refine ⟨15444626615483619680694679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20592835487311492907592905 15444626615483619680694679)
                ·
                  refine ⟨23166939923225429521042019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15444626615483619680694679 23166939923225429521042019)
                  ·
                    refine ⟨34750409884838144281563029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23166939923225429521042019 34750409884838144281563029)
                    ·
                      refine ⟨1628925463351788013198267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34750409884838144281563029 1628925463351788013198267)
                      ·
                        rfl

theorem cell23_3172321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_3172321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172321 prefixEnd_3172321 := by exact prefixLift 3172321
  have htrace : WordTrace (prefixWord ++ tailWord_3172321) baseStart_3172321 baseEnd_3172321 := by
    simpa [prefixWord, tailWord_3172321, baseEnd_3172321] using wordTrace_append hprefix tailTrace_3172321
  have hstable : (prefixWord ++ tailWord_3172321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172321).length < 2 ^ (prefixWord ++ tailWord_3172321).sum := by decide
  have hdescent : baseEnd_3172321 < baseStart_3172321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172328 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3172328 : Nat := 118140960795 + 3172328 * 2 ^ 59
def prefixEnd_3172328 : Nat := 4983230072969 + 3 ^ 40 * 3172328 * 2
def baseEnd_3172328 : Nat := 1628929057716369485810735

theorem tailTrace_3172328 : CollatzResearch.WordTrace tailWord_3172328 prefixEnd_3172328 1628929057716369485810735 := by
  unfold tailWord_3172328
  simp only [CollatzResearch.WordTrace]
  refine ⟨57852153825602460666682819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77136205100803280888910425 57852153825602460666682819)
  ·
    refine ⟨86778230738403691000024229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57852153825602460666682819 86778230738403691000024229)
    ·
      refine ⟨16270918263450692062504543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86778230738403691000024229 16270918263450692062504543)
      ·
        refine ⟨24406377395176038093756815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16270918263450692062504543 24406377395176038093756815)
        ·
          refine ⟨36609566092764057140635223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24406377395176038093756815 36609566092764057140635223)
          ·
            refine ⟨54914349139146085710952835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36609566092764057140635223 54914349139146085710952835)
            ·
              refine ⟨82371523708719128566429253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54914349139146085710952835 82371523708719128566429253)
              ·
                refine ⟨15444660695384836606205485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82371523708719128566429253 15444660695384836606205485)
                ·
                  refine ⟨5791747760769313727327057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15444660695384836606205485 5791747760769313727327057)
                  ·
                    refine ⟨4343810820576985295495293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791747760769313727327057 4343810820576985295495293)
                    ·
                      refine ⟨1628929057716369485810735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4343810820576985295495293 1628929057716369485810735)
                      ·
                        rfl

theorem cell23_3172328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3172328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172328 prefixEnd_3172328 := by exact prefixLift 3172328
  have htrace : WordTrace (prefixWord ++ tailWord_3172328) baseStart_3172328 baseEnd_3172328 := by
    simpa [prefixWord, tailWord_3172328, baseEnd_3172328] using wordTrace_append hprefix tailTrace_3172328
  have hstable : (prefixWord ++ tailWord_3172328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172328).length < 2 ^ (prefixWord ++ tailWord_3172328).sum := by decide
  have hdescent : baseEnd_3172328 < baseStart_3172328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172345 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 3]
def baseStart_3172345 : Nat := 118140960795 + 3172345 * 2 ^ 59
def prefixEnd_3172345 : Nat := 4983230072969 + 3 ^ 40 * 3172345 * 2
def baseEnd_3172345 : Nat := 1628937786887495919298157

theorem tailTrace_3172345 : CollatzResearch.WordTrace tailWord_3172345 prefixEnd_3172345 1628937786887495919298157 := by
  unfold tailWord_3172345
  simp only [CollatzResearch.WordTrace]
  refine ⟨115704927692143333236734489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77136618461428888824489659 115704927692143333236734489)
  ·
    refine ⟨86778695769107499927550867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115704927692143333236734489 86778695769107499927550867)
    ·
      refine ⟨130168043653661249891326301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86778695769107499927550867 130168043653661249891326301)
      ·
        refine ⟨48813016370122968709247363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130168043653661249891326301 48813016370122968709247363)
        ·
          refine ⟨73219524555184453063871045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48813016370122968709247363 73219524555184453063871045)
          ·
            refine ⟨13728660854097084949475821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73219524555184453063871045 13728660854097084949475821)
            ·
              refine ⟨5148247820286406856053433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13728660854097084949475821 5148247820286406856053433)
              ·
                refine ⟨3861185865214805142040075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5148247820286406856053433 3861185865214805142040075)
                ·
                  refine ⟨5791778797822207713060113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861185865214805142040075 5791778797822207713060113)
                  ·
                    refine ⟨4343834098366655784795085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5791778797822207713060113 4343834098366655784795085)
                    ·
                      refine ⟨1628937786887495919298157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4343834098366655784795085 1628937786887495919298157)
                      ·
                        rfl

theorem cell23_3172345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_3172345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172345 prefixEnd_3172345 := by exact prefixLift 3172345
  have htrace : WordTrace (prefixWord ++ tailWord_3172345) baseStart_3172345 baseEnd_3172345 := by
    simpa [prefixWord, tailWord_3172345, baseEnd_3172345] using wordTrace_append hprefix tailTrace_3172345
  have hstable : (prefixWord ++ tailWord_3172345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172345).length < 2 ^ (prefixWord ++ tailWord_3172345).sum := by decide
  have hdescent : baseEnd_3172345 < baseStart_3172345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172362 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5]
def baseStart_3172362 : Nat := 118140960795 + 3172362 * 2 ^ 59
def prefixEnd_3172362 : Nat := 4983230072969 + 3 ^ 40 * 3172362 * 2
def baseEnd_3172362 : Nat := 1628946516058622352785579

theorem tailTrace_3172362 : CollatzResearch.WordTrace tailWord_3172362 prefixEnd_3172362 1628946516058622352785579 := by
  unfold tailWord_3172362
  simp only [CollatzResearch.WordTrace]
  refine ⟨28926386933270436285025835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77137031822054496760068893 28926386933270436285025835)
  ·
    refine ⟨43389580399905654427538753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28926386933270436285025835 43389580399905654427538753)
    ·
      refine ⟨32542185299929240820654065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43389580399905654427538753 32542185299929240820654065)
      ·
        refine ⟨24406638974946930615490549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32542185299929240820654065 24406638974946930615490549)
        ·
          refine ⟨2288122403901274745202239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24406638974946930615490549 2288122403901274745202239)
          ·
            refine ⟨3432183605851912117803359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288122403901274745202239 3432183605851912117803359)
            ·
              refine ⟨5148275408777868176705039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432183605851912117803359 5148275408777868176705039)
              ·
                refine ⟨7722413113166802265057559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5148275408777868176705039 7722413113166802265057559)
                ·
                  refine ⟨11583619669750203397586339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7722413113166802265057559 11583619669750203397586339)
                  ·
                    refine ⟨17375429504625305096379509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11583619669750203397586339 17375429504625305096379509)
                    ·
                      refine ⟨1628946516058622352785579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17375429504625305096379509 1628946516058622352785579)
                      ·
                        rfl

theorem cell23_3172362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_3172362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172362 prefixEnd_3172362 := by exact prefixLift 3172362
  have htrace : WordTrace (prefixWord ++ tailWord_3172362) baseStart_3172362 baseEnd_3172362 := by
    simpa [prefixWord, tailWord_3172362, baseEnd_3172362] using wordTrace_append hprefix tailTrace_3172362
  have hstable : (prefixWord ++ tailWord_3172362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172362).length < 2 ^ (prefixWord ++ tailWord_3172362).sum := by decide
  have hdescent : baseEnd_3172362 < baseStart_3172362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172365 : List Nat := [1, 7, 1, 2, 12]
def baseStart_3172365 : Nat := 118140960795 + 3172365 * 2 ^ 59
def prefixEnd_3172365 : Nat := 4983230072969 + 3 ^ 40 * 3172365 * 2
def baseEnd_3172365 : Nat := 2234496648148951770985

theorem tailTrace_3172365 : CollatzResearch.WordTrace tailWord_3172365 prefixEnd_3172365 2234496648148951770985 := by
  unfold tailWord_3172365
  simp only [CollatzResearch.WordTrace]
  refine ⟨115705657152070876652462549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77137104768047251101641699 115705657152070876652462549)
  ·
    refine ⟨2711851339501661171542091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 115705657152070876652462549 2711851339501661171542091)
    ·
      refine ⟨4067777009252491757313137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2711851339501661171542091 4067777009252491757313137)
      ·
        refine ⟨3050832756939368817984853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4067777009252491757313137 3050832756939368817984853)
        ·
          refine ⟨2234496648148951770985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3050832756939368817984853 2234496648148951770985)
          ·
            rfl

theorem cell23_3172365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 12].length) (baseStart_3172365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172365 prefixEnd_3172365 := by exact prefixLift 3172365
  have htrace : WordTrace (prefixWord ++ tailWord_3172365) baseStart_3172365 baseEnd_3172365 := by
    simpa [prefixWord, tailWord_3172365, baseEnd_3172365] using wordTrace_append hprefix tailTrace_3172365
  have hstable : (prefixWord ++ tailWord_3172365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172365).length < 2 ^ (prefixWord ++ tailWord_3172365).sum := by decide
  have hdescent : baseEnd_3172365 < baseStart_3172365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172371 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5]
def baseStart_3172371 : Nat := 118140960795 + 3172371 * 2 ^ 59
def prefixEnd_3172371 : Nat := 4983230072969 + 3 ^ 40 * 3172371 * 2
def baseEnd_3172371 : Nat := 1628951137384512817573037

theorem tailTrace_3172371 : CollatzResearch.WordTrace tailWord_3172371 prefixEnd_3172371 1628951137384512817573037 := by
  unfold tailWord_3172371
  simp only [CollatzResearch.WordTrace]
  refine ⟨115705875990049139677180967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77137250660032759784787311 115705875990049139677180967)
  ·
    refine ⟨173558813985073709515771451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115705875990049139677180967 173558813985073709515771451)
    ·
      refine ⟨260338220977610564273657177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173558813985073709515771451 260338220977610564273657177)
      ·
        refine ⟨195253665733207923205242883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260338220977610564273657177 195253665733207923205242883)
        ·
          refine ⟨292880498599811884807864325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195253665733207923205242883 292880498599811884807864325)
          ·
            refine ⟨54915093487464728401474561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 292880498599811884807864325 54915093487464728401474561)
            ·
              refine ⟨41186320115598546301105921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54915093487464728401474561 41186320115598546301105921)
              ·
                refine ⟨30889740086698909725829441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41186320115598546301105921 30889740086698909725829441)
                ·
                  refine ⟨23167305065024182294372081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30889740086698909725829441 23167305065024182294372081)
                  ·
                    refine ⟨17375478798768136720779061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23167305065024182294372081 17375478798768136720779061)
                    ·
                      refine ⟨1628951137384512817573037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17375478798768136720779061 1628951137384512817573037)
                      ·
                        rfl

theorem cell23_3172371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_3172371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172371 prefixEnd_3172371 := by exact prefixLift 3172371
  have htrace : WordTrace (prefixWord ++ tailWord_3172371) baseStart_3172371 baseEnd_3172371 := by
    simpa [prefixWord, tailWord_3172371, baseEnd_3172371] using wordTrace_append hprefix tailTrace_3172371
  have hstable : (prefixWord ++ tailWord_3172371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172371).length < 2 ^ (prefixWord ++ tailWord_3172371).sum := by decide
  have hdescent : baseEnd_3172371 < baseStart_3172371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172415 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 1, 4, 2]
def baseStart_3172415 : Nat := 118140960795 + 3172415 * 2 ^ 59
def prefixEnd_3172415 : Nat := 4983230072969 + 3 ^ 40 * 3172415 * 2
def baseEnd_3172415 : Nat := 1628973730533310645422835

theorem tailTrace_3172415 : CollatzResearch.WordTrace tailWord_3172415 prefixEnd_3172415 1628973730533310645422835 := by
  unfold tailWord_3172415
  simp only [CollatzResearch.WordTrace]
  refine ⟨115707480801889735191782699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77138320534593156794521799 115707480801889735191782699)
  ·
    refine ⟨173561221202834602787674049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115707480801889735191782699 173561221202834602787674049)
    ·
      refine ⟨130170915902125952090755537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173561221202834602787674049 130170915902125952090755537)
      ·
        refine ⟨97628186926594464068066653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130170915902125952090755537 97628186926594464068066653)
        ·
          refine ⟨36610570097472924025524995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97628186926594464068066653 36610570097472924025524995)
          ·
            refine ⟨54915855146209386038287493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36610570097472924025524995 54915855146209386038287493)
            ·
              refine ⟨10296722839914259882178905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54915855146209386038287493 10296722839914259882178905)
              ·
                refine ⟨7722542129935694911634179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10296722839914259882178905 7722542129935694911634179)
                ·
                  refine ⟨11583813194903542367451269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7722542129935694911634179 11583813194903542367451269)
                  ·
                    refine ⟨2171964974044414193897113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11583813194903542367451269 2171964974044414193897113)
                    ·
                      refine ⟨1628973730533310645422835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2171964974044414193897113 1628973730533310645422835)
                      ·
                        rfl

theorem cell23_3172415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_3172415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172415 prefixEnd_3172415 := by exact prefixLift 3172415
  have htrace : WordTrace (prefixWord ++ tailWord_3172415) baseStart_3172415 baseEnd_3172415 := by
    simpa [prefixWord, tailWord_3172415, baseEnd_3172415] using wordTrace_append hprefix tailTrace_3172415
  have hstable : (prefixWord ++ tailWord_3172415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172415).length < 2 ^ (prefixWord ++ tailWord_3172415).sum := by decide
  have hdescent : baseEnd_3172415 < baseStart_3172415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172421 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 11]
def baseStart_3172421 : Nat := 118140960795 + 3172421 * 2 ^ 59
def prefixEnd_3172421 : Nat := 4983230072969 + 3 ^ 40 * 3172421 * 2
def baseEnd_3172421 : Nat := 180997423490804180216423

theorem tailTrace_3172421 : CollatzResearch.WordTrace tailWord_3172421 prefixEnd_3172421 180997423490804180216423 := by
  unfold tailWord_3172421
  simp only [CollatzResearch.WordTrace]
  refine ⟨115707699639867998216501117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77138466426578665477667411 115707699639867998216501117)
  ·
    refine ⟨43390387364950499331187919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115707699639867998216501117 43390387364950499331187919)
    ·
      refine ⟨65085581047425748996781879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43390387364950499331187919 65085581047425748996781879)
      ·
        refine ⟨97628371571138623495172819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65085581047425748996781879 97628371571138623495172819)
        ·
          refine ⟨146442557356707935242759229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97628371571138623495172819 146442557356707935242759229)
          ·
            refine ⟨54915959008765475716034711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146442557356707935242759229 54915959008765475716034711)
            ·
              refine ⟨82373938513148213574052067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54915959008765475716034711 82373938513148213574052067)
              ·
                refine ⟨123560907769722320361078101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82373938513148213574052067 123560907769722320361078101)
                ·
                  refine ⟨180997423490804180216423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 123560907769722320361078101 180997423490804180216423)
                  ·
                    rfl

theorem cell23_3172421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_3172421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172421 prefixEnd_3172421 := by exact prefixLift 3172421
  have htrace : WordTrace (prefixWord ++ tailWord_3172421) baseStart_3172421 baseEnd_3172421 := by
    simpa [prefixWord, tailWord_3172421, baseEnd_3172421] using wordTrace_append hprefix tailTrace_3172421
  have hstable : (prefixWord ++ tailWord_3172421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172421).length < 2 ^ (prefixWord ++ tailWord_3172421).sum := by decide
  have hdescent : baseEnd_3172421 < baseStart_3172421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172428 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3172428 : Nat := 118140960795 + 3172428 * 2 ^ 59
def prefixEnd_3172428 : Nat := 4983230072969 + 3 ^ 40 * 3172428 * 2
def baseEnd_3172428 : Nat := 1628980405781819094560275

theorem tailTrace_3172428 : CollatzResearch.WordTrace tailWord_3172428 prefixEnd_3172428 1628980405781819094560275 := by
  unfold tailWord_3172428
  simp only [CollatzResearch.WordTrace]
  refine ⟨57853977475421319206002969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77138636633895092274670625 57853977475421319206002969)
  ·
    refine ⟨43390483106565989404502227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57853977475421319206002969 43390483106565989404502227)
    ·
      refine ⟨65085724659848984106753341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43390483106565989404502227 65085724659848984106753341)
      ·
        refine ⟨24407146747443369040032503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65085724659848984106753341 24407146747443369040032503)
        ·
          refine ⟨36610720121165053560048755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24407146747443369040032503 36610720121165053560048755)
          ·
            refine ⟨54916080181747580340073133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36610720121165053560048755 54916080181747580340073133)
            ·
              refine ⟨20593530068155342627527425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54916080181747580340073133 20593530068155342627527425)
              ·
                refine ⟨15445147551116506970645569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20593530068155342627527425 15445147551116506970645569)
                ·
                  refine ⟨11583860663337380227984177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15445147551116506970645569 11583860663337380227984177)
                  ·
                    refine ⟨8687895497503035170988133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11583860663337380227984177 8687895497503035170988133)
                    ·
                      refine ⟨1628980405781819094560275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8687895497503035170988133 1628980405781819094560275)
                      ·
                        rfl

theorem cell23_3172428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3172428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172428 prefixEnd_3172428 := by exact prefixLift 3172428
  have htrace : WordTrace (prefixWord ++ tailWord_3172428) baseStart_3172428 baseEnd_3172428 := by
    simpa [prefixWord, tailWord_3172428, baseEnd_3172428] using wordTrace_append hprefix tailTrace_3172428
  have hstable : (prefixWord ++ tailWord_3172428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172428).length < 2 ^ (prefixWord ++ tailWord_3172428).sum := by decide
  have hdescent : baseEnd_3172428 < baseStart_3172428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172431 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_3172431 : Nat := 118140960795 + 3172431 * 2 ^ 59
def prefixEnd_3172431 : Nat := 4983230072969 + 3 ^ 40 * 3172431 * 2
def baseEnd_3172431 : Nat := 1628981946223782582822761

theorem tailTrace_3172431 : CollatzResearch.WordTrace tailWord_3172431 prefixEnd_3172431 1628981946223782582822761 := by
  unfold tailWord_3172431
  simp only [CollatzResearch.WordTrace]
  refine ⟨115708064369831769924365147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77138709579887846616243431 115708064369831769924365147)
  ·
    refine ⟨173562096554747654886547721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115708064369831769924365147 173562096554747654886547721)
    ·
      refine ⟨130171572416060741164910791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173562096554747654886547721 130171572416060741164910791)
      ·
        refine ⟨195257358624091111747366187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130171572416060741164910791 195257358624091111747366187)
        ·
          refine ⟨292886037936136667621049281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195257358624091111747366187 292886037936136667621049281)
          ·
            refine ⟨219664528452102500715786961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292886037936136667621049281 219664528452102500715786961)
            ·
              refine ⟨164748396339076875536840221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219664528452102500715786961 164748396339076875536840221)
              ·
                refine ⟨61780648627153828326315083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164748396339076875536840221 61780648627153828326315083)
                ·
                  refine ⟨92670972940730742489472625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61780648627153828326315083 92670972940730742489472625)
                  ·
                    refine ⟨69503229705548056867104469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92670972940730742489472625 69503229705548056867104469)
                    ·
                      refine ⟨1628981946223782582822761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69503229705548056867104469 1628981946223782582822761)
                      ·
                        rfl

theorem cell23_3172431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_3172431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172431 prefixEnd_3172431 := by exact prefixLift 3172431
  have htrace : WordTrace (prefixWord ++ tailWord_3172431) baseStart_3172431 baseEnd_3172431 := by
    simpa [prefixWord, tailWord_3172431, baseEnd_3172431] using wordTrace_append hprefix tailTrace_3172431
  have hstable : (prefixWord ++ tailWord_3172431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172431).length < 2 ^ (prefixWord ++ tailWord_3172431).sum := by decide
  have hdescent : baseEnd_3172431 < baseStart_3172431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172485 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_3172485 : Nat := 118140960795 + 3172485 * 2 ^ 59
def prefixEnd_3172485 : Nat := 4983230072969 + 3 ^ 40 * 3172485 * 2
def baseEnd_3172485 : Nat := 543003224726375123849171

theorem tailTrace_3172485 : CollatzResearch.WordTrace tailWord_3172485 prefixEnd_3172485 543003224726375123849171 := by
  unfold tailWord_3172485
  simp only [CollatzResearch.WordTrace]
  refine ⟨115710033911636137146830909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77140022607757424764553939 115710033911636137146830909)
  ·
    refine ⟨43391262716863551430061591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115710033911636137146830909 43391262716863551430061591)
    ·
      refine ⟨65086894075295327145092387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43391262716863551430061591 65086894075295327145092387)
      ·
        refine ⟨97630341112942990717638581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65086894075295327145092387 97630341112942990717638581)
        ·
          refine ⟨9152844479338405379778617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97630341112942990717638581 9152844479338405379778617)
          ·
            refine ⟨6864633359503804034833963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9152844479338405379778617 6864633359503804034833963)
            ·
              refine ⟨10296950039255706052250945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864633359503804034833963 10296950039255706052250945)
              ·
                refine ⟨7722712529441779539188209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10296950039255706052250945 7722712529441779539188209)
                ·
                  refine ⟨5792034397081334654391157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7722712529441779539188209 5792034397081334654391157)
                  ·
                    refine ⟨543003224726375123849171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5792034397081334654391157 543003224726375123849171)
                    ·
                      rfl

theorem cell23_3172485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_3172485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172485 prefixEnd_3172485 := by exact prefixLift 3172485
  have htrace : WordTrace (prefixWord ++ tailWord_3172485) baseStart_3172485 baseEnd_3172485 := by
    simpa [prefixWord, tailWord_3172485, baseEnd_3172485] using wordTrace_append hprefix tailTrace_3172485
  have hstable : (prefixWord ++ tailWord_3172485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172485).length < 2 ^ (prefixWord ++ tailWord_3172485).sum := by decide
  have hdescent : baseEnd_3172485 < baseStart_3172485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172500 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3172500 : Nat := 118140960795 + 3172500 * 2 ^ 59
def prefixEnd_3172500 : Nat := 4983230072969 + 3 ^ 40 * 3172500 * 2
def baseEnd_3172500 : Nat := 1629017376388942812859945

theorem tailTrace_3172500 : CollatzResearch.WordTrace tailWord_3172500 prefixEnd_3172500 1629017376388942812859945 := by
  unfold tailWord_3172500
  simp only [CollatzResearch.WordTrace]
  refine ⟨57855290503290897354313477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77140387337721196472417969 57855290503290897354313477)
  ·
    refine ⟨10847866969367043253933777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57855290503290897354313477 10847866969367043253933777)
    ·
      refine ⟨8135900227025282440450333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10847866969367043253933777 8135900227025282440450333)
      ·
        refine ⟨3050962585134480915168875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8135900227025282440450333 3050962585134480915168875)
        ·
          refine ⟨4576443877701721372753313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050962585134480915168875 4576443877701721372753313)
          ·
            refine ⟨3432332908276291029564985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4576443877701721372753313 3432332908276291029564985)
            ·
              refine ⟨2574249681207218272173739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432332908276291029564985 2574249681207218272173739)
              ·
                refine ⟨3861374521810827408260609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574249681207218272173739 3861374521810827408260609)
                ·
                  refine ⟨2896030891358120556195457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861374521810827408260609 2896030891358120556195457)
                  ·
                    refine ⟨2172023168518590417146593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2896030891358120556195457 2172023168518590417146593)
                    ·
                      refine ⟨1629017376388942812859945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172023168518590417146593 1629017376388942812859945)
                      ·
                        rfl

theorem cell23_3172500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3172500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172500 prefixEnd_3172500 := by exact prefixLift 3172500
  have htrace : WordTrace (prefixWord ++ tailWord_3172500) baseStart_3172500 baseEnd_3172500 := by
    simpa [prefixWord, tailWord_3172500, baseEnd_3172500] using wordTrace_append hprefix tailTrace_3172500
  have hstable : (prefixWord ++ tailWord_3172500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172500).length < 2 ^ (prefixWord ++ tailWord_3172500).sum := by decide
  have hdescent : baseEnd_3172500 < baseStart_3172500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172505 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 2, 4, 2]
def baseStart_3172505 : Nat := 118140960795 + 3172505 * 2 ^ 59
def prefixEnd_3172505 : Nat := 4983230072969 + 3 ^ 40 * 3172505 * 2
def baseEnd_3172505 : Nat := 1629019943792215293297421

theorem tailTrace_3172505 : CollatzResearch.WordTrace tailWord_3172505 prefixEnd_3172505 1629019943792215293297421 := by
  unfold tailWord_3172505
  simp only [CollatzResearch.WordTrace]
  refine ⟨115710763371563680562558969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77140508914375787041705979 115710763371563680562558969)
  ·
    refine ⟨86783072528672760421919227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115710763371563680562558969 86783072528672760421919227)
    ·
      refine ⟨130174608793009140632878841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86783072528672760421919227 130174608793009140632878841)
      ·
        refine ⟨97630956594756855474659131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130174608793009140632878841 97630956594756855474659131)
        ·
          refine ⟨146446434892135283211988697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97630956594756855474659131 146446434892135283211988697)
          ·
            refine ⟨109834826169101462408991523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146446434892135283211988697 109834826169101462408991523)
            ·
              refine ⟨164752239253652193613487285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109834826169101462408991523 164752239253652193613487285)
              ·
                refine ⟨15445522430029893151264433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164752239253652193613487285 15445522430029893151264433)
                ·
                  refine ⟨11584141822522419863448325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15445522430029893151264433 11584141822522419863448325)
                  ·
                    refine ⟨2172026591722953724396561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11584141822522419863448325 2172026591722953724396561)
                    ·
                      refine ⟨1629019943792215293297421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172026591722953724396561 1629019943792215293297421)
                      ·
                        rfl

theorem cell23_3172505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_3172505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172505 prefixEnd_3172505 := by exact prefixLift 3172505
  have htrace : WordTrace (prefixWord ++ tailWord_3172505) baseStart_3172505 baseEnd_3172505 := by
    simpa [prefixWord, tailWord_3172505, baseEnd_3172505] using wordTrace_append hprefix tailTrace_3172505
  have hstable : (prefixWord ++ tailWord_3172505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172505).length < 2 ^ (prefixWord ++ tailWord_3172505).sum := by decide
  have hdescent : baseEnd_3172505 < baseStart_3172505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172549 : List Nat := [1, 3, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_3172549 : Nat := 118140960795 + 3172549 * 2 ^ 59
def prefixEnd_3172549 : Nat := 4983230072969 + 3 ^ 40 * 3172549 * 2
def baseEnd_3172549 : Nat := 543014178980337707049073

theorem tailTrace_3172549 : CollatzResearch.WordTrace tailWord_3172549 prefixEnd_3172549 543014178980337707049073 := by
  unfold tailWord_3172549
  simp only [CollatzResearch.WordTrace]
  refine ⟨115712368183404276077160701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77141578788936184051440467 115712368183404276077160701)
  ·
    refine ⟨43392138068776603528935263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115712368183404276077160701 43392138068776603528935263)
    ·
      refine ⟨65088207103164905293402895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43392138068776603528935263 65088207103164905293402895)
      ·
        refine ⟨97632310654747357940104343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65088207103164905293402895 97632310654747357940104343)
        ·
          refine ⟨146448465982121036910156515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97632310654747357940104343 146448465982121036910156515)
          ·
            refine ⟨219672698973181555365234773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146448465982121036910156515 219672698973181555365234773)
            ·
              refine ⟨2574289441091971351936345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 219672698973181555365234773 2574289441091971351936345)
              ·
                refine ⟨1930717080818978513952259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574289441091971351936345 1930717080818978513952259)
                ·
                  refine ⟨2896075621228467770928389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930717080818978513952259 2896075621228467770928389)
                  ·
                    refine ⟨543014178980337707049073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2896075621228467770928389 543014178980337707049073)
                    ·
                      rfl

theorem cell23_3172549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_3172549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172549 prefixEnd_3172549 := by exact prefixLift 3172549
  have htrace : WordTrace (prefixWord ++ tailWord_3172549) baseStart_3172549 baseEnd_3172549 := by
    simpa [prefixWord, tailWord_3172549, baseEnd_3172549] using wordTrace_append hprefix tailTrace_3172549
  have hstable : (prefixWord ++ tailWord_3172549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172549).length < 2 ^ (prefixWord ++ tailWord_3172549).sum := by decide
  have hdescent : baseEnd_3172549 < baseStart_3172549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172575 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 1, 5]
def baseStart_3172575 : Nat := 118140960795 + 3172575 * 2 ^ 59
def prefixEnd_3172575 : Nat := 4983230072969 + 3 ^ 40 * 3172575 * 2
def baseEnd_3172575 : Nat := 543018629146010006474033

theorem tailTrace_3172575 : CollatzResearch.WordTrace tailWord_3172575 prefixEnd_3172575 543018629146010006474033 := by
  unfold tailWord_3172575
  simp only [CollatzResearch.WordTrace]
  refine ⟨115713316481310082517607179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77142210987540055011738119 115713316481310082517607179)
  ·
    refine ⟨173569974721965123776410769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115713316481310082517607179 173569974721965123776410769)
    ·
      refine ⟨130177481041473842832308077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173569974721965123776410769 130177481041473842832308077)
      ·
        refine ⟨48816555390552691062115529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130177481041473842832308077 48816555390552691062115529)
        ·
          refine ⟨36612416542914518296586647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48816555390552691062115529 36612416542914518296586647)
          ·
            refine ⟨54918624814371777444879971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36612416542914518296586647 54918624814371777444879971)
            ·
              refine ⟨82377937221557666167319957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54918624814371777444879971 82377937221557666167319957)
              ·
                refine ⟨3861465807260515601593123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82377937221557666167319957 3861465807260515601593123)
                ·
                  refine ⟨5792198710890773402389685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861465807260515601593123 5792198710890773402389685)
                  ·
                    refine ⟨543018629146010006474033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5792198710890773402389685 543018629146010006474033)
                    ·
                      rfl

theorem cell23_3172575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_3172575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172575 prefixEnd_3172575 := by exact prefixLift 3172575
  have htrace : WordTrace (prefixWord ++ tailWord_3172575) baseStart_3172575 baseEnd_3172575 := by
    simpa [prefixWord, tailWord_3172575, baseEnd_3172575] using wordTrace_append hprefix tailTrace_3172575
  have hstable : (prefixWord ++ tailWord_3172575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172575).length < 2 ^ (prefixWord ++ tailWord_3172575).sum := by decide
  have hdescent : baseEnd_3172575 < baseStart_3172575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172606 : List Nat := [4, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_3172606 : Nat := 118140960795 + 3172606 * 2 ^ 59
def prefixEnd_3172606 : Nat := 4983230072969 + 3 ^ 40 * 3172606 * 2
def baseEnd_3172606 : Nat := 1629071805338319398134457

theorem tailTrace_3172606 : CollatzResearch.WordTrace tailWord_3172606 prefixEnd_3172606 1629071805338319398134457 := by
  unfold tailWord_3172606
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464305893024721851498209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77142964762798516541323781 14464305893024721851498209)
  ·
    refine ⟨10848229419768541388623657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14464305893024721851498209 10848229419768541388623657)
    ·
      refine ⟨8136172064826406041467743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10848229419768541388623657 8136172064826406041467743)
      ·
        refine ⟨12204258097239609062201615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8136172064826406041467743 12204258097239609062201615)
        ·
          refine ⟨18306387145859413593302423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12204258097239609062201615 18306387145859413593302423)
          ·
            refine ⟨27459580718789120389953635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18306387145859413593302423 27459580718789120389953635)
            ·
              refine ⟨41189371078183680584930453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27459580718789120389953635 41189371078183680584930453)
              ·
                refine ⟨1930751769289860027418615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41189371078183680584930453 1930751769289860027418615)
                ·
                  refine ⟨2896127653934790041127923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930751769289860027418615 2896127653934790041127923)
                  ·
                    refine ⟨4344191480902185061691885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2896127653934790041127923 4344191480902185061691885)
                    ·
                      refine ⟨1629071805338319398134457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4344191480902185061691885 1629071805338319398134457)
                      ·
                        rfl

theorem cell23_3172606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_3172606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172606 prefixEnd_3172606 := by exact prefixLift 3172606
  have htrace : WordTrace (prefixWord ++ tailWord_3172606) baseStart_3172606 baseEnd_3172606 := by
    simpa [prefixWord, tailWord_3172606, baseEnd_3172606] using wordTrace_append hprefix tailTrace_3172606
  have hstable : (prefixWord ++ tailWord_3172606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172606).length < 2 ^ (prefixWord ++ tailWord_3172606).sum := by decide
  have hdescent : baseEnd_3172606 < baseStart_3172606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172625 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_3172625 : Nat := 118140960795 + 3172625 * 2 ^ 59
def prefixEnd_3172625 : Nat := 4983230072969 + 3 ^ 40 * 3172625 * 2
def baseEnd_3172625 : Nat := 1629081561470754823796869

theorem tailTrace_3172625 : CollatzResearch.WordTrace tailWord_3172625 prefixEnd_3172625 1629081561470754823796869 := by
  unfold tailWord_3172625
  simp only [CollatzResearch.WordTrace]
  refine ⟨115715140131128941056927329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77143426754085960704618219 115715140131128941056927329)
  ·
    refine ⟨86786355098346705792695497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115715140131128941056927329 86786355098346705792695497)
    ·
      refine ⟨65089766323760029344521623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86786355098346705792695497 65089766323760029344521623)
      ·
        refine ⟨97634649485640044016782435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65089766323760029344521623 97634649485640044016782435)
        ·
          refine ⟨146451974228460066025173653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97634649485640044016782435 146451974228460066025173653)
          ·
            refine ⟨6864936291959065594930015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 146451974228460066025173653 6864936291959065594930015)
            ·
              refine ⟨10297404437938598392395023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864936291959065594930015 10297404437938598392395023)
              ·
                refine ⟨15446106656907897588592535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10297404437938598392395023 15446106656907897588592535)
                ·
                  refine ⟨23169159985361846382888803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15446106656907897588592535 23169159985361846382888803)
                  ·
                    refine ⟨34753739978042769574333205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23169159985361846382888803 34753739978042769574333205)
                    ·
                      refine ⟨1629081561470754823796869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34753739978042769574333205 1629081561470754823796869)
                      ·
                        rfl

theorem cell23_3172625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_3172625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172625 prefixEnd_3172625 := by exact prefixLift 3172625
  have htrace : WordTrace (prefixWord ++ tailWord_3172625) baseStart_3172625 baseEnd_3172625 := by
    simpa [prefixWord, tailWord_3172625, baseEnd_3172625] using wordTrace_append hprefix tailTrace_3172625
  have hstable : (prefixWord ++ tailWord_3172625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172625).length < 2 ^ (prefixWord ++ tailWord_3172625).sum := by decide
  have hdescent : baseEnd_3172625 < baseStart_3172625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172629 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_3172629 : Nat := 118140960795 + 3172629 * 2 ^ 59
def prefixEnd_3172629 : Nat := 4983230072969 + 3 ^ 40 * 3172629 * 2
def baseEnd_3172629 : Nat := 1629083615393372808146851

theorem tailTrace_3172629 : CollatzResearch.WordTrace tailWord_3172629 prefixEnd_3172629 1629083615393372808146851 := by
  unfold tailWord_3172629
  simp only [CollatzResearch.WordTrace]
  refine ⟨115715286023114449740072941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77143524015409633160048627 115715286023114449740072941)
  ·
    refine ⟨43393232258667918652527353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115715286023114449740072941 43393232258667918652527353)
    ·
      refine ⟨32544924194000938989395515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43393232258667918652527353 32544924194000938989395515)
      ·
        refine ⟨48817386291001408484093273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32544924194000938989395515 48817386291001408484093273)
        ·
          refine ⟨36613039718251056363069955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48817386291001408484093273 36613039718251056363069955)
          ·
            refine ⟨54919559577376584544604933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36613039718251056363069955 54919559577376584544604933)
            ·
              refine ⟨10297417420758109602113425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54919559577376584544604933 10297417420758109602113425)
              ·
                refine ⟨7723063065568582201585069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10297417420758109602113425 7723063065568582201585069)
                ·
                  refine ⟨2896148649588218325594401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7723063065568582201585069 2896148649588218325594401)
                  ·
                    refine ⟨2172111487191163744195801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2896148649588218325594401 2172111487191163744195801)
                    ·
                      refine ⟨1629083615393372808146851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172111487191163744195801 1629083615393372808146851)
                      ·
                        rfl

theorem cell23_3172629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_3172629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172629 prefixEnd_3172629 := by exact prefixLift 3172629
  have htrace : WordTrace (prefixWord ++ tailWord_3172629) baseStart_3172629 baseEnd_3172629 := by
    simpa [prefixWord, tailWord_3172629, baseEnd_3172629] using wordTrace_append hprefix tailTrace_3172629
  have hstable : (prefixWord ++ tailWord_3172629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172629).length < 2 ^ (prefixWord ++ tailWord_3172629).sum := by decide
  have hdescent : baseEnd_3172629 < baseStart_3172629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172635 : List Nat := [1, 1, 1, 1, 1, 1, 10, 7]
def baseStart_3172635 : Nat := 118140960795 + 3172635 * 2 ^ 59
def prefixEnd_3172635 : Nat := 4983230072969 + 3 ^ 40 * 3172635 * 2
def baseEnd_3172635 : Nat := 60336544306566658691549

theorem tailTrace_3172635 : CollatzResearch.WordTrace tailWord_3172635 prefixEnd_3172635 60336544306566658691549 := by
  unfold tailWord_3172635
  simp only [CollatzResearch.WordTrace]
  refine ⟨115715504861092712764791359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77143669907395141843194239 115715504861092712764791359)
  ·
    refine ⟨173573257291639069147187039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115715504861092712764791359 173573257291639069147187039)
    ·
      refine ⟨260359885937458603720780559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173573257291639069147187039 260359885937458603720780559)
      ·
        refine ⟨390539828906187905581170839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260359885937458603720780559 390539828906187905581170839)
        ·
          refine ⟨585809743359281858371756259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390539828906187905581170839 585809743359281858371756259)
          ·
            refine ⟨878714615038922787557634389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585809743359281858371756259 878714615038922787557634389)
            ·
              refine ⟨2574359223746844104172757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 878714615038922787557634389 2574359223746844104172757)
              ·
                refine ⟨60336544306566658691549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2574359223746844104172757 60336544306566658691549)
                ·
                  rfl

theorem cell23_3172635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 7].length) (baseStart_3172635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172635 prefixEnd_3172635 := by exact prefixLift 3172635
  have htrace : WordTrace (prefixWord ++ tailWord_3172635) baseStart_3172635 baseEnd_3172635 := by
    simpa [prefixWord, tailWord_3172635, baseEnd_3172635] using wordTrace_append hprefix tailTrace_3172635
  have hstable : (prefixWord ++ tailWord_3172635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172635).length < 2 ^ (prefixWord ++ tailWord_3172635).sum := by decide
  have hdescent : baseEnd_3172635 < baseStart_3172635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172673 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3172673 : Nat := 118140960795 + 3172673 * 2 ^ 59
def prefixEnd_3172673 : Nat := 4983230072969 + 3 ^ 40 * 3172673 * 2
def baseEnd_3172673 : Nat := 543035402847390211998883

theorem tailTrace_3172673 : CollatzResearch.WordTrace tailWord_3172673 prefixEnd_3172673 543035402847390211998883 := by
  unfold tailWord_3172673
  simp only [CollatzResearch.WordTrace]
  refine ⟨115716890834955045254674673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77144593889970030169783115 115716890834955045254674673)
  ·
    refine ⟨86787668126216283941006005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115716890834955045254674673 86787668126216283941006005)
    ·
      refine ⟨8136343886832776619469313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86787668126216283941006005 8136343886832776619469313)
      ·
        refine ⟨6102257915124582464601985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8136343886832776619469313 6102257915124582464601985)
        ·
          refine ⟨4576693436343436848451489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6102257915124582464601985 4576693436343436848451489)
          ·
            refine ⟨3432520077257577636338617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4576693436343436848451489 3432520077257577636338617)
            ·
              refine ⟨2574390057943183227253963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432520077257577636338617 2574390057943183227253963)
              ·
                refine ⟨3861585086914774840880945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574390057943183227253963 3861585086914774840880945)
                ·
                  refine ⟨2896188815186081130660709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861585086914774840880945 2896188815186081130660709)
                  ·
                    refine ⟨543035402847390211998883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2896188815186081130660709 543035402847390211998883)
                    ·
                      rfl

theorem cell23_3172673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3172673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172673 prefixEnd_3172673 := by exact prefixLift 3172673
  have htrace : WordTrace (prefixWord ++ tailWord_3172673) baseStart_3172673 baseEnd_3172673 := by
    simpa [prefixWord, tailWord_3172673, baseEnd_3172673] using wordTrace_append hprefix tailTrace_3172673
  have hstable : (prefixWord ++ tailWord_3172673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172673).length < 2 ^ (prefixWord ++ tailWord_3172673).sum := by decide
  have hdescent : baseEnd_3172673 < baseStart_3172673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172679 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_3172679 : Nat := 118140960795 + 3172679 * 2 ^ 59
def prefixEnd_3172679 : Nat := 4983230072969 + 3 ^ 40 * 3172679 * 2
def baseEnd_3172679 : Nat := 1629109289426097612521621

theorem tailTrace_3172679 : CollatzResearch.WordTrace tailWord_3172679 prefixEnd_3172679 1629109289426097612521621 := by
  unfold tailWord_3172679
  simp only [CollatzResearch.WordTrace]
  refine ⟨115717109672933308279393091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77144739781955538852928727 115717109672933308279393091)
  ·
    refine ⟨173575664509399962419089637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115717109672933308279393091 173575664509399962419089637)
    ·
      refine ⟨32545437095512492953579307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173575664509399962419089637 32545437095512492953579307)
      ·
        refine ⟨48818155643268739430368961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32545437095512492953579307 48818155643268739430368961)
        ·
          refine ⟨36613616732451554572776721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48818155643268739430368961 36613616732451554572776721)
          ·
            refine ⟨27460212549338665929582541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36613616732451554572776721 27460212549338665929582541)
            ·
              refine ⟨10297579706001999723593453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27460212549338665929582541 10297579706001999723593453)
              ·
                refine ⟨3861592389750749896347545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10297579706001999723593453 3861592389750749896347545)
                ·
                  refine ⟨2896194292313062422260659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861592389750749896347545 2896194292313062422260659)
                  ·
                    refine ⟨4344291438469593633390989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2896194292313062422260659 4344291438469593633390989)
                    ·
                      refine ⟨1629109289426097612521621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4344291438469593633390989 1629109289426097612521621)
                      ·
                        rfl

theorem cell23_3172679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_3172679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172679 prefixEnd_3172679 := by exact prefixLift 3172679
  have htrace : WordTrace (prefixWord ++ tailWord_3172679) baseStart_3172679 baseEnd_3172679 := by
    simpa [prefixWord, tailWord_3172679, baseEnd_3172679] using wordTrace_append hprefix tailTrace_3172679
  have hstable : (prefixWord ++ tailWord_3172679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172679).length < 2 ^ (prefixWord ++ tailWord_3172679).sum := by decide
  have hdescent : baseEnd_3172679 < baseStart_3172679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172689 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 3, 3, 2]
def baseStart_3172689 : Nat := 118140960795 + 3172689 * 2 ^ 59
def prefixEnd_3172689 : Nat := 4983230072969 + 3 ^ 40 * 3172689 * 2
def baseEnd_3172689 : Nat := 1629114424232642573396575

theorem tailTrace_3172689 : CollatzResearch.WordTrace tailWord_3172689 prefixEnd_3172689 1629114424232642573396575 := by
  unfold tailWord_3172689
  simp only [CollatzResearch.WordTrace]
  refine ⟨115717474402897079987257121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77144982935264719991504747 115717474402897079987257121)
  ·
    refine ⟨86788105802172809990442841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115717474402897079987257121 86788105802172809990442841)
    ·
      refine ⟨65091079351629607492832131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86788105802172809990442841 65091079351629607492832131)
      ·
        refine ⟨97636619027444411239248197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65091079351629607492832131 97636619027444411239248197)
        ·
          refine ⟨18306866067645827107359037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97636619027444411239248197 18306866067645827107359037)
          ·
            refine ⟨6865074775367185165259639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18306866067645827107359037 6865074775367185165259639)
            ·
              refine ⟨10297612163050777747889459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865074775367185165259639 10297612163050777747889459)
              ·
                refine ⟨15446418244576166621834189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10297612163050777747889459 15446418244576166621834189)
                ·
                  refine ⟨5792406841716062483187821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15446418244576166621834189 5792406841716062483187821)
                  ·
                    refine ⟨2172152565643523431195433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5792406841716062483187821 2172152565643523431195433)
                    ·
                      refine ⟨1629114424232642573396575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172152565643523431195433 1629114424232642573396575)
                      ·
                        rfl

theorem cell23_3172689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_3172689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172689 prefixEnd_3172689 := by exact prefixLift 3172689
  have htrace : WordTrace (prefixWord ++ tailWord_3172689) baseStart_3172689 baseEnd_3172689 := by
    simpa [prefixWord, tailWord_3172689, baseEnd_3172689] using wordTrace_append hprefix tailTrace_3172689
  have hstable : (prefixWord ++ tailWord_3172689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172689).length < 2 ^ (prefixWord ++ tailWord_3172689).sum := by decide
  have hdescent : baseEnd_3172689 < baseStart_3172689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172715 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4]
def baseStart_3172715 : Nat := 118140960795 + 3172715 * 2 ^ 59
def prefixEnd_3172715 : Nat := 4983230072969 + 3 ^ 40 * 3172715 * 2
def baseEnd_3172715 : Nat := 1629127774729659471671455

theorem tailTrace_3172715 : CollatzResearch.WordTrace tailWord_3172715 prefixEnd_3172715 1629127774729659471671455 := by
  unfold tailWord_3172715
  simp only [CollatzResearch.WordTrace]
  refine ⟨115718422700802886427703599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77145615133868590951802399 115718422700802886427703599)
  ·
    refine ⟨173577634051204329641555399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115718422700802886427703599 173577634051204329641555399)
    ·
      refine ⟨260366451076806494462333099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173577634051204329641555399 260366451076806494462333099)
      ·
        refine ⟨390549676615209741693499649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260366451076806494462333099 390549676615209741693499649)
        ·
          refine ⟨292912257461407306270124737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390549676615209741693499649 292912257461407306270124737)
          ·
            refine ⟨219684193096055479702593553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292912257461407306270124737 219684193096055479702593553)
            ·
              refine ⟨164763144822041609776945165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219684193096055479702593553 164763144822041609776945165)
              ·
                refine ⟨61786179308265603666354437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164763144822041609776945165 61786179308265603666354437)
                ·
                  refine ⟨11584908620299800687441457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61786179308265603666354437 11584908620299800687441457)
                  ·
                    refine ⟨8688681465224850515581093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11584908620299800687441457 8688681465224850515581093)
                    ·
                      refine ⟨1629127774729659471671455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8688681465224850515581093 1629127774729659471671455)
                      ·
                        rfl

theorem cell23_3172715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_3172715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172715 prefixEnd_3172715 := by exact prefixLift 3172715
  have htrace : WordTrace (prefixWord ++ tailWord_3172715) baseStart_3172715 baseEnd_3172715 := by
    simpa [prefixWord, tailWord_3172715, baseEnd_3172715] using wordTrace_append hprefix tailTrace_3172715
  have hstable : (prefixWord ++ tailWord_3172715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172715).length < 2 ^ (prefixWord ++ tailWord_3172715).sum := by decide
  have hdescent : baseEnd_3172715 < baseStart_3172715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172722 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3172722 : Nat := 118140960795 + 3172722 * 2 ^ 59
def prefixEnd_3172722 : Nat := 4983230072969 + 3 ^ 40 * 3172722 * 2
def baseEnd_3172722 : Nat := 1629131369094240944283923

theorem tailTrace_3172722 : CollatzResearch.WordTrace tailWord_3172722 prefixEnd_3172722 1629131369094240944283923 := by
  unfold tailWord_3172722
  simp only [CollatzResearch.WordTrace]
  refine ⟨28929669502944381655802105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77145785341185017748805613 28929669502944381655802105)
  ·
    refine ⟨21697252127208286241851579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28929669502944381655802105 21697252127208286241851579)
    ·
      refine ⟨32545878190812429362777369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21697252127208286241851579 32545878190812429362777369)
      ·
        refine ⟨24409408643109322022083027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32545878190812429362777369 24409408643109322022083027)
        ·
          refine ⟨36614112964663983033124541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24409408643109322022083027 36614112964663983033124541)
          ·
            refine ⟨13730292361748993637421703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36614112964663983033124541 13730292361748993637421703)
            ·
              refine ⟨20595438542623490456132555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13730292361748993637421703 20595438542623490456132555)
              ·
                refine ⟨30893157813935235684198833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20595438542623490456132555 30893157813935235684198833)
                ·
                  refine ⟨23169868360451426763149125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30893157813935235684198833 23169868360451426763149125)
                  ·
                    refine ⟨4344350317584642518090461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23169868360451426763149125 4344350317584642518090461)
                    ·
                      refine ⟨1629131369094240944283923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4344350317584642518090461 1629131369094240944283923)
                      ·
                        rfl

theorem cell23_3172722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3172722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172722 prefixEnd_3172722 := by exact prefixLift 3172722
  have htrace : WordTrace (prefixWord ++ tailWord_3172722) baseStart_3172722 baseEnd_3172722 := by
    simpa [prefixWord, tailWord_3172722, baseEnd_3172722] using wordTrace_append hprefix tailTrace_3172722
  have hstable : (prefixWord ++ tailWord_3172722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172722).length < 2 ^ (prefixWord ++ tailWord_3172722).sum := by decide
  have hdescent : baseEnd_3172722 < baseStart_3172722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172772 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_3172772 : Nat := 118140960795 + 3172772 * 2 ^ 59
def prefixEnd_3172772 : Nat := 4983230072969 + 3 ^ 40 * 3172772 * 2
def baseEnd_3172772 : Nat := 543052347708988582886231

theorem tailTrace_3172772 : CollatzResearch.WordTrace tailWord_3172772 prefixEnd_3172772 543052347708988582886231 := by
  unfold tailWord_3172772
  simp only [CollatzResearch.WordTrace]
  refine ⟨57860250830798192581264285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77147001107730923441685713 57860250830798192581264285)
  ·
    refine ⟨21697594061549322217974107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57860250830798192581264285 21697594061549322217974107)
    ·
      refine ⟨32546391092323983326961161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21697594061549322217974107 32546391092323983326961161)
      ·
        refine ⟨24409793319242987495220871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32546391092323983326961161 24409793319242987495220871)
        ·
          refine ⟨36614689978864481242831307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24409793319242987495220871 36614689978864481242831307)
          ·
            refine ⟨54922034968296721864246961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36614689978864481242831307 54922034968296721864246961)
            ·
              refine ⟨41191526226222541398185221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54922034968296721864246961 41191526226222541398185221)
              ·
                refine ⟨7723411167416726512159729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41191526226222541398185221 7723411167416726512159729)
                ·
                  refine ⟨5792558375562544884119797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7723411167416726512159729 5792558375562544884119797)
                  ·
                    refine ⟨543052347708988582886231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5792558375562544884119797 543052347708988582886231)
                    ·
                      rfl

theorem cell23_3172772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_3172772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172772 prefixEnd_3172772 := by exact prefixLift 3172772
  have htrace : WordTrace (prefixWord ++ tailWord_3172772) baseStart_3172772 baseEnd_3172772 := by
    simpa [prefixWord, tailWord_3172772, baseEnd_3172772] using wordTrace_append hprefix tailTrace_3172772
  have hstable : (prefixWord ++ tailWord_3172772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172772).length < 2 ^ (prefixWord ++ tailWord_3172772).sum := by decide
  have hdescent : baseEnd_3172772 < baseStart_3172772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172776 : List Nat := [2, 1, 6, 1, 1, 1, 2, 4, 5]
def baseStart_3172776 : Nat := 118140960795 + 3172776 * 2 ^ 59
def prefixEnd_3172776 : Nat := 4983230072969 + 3 ^ 40 * 3172776 * 2
def baseEnd_3172776 : Nat := 181017677449953748112075

theorem tailTrace_3172776 : CollatzResearch.WordTrace tailWord_3172776 prefixEnd_3172776 181017677449953748112075 := by
  unfold tailWord_3172776
  simp only [CollatzResearch.WordTrace]
  refine ⟨57860323776790946922837091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77147098369054595897116121 57860323776790946922837091)
  ·
    refine ⟨86790485665186420384255637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57860323776790946922837091 86790485665186420384255637)
    ·
      refine ⟨4068304015555613455511983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86790485665186420384255637 4068304015555613455511983)
      ·
        refine ⟨6102456023333420183267975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068304015555613455511983 6102456023333420183267975)
        ·
          refine ⟨9153684035000130274901963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102456023333420183267975 9153684035000130274901963)
          ·
            refine ⟨13730526052500195412352945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153684035000130274901963 13730526052500195412352945)
            ·
              refine ⟨10297894539375146559264709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13730526052500195412352945 10297894539375146559264709)
              ·
                refine ⟨1930855226132839979862133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10297894539375146559264709 1930855226132839979862133)
                ·
                  refine ⟨181017677449953748112075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1930855226132839979862133 181017677449953748112075)
                  ·
                    rfl

theorem cell23_3172776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 5].length) (baseStart_3172776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172776 prefixEnd_3172776 := by exact prefixLift 3172776
  have htrace : WordTrace (prefixWord ++ tailWord_3172776) baseStart_3172776 baseEnd_3172776 := by
    simpa [prefixWord, tailWord_3172776, baseEnd_3172776] using wordTrace_append hprefix tailTrace_3172776
  have hstable : (prefixWord ++ tailWord_3172776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172776).length < 2 ^ (prefixWord ++ tailWord_3172776).sum := by decide
  have hdescent : baseEnd_3172776 < baseStart_3172776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172795 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5]
def baseStart_3172795 : Nat := 118140960795 + 3172795 * 2 ^ 59
def prefixEnd_3172795 : Nat := 4983230072969 + 3 ^ 40 * 3172795 * 2
def baseEnd_3172795 : Nat := 1629168853182019158671087

theorem tailTrace_3172795 : CollatzResearch.WordTrace tailWord_3172795 prefixEnd_3172795 1629168853182019158671087 := by
  unfold tailWord_3172795
  simp only [CollatzResearch.WordTrace]
  refine ⟨115721340540513060090615839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77147560360342040060410559 115721340540513060090615839)
  ·
    refine ⟨173582010810769590135923759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115721340540513060090615839 173582010810769590135923759)
    ·
      refine ⟨260373016216154385203885639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173582010810769590135923759 260373016216154385203885639)
      ·
        refine ⟨390559524324231577805828459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260373016216154385203885639 390559524324231577805828459)
        ·
          refine ⟨585839286486347366708742689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390559524324231577805828459 585839286486347366708742689)
          ·
            refine ⟨439379464864760525031557017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585839286486347366708742689 439379464864760525031557017)
            ·
              refine ⟨329534598648570393773667763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439379464864760525031557017 329534598648570393773667763)
              ·
                refine ⟨494301897972855590660501645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329534598648570393773667763 494301897972855590660501645)
                ·
                  refine ⟨185363211739820846497688117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494301897972855590660501645 185363211739820846497688117)
                  ·
                    refine ⟨17377801100608204359158261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 185363211739820846497688117 17377801100608204359158261)
                    ·
                      refine ⟨1629168853182019158671087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17377801100608204359158261 1629168853182019158671087)
                      ·
                        rfl

theorem cell23_3172795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_3172795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172795 prefixEnd_3172795 := by exact prefixLift 3172795
  have htrace : WordTrace (prefixWord ++ tailWord_3172795) baseStart_3172795 baseEnd_3172795 := by
    simpa [prefixWord, tailWord_3172795, baseEnd_3172795] using wordTrace_append hprefix tailTrace_3172795
  have hstable : (prefixWord ++ tailWord_3172795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172795).length < 2 ^ (prefixWord ++ tailWord_3172795).sum := by decide
  have hdescent : baseEnd_3172795 < baseStart_3172795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172832 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 6]
def baseStart_3172832 : Nat := 118140960795 + 3172832 * 2 ^ 59
def prefixEnd_3172832 : Nat := 4983230072969 + 3 ^ 40 * 3172832 * 2
def baseEnd_3172832 : Nat := 181020872440692834878713

theorem tailTrace_3172832 : CollatzResearch.WordTrace tailWord_3172832 prefixEnd_3172832 181020872440692834878713 := by
  unfold tailWord_3172832
  simp only [CollatzResearch.WordTrace]
  refine ⟨57861345020689507704856375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77148460027586010273141833 57861345020689507704856375)
  ·
    refine ⟨86792017531034261557284563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57861345020689507704856375 86792017531034261557284563)
    ·
      refine ⟨130188026296551392335926845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86792017531034261557284563 130188026296551392335926845)
      ·
        refine ⟨48820509861206772125972567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130188026296551392335926845 48820509861206772125972567)
        ·
          refine ⟨73230764791810158188958851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48820509861206772125972567 73230764791810158188958851)
          ·
            refine ⟨109846147187715237283438277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73230764791810158188958851 109846147187715237283438277)
            ·
              refine ⟨20596152597696606990644677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109846147187715237283438277 20596152597696606990644677)
              ·
                refine ⟨3861778612068113810745877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20596152597696606990644677 3861778612068113810745877)
                ·
                  refine ⟨181020872440692834878713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3861778612068113810745877 181020872440692834878713)
                  ·
                    rfl

theorem cell23_3172832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 6].length) (baseStart_3172832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172832 prefixEnd_3172832 := by exact prefixLift 3172832
  have htrace : WordTrace (prefixWord ++ tailWord_3172832) baseStart_3172832 baseEnd_3172832 := by
    simpa [prefixWord, tailWord_3172832, baseEnd_3172832] using wordTrace_append hprefix tailTrace_3172832
  have hstable : (prefixWord ++ tailWord_3172832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172832).length < 2 ^ (prefixWord ++ tailWord_3172832).sum := by decide
  have hdescent : baseEnd_3172832 < baseStart_3172832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172869 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 1, 5, 2]
def baseStart_3172869 : Nat := 118140960795 + 3172869 * 2 ^ 59
def prefixEnd_3172869 : Nat := 4983230072969 + 3 ^ 40 * 3172869 * 2
def baseEnd_3172869 : Nat := 1629206850750451869145747

theorem tailTrace_3172869 : CollatzResearch.WordTrace tailWord_3172869 prefixEnd_3172869 1629206850750451869145747 := by
  unfold tailWord_3172869
  simp only [CollatzResearch.WordTrace]
  refine ⟨115724039542244970728809661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77149359694829980485873107 115724039542244970728809661)
  ·
    refine ⟨43396514828341864023303623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115724039542244970728809661 43396514828341864023303623)
    ·
      refine ⟨65094772242512796034955435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43396514828341864023303623 65094772242512796034955435)
      ·
        refine ⟨97642158363769194052433153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65094772242512796034955435 97642158363769194052433153)
        ·
          refine ⟨73231618772826895539324865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97642158363769194052433153 73231618772826895539324865)
          ·
            refine ⟨54923714079620171654493649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73231618772826895539324865 54923714079620171654493649)
            ·
              refine ⟨41192785559715128740870237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54923714079620171654493649 41192785559715128740870237)
              ·
                refine ⟨15447294584893173277826339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41192785559715128740870237 15447294584893173277826339)
                ·
                  refine ⟨23170941877339759916739509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15447294584893173277826339 23170941877339759916739509)
                  ·
                    refine ⟨2172275801000602492194329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23170941877339759916739509 2172275801000602492194329)
                    ·
                      refine ⟨1629206850750451869145747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172275801000602492194329 1629206850750451869145747)
                      ·
                        rfl

theorem cell23_3172869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_3172869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172869 prefixEnd_3172869 := by exact prefixLift 3172869
  have htrace : WordTrace (prefixWord ++ tailWord_3172869) baseStart_3172869 baseEnd_3172869 := by
    simpa [prefixWord, tailWord_3172869, baseEnd_3172869] using wordTrace_append hprefix tailTrace_3172869
  have hstable : (prefixWord ++ tailWord_3172869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172869).length < 2 ^ (prefixWord ++ tailWord_3172869).sum := by decide
  have hdescent : baseEnd_3172869 < baseStart_3172869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172887 : List Nat := [1, 1, 3, 6, 1, 2, 2, 2, 1, 4]
def baseStart_3172887 : Nat := 118140960795 + 3172887 * 2 ^ 59
def prefixEnd_3172887 : Nat := 4983230072969 + 3 ^ 40 * 3172887 * 2
def baseEnd_3172887 : Nat := 543072031134077599573555

theorem tailTrace_3172887 : CollatzResearch.WordTrace tailWord_3172887 prefixEnd_3172887 543072031134077599573555 := by
  unfold tailWord_3172887
  simp only [CollatzResearch.WordTrace]
  refine ⟨115724696056179759802964915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77149797370786506535309943 115724696056179759802964915)
  ·
    refine ⟨173587044084269639704447373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115724696056179759802964915 173587044084269639704447373)
    ·
      refine ⟨65095141531601114889167765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173587044084269639704447373 65095141531601114889167765)
      ·
        refine ⟨3051334759293802260429739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65095141531601114889167765 3051334759293802260429739)
        ·
          refine ⟨4577002138940703390644609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3051334759293802260429739 4577002138940703390644609)
          ·
            refine ⟨3432751604205527542983457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4577002138940703390644609 3432751604205527542983457)
            ·
              refine ⟨2574563703154145657237593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432751604205527542983457 2574563703154145657237593)
              ·
                refine ⟨1930922777365609242928195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574563703154145657237593 1930922777365609242928195)
                ·
                  refine ⟨2896384166048413864392293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930922777365609242928195 2896384166048413864392293)
                  ·
                    refine ⟨543072031134077599573555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2896384166048413864392293 543072031134077599573555)
                    ·
                      rfl

theorem cell23_3172887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_3172887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172887 prefixEnd_3172887 := by exact prefixLift 3172887
  have htrace : WordTrace (prefixWord ++ tailWord_3172887) baseStart_3172887 baseEnd_3172887 := by
    simpa [prefixWord, tailWord_3172887, baseEnd_3172887] using wordTrace_append hprefix tailTrace_3172887
  have hstable : (prefixWord ++ tailWord_3172887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172887).length < 2 ^ (prefixWord ++ tailWord_3172887).sum := by decide
  have hdescent : baseEnd_3172887 < baseStart_3172887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172899 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 4]
def baseStart_3172899 : Nat := 118140960795 + 3172899 * 2 ^ 59
def prefixEnd_3172899 : Nat := 4983230072969 + 3 ^ 40 * 3172899 * 2
def baseEnd_3172899 : Nat := 1629222255170086751770609

theorem tailTrace_3172899 : CollatzResearch.WordTrace tailWord_3172899 prefixEnd_3172899 1629222255170086751770609 := by
  unfold tailWord_3172899
  simp only [CollatzResearch.WordTrace]
  refine ⟨115725133732136285852401751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77150089154757523901601167 115725133732136285852401751)
  ·
    refine ⟨173587700598204428778602627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115725133732136285852401751 173587700598204428778602627)
    ·
      refine ⟨260381550897306643167903941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173587700598204428778602627 260381550897306643167903941)
      ·
        refine ⟨48821540793244995593981989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260381550897306643167903941 48821540793244995593981989)
        ·
          refine ⟨9154038898733436673871623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48821540793244995593981989 9154038898733436673871623)
          ·
            refine ⟨13731058348100155010807435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9154038898733436673871623 13731058348100155010807435)
            ·
              refine ⟨20596587522150232516211153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13731058348100155010807435 20596587522150232516211153)
              ·
                refine ⟨15447440641612674387158365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20596587522150232516211153 15447440641612674387158365)
                ·
                  refine ⟨5792790240604752895184387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15447440641612674387158365 5792790240604752895184387)
                  ·
                    refine ⟨8689185360907129342776581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5792790240604752895184387 8689185360907129342776581)
                    ·
                      refine ⟨1629222255170086751770609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8689185360907129342776581 1629222255170086751770609)
                      ·
                        rfl

theorem cell23_3172899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_3172899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172899 prefixEnd_3172899 := by exact prefixLift 3172899
  have htrace : WordTrace (prefixWord ++ tailWord_3172899) baseStart_3172899 baseEnd_3172899 := by
    simpa [prefixWord, tailWord_3172899, baseEnd_3172899] using wordTrace_append hprefix tailTrace_3172899
  have hstable : (prefixWord ++ tailWord_3172899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172899).length < 2 ^ (prefixWord ++ tailWord_3172899).sum := by decide
  have hdescent : baseEnd_3172899 < baseStart_3172899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172912 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_3172912 : Nat := 118140960795 + 3172912 * 2 ^ 59
def prefixEnd_3172912 : Nat := 4983230072969 + 3 ^ 40 * 3172912 * 2
def baseEnd_3172912 : Nat := 1629228930418595200908049

theorem tailTrace_3172912 : CollatzResearch.WordTrace tailWord_3172912 prefixEnd_3172912 1629228930418595200908049 := by
  unfold tailWord_3172912
  simp only [CollatzResearch.WordTrace]
  refine ⟨57862803940544594536312495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77150405254059459381749993 57862803940544594536312495)
  ·
    refine ⟨86794205910816891804468743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57862803940544594536312495 86794205910816891804468743)
    ·
      refine ⟨130191308866225337706703115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86794205910816891804468743 130191308866225337706703115)
      ·
        refine ⟨195286963299338006560054673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130191308866225337706703115 195286963299338006560054673)
        ·
          refine ⟨146465222474503504920041005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195286963299338006560054673 146465222474503504920041005)
          ·
            refine ⟨54924458427938814345015377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146465222474503504920041005 54924458427938814345015377)
            ·
              refine ⟨41193343820954110758761533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54924458427938814345015377 41193343820954110758761533)
              ·
                refine ⟨15447503932857791534535575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41193343820954110758761533 15447503932857791534535575)
                ·
                  refine ⟨23171255899286687301803363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15447503932857791534535575 23171255899286687301803363)
                  ·
                    refine ⟨34756883848930030952705045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23171255899286687301803363 34756883848930030952705045)
                    ·
                      refine ⟨1629228930418595200908049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34756883848930030952705045 1629228930418595200908049)
                      ·
                        rfl

theorem cell23_3172912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_3172912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172912 prefixEnd_3172912 := by exact prefixLift 3172912
  have htrace : WordTrace (prefixWord ++ tailWord_3172912) baseStart_3172912 baseEnd_3172912 := by
    simpa [prefixWord, tailWord_3172912, baseEnd_3172912] using wordTrace_append hprefix tailTrace_3172912
  have hstable : (prefixWord ++ tailWord_3172912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172912).length < 2 ^ (prefixWord ++ tailWord_3172912).sum := by decide
  have hdescent : baseEnd_3172912 < baseStart_3172912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172919 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_3172919 : Nat := 118140960795 + 3172919 * 2 ^ 59
def prefixEnd_3172919 : Nat := 4983230072969 + 3 ^ 40 * 3172919 * 2
def baseEnd_3172919 : Nat := 1629232524783176673520517

theorem tailTrace_3172919 : CollatzResearch.WordTrace tailWord_3172919 prefixEnd_3172919 1629232524783176673520517 := by
  unfold tailWord_3172919
  simp only [CollatzResearch.WordTrace]
  refine ⟨115725863192063829268129811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77150575461375886178753207 115725863192063829268129811)
  ·
    refine ⟨173588794788095743902194717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115725863192063829268129811 173588794788095743902194717)
    ·
      refine ⟨65095798045535903963323019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173588794788095743902194717 65095798045535903963323019)
      ·
        refine ⟨97643697068303855944984529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65095798045535903963323019 97643697068303855944984529)
        ·
          refine ⟨73232772801227891958738397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97643697068303855944984529 73232772801227891958738397)
          ·
            refine ⟨27462289800460459484526899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73232772801227891958738397 27462289800460459484526899)
            ·
              refine ⟨41193434700690689226790349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27462289800460459484526899 41193434700690689226790349)
              ·
                refine ⟨15447538012759008460046381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41193434700690689226790349 15447538012759008460046381)
                ·
                  refine ⟨5792826754784628172517393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15447538012759008460046381 5792826754784628172517393)
                  ·
                    refine ⟨4344620066088471129388045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5792826754784628172517393 4344620066088471129388045)
                    ·
                      refine ⟨1629232524783176673520517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4344620066088471129388045 1629232524783176673520517)
                      ·
                        rfl

theorem cell23_3172919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_3172919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172919 prefixEnd_3172919 := by exact prefixLift 3172919
  have htrace : WordTrace (prefixWord ++ tailWord_3172919) baseStart_3172919 baseEnd_3172919 := by
    simpa [prefixWord, tailWord_3172919, baseEnd_3172919] using wordTrace_append hprefix tailTrace_3172919
  have hstable : (prefixWord ++ tailWord_3172919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172919).length < 2 ^ (prefixWord ++ tailWord_3172919).sum := by decide
  have hdescent : baseEnd_3172919 < baseStart_3172919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172933 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 1, 1, 4]
def baseStart_3172933 : Nat := 118140960795 + 3172933 * 2 ^ 59
def prefixEnd_3172933 : Nat := 4983230072969 + 3 ^ 40 * 3172933 * 2
def baseEnd_3172933 : Nat := 1629239713512339618745453

theorem tailTrace_3172933 : CollatzResearch.WordTrace tailWord_3172933 prefixEnd_3172933 1629239713512339618745453 := by
  unfold tailWord_3172933
  simp only [CollatzResearch.WordTrace]
  refine ⟨115726373814013109659139453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77150915876008739772759635 115726373814013109659139453)
  ·
    refine ⟨43397390180254916122177295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115726373814013109659139453 43397390180254916122177295)
    ·
      refine ⟨65096085270382374183265943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43397390180254916122177295 65096085270382374183265943)
      ·
        refine ⟨97644127905573561274898915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65096085270382374183265943 97644127905573561274898915)
        ·
          refine ⟨146466191858360341912348373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97644127905573561274898915 146466191858360341912348373)
          ·
            refine ⟨3432801371680320513570665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 146466191858360341912348373 3432801371680320513570665)
            ·
              refine ⟨2574601028760240385177999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432801371680320513570665 2574601028760240385177999)
              ·
                refine ⟨3861901543140360577766999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574601028760240385177999 3861901543140360577766999)
                ·
                  refine ⟨5792852314710540866650499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861901543140360577766999 5792852314710540866650499)
                  ·
                    refine ⟨8689278472065811299975749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5792852314710540866650499 8689278472065811299975749)
                    ·
                      refine ⟨1629239713512339618745453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8689278472065811299975749 1629239713512339618745453)
                      ·
                        rfl

theorem cell23_3172933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_3172933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172933 prefixEnd_3172933 := by exact prefixLift 3172933
  have htrace : WordTrace (prefixWord ++ tailWord_3172933) baseStart_3172933 baseEnd_3172933 := by
    simpa [prefixWord, tailWord_3172933, baseEnd_3172933] using wordTrace_append hprefix tailTrace_3172933
  have hstable : (prefixWord ++ tailWord_3172933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172933).length < 2 ^ (prefixWord ++ tailWord_3172933).sum := by decide
  have hdescent : baseEnd_3172933 < baseStart_3172933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172949 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_3172949 : Nat := 118140960795 + 3172949 * 2 ^ 59
def prefixEnd_3172949 : Nat := 4983230072969 + 3 ^ 40 * 3172949 * 2
def baseEnd_3172949 : Nat := 1629247929202811556145379

theorem tailTrace_3172949 : CollatzResearch.WordTrace tailWord_3172949 prefixEnd_3172949 1629247929202811556145379 := by
  unfold tailWord_3172949
  simp only [CollatzResearch.WordTrace]
  refine ⟨115726957381955144391721901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77151304921303429594481267 115726957381955144391721901)
  ·
    refine ⟨43397609018233179146895713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115726957381955144391721901 43397609018233179146895713)
    ·
      refine ⟨32548206763674884360171785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43397609018233179146895713 32548206763674884360171785)
      ·
        refine ⟨24411155072756163270128839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32548206763674884360171785 24411155072756163270128839)
        ·
          refine ⟨36616732609134244905193259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24411155072756163270128839 36616732609134244905193259)
          ·
            refine ⟨54925098913701367357789889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36616732609134244905193259 54925098913701367357789889)
            ·
              refine ⟨41193824185276025518342417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54925098913701367357789889 41193824185276025518342417)
              ·
                refine ⟨30895368138957019138756813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41193824185276025518342417 30895368138957019138756813)
                ·
                  refine ⟨11585763052108882177033805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30895368138957019138756813 11585763052108882177033805)
                  ·
                    refine ⟨4344661144540830816387677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11585763052108882177033805 4344661144540830816387677)
                    ·
                      refine ⟨1629247929202811556145379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4344661144540830816387677 1629247929202811556145379)
                      ·
                        rfl

theorem cell23_3172949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_3172949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172949 prefixEnd_3172949 := by exact prefixLift 3172949
  have htrace : WordTrace (prefixWord ++ tailWord_3172949) baseStart_3172949 baseEnd_3172949 := by
    simpa [prefixWord, tailWord_3172949, baseEnd_3172949] using wordTrace_append hprefix tailTrace_3172949
  have hstable : (prefixWord ++ tailWord_3172949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172949).length < 2 ^ (prefixWord ++ tailWord_3172949).sum := by decide
  have hdescent : baseEnd_3172949 < baseStart_3172949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172952 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 9]
def baseStart_3172952 : Nat := 118140960795 + 3172952 * 2 ^ 59
def prefixEnd_3172952 : Nat := 4983230072969 + 3 ^ 40 * 3172952 * 2
def baseEnd_3172952 : Nat := 543083156548258348135955

theorem tailTrace_3172952 : CollatzResearch.WordTrace tailWord_3172952 prefixEnd_3172952 543083156548258348135955 := by
  unfold tailWord_3172952
  simp only [CollatzResearch.WordTrace]
  refine ⟨57863533400472137952040555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77151377867296183936054073 57863533400472137952040555)
  ·
    refine ⟨86795300100708206928060833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57863533400472137952040555 86795300100708206928060833)
    ·
      refine ⟨65096475075531155196045625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86795300100708206928060833 65096475075531155196045625)
      ·
        refine ⟨48822356306648366397034219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65096475075531155196045625 48822356306648366397034219)
        ·
          refine ⟨73233534459972549595551329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48822356306648366397034219 73233534459972549595551329)
          ·
            refine ⟨54925150844979412196663497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73233534459972549595551329 54925150844979412196663497)
            ·
              refine ⟨41193863133734559147497623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54925150844979412196663497 41193863133734559147497623)
              ·
                refine ⟨61790794700601838721246435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41193863133734559147497623 61790794700601838721246435)
                ·
                  refine ⟨92686192050902758081869653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61790794700601838721246435 92686192050902758081869653)
                  ·
                    refine ⟨543083156548258348135955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 92686192050902758081869653 543083156548258348135955)
                    ·
                      rfl

theorem cell23_3172952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_3172952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172952 prefixEnd_3172952 := by exact prefixLift 3172952
  have htrace : WordTrace (prefixWord ++ tailWord_3172952) baseStart_3172952 baseEnd_3172952 := by
    simpa [prefixWord, tailWord_3172952, baseEnd_3172952] using wordTrace_append hprefix tailTrace_3172952
  have hstable : (prefixWord ++ tailWord_3172952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172952).length < 2 ^ (prefixWord ++ tailWord_3172952).sum := by decide
  have hdescent : baseEnd_3172952 < baseStart_3172952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3172993 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_3172993 : Nat := 118140960795 + 3172993 * 2 ^ 59
def prefixEnd_3172993 : Nat := 4983230072969 + 3 ^ 40 * 3172993 * 2
def baseEnd_3172993 : Nat := 1629270522351609383995177

theorem tailTrace_3172993 : CollatzResearch.WordTrace tailWord_3172993 prefixEnd_3172993 1629270522351609383995177 := by
  unfold tailWord_3172993
  simp only [CollatzResearch.WordTrace]
  refine ⟨115728562193795739906323633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77152374795863826604215755 115728562193795739906323633)
  ·
    refine ⟨86796421645346804929742725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115728562193795739906323633 86796421645346804929742725)
    ·
      refine ⟨16274329058502525924326761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86796421645346804929742725 16274329058502525924326761)
      ·
        refine ⟨12205746793876894443245071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16274329058502525924326761 12205746793876894443245071)
        ·
          refine ⟨18308620190815341664867607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12205746793876894443245071 18308620190815341664867607)
          ·
            refine ⟨27462930286223012497301411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18308620190815341664867607 27462930286223012497301411)
            ·
              refine ⟨41194395429334518745952117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27462930286223012497301411 41194395429334518745952117)
              ·
                refine ⟨3861974571500111132433011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41194395429334518745952117 3861974571500111132433011)
                ·
                  refine ⟨5792961857250166698649517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861974571500111132433011 5792961857250166698649517)
                  ·
                    refine ⟨2172360696468812511993569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5792961857250166698649517 2172360696468812511993569)
                    ·
                      refine ⟨1629270522351609383995177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172360696468812511993569 1629270522351609383995177)
                      ·
                        rfl

theorem cell23_3172993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_3172993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3172993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3172993 prefixEnd_3172993 := by exact prefixLift 3172993
  have htrace : WordTrace (prefixWord ++ tailWord_3172993) baseStart_3172993 baseEnd_3172993 := by
    simpa [prefixWord, tailWord_3172993, baseEnd_3172993] using wordTrace_append hprefix tailTrace_3172993
  have hstable : (prefixWord ++ tailWord_3172993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3172993).length < 2 ^ (prefixWord ++ tailWord_3172993).sum := by decide
  have hdescent : baseEnd_3172993 < baseStart_3172993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3172993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173093 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_3173093 : Nat := 118140960795 + 3173093 * 2 ^ 59
def prefixEnd_3173093 : Nat := 4983230072969 + 3 ^ 40 * 3173093 * 2
def baseEnd_3173093 : Nat := 543107290139019664248239

theorem tailTrace_3173093 : CollatzResearch.WordTrace tailWord_3173093 prefixEnd_3173093 543107290139019664248239 := by
  unfold tailWord_3173093
  simp only [CollatzResearch.WordTrace]
  refine ⟨115732209493433456984963933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77154806328955637989975955 115732209493433456984963933)
  ·
    refine ⟨43399578560037546369361475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115732209493433456984963933 43399578560037546369361475)
    ·
      refine ⟨65099367840056319554042213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43399578560037546369361475 65099367840056319554042213)
      ·
        refine ⟨12206131470010559916382915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65099367840056319554042213 12206131470010559916382915)
        ·
          refine ⟨18309197205015839874574373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12206131470010559916382915 18309197205015839874574373)
          ·
            refine ⟨3432974475940469976482695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18309197205015839874574373 3432974475940469976482695)
            ·
              refine ⟨5149461713910704964724043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432974475940469976482695 5149461713910704964724043)
              ·
                refine ⟨7724192570866057447086065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149461713910704964724043 7724192570866057447086065)
                ·
                  refine ⟨5793144428149543085314549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7724192570866057447086065 5793144428149543085314549)
                  ·
                    refine ⟨543107290139019664248239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5793144428149543085314549 543107290139019664248239)
                    ·
                      rfl

theorem cell23_3173093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_3173093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173093 prefixEnd_3173093 := by exact prefixLift 3173093
  have htrace : WordTrace (prefixWord ++ tailWord_3173093) baseStart_3173093 baseEnd_3173093 := by
    simpa [prefixWord, tailWord_3173093, baseEnd_3173093] using wordTrace_append hprefix tailTrace_3173093
  have hstable : (prefixWord ++ tailWord_3173093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173093).length < 2 ^ (prefixWord ++ tailWord_3173093).sum := by decide
  have hdescent : baseEnd_3173093 < baseStart_3173093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173108 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3173108 : Nat := 118140960795 + 3173108 * 2 ^ 59
def prefixEnd_3173108 : Nat := 4983230072969 + 3 ^ 40 * 3173108 * 2
def baseEnd_3173108 : Nat := 1629329572626876434057149

theorem tailTrace_3173108 : CollatzResearch.WordTrace tailWord_3173108 prefixEnd_3173108 1629329572626876434057149 := by
  unfold tailWord_3173108
  simp only [CollatzResearch.WordTrace]
  refine ⟨57866378294189557273379989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77155171058919409697839985 57866378294189557273379989)
  ·
    refine ⟨2712486482540135497189687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57866378294189557273379989 2712486482540135497189687)
    ·
      refine ⟨4068729723810203245784531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2712486482540135497189687 4068729723810203245784531)
      ·
        refine ⟨6103094585715304868676797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068729723810203245784531 6103094585715304868676797)
        ·
          refine ⟨2288660469643239325753799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6103094585715304868676797 2288660469643239325753799)
          ·
            refine ⟨3432990704464858988630699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288660469643239325753799 3432990704464858988630699)
            ·
              refine ⟨5149486056697288482946049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432990704464858988630699 5149486056697288482946049)
              ·
                refine ⟨3862114542522966362209537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5149486056697288482946049 3862114542522966362209537)
                ·
                  refine ⟨2896585906892224771657153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862114542522966362209537 2896585906892224771657153)
                  ·
                    refine ⟨2172439430169168578742865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2896585906892224771657153 2172439430169168578742865)
                    ·
                      refine ⟨1629329572626876434057149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172439430169168578742865 1629329572626876434057149)
                      ·
                        rfl

theorem cell23_3173108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3173108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173108 prefixEnd_3173108 := by exact prefixLift 3173108
  have htrace : WordTrace (prefixWord ++ tailWord_3173108) baseStart_3173108 baseEnd_3173108 := by
    simpa [prefixWord, tailWord_3173108, baseEnd_3173108] using wordTrace_append hprefix tailTrace_3173108
  have hstable : (prefixWord ++ tailWord_3173108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173108).length < 2 ^ (prefixWord ++ tailWord_3173108).sum := by decide
  have hdescent : baseEnd_3173108 < baseStart_3173108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173139 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6]
def baseStart_3173139 : Nat := 118140960795 + 3173139 * 2 ^ 59
def prefixEnd_3173139 : Nat := 4983230072969 + 3 ^ 40 * 3173139 * 2
def baseEnd_3173139 : Nat := 1629345490527165812769505

theorem tailTrace_3173139 : CollatzResearch.WordTrace tailWord_3173139 prefixEnd_3173139 1629345490527165812769505 := by
  unfold tailWord_3173139
  simp only [CollatzResearch.WordTrace]
  refine ⟨115733887251266806841138471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77155924834177871227425647 115733887251266806841138471)
  ·
    refine ⟨173600830876900210261707707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115733887251266806841138471 173600830876900210261707707)
    ·
      refine ⟨260401246315350315392561561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173600830876900210261707707 260401246315350315392561561)
      ·
        refine ⟨195300934736512736544421171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260401246315350315392561561 195300934736512736544421171)
        ·
          refine ⟨292951402104769104816631757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195300934736512736544421171 292951402104769104816631757)
          ·
            refine ⟨109856775789288414306236909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292951402104769104816631757 109856775789288414306236909)
            ·
              refine ⟨41196290920983155364838841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109856775789288414306236909 41196290920983155364838841)
              ·
                refine ⟨30897218190737366523629131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41196290920983155364838841 30897218190737366523629131)
                ·
                  refine ⟨46345827286106049785443697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30897218190737366523629131 46345827286106049785443697)
                  ·
                    refine ⟨34759370464579537339082773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46345827286106049785443697 34759370464579537339082773)
                    ·
                      refine ⟨1629345490527165812769505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34759370464579537339082773 1629345490527165812769505)
                      ·
                        rfl

theorem cell23_3173139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_3173139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173139 prefixEnd_3173139 := by exact prefixLift 3173139
  have htrace : WordTrace (prefixWord ++ tailWord_3173139) baseStart_3173139 baseEnd_3173139 := by
    simpa [prefixWord, tailWord_3173139, baseEnd_3173139] using wordTrace_append hprefix tailTrace_3173139
  have hstable : (prefixWord ++ tailWord_3173139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173139).length < 2 ^ (prefixWord ++ tailWord_3173139).sum := by decide
  have hdescent : baseEnd_3173139 < baseStart_3173139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173146 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_3173146 : Nat := 118140960795 + 3173146 * 2 ^ 59
def prefixEnd_3173146 : Nat := 4983230072969 + 3 ^ 40 * 3173146 * 2
def baseEnd_3173146 : Nat := 1629349084891747285381973

theorem tailTrace_3173146 : CollatzResearch.WordTrace tailWord_3173146 prefixEnd_3173146 1629349084891747285381973 := by
  unfold tailWord_3173146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28933535640560361759160823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77156095041494298024428861 28933535640560361759160823)
  ·
    refine ⟨43400303460840542638741235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28933535640560361759160823 43400303460840542638741235)
    ·
      refine ⟨65100455191260813958111853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43400303460840542638741235 65100455191260813958111853)
      ·
        refine ⟨24412670696722805234291945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65100455191260813958111853 24412670696722805234291945)
        ·
          refine ⟨18309503022542103925718959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24412670696722805234291945 18309503022542103925718959)
          ·
            refine ⟨27464254533813155888578439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18309503022542103925718959 27464254533813155888578439)
            ·
              refine ⟨41196381800719733832867659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27464254533813155888578439 41196381800719733832867659)
              ·
                refine ⟨61794572701079600749301489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41196381800719733832867659 61794572701079600749301489)
                ·
                  refine ⟨46345929525809700561976117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61794572701079600749301489 46345929525809700561976117)
                  ·
                    refine ⟨4344930893044659427685261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46345929525809700561976117 4344930893044659427685261)
                    ·
                      refine ⟨1629349084891747285381973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4344930893044659427685261 1629349084891747285381973)
                      ·
                        rfl

theorem cell23_3173146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_3173146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173146 prefixEnd_3173146 := by exact prefixLift 3173146
  have htrace : WordTrace (prefixWord ++ tailWord_3173146) baseStart_3173146 baseEnd_3173146 := by
    simpa [prefixWord, tailWord_3173146, baseEnd_3173146] using wordTrace_append hprefix tailTrace_3173146
  have hstable : (prefixWord ++ tailWord_3173146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173146).length < 2 ^ (prefixWord ++ tailWord_3173146).sum := by decide
  have hdescent : baseEnd_3173146 < baseStart_3173146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173174 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3173174 : Nat := 118140960795 + 3173174 * 2 ^ 59
def prefixEnd_3173174 : Nat := 4983230072969 + 3 ^ 40 * 3173174 * 2
def baseEnd_3173174 : Nat := 543121154116691058610615

theorem tailTrace_3173174 : CollatzResearch.WordTrace tailWord_3173174 prefixEnd_3173174 543121154116691058610615 := by
  unfold tailWord_3173174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233447737883750488666411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77156775870760005212441717 7233447737883750488666411)
  ·
    refine ⟨10850171606825625732999617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7233447737883750488666411 10850171606825625732999617)
    ·
      refine ⟨8137628705119219299749713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10850171606825625732999617 8137628705119219299749713)
      ·
        refine ⟨6103221528839414474812285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8137628705119219299749713 6103221528839414474812285)
        ·
          refine ⟨2288708073314780428054607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6103221528839414474812285 2288708073314780428054607)
          ·
            refine ⟨3433062109972170642081911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288708073314780428054607 3433062109972170642081911)
            ·
              refine ⟨5149593164958255963122867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433062109972170642081911 5149593164958255963122867)
              ·
                refine ⟨7724389747437383944684301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149593164958255963122867 7724389747437383944684301)
                ·
                  refine ⟨2896646155289018979256613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7724389747437383944684301 2896646155289018979256613)
                  ·
                    refine ⟨543121154116691058610615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2896646155289018979256613 543121154116691058610615)
                    ·
                      rfl

theorem cell23_3173174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3173174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173174 prefixEnd_3173174 := by exact prefixLift 3173174
  have htrace : WordTrace (prefixWord ++ tailWord_3173174) baseStart_3173174 baseEnd_3173174 := by
    simpa [prefixWord, tailWord_3173174, baseEnd_3173174] using wordTrace_append hprefix tailTrace_3173174
  have hstable : (prefixWord ++ tailWord_3173174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173174).length < 2 ^ (prefixWord ++ tailWord_3173174).sum := by decide
  have hdescent : baseEnd_3173174 < baseStart_3173174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173223 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3173223 : Nat := 118140960795 + 3173223 * 2 ^ 59
def prefixEnd_3173223 : Nat := 4983230072969 + 3 ^ 40 * 3173223 * 2
def baseEnd_3173223 : Nat := 1629388622902143484119119

theorem tailTrace_3173223 : CollatzResearch.WordTrace tailWord_3173223 prefixEnd_3173223 1629388622902143484119119 := by
  unfold tailWord_3173223
  simp only [CollatzResearch.WordTrace]
  refine ⟨115736950982962489187196323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77157967321974992791464215 115736950982962489187196323)
  ·
    refine ⟨173605426474443733780794485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115736950982962489187196323 173605426474443733780794485)
    ·
      refine ⟨16275508731979100041949483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173605426474443733780794485 16275508731979100041949483)
      ·
        refine ⟨24413263097968650062924225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16275508731979100041949483 24413263097968650062924225)
        ·
          refine ⟨18309947323476487547193169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24413263097968650062924225 18309947323476487547193169)
          ·
            refine ⟨13732460492607365660394877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18309947323476487547193169 13732460492607365660394877)
            ·
              refine ⟨5149672684727762122648079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13732460492607365660394877 5149672684727762122648079)
              ·
                refine ⟨7724509027091643183972119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5149672684727762122648079 7724509027091643183972119)
                ·
                  refine ⟨11586763540637464775958179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7724509027091643183972119 11586763540637464775958179)
                  ·
                    refine ⟨17380145310956197163937269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11586763540637464775958179 17380145310956197163937269)
                    ·
                      refine ⟨1629388622902143484119119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17380145310956197163937269 1629388622902143484119119)
                      ·
                        rfl

theorem cell23_3173223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3173223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173223 prefixEnd_3173223 := by exact prefixLift 3173223
  have htrace : WordTrace (prefixWord ++ tailWord_3173223) baseStart_3173223 baseEnd_3173223 := by
    simpa [prefixWord, tailWord_3173223, baseEnd_3173223] using wordTrace_append hprefix tailTrace_3173223
  have hstable : (prefixWord ++ tailWord_3173223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173223).length < 2 ^ (prefixWord ++ tailWord_3173223).sum := by decide
  have hdescent : baseEnd_3173223 < baseStart_3173223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173253 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_3173253 : Nat := 118140960795 + 3173253 * 2 ^ 59
def prefixEnd_3173253 : Nat := 4983230072969 + 3 ^ 40 * 3173253 * 2
def baseEnd_3173253 : Nat := 1629404027321778366743981

theorem tailTrace_3173253 : CollatzResearch.WordTrace tailWord_3173253 prefixEnd_3173253 1629404027321778366743981 := by
  unfold tailWord_3173253
  simp only [CollatzResearch.WordTrace]
  refine ⟨115738045172853804310788413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77158696781902536207192275 115738045172853804310788413)
  ·
    refine ⟨43401766939820176616545655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115738045172853804310788413 43401766939820176616545655)
    ·
      refine ⟨65102650409730264924818483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43401766939820176616545655 65102650409730264924818483)
      ·
        refine ⟨97653975614595397387227725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65102650409730264924818483 97653975614595397387227725)
        ·
          refine ⟨36620240855473274020210397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97653975614595397387227725 36620240855473274020210397)
          ·
            refine ⟨13732590320802477757578899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36620240855473274020210397 13732590320802477757578899)
            ·
              refine ⟨20598885481203716636368349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13732590320802477757578899 20598885481203716636368349)
              ·
                refine ⟨7724582055451393738638131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20598885481203716636368349 7724582055451393738638131)
                ·
                  refine ⟨11586873083177090607957197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7724582055451393738638131 11586873083177090607957197)
                  ·
                    refine ⟨4345077406191408977983949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11586873083177090607957197 4345077406191408977983949)
                    ·
                      refine ⟨1629404027321778366743981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4345077406191408977983949 1629404027321778366743981)
                      ·
                        rfl

theorem cell23_3173253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_3173253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173253 prefixEnd_3173253 := by exact prefixLift 3173253
  have htrace : WordTrace (prefixWord ++ tailWord_3173253) baseStart_3173253 baseEnd_3173253 := by
    simpa [prefixWord, tailWord_3173253, baseEnd_3173253] using wordTrace_append hprefix tailTrace_3173253
  have hstable : (prefixWord ++ tailWord_3173253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173253).length < 2 ^ (prefixWord ++ tailWord_3173253).sum := by decide
  have hdescent : baseEnd_3173253 < baseStart_3173253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173274 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3]
def baseStart_3173274 : Nat := 118140960795 + 3173274 * 2 ^ 59
def prefixEnd_3173274 : Nat := 4983230072969 + 3 ^ 40 * 3173274 * 2
def baseEnd_3173274 : Nat := 1629414810415522784581385

theorem tailTrace_3173274 : CollatzResearch.WordTrace tailWord_3173274 prefixEnd_3173274 1629414810415522784581385 := by
  unfold tailWord_3173274
  simp only [CollatzResearch.WordTrace]
  refine ⟨28934702776444431224325719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77159207403851816598201917 28934702776444431224325719)
  ·
    refine ⟨43402054164666646836488579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28934702776444431224325719 43402054164666646836488579)
    ·
      refine ⟨65103081246999970254732869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43402054164666646836488579 65103081246999970254732869)
      ·
        refine ⟨12206827733812494422762413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65103081246999970254732869 12206827733812494422762413)
        ·
          refine ⟨4577560400179685408535905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12206827733812494422762413 4577560400179685408535905)
          ·
            refine ⟨3433170300134764056401929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4577560400179685408535905 3433170300134764056401929)
            ·
              refine ⟨2574877725101073042301447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3433170300134764056401929 2574877725101073042301447)
              ·
                refine ⟨3862316587651609563452171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574877725101073042301447 3862316587651609563452171)
                ·
                  refine ⟨5793474881477414345178257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862316587651609563452171 5793474881477414345178257)
                  ·
                    refine ⟨4345106161108060758883693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5793474881477414345178257 4345106161108060758883693)
                    ·
                      refine ⟨1629414810415522784581385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4345106161108060758883693 1629414810415522784581385)
                      ·
                        rfl

theorem cell23_3173274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_3173274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173274 prefixEnd_3173274 := by exact prefixLift 3173274
  have htrace : WordTrace (prefixWord ++ tailWord_3173274) baseStart_3173274 baseEnd_3173274 := by
    simpa [prefixWord, tailWord_3173274, baseEnd_3173274] using wordTrace_append hprefix tailTrace_3173274
  have hstable : (prefixWord ++ tailWord_3173274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173274).length < 2 ^ (prefixWord ++ tailWord_3173274).sum := by decide
  have hdescent : baseEnd_3173274 < baseStart_3173274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173287 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3173287 : Nat := 118140960795 + 3173287 * 2 ^ 59
def prefixEnd_3173287 : Nat := 4983230072969 + 3 ^ 40 * 3173287 * 2
def baseEnd_3173287 : Nat := 1629421485664031233718825

theorem tailTrace_3173287 : CollatzResearch.WordTrace tailWord_3173287 prefixEnd_3173287 1629421485664031233718825 := by
  unfold tailWord_3173287
  simp only [CollatzResearch.WordTrace]
  refine ⟨115739285254730628117526115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77159523503153752078350743 115739285254730628117526115)
  ·
    refine ⟨173608927882095942176289173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115739285254730628117526115 173608927882095942176289173)
    ·
      refine ⟨8137918494473247289513555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173608927882095942176289173 8137918494473247289513555)
      ·
        refine ⟨12206877741709870934270333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137918494473247289513555 12206877741709870934270333)
        ·
          refine ⟨4577579153141201600351375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12206877741709870934270333 4577579153141201600351375)
          ·
            refine ⟨6866368729711802400527063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577579153141201600351375 6866368729711802400527063)
            ·
              refine ⟨10299553094567703600790595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866368729711802400527063 10299553094567703600790595)
              ·
                refine ⟨15449329641851555401185893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299553094567703600790595 15449329641851555401185893)
                ·
                  refine ⟨2896749307847166637722355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15449329641851555401185893 2896749307847166637722355)
                  ·
                    refine ⟨4345123961770749956583533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2896749307847166637722355 4345123961770749956583533)
                    ·
                      refine ⟨1629421485664031233718825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4345123961770749956583533 1629421485664031233718825)
                      ·
                        rfl

theorem cell23_3173287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3173287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173287 prefixEnd_3173287 := by exact prefixLift 3173287
  have htrace : WordTrace (prefixWord ++ tailWord_3173287) baseStart_3173287 baseEnd_3173287 := by
    simpa [prefixWord, tailWord_3173287, baseEnd_3173287] using wordTrace_append hprefix tailTrace_3173287
  have hstable : (prefixWord ++ tailWord_3173287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173287).length < 2 ^ (prefixWord ++ tailWord_3173287).sum := by decide
  have hdescent : baseEnd_3173287 < baseStart_3173287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173330 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3173330 : Nat := 118140960795 + 3173330 * 2 ^ 59
def prefixEnd_3173330 : Nat := 4983230072969 + 3 ^ 40 * 3173330 * 2
def baseEnd_3173330 : Nat := 1629443565332174565481127

theorem tailTrace_3173330 : CollatzResearch.WordTrace tailWord_3173330 prefixEnd_3173330 1629443565332174565481127 := by
  unfold tailWord_3173330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28935213398393711615335361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77160569062383230974227629 28935213398393711615335361)
  ·
    refine ⟨21701410048795283711501521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28935213398393711615335361 21701410048795283711501521)
    ·
      refine ⟨16276057536596462783626141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21701410048795283711501521 16276057536596462783626141)
      ·
        refine ⟨6103521576223673543859803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16276057536596462783626141 6103521576223673543859803)
        ·
          refine ⟨9155282364335510315789705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103521576223673543859803 9155282364335510315789705)
          ·
            refine ⟨6866461773251632736842279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9155282364335510315789705 6866461773251632736842279)
            ·
              refine ⟨10299692659877449105263419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866461773251632736842279 10299692659877449105263419)
              ·
                refine ⟨15449538989816173657895129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299692659877449105263419 15449538989816173657895129)
                ·
                  refine ⟨11587154242362130243421347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15449538989816173657895129 11587154242362130243421347)
                  ·
                    refine ⟨17380731363543195365132021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11587154242362130243421347 17380731363543195365132021)
                    ·
                      refine ⟨1629443565332174565481127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17380731363543195365132021 1629443565332174565481127)
                      ·
                        rfl

theorem cell23_3173330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3173330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173330 prefixEnd_3173330 := by exact prefixLift 3173330
  have htrace : WordTrace (prefixWord ++ tailWord_3173330) baseStart_3173330 baseEnd_3173330 := by
    simpa [prefixWord, tailWord_3173330, baseEnd_3173330] using wordTrace_append hprefix tailTrace_3173330
  have hstable : (prefixWord ++ tailWord_3173330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173330).length < 2 ^ (prefixWord ++ tailWord_3173330).sum := by decide
  have hdescent : baseEnd_3173330 < baseStart_3173330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173361 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 2, 2, 2]
def baseStart_3173361 : Nat := 118140960795 + 3173361 * 2 ^ 59
def prefixEnd_3173361 : Nat := 4983230072969 + 3 ^ 40 * 3173361 * 2
def baseEnd_3173361 : Nat := 1629459483232463944193485

theorem tailTrace_3173361 : CollatzResearch.WordTrace tailWord_3173361 prefixEnd_3173361 1629459483232463944193485 := by
  unfold tailWord_3173361
  simp only [CollatzResearch.WordTrace]
  refine ⟨115741984256462538755719937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77161322837641692503813291 115741984256462538755719937)
  ·
    refine ⟨86806488192346904066789953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115741984256462538755719937 86806488192346904066789953)
    ·
      refine ⟨65104866144260178050092465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86806488192346904066789953 65104866144260178050092465)
      ·
        refine ⟨48828649608195133537569349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65104866144260178050092465 48828649608195133537569349)
        ·
          refine ⟨9155371801536587538294253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48828649608195133537569349 9155371801536587538294253)
          ·
            refine ⟨3433264425576220326860345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9155371801536587538294253 3433264425576220326860345)
            ·
              refine ⟨2574948319182165245145259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3433264425576220326860345 2574948319182165245145259)
              ·
                refine ⟨3862422478773247867717889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574948319182165245145259 3862422478773247867717889)
                ·
                  refine ⟨2896816859079935900788417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862422478773247867717889 2896816859079935900788417)
                  ·
                    refine ⟨2172612644309951925591313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2896816859079935900788417 2172612644309951925591313)
                    ·
                      refine ⟨1629459483232463944193485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172612644309951925591313 1629459483232463944193485)
                      ·
                        rfl

theorem cell23_3173361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_3173361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173361 prefixEnd_3173361 := by exact prefixLift 3173361
  have htrace : WordTrace (prefixWord ++ tailWord_3173361) baseStart_3173361 baseEnd_3173361 := by
    simpa [prefixWord, tailWord_3173361, baseEnd_3173361] using wordTrace_append hprefix tailTrace_3173361
  have hstable : (prefixWord ++ tailWord_3173361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173361).length < 2 ^ (prefixWord ++ tailWord_3173361).sum := by decide
  have hdescent : baseEnd_3173361 < baseStart_3173361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173400 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3173400 : Nat := 118140960795 + 3173400 * 2 ^ 59
def prefixEnd_3173400 : Nat := 4983230072969 + 3 ^ 40 * 3173400 * 2
def baseEnd_3173400 : Nat := 1629479508977989291605805

theorem tailTrace_3173400 : CollatzResearch.WordTrace tailWord_3173400 prefixEnd_3173400 1629479508977989291605805 := by
  unfold tailWord_3173400
  simp only [CollatzResearch.WordTrace]
  refine ⟨57871703351660624208194827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77162271135547498944259769 57871703351660624208194827)
  ·
    refine ⟨86807555027490936312292241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57871703351660624208194827 86807555027490936312292241)
    ·
      refine ⟨65105666270618202234219181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86807555027490936312292241 65105666270618202234219181)
      ·
        refine ⟨24414624851481825837832193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65105666270618202234219181 24414624851481825837832193)
        ·
          refine ⟨18310968638611369378374145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24414624851481825837832193 18310968638611369378374145)
          ·
            refine ⟨13733226478958527033780609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18310968638611369378374145 13733226478958527033780609)
            ·
              refine ⟨10299919859218895275335457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13733226478958527033780609 10299919859218895275335457)
              ·
                refine ⟨7724939894414171456501593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10299919859218895275335457 7724939894414171456501593)
                ·
                  refine ⟨5793704920810628592376195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7724939894414171456501593 5793704920810628592376195)
                  ·
                    refine ⟨8690557381215942888564293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5793704920810628592376195 8690557381215942888564293)
                    ·
                      refine ⟨1629479508977989291605805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8690557381215942888564293 1629479508977989291605805)
                      ·
                        rfl

theorem cell23_3173400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3173400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173400 prefixEnd_3173400 := by exact prefixLift 3173400
  have htrace : WordTrace (prefixWord ++ tailWord_3173400) baseStart_3173400 baseEnd_3173400 := by
    simpa [prefixWord, tailWord_3173400, baseEnd_3173400] using wordTrace_append hprefix tailTrace_3173400
  have hstable : (prefixWord ++ tailWord_3173400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173400).length < 2 ^ (prefixWord ++ tailWord_3173400).sum := by decide
  have hdescent : baseEnd_3173400 < baseStart_3173400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173437 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3173437 : Nat := 118140960795 + 3173437 * 2 ^ 59
def prefixEnd_3173437 : Nat := 4983230072969 + 3 ^ 40 * 3173437 * 2
def baseEnd_3173437 : Nat := 1629498507762205646843135

theorem tailTrace_3173437 : CollatzResearch.WordTrace tailWord_3173437 prefixEnd_3173437 1629498507762205646843135 := by
  unfold tailWord_3173437
  simp only [CollatzResearch.WordTrace]
  refine ⟨115744756204187203735486565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77163170802791469156991043 115744756204187203735486565)
  ·
    refine ⟨21702141788285100700403731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115744756204187203735486565 21702141788285100700403731)
    ·
      refine ⟨32553212682427651050605597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21702141788285100700403731 32553212682427651050605597)
      ·
        refine ⟨12207454755910369143977099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32553212682427651050605597 12207454755910369143977099)
        ·
          refine ⟨18311182133865553715965649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12207454755910369143977099 18311182133865553715965649)
          ·
            refine ⟨13733386600399165286974237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18311182133865553715965649 13733386600399165286974237)
            ·
              refine ⟨5150019975149686982615339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13733386600399165286974237 5150019975149686982615339)
              ·
                refine ⟨7725029962724530473923009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5150019975149686982615339 7725029962724530473923009)
                ·
                  refine ⟨5793772472043397855442257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725029962724530473923009 5793772472043397855442257)
                  ·
                    refine ⟨4345329354032548391581693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5793772472043397855442257 4345329354032548391581693)
                    ·
                      refine ⟨1629498507762205646843135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4345329354032548391581693 1629498507762205646843135)
                      ·
                        rfl

theorem cell23_3173437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3173437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173437 prefixEnd_3173437 := by exact prefixLift 3173437
  have htrace : WordTrace (prefixWord ++ tailWord_3173437) baseStart_3173437 baseEnd_3173437 := by
    simpa [prefixWord, tailWord_3173437, baseEnd_3173437] using wordTrace_append hprefix tailTrace_3173437
  have hstable : (prefixWord ++ tailWord_3173437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173437).length < 2 ^ (prefixWord ++ tailWord_3173437).sum := by decide
  have hdescent : baseEnd_3173437 < baseStart_3173437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173474 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 6]
def baseStart_3173474 : Nat := 118140960795 + 3173474 * 2 ^ 59
def prefixEnd_3173474 : Nat := 4983230072969 + 3 ^ 40 * 3173474 * 2
def baseEnd_3173474 : Nat := 181057500727380222453385

theorem tailTrace_3173474 : CollatzResearch.WordTrace tailWord_3173474 prefixEnd_3173474 181057500727380222453385 := by
  unfold tailWord_3173474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28936526426263289763645869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77164070470035439369722317 28936526426263289763645869)
  ·
    refine ⟨10851197409848733661367201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28936526426263289763645869 10851197409848733661367201)
    ·
      refine ⟨8138398057386550246025401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10851197409848733661367201 8138398057386550246025401)
      ·
        refine ⟨6103798543039912684519051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8138398057386550246025401 6103798543039912684519051)
        ·
          refine ⟨9155697814559869026778577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103798543039912684519051 9155697814559869026778577)
          ·
            refine ⟨6866773360919901770083933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9155697814559869026778577 6866773360919901770083933)
            ·
              refine ⟨2575040010344963163781475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6866773360919901770083933 2575040010344963163781475)
              ·
                refine ⟨3862560015517444745672213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575040010344963163781475 3862560015517444745672213)
                ·
                  refine ⟨181057500727380222453385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3862560015517444745672213 181057500727380222453385)
                  ·
                    rfl

theorem cell23_3173474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_3173474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173474 prefixEnd_3173474 := by exact prefixLift 3173474
  have htrace : WordTrace (prefixWord ++ tailWord_3173474) baseStart_3173474 baseEnd_3173474 := by
    simpa [prefixWord, tailWord_3173474, baseEnd_3173474] using wordTrace_append hprefix tailTrace_3173474
  have hstable : (prefixWord ++ tailWord_3173474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173474).length < 2 ^ (prefixWord ++ tailWord_3173474).sum := by decide
  have hdescent : baseEnd_3173474 < baseStart_3173474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173494 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3173494 : Nat := 118140960795 + 3173494 * 2 ^ 59
def prefixEnd_3173494 : Nat := 4983230072969 + 3 ^ 40 * 3173494 * 2
def baseEnd_3173494 : Nat := 1629527776159511923830373

theorem tailTrace_3173494 : CollatzResearch.WordTrace tailWord_3173494 prefixEnd_3173494 1629527776159511923830373 := by
  unfold tailWord_3173494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234177197811293904394471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77164556776653801646874357 7234177197811293904394471)
  ·
    refine ⟨10851265796716940856591707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7234177197811293904394471 10851265796716940856591707)
    ·
      refine ⟨16276898695075411284887561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10851265796716940856591707 16276898695075411284887561)
      ·
        refine ⟨12207674021306558463665671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16276898695075411284887561 12207674021306558463665671)
        ·
          refine ⟨18311511031959837695498507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12207674021306558463665671 18311511031959837695498507)
          ·
            refine ⟨27467266547939756543247761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18311511031959837695498507 27467266547939756543247761)
            ·
              refine ⟨20600449910954817407435821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27467266547939756543247761 20600449910954817407435821)
              ·
                refine ⟨7725168716608056527788433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20600449910954817407435821 7725168716608056527788433)
                ·
                  refine ⟨5793876537456042395841325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725168716608056527788433 5793876537456042395841325)
                  ·
                    refine ⟨2172703701546015898440497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5793876537456042395841325 2172703701546015898440497)
                    ·
                      refine ⟨1629527776159511923830373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172703701546015898440497 1629527776159511923830373)
                      ·
                        rfl

theorem cell23_3173494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3173494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173494 prefixEnd_3173494 := by exact prefixLift 3173494
  have htrace : WordTrace (prefixWord ++ tailWord_3173494) baseStart_3173494 baseEnd_3173494 := by
    simpa [prefixWord, tailWord_3173494, baseEnd_3173494] using wordTrace_append hprefix tailTrace_3173494
  have hstable : (prefixWord ++ tailWord_3173494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173494).length < 2 ^ (prefixWord ++ tailWord_3173494).sum := by decide
  have hdescent : baseEnd_3173494 < baseStart_3173494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173500 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_3173500 : Nat := 118140960795 + 3173500 * 2 ^ 59
def prefixEnd_3173500 : Nat := 4983230072969 + 3 ^ 40 * 3173500 * 2
def baseEnd_3173500 : Nat := 543176952347812966785115

theorem tailTrace_3173500 : CollatzResearch.WordTrace tailWord_3173500 prefixEnd_3173500 543176952347812966785115 := by
  unfold tailWord_3173500
  simp only [CollatzResearch.WordTrace]
  refine ⟨57873527001479482747514977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77164702668639310330019969 57873527001479482747514977)
  ·
    refine ⟨43405145251109612060636233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57873527001479482747514977 43405145251109612060636233)
    ·
      refine ⟨32553858938332209045477175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43405145251109612060636233 32553858938332209045477175)
      ·
        refine ⟨48830788407498313568215763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32553858938332209045477175 48830788407498313568215763)
        ·
          refine ⟨73246182611247470352323645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48830788407498313568215763 73246182611247470352323645)
          ·
            refine ⟨27467318479217801382121367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73246182611247470352323645 27467318479217801382121367)
            ·
              refine ⟨41200977718826702073182051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27467318479217801382121367 41200977718826702073182051)
              ·
                refine ⟨61801466578240053109773077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41200977718826702073182051 61801466578240053109773077)
                ·
                  refine ⟨2896943745855002489520613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61801466578240053109773077 2896943745855002489520613)
                  ·
                    refine ⟨543176952347812966785115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2896943745855002489520613 543176952347812966785115)
                    ·
                      rfl

theorem cell23_3173500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_3173500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173500 prefixEnd_3173500 := by exact prefixLift 3173500
  have htrace : WordTrace (prefixWord ++ tailWord_3173500) baseStart_3173500 baseEnd_3173500 := by
    simpa [prefixWord, tailWord_3173500, baseEnd_3173500] using wordTrace_append hprefix tailTrace_3173500
  have hstable : (prefixWord ++ tailWord_3173500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173500).length < 2 ^ (prefixWord ++ tailWord_3173500).sum := by decide
  have hdescent : baseEnd_3173500 < baseStart_3173500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173513 : List Nat := [1, 2, 1, 1, 4, 3, 11]
def baseStart_3173513 : Nat := 118140960795 + 3173513 * 2 ^ 59
def prefixEnd_3173513 : Nat := 4983230072969 + 3 ^ 40 * 3173513 * 2
def baseEnd_3173513 : Nat := 20117747312246263573985

theorem tailTrace_3173513 : CollatzResearch.WordTrace tailWord_3173513 prefixEnd_3173513 20117747312246263573985 := by
  unfold tailWord_3173513
  simp only [CollatzResearch.WordTrace]
  refine ⟨115747528151911868715253193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77165018767941245810168795 115747528151911868715253193)
  ·
    refine ⟨86810646113933901536439895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115747528151911868715253193 86810646113933901536439895)
    ·
      refine ⟨130215969170900852304659843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86810646113933901536439895 130215969170900852304659843)
      ·
        refine ⟨195323953756351278456989765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130215969170900852304659843 195323953756351278456989765)
        ·
          refine ⟨36623241329315864710685581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195323953756351278456989765 36623241329315864710685581)
          ·
            refine ⟨13733715498493449266507093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36623241329315864710685581 13733715498493449266507093)
            ·
              refine ⟨20117747312246263573985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13733715498493449266507093 20117747312246263573985)
              ·
                rfl

theorem cell23_3173513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 11].length) (baseStart_3173513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173513 prefixEnd_3173513 := by exact prefixLift 3173513
  have htrace : WordTrace (prefixWord ++ tailWord_3173513) baseStart_3173513 baseEnd_3173513 := by
    simpa [prefixWord, tailWord_3173513, baseEnd_3173513] using wordTrace_append hprefix tailTrace_3173513
  have hstable : (prefixWord ++ tailWord_3173513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173513).length < 2 ^ (prefixWord ++ tailWord_3173513).sum := by decide
  have hdescent : baseEnd_3173513 < baseStart_3173513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173518 : List Nat := [4, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3173518 : Nat := 118140960795 + 3173518 * 2 ^ 59
def prefixEnd_3173518 : Nat := 4983230072969 + 3 ^ 40 * 3173518 * 2
def baseEnd_3173518 : Nat := 1629540099695219829930263

theorem tailTrace_3173518 : CollatzResearch.WordTrace tailWord_3173518 prefixEnd_3173518 1629540099695219829930263 := by
  unfold tailWord_3173518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14468463814611719321148151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77165140344595836379456805 14468463814611719321148151)
  ·
    refine ⟨21702695721917578981722227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14468463814611719321148151 21702695721917578981722227)
    ·
      refine ⟨32554043582876368472583341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21702695721917578981722227 32554043582876368472583341)
      ·
        refine ⟨12207766343578638177218753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32554043582876368472583341 12207766343578638177218753)
        ·
          refine ⟨9155824757683978632914065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12207766343578638177218753 9155824757683978632914065)
          ·
            refine ⟨6866868568262983974685549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9155824757683978632914065 6866868568262983974685549)
            ·
              refine ⟨2575075713098618990507081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6866868568262983974685549 2575075713098618990507081)
              ·
                refine ⟨1931306784823964242880311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575075713098618990507081 1931306784823964242880311)
                ·
                  refine ⟨2896960177235946364320467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931306784823964242880311 2896960177235946364320467)
                  ·
                    refine ⟨4345440265853919546480701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2896960177235946364320467 4345440265853919546480701)
                    ·
                      refine ⟨1629540099695219829930263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4345440265853919546480701 1629540099695219829930263)
                      ·
                        rfl

theorem cell23_3173518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3173518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173518 prefixEnd_3173518 := by exact prefixLift 3173518
  have htrace : WordTrace (prefixWord ++ tailWord_3173518) baseStart_3173518 baseEnd_3173518 := by
    simpa [prefixWord, tailWord_3173518, baseEnd_3173518] using wordTrace_append hprefix tailTrace_3173518
  have hstable : (prefixWord ++ tailWord_3173518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173518).length < 2 ^ (prefixWord ++ tailWord_3173518).sum := by decide
  have hdescent : baseEnd_3173518 < baseStart_3173518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173530 : List Nat := [3, 1, 1, 5, 1, 1, 1, 10]
def baseStart_3173530 : Nat := 118140960795 + 3173530 * 2 ^ 59
def prefixEnd_3173530 : Nat := 4983230072969 + 3 ^ 40 * 3173530 * 2
def baseEnd_3173530 : Nat := 60353565239373103073341

theorem tailTrace_3173530 : CollatzResearch.WordTrace tailWord_3173530 prefixEnd_3173530 60353565239373103073341 := by
  unfold tailWord_3173530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937037048212570154655511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77165432128566853745748029 28937037048212570154655511)
  ·
    refine ⟨43405555572318855231983267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28937037048212570154655511 43405555572318855231983267)
    ·
      refine ⟨65108333358478282847974901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43405555572318855231983267 65108333358478282847974901)
      ·
        refine ⟨6103906252357339016997647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65108333358478282847974901 6103906252357339016997647)
        ·
          refine ⟨9155859378536008525496471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103906252357339016997647 9155859378536008525496471)
          ·
            refine ⟨13733789067804012788244707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155859378536008525496471 13733789067804012788244707)
            ·
              refine ⟨20600683601706019182367061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13733789067804012788244707 20600683601706019182367061)
              ·
                refine ⟨60353565239373103073341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20600683601706019182367061 60353565239373103073341)
                ·
                  rfl

theorem cell23_3173530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_3173530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173530 prefixEnd_3173530 := by exact prefixLift 3173530
  have htrace : WordTrace (prefixWord ++ tailWord_3173530) baseStart_3173530 baseEnd_3173530 := by
    simpa [prefixWord, tailWord_3173530, baseEnd_3173530] using wordTrace_append hprefix tailTrace_3173530
  have hstable : (prefixWord ++ tailWord_3173530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173530).length < 2 ^ (prefixWord ++ tailWord_3173530).sum := by decide
  have hdescent : baseEnd_3173530 < baseStart_3173530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173581 : List Nat := [1, 6, 2, 2, 1, 2, 1, 8]
def baseStart_3173581 : Nat := 118140960795 + 3173581 * 2 ^ 59
def prefixEnd_3173581 : Nat := 4983230072969 + 3 ^ 40 * 3173581 * 2
def baseEnd_3173581 : Nat := 60354535147276040127499

theorem tailTrace_3173581 : CollatzResearch.WordTrace tailWord_3173581 prefixEnd_3173581 60354535147276040127499 := by
  unfold tailWord_3173581
  simp only [CollatzResearch.WordTrace]
  refine ⟨115750008315665516328728597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77166672210443677552485731 115750008315665516328728597)
  ·
    refine ⟨5425781639796821077909153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115750008315665516328728597 5425781639796821077909153)
    ·
      refine ⟨4069336229847615808431865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5425781639796821077909153 4069336229847615808431865)
      ·
        refine ⟨3052002172385711856323899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4069336229847615808431865 3052002172385711856323899)
        ·
          refine ⟨4578003258578567784485849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052002172385711856323899 4578003258578567784485849)
          ·
            refine ⟨3433502443933925838364387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4578003258578567784485849 3433502443933925838364387)
            ·
              refine ⟨5150253665900888757546581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433502443933925838364387 5150253665900888757546581)
              ·
                refine ⟨60354535147276040127499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5150253665900888757546581 60354535147276040127499)
                ·
                  rfl

theorem cell23_3173581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 8].length) (baseStart_3173581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173581 prefixEnd_3173581 := by exact prefixLift 3173581
  have htrace : WordTrace (prefixWord ++ tailWord_3173581) baseStart_3173581 baseEnd_3173581 := by
    simpa [prefixWord, tailWord_3173581, baseEnd_3173581] using wordTrace_append hprefix tailTrace_3173581
  have hstable : (prefixWord ++ tailWord_3173581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173581).length < 2 ^ (prefixWord ++ tailWord_3173581).sum := by decide
  have hdescent : baseEnd_3173581 < baseStart_3173581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173614 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_3173614 : Nat := 118140960795 + 3173614 * 2 ^ 59
def prefixEnd_3173614 : Nat := 4983230072969 + 3 ^ 40 * 3173614 * 2
def baseEnd_3173614 : Nat := 1629589393838051454329821

theorem tailTrace_3173614 : CollatzResearch.WordTrace tailWord_3173614 prefixEnd_3173614 1629589393838051454329821 := by
  unfold tailWord_3173614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14468901490568245370584987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77167474616363975309786597 14468901490568245370584987)
  ·
    refine ⟨21703352235852368055877481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14468901490568245370584987 21703352235852368055877481)
    ·
      refine ⟨16277514176889276041908111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21703352235852368055877481 16277514176889276041908111)
      ·
        refine ⟨24416271265333914062862167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16277514176889276041908111 24416271265333914062862167)
        ·
          refine ⟨36624406898000871094293251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24416271265333914062862167 36624406898000871094293251)
          ·
            refine ⟨54936610347001306641439877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36624406898000871094293251 54936610347001306641439877)
            ·
              refine ⟨10300614440062744995269977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54936610347001306641439877 10300614440062744995269977)
              ·
                refine ⟨7725460830047058746452483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10300614440062744995269977 7725460830047058746452483)
                ·
                  refine ⟨11588191245070588119678725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7725460830047058746452483 11588191245070588119678725)
                  ·
                    refine ⟨2172785858450735272439761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11588191245070588119678725 2172785858450735272439761)
                    ·
                      refine ⟨1629589393838051454329821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172785858450735272439761 1629589393838051454329821)
                      ·
                        rfl

theorem cell23_3173614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_3173614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173614 prefixEnd_3173614 := by exact prefixLift 3173614
  have htrace : WordTrace (prefixWord ++ tailWord_3173614) baseStart_3173614 baseEnd_3173614 := by
    simpa [prefixWord, tailWord_3173614, baseEnd_3173614] using wordTrace_append hprefix tailTrace_3173614
  have hstable : (prefixWord ++ tailWord_3173614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173614).length < 2 ^ (prefixWord ++ tailWord_3173614).sum := by decide
  have hdescent : baseEnd_3173614 < baseStart_3173614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173631 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 2, 2, 2]
def baseStart_3173631 : Nat := 118140960795 + 3173631 * 2 ^ 59
def prefixEnd_3173631 : Nat := 4983230072969 + 3 ^ 40 * 3173631 * 2
def baseEnd_3173631 : Nat := 1629598123009177887817243

theorem tailTrace_3173631 : CollatzResearch.WordTrace tailWord_3173631 prefixEnd_3173631 1629598123009177887817243 := by
  unfold tailWord_3173631
  simp only [CollatzResearch.WordTrace]
  refine ⟨115751831965484374868048747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77167887976989583245365831 115751831965484374868048747)
  ·
    refine ⟨173627747948226562302073121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115751831965484374868048747 173627747948226562302073121)
    ·
      refine ⟨130220810961169921726554841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173627747948226562302073121 130220810961169921726554841)
      ·
        refine ⟨97665608220877441294916131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130220810961169921726554841 97665608220877441294916131)
        ·
          refine ⟨146498412331316161942374197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97665608220877441294916131 146498412331316161942374197)
          ·
            refine ⟨13734226156060890182097581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146498412331316161942374197 13734226156060890182097581)
            ·
              refine ⟨5150334808522833818286593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13734226156060890182097581 5150334808522833818286593)
              ·
                refine ⟨3862751106392125363714945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150334808522833818286593 3862751106392125363714945)
                ·
                  refine ⟨2897063329794094022786209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862751106392125363714945 2897063329794094022786209)
                  ·
                    refine ⟨2172797497345570517089657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2897063329794094022786209 2172797497345570517089657)
                    ·
                      refine ⟨1629598123009177887817243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172797497345570517089657 1629598123009177887817243)
                      ·
                        rfl

theorem cell23_3173631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_3173631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173631 prefixEnd_3173631 := by exact prefixLift 3173631
  have htrace : WordTrace (prefixWord ++ tailWord_3173631) baseStart_3173631 baseEnd_3173631 := by
    simpa [prefixWord, tailWord_3173631, baseEnd_3173631] using wordTrace_append hprefix tailTrace_3173631
  have hstable : (prefixWord ++ tailWord_3173631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173631).length < 2 ^ (prefixWord ++ tailWord_3173631).sum := by decide
  have hdescent : baseEnd_3173631 < baseStart_3173631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173637 : List Nat := [1, 3, 1, 1, 2, 1, 3, 6, 5]
def baseStart_3173637 : Nat := 118140960795 + 3173637 * 2 ^ 59
def prefixEnd_3173637 : Nat := 4983230072969 + 3 ^ 40 * 3173637 * 2
def baseEnd_3173637 : Nat := 181066800432567207149135

theorem tailTrace_3173637 : CollatzResearch.WordTrace tailWord_3173637 prefixEnd_3173637 181066800432567207149135 := by
  unfold tailWord_3173637
  simp only [CollatzResearch.WordTrace]
  refine ⟨115752050803462637892767165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77168033868975091928511443 115752050803462637892767165)
  ·
    refine ⟨43407019051298489209787687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115752050803462637892767165 43407019051298489209787687)
    ·
      refine ⟨65110528576947733814681531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43407019051298489209787687 65110528576947733814681531)
      ·
        refine ⟨97665792865421600722022297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65110528576947733814681531 97665792865421600722022297)
        ·
          refine ⟨73249344649066200541516723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97665792865421600722022297 73249344649066200541516723)
          ·
            refine ⟨109874016973599300812275085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73249344649066200541516723 109874016973599300812275085)
            ·
              refine ⟨41202756365099737804603157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109874016973599300812275085 41202756365099737804603157)
              ·
                refine ⟨1931379204614050209590773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41202756365099737804603157 1931379204614050209590773)
                ·
                  refine ⟨181066800432567207149135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1931379204614050209590773 181066800432567207149135)
                  ·
                    rfl

theorem cell23_3173637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_3173637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173637 prefixEnd_3173637 := by exact prefixLift 3173637
  have htrace : WordTrace (prefixWord ++ tailWord_3173637) baseStart_3173637 baseEnd_3173637 := by
    simpa [prefixWord, tailWord_3173637, baseEnd_3173637] using wordTrace_append hprefix tailTrace_3173637
  have hstable : (prefixWord ++ tailWord_3173637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173637).length < 2 ^ (prefixWord ++ tailWord_3173637).sum := by decide
  have hdescent : baseEnd_3173637 < baseStart_3173637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173684 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_3173684 : Nat := 118140960795 + 3173684 * 2 ^ 59
def prefixEnd_3173684 : Nat := 4983230072969 + 3 ^ 40 * 3173684 * 2
def baseEnd_3173684 : Nat := 543208445827955393484833

theorem tailTrace_3173684 : CollatzResearch.WordTrace tailWord_3173684 prefixEnd_3173684 543208445827955393484833 := by
  unfold tailWord_3173684
  simp only [CollatzResearch.WordTrace]
  refine ⟨57876882517146182459864053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77169176689528243279818737 57876882517146182459864053)
  ·
    refine ⟨5425957735982454605612255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57876882517146182459864053 5425957735982454605612255)
    ·
      refine ⟨8138936603973681908418383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5425957735982454605612255 8138936603973681908418383)
      ·
        refine ⟨12208404905960522862627575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8138936603973681908418383 12208404905960522862627575)
        ·
          refine ⟨18312607358940784293941363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12208404905960522862627575 18312607358940784293941363)
          ·
            refine ⟨27468911038411176440912045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18312607358940784293941363 27468911038411176440912045)
            ·
              refine ⟨10300841639404191165342017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27468911038411176440912045 10300841639404191165342017)
              ·
                refine ⟨7725631229553143374006513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10300841639404191165342017 7725631229553143374006513)
                ·
                  refine ⟨5794223422164857530504885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725631229553143374006513 5794223422164857530504885)
                  ·
                    refine ⟨543208445827955393484833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5794223422164857530504885 543208445827955393484833)
                    ·
                      rfl

theorem cell23_3173684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_3173684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173684 prefixEnd_3173684 := by exact prefixLift 3173684
  have htrace : WordTrace (prefixWord ++ tailWord_3173684) baseStart_3173684 baseEnd_3173684 := by
    simpa [prefixWord, tailWord_3173684, baseEnd_3173684] using wordTrace_append hprefix tailTrace_3173684
  have hstable : (prefixWord ++ tailWord_3173684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173684).length < 2 ^ (prefixWord ++ tailWord_3173684).sum := by decide
  have hdescent : baseEnd_3173684 < baseStart_3173684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173757 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_3173757 : Nat := 118140960795 + 3173757 * 2 ^ 59
def prefixEnd_3173757 : Nat := 4983230072969 + 3 ^ 40 * 3173757 * 2
def baseEnd_3173757 : Nat := 543220940523881464947221

theorem tailTrace_3173757 : CollatzResearch.WordTrace tailWord_3173757 prefixEnd_3173757 543220940523881464947221 := by
  unfold tailWord_3173757
  simp only [CollatzResearch.WordTrace]
  refine ⟨115756427563027898387135525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77170951708685265591423683 115756427563027898387135525)
  ·
    refine ⟨21704330168067730947587911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115756427563027898387135525 21704330168067730947587911)
    ·
      refine ⟨32556495252101596421381867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21704330168067730947587911 32556495252101596421381867)
      ·
        refine ⟨48834742878152394632072801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32556495252101596421381867 48834742878152394632072801)
        ·
          refine ⟨36626057158614295974054601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48834742878152394632072801 36626057158614295974054601)
          ·
            refine ⟨27469542868960721980540951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36626057158614295974054601 27469542868960721980540951)
            ·
              refine ⟨41204314303441082970811427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27469542868960721980540951 41204314303441082970811427)
              ·
                refine ⟨61806471455161624456217141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41204314303441082970811427 61806471455161624456217141)
                ·
                  refine ⟨5794356698921402292770357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61806471455161624456217141 5794356698921402292770357)
                  ·
                    refine ⟨543220940523881464947221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5794356698921402292770357 543220940523881464947221)
                    ·
                      rfl

theorem cell23_3173757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_3173757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173757 prefixEnd_3173757 := by exact prefixLift 3173757
  have htrace : WordTrace (prefixWord ++ tailWord_3173757) baseStart_3173757 baseEnd_3173757 := by
    simpa [prefixWord, tailWord_3173757, baseEnd_3173757] using wordTrace_append hprefix tailTrace_3173757
  have hstable : (prefixWord ++ tailWord_3173757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173757).length < 2 ^ (prefixWord ++ tailWord_3173757).sum := by decide
  have hdescent : baseEnd_3173757 < baseStart_3173757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173781 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_3173781 : Nat := 118140960795 + 3173781 * 2 ^ 59
def prefixEnd_3173781 : Nat := 4983230072969 + 3 ^ 40 * 3173781 * 2
def baseEnd_3173781 : Nat := 1629675145107352300941553

theorem tailTrace_3173781 : CollatzResearch.WordTrace tailWord_3173781 prefixEnd_3173781 1629675145107352300941553 := by
  unfold tailWord_3173781
  simp only [CollatzResearch.WordTrace]
  refine ⟨115757302914940950486009197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77171535276627300324006131 115757302914940950486009197)
  ·
    refine ⟨43408988593102856432253449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115757302914940950486009197 43408988593102856432253449)
    ·
      refine ⟨32556741444827142324190087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43408988593102856432253449 32556741444827142324190087)
      ·
        refine ⟨48835112167240713486285131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32556741444827142324190087 48835112167240713486285131)
        ·
          refine ⟨73252668250861070229427697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48835112167240713486285131 73252668250861070229427697)
          ·
            refine ⟨54939501188145802672070773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73252668250861070229427697 54939501188145802672070773)
            ·
              refine ⟨5150578236388669000506635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54939501188145802672070773 5150578236388669000506635)
              ·
                refine ⟨7725867354583003500759953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5150578236388669000506635 7725867354583003500759953)
                ·
                  refine ⟨5794400515937252625569965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7725867354583003500759953 5794400515937252625569965)
                  ·
                    refine ⟨2172900193476469734588737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5794400515937252625569965 2172900193476469734588737)
                    ·
                      refine ⟨1629675145107352300941553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2172900193476469734588737 1629675145107352300941553)
                      ·
                        rfl

theorem cell23_3173781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_3173781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173781 prefixEnd_3173781 := by exact prefixLift 3173781
  have htrace : WordTrace (prefixWord ++ tailWord_3173781) baseStart_3173781 baseEnd_3173781 := by
    simpa [prefixWord, tailWord_3173781, baseEnd_3173781] using wordTrace_append hprefix tailTrace_3173781
  have hstable : (prefixWord ++ tailWord_3173781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173781).length < 2 ^ (prefixWord ++ tailWord_3173781).sum := by decide
  have hdescent : baseEnd_3173781 < baseStart_3173781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173791 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 1, 5]
def baseStart_3173791 : Nat := 118140960795 + 3173791 * 2 ^ 59
def prefixEnd_3173791 : Nat := 4983230072969 + 3 ^ 40 * 3173791 * 2
def baseEnd_3173791 : Nat := 543226759971299087272169

theorem tailTrace_3173791 : CollatzResearch.WordTrace tailWord_3173791 prefixEnd_3173791 543226759971299087272169 := by
  unfold tailWord_3173791
  simp only [CollatzResearch.WordTrace]
  refine ⟨115757667644904722193873227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77171778429936481462582151 115757667644904722193873227)
  ·
    refine ⟨173636501467357083290809841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115757667644904722193873227 173636501467357083290809841)
    ·
      refine ⟨130227376100517812468107381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173636501467357083290809841 130227376100517812468107381)
      ·
        refine ⟨12208816509423544918885067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130227376100517812468107381 12208816509423544918885067)
        ·
          refine ⟨18313224764135317378327601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12208816509423544918885067 18313224764135317378327601)
          ·
            refine ⟨13734918573101488033745701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18313224764135317378327601 13734918573101488033745701)
            ·
              refine ⟨2575297232456529006327319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13734918573101488033745701 2575297232456529006327319)
              ·
                refine ⟨3862945848684793509490979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575297232456529006327319 3862945848684793509490979)
                ·
                  refine ⟨5794418773027190264236469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862945848684793509490979 5794418773027190264236469)
                  ·
                    refine ⟨543226759971299087272169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5794418773027190264236469 543226759971299087272169)
                    ·
                      rfl

theorem cell23_3173791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 1, 5].length) (baseStart_3173791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173791 prefixEnd_3173791 := by exact prefixLift 3173791
  have htrace : WordTrace (prefixWord ++ tailWord_3173791) baseStart_3173791 baseEnd_3173791 := by
    simpa [prefixWord, tailWord_3173791, baseEnd_3173791] using wordTrace_append hprefix tailTrace_3173791
  have hstable : (prefixWord ++ tailWord_3173791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173791).length < 2 ^ (prefixWord ++ tailWord_3173791).sum := by decide
  have hdescent : baseEnd_3173791 < baseStart_3173791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173805 : List Nat := [1, 5, 2, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3173805 : Nat := 118140960795 + 3173805 * 2 ^ 59
def prefixEnd_3173805 : Nat := 4983230072969 + 3 ^ 40 * 3173805 * 2
def baseEnd_3173805 : Nat := 1629687468643060207041443

theorem tailTrace_3173805 : CollatzResearch.WordTrace tailWord_3173805 prefixEnd_3173805 1629687468643060207041443 := by
  unfold tailWord_3173805
  simp only [CollatzResearch.WordTrace]
  refine ⟨115758178266854002584882869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77172118844569335056588579 115758178266854002584882869)
  ·
    refine ⟨10852329212517562742332769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115758178266854002584882869 10852329212517562742332769)
    ·
      refine ⟨8139246909388172056749577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10852329212517562742332769 8139246909388172056749577)
      ·
        refine ⟨6104435182041129042562183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139246909388172056749577 6104435182041129042562183)
        ·
          refine ⟨9156652773061693563843275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104435182041129042562183 9156652773061693563843275)
          ·
            refine ⟨13734979159592540345764913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156652773061693563843275 13734979159592540345764913)
            ·
              refine ⟨10301234369694405259323685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13734979159592540345764913 10301234369694405259323685)
              ·
                refine ⟨1931481444317700986123191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10301234369694405259323685 1931481444317700986123191)
                ·
                  refine ⟨2897222166476551479184787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931481444317700986123191 2897222166476551479184787)
                  ·
                    refine ⟨4345833249714827218777181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2897222166476551479184787 4345833249714827218777181)
                    ·
                      refine ⟨1629687468643060207041443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4345833249714827218777181 1629687468643060207041443)
                      ·
                        rfl

theorem cell23_3173805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3173805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173805 prefixEnd_3173805 := by exact prefixLift 3173805
  have htrace : WordTrace (prefixWord ++ tailWord_3173805) baseStart_3173805 baseEnd_3173805 := by
    simpa [prefixWord, tailWord_3173805, baseEnd_3173805] using wordTrace_append hprefix tailTrace_3173805
  have hstable : (prefixWord ++ tailWord_3173805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173805).length < 2 ^ (prefixWord ++ tailWord_3173805).sum := by decide
  have hdescent : baseEnd_3173805 < baseStart_3173805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173807 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_3173807 : Nat := 118140960795 + 3173807 * 2 ^ 59
def prefixEnd_3173807 : Nat := 4983230072969 + 3 ^ 40 * 3173807 * 2
def baseEnd_3173807 : Nat := 1629688495604369199216433

theorem tailTrace_3173807 : CollatzResearch.WordTrace tailWord_3173807 prefixEnd_3173807 1629688495604369199216433 := by
  unfold tailWord_3173807
  simp only [CollatzResearch.WordTrace]
  refine ⟨115758251212846756926455675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77172167475231171284303783 115758251212846756926455675)
  ·
    refine ⟨173637376819270135389683513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115758251212846756926455675 173637376819270135389683513)
    ·
      refine ⟨130228032614452601542262635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173637376819270135389683513 130228032614452601542262635)
      ·
        refine ⟨195342048921678902313393953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130228032614452601542262635 195342048921678902313393953)
        ·
          refine ⟨146506536691259176735045465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195342048921678902313393953 146506536691259176735045465)
          ·
            refine ⟨109879902518444382551284099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146506536691259176735045465 109879902518444382551284099)
            ·
              refine ⟨164819853777666573826926149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109879902518444382551284099 164819853777666573826926149)
              ·
                refine ⟨30903722583312482592548653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164819853777666573826926149 30903722583312482592548653)
                ·
                  refine ⟨11588895968742180972205745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30903722583312482592548653 11588895968742180972205745)
                  ·
                    refine ⟨8691671976556635729154309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11588895968742180972205745 8691671976556635729154309)
                    ·
                      refine ⟨1629688495604369199216433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8691671976556635729154309 1629688495604369199216433)
                      ·
                        rfl

theorem cell23_3173807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_3173807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173807 prefixEnd_3173807 := by exact prefixLift 3173807
  have htrace : WordTrace (prefixWord ++ tailWord_3173807) baseStart_3173807 baseEnd_3173807 := by
    simpa [prefixWord, tailWord_3173807, baseEnd_3173807] using wordTrace_append hprefix tailTrace_3173807
  have hstable : (prefixWord ++ tailWord_3173807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173807).length < 2 ^ (prefixWord ++ tailWord_3173807).sum := by decide
  have hdescent : baseEnd_3173807 < baseStart_3173807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173824 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4]
def baseStart_3173824 : Nat := 118140960795 + 3173824 * 2 ^ 59
def prefixEnd_3173824 : Nat := 4983230072969 + 3 ^ 40 * 3173824 * 2
def baseEnd_3173824 : Nat := 1629697224775495632703855

theorem tailTrace_3173824 : CollatzResearch.WordTrace tailWord_3173824 prefixEnd_3173824 1629697224775495632703855 := by
  unfold tailWord_3173824
  simp only [CollatzResearch.WordTrace]
  refine ⟨57879435626892584414912263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77172580835856779219883017 57879435626892584414912263)
  ·
    refine ⟨86819153440338876622368395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57879435626892584414912263 86819153440338876622368395)
    ·
      refine ⟨130228730160508314933552593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86819153440338876622368395 130228730160508314933552593)
      ·
        refine ⟨97671547620381236200164445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130228730160508314933552593 97671547620381236200164445)
        ·
          refine ⟨36626830357642963575061667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97671547620381236200164445 36626830357642963575061667)
          ·
            refine ⟨54940245536464445362592501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36626830357642963575061667 54940245536464445362592501)
            ·
              refine ⟨5150648019043541752743047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54940245536464445362592501 5150648019043541752743047)
              ·
                refine ⟨7725972028565312629114571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5150648019043541752743047 7725972028565312629114571)
                ·
                  refine ⟨11588958042847968943671857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7725972028565312629114571 11588958042847968943671857)
                  ·
                    refine ⟨8691718532135976707753893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11588958042847968943671857 8691718532135976707753893)
                    ·
                      refine ⟨1629697224775495632703855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8691718532135976707753893 1629697224775495632703855)
                      ·
                        rfl

theorem cell23_3173824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_3173824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173824 prefixEnd_3173824 := by exact prefixLift 3173824
  have htrace : WordTrace (prefixWord ++ tailWord_3173824) baseStart_3173824 baseEnd_3173824 := by
    simpa [prefixWord, tailWord_3173824, baseEnd_3173824] using wordTrace_append hprefix tailTrace_3173824
  have hstable : (prefixWord ++ tailWord_3173824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173824).length < 2 ^ (prefixWord ++ tailWord_3173824).sum := by decide
  have hdescent : baseEnd_3173824 < baseStart_3173824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173828 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3173828 : Nat := 118140960795 + 3173828 * 2 ^ 59
def prefixEnd_3173828 : Nat := 4983230072969 + 3 ^ 40 * 3173828 * 2
def baseEnd_3173828 : Nat := 1629699278698113617053837

theorem tailTrace_3173828 : CollatzResearch.WordTrace tailWord_3173828 prefixEnd_3173828 1629699278698113617053837 := by
  unfold tailWord_3173828
  simp only [CollatzResearch.WordTrace]
  refine ⟨57879508572885338756485069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77172678097180451675313425 57879508572885338756485069)
  ·
    refine ⟨21704815714832002033681901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57879508572885338756485069 21704815714832002033681901)
    ·
      refine ⟨8139305893062000762630713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21704815714832002033681901 8139305893062000762630713)
      ·
        refine ⟨6104479419796500571973035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139305893062000762630713 6104479419796500571973035)
        ·
          refine ⟨9156719129694750857959553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104479419796500571973035 9156719129694750857959553)
          ·
            refine ⟨6867539347271063143469665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9156719129694750857959553 6867539347271063143469665)
            ·
              refine ⟨5150654510453297357602249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6867539347271063143469665 5150654510453297357602249)
              ·
                refine ⟨3862990882839973018201687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150654510453297357602249 3862990882839973018201687)
                ·
                  refine ⟨5794486324259959527302531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862990882839973018201687 5794486324259959527302531)
                  ·
                    refine ⟨8691729486389939290953797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5794486324259959527302531 8691729486389939290953797)
                    ·
                      refine ⟨1629699278698113617053837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8691729486389939290953797 1629699278698113617053837)
                      ·
                        rfl

theorem cell23_3173828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3173828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173828 prefixEnd_3173828 := by exact prefixLift 3173828
  have htrace : WordTrace (prefixWord ++ tailWord_3173828) baseStart_3173828 baseEnd_3173828 := by
    simpa [prefixWord, tailWord_3173828, baseEnd_3173828] using wordTrace_append hprefix tailTrace_3173828
  have hstable : (prefixWord ++ tailWord_3173828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173828).length < 2 ^ (prefixWord ++ tailWord_3173828).sum := by decide
  have hdescent : baseEnd_3173828 < baseStart_3173828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173831 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_3173831 : Nat := 118140960795 + 3173831 * 2 ^ 59
def prefixEnd_3173831 : Nat := 4983230072969 + 3 ^ 40 * 3173831 * 2
def baseEnd_3173831 : Nat := 1629700819140077105316323

theorem tailTrace_3173831 : CollatzResearch.WordTrace tailWord_3173831 prefixEnd_3173831 1629700819140077105316323 := by
  unfold tailWord_3173831
  simp only [CollatzResearch.WordTrace]
  refine ⟨115759126564759809025329347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77172751043173206016886231 115759126564759809025329347)
  ·
    refine ⟨173638689847139713537994021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115759126564759809025329347 173638689847139713537994021)
    ·
      refine ⟨32557254346338696288373879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173638689847139713537994021 32557254346338696288373879)
      ·
        refine ⟨48835881519508044432560819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32557254346338696288373879 48835881519508044432560819)
        ·
          refine ⟨73253822279262066648841229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48835881519508044432560819 73253822279262066648841229)
          ·
            refine ⟨27470183354723274993315461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73253822279262066648841229 27470183354723274993315461)
            ·
              refine ⟨5150659379010614061246649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27470183354723274993315461 5150659379010614061246649)
              ·
                refine ⟨3862994534257960545934987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150659379010614061246649 3862994534257960545934987)
                ·
                  refine ⟨5794491801386940818902481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862994534257960545934987 5794491801386940818902481)
                  ·
                    refine ⟨4345868851040205614176861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794491801386940818902481 4345868851040205614176861)
                    ·
                      refine ⟨1629700819140077105316323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4345868851040205614176861 1629700819140077105316323)
                      ·
                        rfl

theorem cell23_3173831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_3173831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173831 prefixEnd_3173831 := by exact prefixLift 3173831
  have htrace : WordTrace (prefixWord ++ tailWord_3173831) baseStart_3173831 baseEnd_3173831 := by
    simpa [prefixWord, tailWord_3173831, baseEnd_3173831] using wordTrace_append hprefix tailTrace_3173831
  have hstable : (prefixWord ++ tailWord_3173831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173831).length < 2 ^ (prefixWord ++ tailWord_3173831).sum := by decide
  have hdescent : baseEnd_3173831 < baseStart_3173831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173834 : List Nat := [3, 1, 2, 1, 2, 3, 4, 7]
def baseStart_3173834 : Nat := 118140960795 + 3173834 * 2 ^ 59
def prefixEnd_3173834 : Nat := 4983230072969 + 3 ^ 40 * 3173834 * 2
def baseEnd_3173834 : Nat := 60359346651186688651067

theorem tailTrace_3173834 : CollatzResearch.WordTrace tailWord_3173834 prefixEnd_3173834 60359346651186688651067 := by
  unfold tailWord_3173834
  simp only [CollatzResearch.WordTrace]
  refine ⟨28939808995937235134422139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77172823989165960358459037 28939808995937235134422139)
  ·
    refine ⟨43409713493905852701633209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28939808995937235134422139 43409713493905852701633209)
    ·
      refine ⟨32557285120429389526224907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43409713493905852701633209 32557285120429389526224907)
      ·
        refine ⟨48835927680644084289337361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32557285120429389526224907 48835927680644084289337361)
        ·
          refine ⟨36626945760483063217003021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48835927680644084289337361 36626945760483063217003021)
          ·
            refine ⟨13735104660181148706376133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36626945760483063217003021 13735104660181148706376133)
            ·
              refine ⟨2575332123783965382445525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13735104660181148706376133 2575332123783965382445525)
              ·
                refine ⟨60359346651186688651067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2575332123783965382445525 60359346651186688651067)
                ·
                  rfl

theorem cell23_3173834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_3173834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173834 prefixEnd_3173834 := by exact prefixLift 3173834
  have htrace : WordTrace (prefixWord ++ tailWord_3173834) baseStart_3173834 baseEnd_3173834 := by
    simpa [prefixWord, tailWord_3173834, baseEnd_3173834] using wordTrace_append hprefix tailTrace_3173834
  have hstable : (prefixWord ++ tailWord_3173834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173834).length < 2 ^ (prefixWord ++ tailWord_3173834).sum := by decide
  have hdescent : baseEnd_3173834 < baseStart_3173834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3173914 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3173914 : Nat := 118140960795 + 3173914 * 2 ^ 59
def prefixEnd_3173914 : Nat := 4983230072969 + 3 ^ 40 * 3173914 * 2
def baseEnd_3173914 : Nat := 1629743438034400280578441

theorem tailTrace_3173914 : CollatzResearch.WordTrace tailWord_3173914 prefixEnd_3173914 1629743438034400280578441 := by
  unfold tailWord_3173914
  simp only [CollatzResearch.WordTrace]
  refine ⟨28940538455864778550150199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77174769215639409467067197 28940538455864778550150199)
  ·
    refine ⟨43410807683797167825225299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28940538455864778550150199 43410807683797167825225299)
    ·
      refine ⟨65116211525695751737837949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43410807683797167825225299 65116211525695751737837949)
      ·
        refine ⟨24418579322135906901689231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65116211525695751737837949 24418579322135906901689231)
        ·
          refine ⟨36627868983203860352533847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24418579322135906901689231 36627868983203860352533847)
          ·
            refine ⟨54941803474805790528800771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36627868983203860352533847 54941803474805790528800771)
            ·
              refine ⟨82412705212208685793201157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54941803474805790528800771 82412705212208685793201157)
              ·
                refine ⟨15452382227289128586225217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82412705212208685793201157 15452382227289128586225217)
                ·
                  refine ⟨11589286670466846439668913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15452382227289128586225217 11589286670466846439668913)
                  ·
                    refine ⟨8691965002850134829751685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11589286670466846439668913 8691965002850134829751685)
                    ·
                      refine ⟨1629743438034400280578441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8691965002850134829751685 1629743438034400280578441)
                      ·
                        rfl

theorem cell23_3173914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3173914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3173914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3173914 prefixEnd_3173914 := by exact prefixLift 3173914
  have htrace : WordTrace (prefixWord ++ tailWord_3173914) baseStart_3173914 baseEnd_3173914 := by
    simpa [prefixWord, tailWord_3173914, baseEnd_3173914] using wordTrace_append hprefix tailTrace_3173914
  have hstable : (prefixWord ++ tailWord_3173914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3173914).length < 2 ^ (prefixWord ++ tailWord_3173914).sum := by decide
  have hdescent : baseEnd_3173914 < baseStart_3173914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3173914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174011 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 3]
def baseStart_3174011 : Nat := 118140960795 + 3174011 * 2 ^ 59
def prefixEnd_3174011 : Nat := 4983230072969 + 3 ^ 40 * 3174011 * 2
def baseEnd_3174011 : Nat := 1629793245657886401065495

theorem tailTrace_3174011 : CollatzResearch.WordTrace tailWord_3174011 prefixEnd_3174011 1629793245657886401065495 := by
  unfold tailWord_3174011
  simp only [CollatzResearch.WordTrace]
  refine ⟨115765691704107699766881887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77177127802738466511254591 115765691704107699766881887)
  ·
    refine ⟨173648537556161549650322831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115765691704107699766881887 173648537556161549650322831)
    ·
      refine ⟨260472806334242324475484247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173648537556161549650322831 260472806334242324475484247)
      ·
        refine ⟨390709209501363486713226371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260472806334242324475484247 390709209501363486713226371)
        ·
          refine ⟨586063814252045230069839557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390709209501363486713226371 586063814252045230069839557)
          ·
            refine ⟨109886965172258480638094917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 586063814252045230069839557 109886965172258480638094917)
            ·
              refine ⟨20603805969798465119642797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109886965172258480638094917 20603805969798465119642797)
              ·
                refine ⟨7726427238674424419866049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20603805969798465119642797 7726427238674424419866049)
                ·
                  refine ⟨5794820429005818314899537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7726427238674424419866049 5794820429005818314899537)
                  ·
                    refine ⟨4346115321754363736174653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794820429005818314899537 4346115321754363736174653)
                    ·
                      refine ⟨1629793245657886401065495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4346115321754363736174653 1629793245657886401065495)
                      ·
                        rfl

theorem cell23_3174011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 3].length) (baseStart_3174011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174011 prefixEnd_3174011 := by exact prefixLift 3174011
  have htrace : WordTrace (prefixWord ++ tailWord_3174011) baseStart_3174011 baseEnd_3174011 := by
    simpa [prefixWord, tailWord_3174011, baseEnd_3174011] using wordTrace_append hprefix tailTrace_3174011
  have hstable : (prefixWord ++ tailWord_3174011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174011).length < 2 ^ (prefixWord ++ tailWord_3174011).sum := by decide
  have hdescent : baseEnd_3174011 < baseStart_3174011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174048 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 6]
def baseStart_3174048 : Nat := 118140960795 + 3174048 * 2 ^ 59
def prefixEnd_3174048 : Nat := 4983230072969 + 3 ^ 40 * 3174048 * 2
def baseEnd_3174048 : Nat := 181090249382455861811425

theorem tailTrace_3174048 : CollatzResearch.WordTrace tailWord_3174048 prefixEnd_3174048 181090249382455861811425 := by
  unfold tailWord_3174048
  simp only [CollatzResearch.WordTrace]
  refine ⟨57883520602486827542989399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77178027469982436723985865 57883520602486827542989399)
  ·
    refine ⟨86825280903730241314484099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57883520602486827542989399 86825280903730241314484099)
    ·
      refine ⟨130237921355595361971726149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86825280903730241314484099 130237921355595361971726149)
      ·
        refine ⟨24419610254174130369698653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130237921355595361971726149 24419610254174130369698653)
        ·
          refine ⟨9157353845315298888636995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24419610254174130369698653 9157353845315298888636995)
          ·
            refine ⟨13736030767972948332955493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157353845315298888636995 13736030767972948332955493)
            ·
              refine ⟨2575505768994927812429155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13736030767972948332955493 2575505768994927812429155)
              ·
                refine ⟨3863258653492391718643733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575505768994927812429155 3863258653492391718643733)
                ·
                  refine ⟨181090249382455861811425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3863258653492391718643733 181090249382455861811425)
                  ·
                    rfl

theorem cell23_3174048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 6].length) (baseStart_3174048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174048 prefixEnd_3174048 := by exact prefixLift 3174048
  have htrace : WordTrace (prefixWord ++ tailWord_3174048) baseStart_3174048 baseEnd_3174048 := by
    simpa [prefixWord, tailWord_3174048, baseEnd_3174048] using wordTrace_append hprefix tailTrace_3174048
  have hstable : (prefixWord ++ tailWord_3174048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174048).length < 2 ^ (prefixWord ++ tailWord_3174048).sum := by decide
  have hdescent : baseEnd_3174048 < baseStart_3174048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174062 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3174062 : Nat := 118140960795 + 3174062 * 2 ^ 59
def prefixEnd_3174062 : Nat := 4983230072969 + 3 ^ 40 * 3174062 * 2
def baseEnd_3174062 : Nat := 1629819433171265701527761

theorem tailTrace_3174062 : CollatzResearch.WordTrace tailWord_3174062 prefixEnd_3174062 1629819433171265701527761 := by
  unfold tailWord_3174062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14470943978365366934623555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77178367884615290317992293 14470943978365366934623555)
  ·
    refine ⟨21706415967548050401935333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14470943978365366934623555 21706415967548050401935333)
    ·
      refine ⟨4069952993915259450362875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21706415967548050401935333 4069952993915259450362875)
      ·
        refine ⟨6104929490872889175544313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069952993915259450362875 6104929490872889175544313)
        ·
          refine ⟨4578697118154666881658235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104929490872889175544313 4578697118154666881658235)
          ·
            refine ⟨6868045677232000322487353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578697118154666881658235 6868045677232000322487353)
            ·
              refine ⟨5151034257924000241865515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6868045677232000322487353 5151034257924000241865515)
              ·
                refine ⟨7726551386886000362798273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151034257924000241865515 7726551386886000362798273)
                ·
                  refine ⟨5794913540164500272098705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7726551386886000362798273 5794913540164500272098705)
                  ·
                    refine ⟨4346185155123375204074029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5794913540164500272098705 4346185155123375204074029)
                    ·
                      refine ⟨1629819433171265701527761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4346185155123375204074029 1629819433171265701527761)
                      ·
                        rfl

theorem cell23_3174062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3174062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174062 prefixEnd_3174062 := by exact prefixLift 3174062
  have htrace : WordTrace (prefixWord ++ tailWord_3174062) baseStart_3174062 baseEnd_3174062 := by
    simpa [prefixWord, tailWord_3174062, baseEnd_3174062] using wordTrace_append hprefix tailTrace_3174062
  have hstable : (prefixWord ++ tailWord_3174062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174062).length < 2 ^ (prefixWord ++ tailWord_3174062).sum := by decide
  have hdescent : baseEnd_3174062 < baseStart_3174062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174086 : List Nat := [6, 1, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3174086 : Nat := 118140960795 + 3174086 * 2 ^ 59
def prefixEnd_3174086 : Nat := 4983230072969 + 3 ^ 40 * 3174086 * 2
def baseEnd_3174086 : Nat := 543277252235657869209217

theorem tailTrace_3174086 : CollatzResearch.WordTrace tailWord_3174086 prefixEnd_3174086 543277252235657869209217 := by
  unfold tailWord_3174086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3617763349338624611745691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77178951452557325050574741 3617763349338624611745691)
  ·
    refine ⟨5426645024007936917618537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3617763349338624611745691 5426645024007936917618537)
    ·
      refine ⟨4069983768005952688213903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5426645024007936917618537 4069983768005952688213903)
      ·
        refine ⟨6104975652008929032320855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069983768005952688213903 6104975652008929032320855)
        ·
          refine ⟨9157463478013393548481283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104975652008929032320855 9157463478013393548481283)
          ·
            refine ⟨13736195217020090322721925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157463478013393548481283 13736195217020090322721925)
            ·
              refine ⟨2575536603191266935510361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13736195217020090322721925 2575536603191266935510361)
              ·
                refine ⟨1931652452393450201632771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575536603191266935510361 1931652452393450201632771)
                ·
                  refine ⟨2897478678590175302449157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931652452393450201632771 2897478678590175302449157)
                  ·
                    refine ⟨543277252235657869209217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2897478678590175302449157 543277252235657869209217)
                    ·
                      rfl

theorem cell23_3174086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3174086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174086 prefixEnd_3174086 := by exact prefixLift 3174086
  have htrace : WordTrace (prefixWord ++ tailWord_3174086) baseStart_3174086 baseEnd_3174086 := by
    simpa [prefixWord, tailWord_3174086, baseEnd_3174086] using wordTrace_append hprefix tailTrace_3174086
  have hstable : (prefixWord ++ tailWord_3174086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174086).length < 2 ^ (prefixWord ++ tailWord_3174086).sum := by decide
  have hdescent : baseEnd_3174086 < baseStart_3174086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174091 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 4, 4]
def baseStart_3174091 : Nat := 118140960795 + 3174091 * 2 ^ 59
def prefixEnd_3174091 : Nat := 4983230072969 + 3 ^ 40 * 3174091 * 2
def baseEnd_3174091 : Nat := 543278108036748696021709

theorem tailTrace_3174091 : CollatzResearch.WordTrace tailWord_3174091 prefixEnd_3174091 543278108036748696021709 := by
  unfold tailWord_3174091
  simp only [CollatzResearch.WordTrace]
  refine ⟨115768609543817873429794127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77179073029211915619862751 115768609543817873429794127)
  ·
    refine ⟨173652914315726810144691191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115768609543817873429794127 173652914315726810144691191)
    ·
      refine ⟨260479371473590215217036787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173652914315726810144691191 260479371473590215217036787)
      ·
        refine ⟨390719057210385322825555181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260479371473590215217036787 390719057210385322825555181)
        ·
          refine ⟨146519646453894496059583193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390719057210385322825555181 146519646453894496059583193)
          ·
            refine ⟨109889734840420872044687395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146519646453894496059583193 109889734840420872044687395)
            ·
              refine ⟨164834602260631308067031093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109889734840420872044687395 164834602260631308067031093)
              ·
                refine ⟨15453243961934185131284165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164834602260631308067031093 15453243961934185131284165)
                ·
                  refine ⟨2897483242862659712115781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15453243961934185131284165 2897483242862659712115781)
                  ·
                    refine ⟨543278108036748696021709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2897483242862659712115781 543278108036748696021709)
                    ·
                      rfl

theorem cell23_3174091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 4].length) (baseStart_3174091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174091 prefixEnd_3174091 := by exact prefixLift 3174091
  have htrace : WordTrace (prefixWord ++ tailWord_3174091) baseStart_3174091 baseEnd_3174091 := by
    simpa [prefixWord, tailWord_3174091, baseEnd_3174091] using wordTrace_append hprefix tailTrace_3174091
  have hstable : (prefixWord ++ tailWord_3174091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174091).length < 2 ^ (prefixWord ++ tailWord_3174091).sum := by decide
  have hdescent : baseEnd_3174091 < baseStart_3174091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174098 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3174098 : Nat := 118140960795 + 3174098 * 2 ^ 59
def prefixEnd_3174098 : Nat := 4983230072969 + 3 ^ 40 * 3174098 * 2
def baseEnd_3174098 : Nat := 1629837918474827560677595

theorem tailTrace_3174098 : CollatzResearch.WordTrace tailWord_3174098 prefixEnd_3174098 1629837918474827560677595 := by
  unfold tailWord_3174098
  simp only [CollatzResearch.WordTrace]
  refine ⟨28942216213698128406324737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77179243236528342416865965 28942216213698128406324737)
  ·
    refine ⟨21706662160273596304743553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28942216213698128406324737 21706662160273596304743553)
    ·
      refine ⟨16279996620205197228557665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21706662160273596304743553 16279996620205197228557665)
      ·
        refine ⟨12209997465153897921418249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16279996620205197228557665 12209997465153897921418249)
        ·
          refine ⟨9157498098865423441063687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12209997465153897921418249 9157498098865423441063687)
          ·
            refine ⟨13736247148298135161595531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157498098865423441063687 13736247148298135161595531)
            ·
              refine ⟨20604370722447202742393297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736247148298135161595531 20604370722447202742393297)
              ·
                refine ⟨15453278041835402056794973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20604370722447202742393297 15453278041835402056794973)
                ·
                  refine ⟨5794979265688275771298115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15453278041835402056794973 5794979265688275771298115)
                  ·
                    refine ⟨8692468898532413656947173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5794979265688275771298115 8692468898532413656947173)
                    ·
                      refine ⟨1629837918474827560677595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8692468898532413656947173 1629837918474827560677595)
                      ·
                        rfl

theorem cell23_3174098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3174098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174098 prefixEnd_3174098 := by exact prefixLift 3174098
  have htrace : WordTrace (prefixWord ++ tailWord_3174098) baseStart_3174098 baseEnd_3174098 := by
    simpa [prefixWord, tailWord_3174098, baseEnd_3174098] using wordTrace_append hprefix tailTrace_3174098
  have hstable : (prefixWord ++ tailWord_3174098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174098).length < 2 ^ (prefixWord ++ tailWord_3174098).sum := by decide
  have hdescent : baseEnd_3174098 < baseStart_3174098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174119 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3174119 : Nat := 118140960795 + 3174119 * 2 ^ 59
def prefixEnd_3174119 : Nat := 4983230072969 + 3 ^ 40 * 3174119 * 2
def baseEnd_3174119 : Nat := 1629848701568571978514999

theorem tailTrace_3174119 : CollatzResearch.WordTrace tailWord_3174119 prefixEnd_3174119 1629848701568571978514999 := by
  unfold tailWord_3174119
  simp only [CollatzResearch.WordTrace]
  refine ⟨115769630787716434211813411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77179753858477622807875607 115769630787716434211813411)
  ·
    refine ⟨173654446181574651317720117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115769630787716434211813411 173654446181574651317720117)
    ·
      refine ⟨16280104329522623561036261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173654446181574651317720117 16280104329522623561036261)
      ·
        refine ⟨3052519561785491917694299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16280104329522623561036261 3052519561785491917694299)
        ·
          refine ⟨4578779342678237876541449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052519561785491917694299 4578779342678237876541449)
          ·
            refine ⟨3434084507008678407406087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4578779342678237876541449 3434084507008678407406087)
            ·
              refine ⟨5151126760513017611109131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434084507008678407406087 5151126760513017611109131)
              ·
                refine ⟨7726690140769526416663697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151126760513017611109131 7726690140769526416663697)
                ·
                  refine ⟨5795017605577144812497773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7726690140769526416663697 5795017605577144812497773)
                  ·
                    refine ⟨2173131602091429304686665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5795017605577144812497773 2173131602091429304686665)
                    ·
                      refine ⟨1629848701568571978514999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173131602091429304686665 1629848701568571978514999)
                      ·
                        rfl

theorem cell23_3174119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3174119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174119 prefixEnd_3174119 := by exact prefixLift 3174119
  have htrace : WordTrace (prefixWord ++ tailWord_3174119) baseStart_3174119 baseEnd_3174119 := by
    simpa [prefixWord, tailWord_3174119, baseEnd_3174119] using wordTrace_append hprefix tailTrace_3174119
  have hstable : (prefixWord ++ tailWord_3174119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174119).length < 2 ^ (prefixWord ++ tailWord_3174119).sum := by decide
  have hdescent : baseEnd_3174119 < baseStart_3174119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174135 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 1, 2, 3]
def baseStart_3174135 : Nat := 118140960795 + 3174135 * 2 ^ 59
def prefixEnd_3174135 : Nat := 4983230072969 + 3 ^ 40 * 3174135 * 2
def baseEnd_3174135 : Nat := 1629856917259043915914925

theorem tailTrace_3174135 : CollatzResearch.WordTrace tailWord_3174135 prefixEnd_3174135 1629856917259043915914925 := by
  unfold tailWord_3174135
  simp only [CollatzResearch.WordTrace]
  refine ⟨115770214355658468944395859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77180142903772312629597239 115770214355658468944395859)
  ·
    refine ⟨173655321533487703416593789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115770214355658468944395859 173655321533487703416593789)
    ·
      refine ⟨65120745575057888781222671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173655321533487703416593789 65120745575057888781222671)
      ·
        refine ⟨97681118362586833171834007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65120745575057888781222671 97681118362586833171834007)
        ·
          refine ⟨146521677543880249757751011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97681118362586833171834007 146521677543880249757751011)
          ·
            refine ⟨219782516315820374636626517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146521677543880249757751011 219782516315820374636626517)
            ·
              refine ⟨2575576363076020015272967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 219782516315820374636626517 2575576363076020015272967)
              ·
                refine ⟨3863364544614030022909451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575576363076020015272967 3863364544614030022909451)
                ·
                  refine ⟨5795046816921045034364177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863364544614030022909451 5795046816921045034364177)
                  ·
                    refine ⟨4346285112690783775773133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5795046816921045034364177 4346285112690783775773133)
                    ·
                      refine ⟨1629856917259043915914925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4346285112690783775773133 1629856917259043915914925)
                      ·
                        rfl

theorem cell23_3174135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_3174135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174135 prefixEnd_3174135 := by exact prefixLift 3174135
  have htrace : WordTrace (prefixWord ++ tailWord_3174135) baseStart_3174135 baseEnd_3174135 := by
    simpa [prefixWord, tailWord_3174135, baseEnd_3174135] using wordTrace_append hprefix tailTrace_3174135
  have hstable : (prefixWord ++ tailWord_3174135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174135).length < 2 ^ (prefixWord ++ tailWord_3174135).sum := by decide
  have hdescent : baseEnd_3174135 < baseStart_3174135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174162 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3174162 : Nat := 118140960795 + 3174162 * 2 ^ 59
def prefixEnd_3174162 : Nat := 4983230072969 + 3 ^ 40 * 3174162 * 2
def baseEnd_3174162 : Nat := 1629870781236715310277301

theorem tailTrace_3174162 : CollatzResearch.WordTrace tailWord_3174162 prefixEnd_3174162 1629870781236715310277301 := by
  unfold tailWord_3174162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28942799781640163138907185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77180799417707101703752493 28942799781640163138907185)
  ·
    refine ⟨21707099836230122354180389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28942799781640163138907185 21707099836230122354180389)
    ·
      refine ⟨4070081219293147941408823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21707099836230122354180389 4070081219293147941408823)
      ·
        refine ⟨6105121828939721912113235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070081219293147941408823 6105121828939721912113235)
        ·
          refine ⟨9157682743409582868169853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105121828939721912113235 9157682743409582868169853)
          ·
            refine ⟨3434131028778593575563695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9157682743409582868169853 3434131028778593575563695)
            ·
              refine ⟨5151196543167890363345543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434131028778593575563695 5151196543167890363345543)
              ·
                refine ⟨7726794814751835545018315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151196543167890363345543 7726794814751835545018315)
                ·
                  refine ⟨11590192222127753317527473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7726794814751835545018315 11590192222127753317527473)
                  ·
                    refine ⟨8692644166595814988145605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11590192222127753317527473 8692644166595814988145605)
                    ·
                      refine ⟨1629870781236715310277301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8692644166595814988145605 1629870781236715310277301)
                      ·
                        rfl

theorem cell23_3174162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3174162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174162 prefixEnd_3174162 := by exact prefixLift 3174162
  have htrace : WordTrace (prefixWord ++ tailWord_3174162) baseStart_3174162 baseEnd_3174162 := by
    simpa [prefixWord, tailWord_3174162, baseEnd_3174162] using wordTrace_append hprefix tailTrace_3174162
  have hstable : (prefixWord ++ tailWord_3174162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174162).length < 2 ^ (prefixWord ++ tailWord_3174162).sum := by decide
  have hdescent : baseEnd_3174162 < baseStart_3174162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174165 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_3174165 : Nat := 118140960795 + 3174165 * 2 ^ 59
def prefixEnd_3174165 : Nat := 4983230072969 + 3 ^ 40 * 3174165 * 2
def baseEnd_3174165 : Nat := 1629872321678678798539787

theorem tailTrace_3174165 : CollatzResearch.WordTrace tailWord_3174165 prefixEnd_3174165 1629872321678678798539787 := by
  unfold tailWord_3174165
  simp only [CollatzResearch.WordTrace]
  refine ⟨115771308545549784067987949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77180872363699856045325299 115771308545549784067987949)
  ·
    refine ⟨43414240704581169025495481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115771308545549784067987949 43414240704581169025495481)
    ·
      refine ⟨32560680528435876769121611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43414240704581169025495481 32560680528435876769121611)
      ·
        refine ⟨48841020792653815153682417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32560680528435876769121611 48841020792653815153682417)
        ·
          refine ⟨36630765594490361365261813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48841020792653815153682417 36630765594490361365261813)
          ·
            refine ⟨3434134274483471377993295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36630765594490361365261813 3434134274483471377993295)
            ·
              refine ⟨5151201411725207066989943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434134274483471377993295 5151201411725207066989943)
              ·
                refine ⟨7726802117587810600484915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151201411725207066989943 7726802117587810600484915)
                ·
                  refine ⟨11590203176381715900727373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7726802117587810600484915 11590203176381715900727373)
                  ·
                    refine ⟨4346326191143143462772765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11590203176381715900727373 4346326191143143462772765)
                    ·
                      refine ⟨1629872321678678798539787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4346326191143143462772765 1629872321678678798539787)
                      ·
                        rfl

theorem cell23_3174165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_3174165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174165 prefixEnd_3174165 := by exact prefixLift 3174165
  have htrace : WordTrace (prefixWord ++ tailWord_3174165) baseStart_3174165 baseEnd_3174165 := by
    simpa [prefixWord, tailWord_3174165, baseEnd_3174165] using wordTrace_append hprefix tailTrace_3174165
  have hstable : (prefixWord ++ tailWord_3174165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174165).length < 2 ^ (prefixWord ++ tailWord_3174165).sum := by decide
  have hdescent : baseEnd_3174165 < baseStart_3174165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174191 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_3174191 : Nat := 118140960795 + 3174191 * 2 ^ 59
def prefixEnd_3174191 : Nat := 4983230072969 + 3 ^ 40 * 3174191 * 2
def baseEnd_3174191 : Nat := 1629885672175695696814667

theorem tailTrace_3174191 : CollatzResearch.WordTrace tailWord_3174191 prefixEnd_3174191 1629885672175695696814667 := by
  unfold tailWord_3174191
  simp only [CollatzResearch.WordTrace]
  refine ⟨115772256843455590508434427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77181504562303727005622951 115772256843455590508434427)
  ·
    refine ⟨173658385265183385762651641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115772256843455590508434427 173658385265183385762651641)
    ·
      refine ⟨130243788948887539321988731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173658385265183385762651641 130243788948887539321988731)
      ·
        refine ⟨195365683423331308982983097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130243788948887539321988731 195365683423331308982983097)
        ·
          refine ⟨146524262567498481737237323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195365683423331308982983097 146524262567498481737237323)
          ·
            refine ⟨219786393851247722605855985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146524262567498481737237323 219786393851247722605855985)
            ·
              refine ⟨164839795388435791954391989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219786393851247722605855985 164839795388435791954391989)
              ·
                refine ⟨15453730817665855495724249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164839795388435791954391989 15453730817665855495724249)
                ·
                  refine ⟨11590298113249391621793187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15453730817665855495724249 11590298113249391621793187)
                  ·
                    refine ⟨17385447169874087432689781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11590298113249391621793187 17385447169874087432689781)
                    ·
                      refine ⟨1629885672175695696814667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17385447169874087432689781 1629885672175695696814667)
                      ·
                        rfl

theorem cell23_3174191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_3174191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174191 prefixEnd_3174191 := by exact prefixLift 3174191
  have htrace : WordTrace (prefixWord ++ tailWord_3174191) baseStart_3174191 baseEnd_3174191 := by
    simpa [prefixWord, tailWord_3174191, baseEnd_3174191] using wordTrace_append hprefix tailTrace_3174191
  have hstable : (prefixWord ++ tailWord_3174191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174191).length < 2 ^ (prefixWord ++ tailWord_3174191).sum := by decide
  have hdescent : baseEnd_3174191 < baseStart_3174191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174271 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 2, 8]
def baseStart_3174271 : Nat := 118140960795 + 3174271 * 2 ^ 59
def prefixEnd_3174271 : Nat := 4983230072969 + 3 ^ 40 * 3174271 * 2
def baseEnd_3174271 : Nat := 543308916876018461271433

theorem tailTrace_3174271 : CollatzResearch.WordTrace tailWord_3174271 prefixEnd_3174271 543308916876018461271433 := by
  unfold tailWord_3174271
  simp only [CollatzResearch.WordTrace]
  refine ⟨115775174683165764171346667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77183449788777176114231111 115775174683165764171346667)
  ·
    refine ⟨173662762024748646257020001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115775174683165764171346667 173662762024748646257020001)
    ·
      refine ⟨130247071518561484692765001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173662762024748646257020001 130247071518561484692765001)
      ·
        refine ⟨97685303638921113519573751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130247071518561484692765001 97685303638921113519573751)
        ·
          refine ⟨146527955458381670279360627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97685303638921113519573751 146527955458381670279360627)
          ·
            refine ⟨219791933187572505419040941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146527955458381670279360627 219791933187572505419040941)
            ·
              refine ⟨82421974945339689532140353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219791933187572505419040941 82421974945339689532140353)
              ·
                refine ⟨61816481209004767149105265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82421974945339689532140353 61816481209004767149105265)
                ·
                  refine ⟨46362360906753575361828949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61816481209004767149105265 46362360906753575361828949)
                  ·
                    refine ⟨543308916876018461271433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46362360906753575361828949 543308916876018461271433)
                    ·
                      rfl

theorem cell23_3174271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_3174271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174271 prefixEnd_3174271 := by exact prefixLift 3174271
  have htrace : WordTrace (prefixWord ++ tailWord_3174271) baseStart_3174271 baseEnd_3174271 := by
    simpa [prefixWord, tailWord_3174271, baseEnd_3174271] using wordTrace_append hprefix tailTrace_3174271
  have hstable : (prefixWord ++ tailWord_3174271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174271).length < 2 ^ (prefixWord ++ tailWord_3174271).sum := by decide
  have hdescent : baseEnd_3174271 < baseStart_3174271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174288 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 5, 4]
def baseStart_3174288 : Nat := 118140960795 + 3174288 * 2 ^ 59
def prefixEnd_3174288 : Nat := 4983230072969 + 3 ^ 40 * 3174288 * 2
def baseEnd_3174288 : Nat := 543311826599727272433907

theorem tailTrace_3174288 : CollatzResearch.WordTrace tailWord_3174288 prefixEnd_3174288 543311826599727272433907 := by
  unfold tailWord_3174288
  simp only [CollatzResearch.WordTrace]
  refine ⟨57887897362052088037357759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77183863149402784049810345 57887897362052088037357759)
  ·
    refine ⟨86831846043078132056036639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57887897362052088037357759 86831846043078132056036639)
    ·
      refine ⟨130247769064617198084054959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86831846043078132056036639 130247769064617198084054959)
      ·
        refine ⟨195371653596925797126082439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130247769064617198084054959 195371653596925797126082439)
        ·
          refine ⟨293057480395388695689123659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195371653596925797126082439 293057480395388695689123659)
          ·
            refine ⟨439586220593083043533685489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293057480395388695689123659 439586220593083043533685489)
            ·
              refine ⟨329689665444812282650264117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439586220593083043533685489 329689665444812282650264117)
              ·
                refine ⟨30908406135451151498462261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 329689665444812282650264117 30908406135451151498462261)
                ·
                  refine ⟨2897663075198545452980837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30908406135451151498462261 2897663075198545452980837)
                  ·
                    refine ⟨543311826599727272433907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2897663075198545452980837 543311826599727272433907)
                    ·
                      rfl

theorem cell23_3174288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_3174288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174288 prefixEnd_3174288 := by exact prefixLift 3174288
  have htrace : WordTrace (prefixWord ++ tailWord_3174288) baseStart_3174288 baseEnd_3174288 := by
    simpa [prefixWord, tailWord_3174288, baseEnd_3174288] using wordTrace_append hprefix tailTrace_3174288
  have hstable : (prefixWord ++ tailWord_3174288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174288).length < 2 ^ (prefixWord ++ tailWord_3174288).sum := by decide
  have hdescent : baseEnd_3174288 < baseStart_3174288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174292 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3174292 : Nat := 118140960795 + 3174292 * 2 ^ 59
def prefixEnd_3174292 : Nat := 4983230072969 + 3 ^ 40 * 3174292 * 2
def baseEnd_3174292 : Nat := 543312511240599933883901

theorem tailTrace_3174292 : CollatzResearch.WordTrace tailWord_3174292 prefixEnd_3174292 543312511240599933883901 := by
  unfold tailWord_3174292
  simp only [CollatzResearch.WordTrace]
  refine ⟨57887970308044842378930565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77183960410726456505240753 57887970308044842378930565)
  ·
    refine ⟨10853994432758407946049481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57887970308044842378930565 10853994432758407946049481)
    ·
      refine ⟨8140495824568805959537111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10853994432758407946049481 8140495824568805959537111)
      ·
        refine ⟨12210743736853208939305667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140495824568805959537111 12210743736853208939305667)
        ·
          refine ⟨18316115605279813408958501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12210743736853208939305667 18316115605279813408958501)
          ·
            refine ⟨3434271675989965014179719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18316115605279813408958501 3434271675989965014179719)
            ·
              refine ⟨5151407513984947521269579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434271675989965014179719 5151407513984947521269579)
              ·
                refine ⟨7727111270977421281904369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151407513984947521269579 7727111270977421281904369)
                ·
                  refine ⟨5795333453233065961428277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7727111270977421281904369 5795333453233065961428277)
                  ·
                    refine ⟨543312511240599933883901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5795333453233065961428277 543312511240599933883901)
                    ·
                      rfl

theorem cell23_3174292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3174292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174292 prefixEnd_3174292 := by exact prefixLift 3174292
  have htrace : WordTrace (prefixWord ++ tailWord_3174292) baseStart_3174292 baseEnd_3174292 := by
    simpa [prefixWord, tailWord_3174292, baseEnd_3174292] using wordTrace_append hprefix tailTrace_3174292
  have hstable : (prefixWord ++ tailWord_3174292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174292).length < 2 ^ (prefixWord ++ tailWord_3174292).sum := by decide
  have hdescent : baseEnd_3174292 < baseStart_3174292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174295 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_3174295 : Nat := 118140960795 + 3174295 * 2 ^ 59
def prefixEnd_3174295 : Nat := 4983230072969 + 3 ^ 40 * 3174295 * 2
def baseEnd_3174295 : Nat := 1629939074163763289914189

theorem tailTrace_3174295 : CollatzResearch.WordTrace tailWord_3174295 prefixEnd_3174295 1629939074163763289914189 := by
  unfold tailWord_3174295
  simp only [CollatzResearch.WordTrace]
  refine ⟨115776050035078816270220339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77184033356719210846813559 115776050035078816270220339)
  ·
    refine ⟨173664075052618224405330509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115776050035078816270220339 173664075052618224405330509)
    ·
      refine ⟨65124028144731834151998941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173664075052618224405330509 65124028144731834151998941)
      ·
        refine ⟨24421510554274437806999603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65124028144731834151998941 24421510554274437806999603)
        ·
          refine ⟨36632265831411656710499405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24421510554274437806999603 36632265831411656710499405)
          ·
            refine ⟨13737099686779371266437277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36632265831411656710499405 13737099686779371266437277)
            ·
              refine ⟨5151412382542264224913979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13737099686779371266437277 5151412382542264224913979)
              ·
                refine ⟨7727118573813396337370969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151412382542264224913979 7727118573813396337370969)
                ·
                  refine ⟨5795338930360047253028227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7727118573813396337370969 5795338930360047253028227)
                  ·
                    refine ⟨8693008395540070879542341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5795338930360047253028227 8693008395540070879542341)
                    ·
                      refine ⟨1629939074163763289914189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8693008395540070879542341 1629939074163763289914189)
                      ·
                        rfl

theorem cell23_3174295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_3174295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174295 prefixEnd_3174295 := by exact prefixLift 3174295
  have htrace : WordTrace (prefixWord ++ tailWord_3174295) baseStart_3174295 baseEnd_3174295 := by
    simpa [prefixWord, tailWord_3174295, baseEnd_3174295] using wordTrace_append hprefix tailTrace_3174295
  have hstable : (prefixWord ++ tailWord_3174295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174295).length < 2 ^ (prefixWord ++ tailWord_3174295).sum := by decide
  have hdescent : baseEnd_3174295 < baseStart_3174295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174308 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3174308 : Nat := 118140960795 + 3174308 * 2 ^ 59
def prefixEnd_3174308 : Nat := 4983230072969 + 3 ^ 40 * 3174308 * 2
def baseEnd_3174308 : Nat := 1629945749412271739051629

theorem tailTrace_3174308 : CollatzResearch.WordTrace tailWord_3174308 prefixEnd_3174308 1629945749412271739051629 := by
  unfold tailWord_3174308
  simp only [CollatzResearch.WordTrace]
  refine ⟨57888262092015859745221789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77184349456021146326962385 57888262092015859745221789)
  ·
    refine ⟨21708098284505947404458171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57888262092015859745221789 21708098284505947404458171)
    ·
      refine ⟨32562147426758921106687257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21708098284505947404458171 32562147426758921106687257)
      ·
        refine ⟨24421610570069190830015443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32562147426758921106687257 24421610570069190830015443)
        ·
          refine ⟨36632415855103786245023165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24421610570069190830015443 36632415855103786245023165)
          ·
            refine ⟨13737155945663919841883687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36632415855103786245023165 13737155945663919841883687)
            ·
              refine ⟨20605733918495879762825531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737155945663919841883687 20605733918495879762825531)
              ·
                refine ⟨30908600877743819644238297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20605733918495879762825531 30908600877743819644238297)
                ·
                  refine ⟨23181450658307864733178723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30908600877743819644238297 23181450658307864733178723)
                  ·
                    refine ⟨34772175987461797099768085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23181450658307864733178723 34772175987461797099768085)
                    ·
                      refine ⟨1629945749412271739051629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34772175987461797099768085 1629945749412271739051629)
                      ·
                        rfl

theorem cell23_3174308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3174308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174308 prefixEnd_3174308 := by exact prefixLift 3174308
  have htrace : WordTrace (prefixWord ++ tailWord_3174308) baseStart_3174308 baseEnd_3174308 := by
    simpa [prefixWord, tailWord_3174308, baseEnd_3174308] using wordTrace_append hprefix tailTrace_3174308
  have hstable : (prefixWord ++ tailWord_3174308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174308).length < 2 ^ (prefixWord ++ tailWord_3174308).sum := by decide
  have hdescent : baseEnd_3174308 < baseStart_3174308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174335 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 6]
def baseStart_3174335 : Nat := 118140960795 + 3174335 * 2 ^ 59
def prefixEnd_3174335 : Nat := 4983230072969 + 3 ^ 40 * 3174335 * 2
def baseEnd_3174335 : Nat := 181106623709993681490445

theorem tailTrace_3174335 : CollatzResearch.WordTrace tailWord_3174335 prefixEnd_3174335 181106623709993681490445 := by
  unfold tailWord_3174335
  simp only [CollatzResearch.WordTrace]
  refine ⟨115777508954933903101676459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77185005969955935401117639 115777508954933903101676459)
  ·
    refine ⟨173666263432400854652514689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115777508954933903101676459 173666263432400854652514689)
    ·
      refine ⟨130249697574300640989386017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173666263432400854652514689 130249697574300640989386017)
      ·
        refine ⟨97687273180725480742039513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130249697574300640989386017 97687273180725480742039513)
        ·
          refine ⟨73265454885544110556529635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97687273180725480742039513 73265454885544110556529635)
          ·
            refine ⟨109898182328316165834794453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73265454885544110556529635 109898182328316165834794453)
            ·
              refine ⟨2575738648319910136752995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109898182328316165834794453 2575738648319910136752995)
              ·
                refine ⟨3863607972479865205129493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575738648319910136752995 3863607972479865205129493)
                ·
                  refine ⟨181106623709993681490445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3863607972479865205129493 181106623709993681490445)
                  ·
                    rfl

theorem cell23_3174335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 6].length) (baseStart_3174335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174335 prefixEnd_3174335 := by exact prefixLift 3174335
  have htrace : WordTrace (prefixWord ++ tailWord_3174335) baseStart_3174335 baseEnd_3174335 := by
    simpa [prefixWord, tailWord_3174335, baseEnd_3174335] using wordTrace_append hprefix tailTrace_3174335
  have hstable : (prefixWord ++ tailWord_3174335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174335).length < 2 ^ (prefixWord ++ tailWord_3174335).sum := by decide
  have hdescent : baseEnd_3174335 < baseStart_3174335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174372 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_3174372 : Nat := 118140960795 + 3174372 * 2 ^ 59
def prefixEnd_3174372 : Nat := 4983230072969 + 3 ^ 40 * 3174372 * 2
def baseEnd_3174372 : Nat := 1629978612174159488651335

theorem tailTrace_3174372 : CollatzResearch.WordTrace tailWord_3174372 prefixEnd_3174372 1629978612174159488651335 := by
  unfold tailWord_3174372
  simp only [CollatzResearch.WordTrace]
  refine ⟨57889429227899929210386685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77185905637199905613848913 57889429227899929210386685)
  ·
    refine ⟨21708535960462473453895007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57889429227899929210386685 21708535960462473453895007)
    ·
      refine ⟨32562803940693710180842511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21708535960462473453895007 32562803940693710180842511)
      ·
        refine ⟨48844205911040565271263767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32562803940693710180842511 48844205911040565271263767)
        ·
          refine ⟨73266308866560847906895651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48844205911040565271263767 73266308866560847906895651)
          ·
            refine ⟨109899463299841271860343477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73266308866560847906895651 109899463299841271860343477)
            ·
              refine ⟨10303074684360119236907201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109899463299841271860343477 10303074684360119236907201)
              ·
                refine ⟨7727306013270089427680401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10303074684360119236907201 7727306013270089427680401)
                ·
                  refine ⟨5795479509952567070760301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7727306013270089427680401 5795479509952567070760301)
                  ·
                    refine ⟨2173304816232212651535113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5795479509952567070760301 2173304816232212651535113)
                    ·
                      refine ⟨1629978612174159488651335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173304816232212651535113 1629978612174159488651335)
                      ·
                        rfl

theorem cell23_3174372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_3174372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174372 prefixEnd_3174372 := by exact prefixLift 3174372
  have htrace : WordTrace (prefixWord ++ tailWord_3174372) baseStart_3174372 baseEnd_3174372 := by
    simpa [prefixWord, tailWord_3174372, baseEnd_3174372] using wordTrace_append hprefix tailTrace_3174372
  have hstable : (prefixWord ++ tailWord_3174372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174372).length < 2 ^ (prefixWord ++ tailWord_3174372).sum := by decide
  have hdescent : baseEnd_3174372 < baseStart_3174372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174408 : List Nat := [2, 1, 3, 2, 1, 2, 1, 11]
def baseStart_3174408 : Nat := 118140960795 + 3174408 * 2 ^ 59
def prefixEnd_3174408 : Nat := 4983230072969 + 3 ^ 40 * 3174408 * 2
def baseEnd_3174408 : Nat := 60370262869545235103747

theorem tailTrace_3174408 : CollatzResearch.WordTrace tailWord_3174408 prefixEnd_3174408 60370262869545235103747 := by
  unfold tailWord_3174408
  simp only [CollatzResearch.WordTrace]
  refine ⟨57890085741834718284541939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77186780989112957712722585 57890085741834718284541939)
  ·
    refine ⟨86835128612752077426812909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57890085741834718284541939 86835128612752077426812909)
    ·
      refine ⟨32563173229782029035054841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86835128612752077426812909 32563173229782029035054841)
      ·
        refine ⟨24422379922336521776291131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32563173229782029035054841 24422379922336521776291131)
        ·
          refine ⟨36633569883504782664436697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24422379922336521776291131 36633569883504782664436697)
          ·
            refine ⟨27475177412628586998327523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36633569883504782664436697 27475177412628586998327523)
            ·
              refine ⟨41212766118942880497491285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27475177412628586998327523 41212766118942880497491285)
              ·
                refine ⟨60370262869545235103747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 41212766118942880497491285 60370262869545235103747)
                ·
                  rfl

theorem cell23_3174408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 11].length) (baseStart_3174408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174408 prefixEnd_3174408 := by exact prefixLift 3174408
  have htrace : WordTrace (prefixWord ++ tailWord_3174408) baseStart_3174408 baseEnd_3174408 := by
    simpa [prefixWord, tailWord_3174408, baseEnd_3174408] using wordTrace_append hprefix tailTrace_3174408
  have hstable : (prefixWord ++ tailWord_3174408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174408).length < 2 ^ (prefixWord ++ tailWord_3174408).sum := by decide
  have hdescent : baseEnd_3174408 < baseStart_3174408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174429 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_3174429 : Nat := 118140960795 + 3174429 * 2 ^ 59
def prefixEnd_3174429 : Nat := 4983230072969 + 3 ^ 40 * 3174429 * 2
def baseEnd_3174429 : Nat := 543335960190488588546191

theorem tailTrace_3174429 : CollatzResearch.WordTrace tailWord_3174429 prefixEnd_3174429 543335960190488588546191 := by
  unfold tailWord_3174429
  simp only [CollatzResearch.WordTrace]
  refine ⟨115780937416593357155598341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77187291611062238103732227 115780937416593357155598341)
  ·
    refine ⟨21708925765611254466674689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115780937416593357155598341 21708925765611254466674689)
    ·
      refine ⟨16281694324208440850006017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21708925765611254466674689 16281694324208440850006017)
      ·
        refine ⟨12211270743156330637504513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16281694324208440850006017 12211270743156330637504513)
        ·
          refine ⟨9158453057367247978128385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12211270743156330637504513 9158453057367247978128385)
          ·
            refine ⟨6868839793025435983596289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9158453057367247978128385 6868839793025435983596289)
            ·
              refine ⟨5151629844769076987697217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6868839793025435983596289 5151629844769076987697217)
              ·
                refine ⟨3863722383576807740772913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151629844769076987697217 3863722383576807740772913)
                ·
                  refine ⟨2897791787682605805579685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3863722383576807740772913 2897791787682605805579685)
                  ·
                    refine ⟨543335960190488588546191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2897791787682605805579685 543335960190488588546191)
                    ·
                      rfl

theorem cell23_3174429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_3174429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174429 prefixEnd_3174429 := by exact prefixLift 3174429
  have htrace : WordTrace (prefixWord ++ tailWord_3174429) baseStart_3174429 baseEnd_3174429 := by
    simpa [prefixWord, tailWord_3174429, baseEnd_3174429] using wordTrace_append hprefix tailTrace_3174429
  have hstable : (prefixWord ++ tailWord_3174429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174429).length < 2 ^ (prefixWord ++ tailWord_3174429).sum := by decide
  have hdescent : baseEnd_3174429 < baseStart_3174429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174435 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 3]
def baseStart_3174435 : Nat := 118140960795 + 3174435 * 2 ^ 59
def prefixEnd_3174435 : Nat := 4983230072969 + 3 ^ 40 * 3174435 * 2
def baseEnd_3174435 : Nat := 1630010961455392742163545

theorem tailTrace_3174435 : CollatzResearch.WordTrace tailWord_3174435 prefixEnd_3174435 1630010961455392742163545 := by
  unfold tailWord_3174435
  simp only [CollatzResearch.WordTrace]
  refine ⟨115781156254571620180316759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77187437503047746786877839 115781156254571620180316759)
  ·
    refine ⟨173671734381857430270475139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115781156254571620180316759 173671734381857430270475139)
    ·
      refine ⟨260507601572786145405712709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173671734381857430270475139 260507601572786145405712709)
      ·
        refine ⟨48845175294897402263571133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260507601572786145405712709 48845175294897402263571133)
        ·
          refine ⟨18316940735586525848839175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48845175294897402263571133 18316940735586525848839175)
          ·
            refine ⟨27475411103379788773258763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18316940735586525848839175 27475411103379788773258763)
            ·
              refine ⟨41213116655069683159888145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27475411103379788773258763 41213116655069683159888145)
              ·
                refine ⟨30909837491302262369916109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41213116655069683159888145 30909837491302262369916109)
                ·
                  refine ⟨11591189059238348388718541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30909837491302262369916109 11591189059238348388718541)
                  ·
                    refine ⟨4346695897214380645769453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11591189059238348388718541 4346695897214380645769453)
                    ·
                      refine ⟨1630010961455392742163545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4346695897214380645769453 1630010961455392742163545)
                      ·
                        rfl

theorem cell23_3174435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_3174435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174435 prefixEnd_3174435 := by exact prefixLift 3174435
  have htrace : WordTrace (prefixWord ++ tailWord_3174435) baseStart_3174435 baseEnd_3174435 := by
    simpa [prefixWord, tailWord_3174435, baseEnd_3174435] using wordTrace_append hprefix tailTrace_3174435
  have hstable : (prefixWord ++ tailWord_3174435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174435).length < 2 ^ (prefixWord ++ tailWord_3174435).sum := by decide
  have hdescent : baseEnd_3174435 < baseStart_3174435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174442 : List Nat := [3, 1, 4, 1, 2, 3, 1, 8]
def baseStart_3174442 : Nat := 118140960795 + 3174442 * 2 ^ 59
def prefixEnd_3174442 : Nat := 4983230072969 + 3 ^ 40 * 3174442 * 2
def baseEnd_3174442 : Nat := 60370909474813859806519

theorem tailTrace_3174442 : CollatzResearch.WordTrace tailWord_3174442 prefixEnd_3174442 60370909474813859806519 := by
  unfold tailWord_3174442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28945352891386565093955395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77187607710364173583881053 28945352891386565093955395)
  ·
    refine ⟨43418029337079847640933093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28945352891386565093955395 43418029337079847640933093)
    ·
      refine ⟨8140880500702471432674955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43418029337079847640933093 8140880500702471432674955)
      ·
        refine ⟨12211320751053707149012433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140880500702471432674955 12211320751053707149012433)
        ·
          refine ⟨9158490563290280361759325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12211320751053707149012433 9158490563290280361759325)
          ·
            refine ⟨3434433961233855135659747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9158490563290280361759325 3434433961233855135659747)
            ·
              refine ⟨5151650941850782703489621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434433961233855135659747 5151650941850782703489621)
              ·
                refine ⟨60370909474813859806519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5151650941850782703489621 60370909474813859806519)
                ·
                  rfl

theorem cell23_3174442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_3174442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174442 prefixEnd_3174442 := by exact prefixLift 3174442
  have htrace : WordTrace (prefixWord ++ tailWord_3174442) baseStart_3174442 baseEnd_3174442 := by
    simpa [prefixWord, tailWord_3174442, baseEnd_3174442] using wordTrace_append hprefix tailTrace_3174442
  have hstable : (prefixWord ++ tailWord_3174442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174442).length < 2 ^ (prefixWord ++ tailWord_3174442).sum := by decide
  have hdescent : baseEnd_3174442 < baseStart_3174442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174470 : List Nat := [6, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3174470 : Nat := 118140960795 + 3174470 * 2 ^ 59
def prefixEnd_3174470 : Nat := 4983230072969 + 3 ^ 40 * 3174470 * 2
def baseEnd_3174470 : Nat := 1630028933278300105225885

theorem tailTrace_3174470 : CollatzResearch.WordTrace tailWord_3174470 prefixEnd_3174470 1630028933278300105225885 := by
  unfold tailWord_3174470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618201025295150661182527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77188288539629880771893909 3618201025295150661182527)
  ·
    refine ⟨5427301537942725991773791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3618201025295150661182527 5427301537942725991773791)
    ·
      refine ⟨8140952306914088987660687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5427301537942725991773791 8140952306914088987660687)
      ·
        refine ⟨12211428460371133481491031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140952306914088987660687 12211428460371133481491031)
        ·
          refine ⟨18317142690556700222236547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12211428460371133481491031 18317142690556700222236547)
          ·
            refine ⟨27475714035835050333354821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18317142690556700222236547 27475714035835050333354821)
            ·
              refine ⟨5151696381719071937504029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27475714035835050333354821 5151696381719071937504029)
              ·
                refine ⟨1931886143144651976564011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5151696381719071937504029 1931886143144651976564011)
                ·
                  refine ⟨2897829214716977964846017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931886143144651976564011 2897829214716977964846017)
                  ·
                    refine ⟨2173371911037733473634513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2897829214716977964846017 2173371911037733473634513)
                    ·
                      refine ⟨1630028933278300105225885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173371911037733473634513 1630028933278300105225885)
                      ·
                        rfl

theorem cell23_3174470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3174470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174470 prefixEnd_3174470 := by exact prefixLift 3174470
  have htrace : WordTrace (prefixWord ++ tailWord_3174470) baseStart_3174470 baseEnd_3174470 := by
    simpa [prefixWord, tailWord_3174470, baseEnd_3174470] using wordTrace_append hprefix tailTrace_3174470
  have hstable : (prefixWord ++ tailWord_3174470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174470).length < 2 ^ (prefixWord ++ tailWord_3174470).sum := by decide
  have hdescent : baseEnd_3174470 < baseStart_3174470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174485 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_3174485 : Nat := 118140960795 + 3174485 * 2 ^ 59
def prefixEnd_3174485 : Nat := 4983230072969 + 3 ^ 40 * 3174485 * 2
def baseEnd_3174485 : Nat := 543345545162705848846105

theorem tailTrace_3174485 : CollatzResearch.WordTrace tailWord_3174485 prefixEnd_3174485 543345545162705848846105 := by
  unfold tailWord_3174485
  simp only [CollatzResearch.WordTrace]
  refine ⟨115782979904390478719636909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77188653269593652479757939 115782979904390478719636909)
  ·
    refine ⟨43418617464146429519863841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115782979904390478719636909 43418617464146429519863841)
    ·
      refine ⟨32563963098109822139897881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43418617464146429519863841 32563963098109822139897881)
      ·
        refine ⟨24422972323582366604923411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32563963098109822139897881 24422972323582366604923411)
        ·
          refine ⟨36634458485373549907385117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24422972323582366604923411 36634458485373549907385117)
          ·
            refine ⟨13737921932015081215269419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36634458485373549907385117 13737921932015081215269419)
            ·
              refine ⟨20606882898022621822904129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737921932015081215269419 20606882898022621822904129)
              ·
                refine ⟨15455162173516966367178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20606882898022621822904129 15455162173516966367178097)
                ·
                  refine ⟨11591371630137724775383573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15455162173516966367178097 11591371630137724775383573)
                  ·
                    refine ⟨543345545162705848846105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11591371630137724775383573 543345545162705848846105)
                    ·
                      rfl

theorem cell23_3174485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_3174485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174485 prefixEnd_3174485 := by exact prefixLift 3174485
  have htrace : WordTrace (prefixWord ++ tailWord_3174485) baseStart_3174485 baseEnd_3174485 := by
    simpa [prefixWord, tailWord_3174485, baseEnd_3174485] using wordTrace_append hprefix tailTrace_3174485
  have hstable : (prefixWord ++ tailWord_3174485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174485).length < 2 ^ (prefixWord ++ tailWord_3174485).sum := by decide
  have hdescent : baseEnd_3174485 < baseStart_3174485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174495 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 3]
def baseStart_3174495 : Nat := 118140960795 + 3174495 * 2 ^ 59
def prefixEnd_3174495 : Nat := 4983230072969 + 3 ^ 40 * 3174495 * 2
def baseEnd_3174495 : Nat := 1630041770294662507413269

theorem tailTrace_3174495 : CollatzResearch.WordTrace tailWord_3174495 prefixEnd_3174495 1630041770294662507413269 := by
  unfold tailWord_3174495
  simp only [CollatzResearch.WordTrace]
  refine ⟨115783344634354250427500939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77188896422902833618333959 115783344634354250427500939)
  ·
    refine ⟨173675016951531375641251409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115783344634354250427500939 173675016951531375641251409)
    ·
      refine ⟨130256262713648531730938557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173675016951531375641251409 130256262713648531730938557)
      ·
        refine ⟨48846098517618199399101959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130256262713648531730938557 48846098517618199399101959)
        ·
          refine ⟨73269147776427299098652939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48846098517618199399101959 73269147776427299098652939)
          ·
            refine ⟨109903721664640948647979409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73269147776427299098652939 109903721664640948647979409)
            ·
              refine ⟨82427791248480711485984557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109903721664640948647979409 82427791248480711485984557)
              ·
                refine ⟨30910421718180266807244209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82427791248480711485984557 30910421718180266807244209)
                ·
                  refine ⟨23182816288635200105433157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30910421718180266807244209 23182816288635200105433157)
                  ·
                    refine ⟨4346778054119100019768717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23182816288635200105433157 4346778054119100019768717)
                    ·
                      refine ⟨1630041770294662507413269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4346778054119100019768717 1630041770294662507413269)
                      ·
                        rfl

theorem cell23_3174495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_3174495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174495 prefixEnd_3174495 := by exact prefixLift 3174495
  have htrace : WordTrace (prefixWord ++ tailWord_3174495) baseStart_3174495 baseEnd_3174495 := by
    simpa [prefixWord, tailWord_3174495, baseEnd_3174495] using wordTrace_append hprefix tailTrace_3174495
  have hstable : (prefixWord ++ tailWord_3174495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174495).length < 2 ^ (prefixWord ++ tailWord_3174495).sum := by decide
  have hdescent : baseEnd_3174495 < baseStart_3174495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174505 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_3174505 : Nat := 118140960795 + 3174505 * 2 ^ 59
def prefixEnd_3174505 : Nat := 4983230072969 + 3 ^ 40 * 3174505 * 2
def baseEnd_3174505 : Nat := 1630046905101207468288223

theorem tailTrace_3174505 : CollatzResearch.WordTrace tailWord_3174505 prefixEnd_3174505 1630046905101207468288223 := by
  unfold tailWord_3174505
  simp only [CollatzResearch.WordTrace]
  refine ⟨115783709364318022135364969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77189139576212014756909979 115783709364318022135364969)
  ·
    refine ⟨86837782023238516601523727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115783709364318022135364969 86837782023238516601523727)
    ·
      refine ⟨130256673034857774902285591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86837782023238516601523727 130256673034857774902285591)
      ·
        refine ⟨195385009552286662353428387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130256673034857774902285591 195385009552286662353428387)
        ·
          refine ⟨293077514328429993530142581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195385009552286662353428387 293077514328429993530142581)
          ·
            refine ⟨27476016968290311893450867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 293077514328429993530142581 27476016968290311893450867)
            ·
              refine ⟨41214025452435467840176301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27476016968290311893450867 41214025452435467840176301)
              ·
                refine ⟨15455259544663300440066113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41214025452435467840176301 15455259544663300440066113)
                ·
                  refine ⟨11591444658497475330049585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15455259544663300440066113 11591444658497475330049585)
                  ·
                    refine ⟨8693583493873106497537189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11591444658497475330049585 8693583493873106497537189)
                    ·
                      refine ⟨1630046905101207468288223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8693583493873106497537189 1630046905101207468288223)
                      ·
                        rfl

theorem cell23_3174505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_3174505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174505 prefixEnd_3174505 := by exact prefixLift 3174505
  have htrace : WordTrace (prefixWord ++ tailWord_3174505) baseStart_3174505 baseEnd_3174505 := by
    simpa [prefixWord, tailWord_3174505, baseEnd_3174505] using wordTrace_append hprefix tailTrace_3174505
  have hstable : (prefixWord ++ tailWord_3174505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174505).length < 2 ^ (prefixWord ++ tailWord_3174505).sum := by decide
  have hdescent : baseEnd_3174505 < baseStart_3174505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174549 : List Nat := [1, 3, 2, 1, 1, 1, 7, 2, 5]
def baseStart_3174549 : Nat := 118140960795 + 3174549 * 2 ^ 59
def prefixEnd_3174549 : Nat := 4983230072969 + 3 ^ 40 * 3174549 * 2
def baseEnd_3174549 : Nat := 181118833138889477348669

theorem tailTrace_3174549 : CollatzResearch.WordTrace tailWord_3174549 prefixEnd_3174549 181118833138889477348669 := by
  unfold tailWord_3174549
  simp only [CollatzResearch.WordTrace]
  refine ⟨115785314176158617649966701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77190209450772411766644467 115785314176158617649966701)
  ·
    refine ⟨43419492816059481618737513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115785314176158617649966701 43419492816059481618737513)
    ·
      refine ⟨32564619612044611214053135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43419492816059481618737513 32564619612044611214053135)
      ·
        refine ⟨48846929418066916821079703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32564619612044611214053135 48846929418066916821079703)
        ·
          refine ⟨73270394127100375231619555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48846929418066916821079703 73270394127100375231619555)
          ·
            refine ⟨109905591190650562847429333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73270394127100375231619555 109905591190650562847429333)
            ·
              refine ⟨2575912293530872566736625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109905591190650562847429333 2575912293530872566736625)
              ·
                refine ⟨1931934220148154425052469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575912293530872566736625 1931934220148154425052469)
                ·
                  refine ⟨181118833138889477348669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1931934220148154425052469 181118833138889477348669)
                  ·
                    rfl

theorem cell23_3174549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_3174549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174549 prefixEnd_3174549 := by exact prefixLift 3174549
  have htrace : WordTrace (prefixWord ++ tailWord_3174549) baseStart_3174549 baseEnd_3174549 := by
    simpa [prefixWord, tailWord_3174549, baseEnd_3174549] using wordTrace_append hprefix tailTrace_3174549
  have hstable : (prefixWord ++ tailWord_3174549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174549).length < 2 ^ (prefixWord ++ tailWord_3174549).sum := by decide
  have hdescent : baseEnd_3174549 < baseStart_3174549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174595 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4]
def baseStart_3174595 : Nat := 118140960795 + 3174595 * 2 ^ 59
def prefixEnd_3174595 : Nat := 4983230072969 + 3 ^ 40 * 3174595 * 2
def baseEnd_3174595 : Nat := 1630093118360112116162809

theorem tailTrace_3174595 : CollatzResearch.WordTrace tailWord_3174595 prefixEnd_3174595 1630093118360112116162809 := by
  unfold tailWord_3174595
  simp only [CollatzResearch.WordTrace]
  refine ⟨115786991933991967506141239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77191327955994645004094159 115786991933991967506141239)
  ·
    refine ⟨173680487900987951259211859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115786991933991967506141239 173680487900987951259211859)
    ·
      refine ⟨260520731851481926888817789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173680487900987951259211859 260520731851481926888817789)
      ·
        refine ⟨97695274444305722583306671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260520731851481926888817789 97695274444305722583306671)
        ·
          refine ⟨146542911666458583874960007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97695274444305722583306671 146542911666458583874960007)
          ·
            refine ⟨219814367499687875812440011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146542911666458583874960007 219814367499687875812440011)
            ·
              refine ⟨329721551249531813718660017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219814367499687875812440011 329721551249531813718660017)
              ·
                refine ⟨247291163437148860288995013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329721551249531813718660017 247291163437148860288995013)
                ·
                  refine ⟨46367093144465411304186565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247291163437148860288995013 46367093144465411304186565)
                  ·
                    refine ⟨8693829964587264619534981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46367093144465411304186565 8693829964587264619534981)
                    ·
                      refine ⟨1630093118360112116162809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8693829964587264619534981 1630093118360112116162809)
                      ·
                        rfl

theorem cell23_3174595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_3174595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174595 prefixEnd_3174595 := by exact prefixLift 3174595
  have htrace : WordTrace (prefixWord ++ tailWord_3174595) baseStart_3174595 baseEnd_3174595 := by
    simpa [prefixWord, tailWord_3174595, baseEnd_3174595] using wordTrace_append hprefix tailTrace_3174595
  have hstable : (prefixWord ++ tailWord_3174595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174595).length < 2 ^ (prefixWord ++ tailWord_3174595).sum := by decide
  have hdescent : baseEnd_3174595 < baseStart_3174595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174659 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 4, 3, 2]
def baseStart_3174659 : Nat := 118140960795 + 3174659 * 2 ^ 59
def prefixEnd_3174659 : Nat := 4983230072969 + 3 ^ 40 * 3174659 * 2
def baseEnd_3174659 : Nat := 1630125981121999865762515

theorem tailTrace_3174659 : CollatzResearch.WordTrace tailWord_3174659 prefixEnd_3174659 1630125981121999865762515 := by
  unfold tailWord_3174659
  simp only [CollatzResearch.WordTrace]
  refine ⟨115789326205760106436471031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77192884137173404290980687 115789326205760106436471031)
  ·
    refine ⟨173683989308640159654706547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115789326205760106436471031 173683989308640159654706547)
    ·
      refine ⟨260525983962960239482059821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173683989308640159654706547 260525983962960239482059821)
      ·
        refine ⟨97697243986110089805772433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260525983962960239482059821 97697243986110089805772433)
        ·
          refine ⟨73272932989582567354329325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97697243986110089805772433 73272932989582567354329325)
          ·
            refine ⟨27477349871093462757873497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73272932989582567354329325 27477349871093462757873497)
            ·
              refine ⟨20608012403320097068405123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27477349871093462757873497 20608012403320097068405123)
              ·
                refine ⟨30912018604980145602607685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20608012403320097068405123 30912018604980145602607685)
                ·
                  refine ⟨5796003488433777300488941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30912018604980145602607685 5796003488433777300488941)
                  ·
                    refine ⟨2173501308162666487683353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5796003488433777300488941 2173501308162666487683353)
                    ·
                      refine ⟨1630125981121999865762515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173501308162666487683353 1630125981121999865762515)
                      ·
                        rfl

theorem cell23_3174659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_3174659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174659 prefixEnd_3174659 := by exact prefixLift 3174659
  have htrace : WordTrace (prefixWord ++ tailWord_3174659) baseStart_3174659 baseEnd_3174659 := by
    simpa [prefixWord, tailWord_3174659, baseEnd_3174659] using wordTrace_append hprefix tailTrace_3174659
  have hstable : (prefixWord ++ tailWord_3174659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174659).length < 2 ^ (prefixWord ++ tailWord_3174659).sum := by decide
  have hdescent : baseEnd_3174659 < baseStart_3174659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174689 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3174689 : Nat := 118140960795 + 3174689 * 2 ^ 59
def prefixEnd_3174689 : Nat := 4983230072969 + 3 ^ 40 * 3174689 * 2
def baseEnd_3174689 : Nat := 1630141385541634748387377

theorem tailTrace_3174689 : CollatzResearch.WordTrace tailWord_3174689 prefixEnd_3174689 1630141385541634748387377 := by
  unfold tailWord_3174689
  simp only [CollatzResearch.WordTrace]
  refine ⟨115790420395651421560063121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77193613597100947706708747 115790420395651421560063121)
  ·
    refine ⟨86842815296738566170047341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115790420395651421560063121 86842815296738566170047341)
    ·
      refine ⟨32566055736276962313767753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86842815296738566170047341 32566055736276962313767753)
      ·
        refine ⟨24424541802207721735325815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32566055736276962313767753 24424541802207721735325815)
        ·
          refine ⟨36636812703311582602988723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24424541802207721735325815 36636812703311582602988723)
          ·
            refine ⟨54955219054967373904483085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36636812703311582602988723 54955219054967373904483085)
            ·
              refine ⟨20608207145612765214181157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54955219054967373904483085 20608207145612765214181157)
              ·
                refine ⟨3864038839802393477658967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20608207145612765214181157 3864038839802393477658967)
                ·
                  refine ⟨5796058259703590216488451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864038839802393477658967 5796058259703590216488451)
                  ·
                    refine ⟨8694087389555385324732677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5796058259703590216488451 8694087389555385324732677)
                    ·
                      refine ⟨1630141385541634748387377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8694087389555385324732677 1630141385541634748387377)
                      ·
                        rfl

theorem cell23_3174689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3174689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174689 prefixEnd_3174689 := by exact prefixLift 3174689
  have htrace : WordTrace (prefixWord ++ tailWord_3174689) baseStart_3174689 baseEnd_3174689 := by
    simpa [prefixWord, tailWord_3174689, baseEnd_3174689] using wordTrace_append hprefix tailTrace_3174689
  have hstable : (prefixWord ++ tailWord_3174689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174689).length < 2 ^ (prefixWord ++ tailWord_3174689).sum := by decide
  have hdescent : baseEnd_3174689 < baseStart_3174689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174709 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_3174709 : Nat := 118140960795 + 3174709 * 2 ^ 59
def prefixEnd_3174709 : Nat := 4983230072969 + 3 ^ 40 * 3174709 * 2
def baseEnd_3174709 : Nat := 1630151655154724670137285

theorem tailTrace_3174709 : CollatzResearch.WordTrace tailWord_3174709 prefixEnd_3174709 1630151655154724670137285 := by
  unfold tailWord_3174709
  simp only [CollatzResearch.WordTrace]
  refine ⟨115791149855578964975791181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77194099903719309983860787 115791149855578964975791181)
  ·
    refine ⟨43421681195842111865921693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115791149855578964975791181 43421681195842111865921693)
    ·
      refine ⟨16283130448440791949720635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43421681195842111865921693 16283130448440791949720635)
      ·
        refine ⟨24424695672661187924580953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16283130448440791949720635 24424695672661187924580953)
        ·
          refine ⟨18318521754495890943435715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24424695672661187924580953 18318521754495890943435715)
          ·
            refine ⟨27477782631743836415153573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18318521754495890943435715 27477782631743836415153573)
            ·
              refine ⟨5152084243451969327841295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27477782631743836415153573 5152084243451969327841295)
              ·
                refine ⟨7728126365177953991761943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152084243451969327841295 7728126365177953991761943)
                ·
                  refine ⟨11592189547766930987642915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728126365177953991761943 11592189547766930987642915)
                  ·
                    refine ⟨17388284321650396481464373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11592189547766930987642915 17388284321650396481464373)
                    ·
                      refine ⟨1630151655154724670137285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17388284321650396481464373 1630151655154724670137285)
                      ·
                        rfl

theorem cell23_3174709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_3174709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174709 prefixEnd_3174709 := by exact prefixLift 3174709
  have htrace : WordTrace (prefixWord ++ tailWord_3174709) baseStart_3174709 baseEnd_3174709 := by
    simpa [prefixWord, tailWord_3174709, baseEnd_3174709] using wordTrace_append hprefix tailTrace_3174709
  have hstable : (prefixWord ++ tailWord_3174709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174709).length < 2 ^ (prefixWord ++ tailWord_3174709).sum := by decide
  have hdescent : baseEnd_3174709 < baseStart_3174709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174723 : List Nat := [1, 1, 1, 3, 1, 3, 2, 6, 1, 2, 2]
def baseStart_3174723 : Nat := 118140960795 + 3174723 * 2 ^ 59
def prefixEnd_3174723 : Nat := 4983230072969 + 3 ^ 40 * 3174723 * 2
def baseEnd_3174723 : Nat := 1630158843883887615362221

theorem tailTrace_3174723 : CollatzResearch.WordTrace tailWord_3174723 prefixEnd_3174723 1630158843883887615362221 := by
  unfold tailWord_3174723
  simp only [CollatzResearch.WordTrace]
  refine ⟨115791660477528245366800823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77194440318352163577867215 115791660477528245366800823)
  ·
    refine ⟨173687490716292368050201235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115791660477528245366800823 173687490716292368050201235)
    ·
      refine ⟨260531236074438552075301853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173687490716292368050201235 260531236074438552075301853)
      ·
        refine ⟨97699213527914457028238195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260531236074438552075301853 97699213527914457028238195)
        ·
          refine ⟨146548820291871685542357293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97699213527914457028238195 146548820291871685542357293)
          ·
            refine ⟨54955807609451882078383985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146548820291871685542357293 54955807609451882078383985)
            ·
              refine ⟨41216855707088911558787989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54955807609451882078383985 41216855707088911558787989)
              ·
                refine ⟨1932040111269792729318187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41216855707088911558787989 1932040111269792729318187)
                ·
                  refine ⟨2898060166904689093977281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932040111269792729318187 2898060166904689093977281)
                  ·
                    refine ⟨2173545125178516820482961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898060166904689093977281 2173545125178516820482961)
                    ·
                      refine ⟨1630158843883887615362221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173545125178516820482961 1630158843883887615362221)
                      ·
                        rfl

theorem cell23_3174723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_3174723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174723 prefixEnd_3174723 := by exact prefixLift 3174723
  have htrace : WordTrace (prefixWord ++ tailWord_3174723) baseStart_3174723 baseEnd_3174723 := by
    simpa [prefixWord, tailWord_3174723, baseEnd_3174723] using wordTrace_append hprefix tailTrace_3174723
  have hstable : (prefixWord ++ tailWord_3174723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174723).length < 2 ^ (prefixWord ++ tailWord_3174723).sum := by decide
  have hdescent : baseEnd_3174723 < baseStart_3174723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174732 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3174732 : Nat := 118140960795 + 3174732 * 2 ^ 59
def prefixEnd_3174732 : Nat := 4983230072969 + 3 ^ 40 * 3174732 * 2
def baseEnd_3174732 : Nat := 1630163465209778080149679

theorem tailTrace_3174732 : CollatzResearch.WordTrace tailWord_3174732 prefixEnd_3174732 1630163465209778080149679 := by
  unfold tailWord_3174732
  simp only [CollatzResearch.WordTrace]
  refine ⟨57895994367247819951939225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77194659156330426602585633 57895994367247819951939225)
  ·
    refine ⟨43421995775435864963954419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57895994367247819951939225 43421995775435864963954419)
    ·
      refine ⟨65132993663153797445931629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43421995775435864963954419 65132993663153797445931629)
      ·
        refine ⟨24424872623682674042224361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65132993663153797445931629 24424872623682674042224361)
        ·
          refine ⟨18318654467762005531668271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24424872623682674042224361 18318654467762005531668271)
          ·
            refine ⟨27477981701643008297502407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18318654467762005531668271 27477981701643008297502407)
            ·
              refine ⟨41216972552464512446253611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27477981701643008297502407 41216972552464512446253611)
              ·
                refine ⟨61825458828696768669380417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41216972552464512446253611 61825458828696768669380417)
                ·
                  refine ⟨46369094121522576502035313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61825458828696768669380417 46369094121522576502035313)
                  ·
                    refine ⟨34776820591141932376526485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46369094121522576502035313 34776820591141932376526485)
                    ·
                      refine ⟨1630163465209778080149679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34776820591141932376526485 1630163465209778080149679)
                      ·
                        rfl

theorem cell23_3174732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3174732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174732 prefixEnd_3174732 := by exact prefixLift 3174732
  have htrace : WordTrace (prefixWord ++ tailWord_3174732) baseStart_3174732 baseEnd_3174732 := by
    simpa [prefixWord, tailWord_3174732, baseEnd_3174732] using wordTrace_append hprefix tailTrace_3174732
  have hstable : (prefixWord ++ tailWord_3174732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174732).length < 2 ^ (prefixWord ++ tailWord_3174732).sum := by decide
  have hdescent : baseEnd_3174732 < baseStart_3174732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174739 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 3]
def baseStart_3174739 : Nat := 118140960795 + 3174739 * 2 ^ 59
def prefixEnd_3174739 : Nat := 4983230072969 + 3 ^ 40 * 3174739 * 2
def baseEnd_3174739 : Nat := 1630167059574359552762147

theorem tailTrace_3174739 : CollatzResearch.WordTrace tailWord_3174739 prefixEnd_3174739 1630167059574359552762147 := by
  unfold tailWord_3174739
  simp only [CollatzResearch.WordTrace]
  refine ⟨115792244045470280099383271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77194829363646853399588847 115792244045470280099383271)
  ·
    refine ⟨173688366068205420149074907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115792244045470280099383271 173688366068205420149074907)
    ·
      refine ⟨260532549102308130223612361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173688366068205420149074907 260532549102308130223612361)
      ·
        refine ⟨195399411826731097667709271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260532549102308130223612361 195399411826731097667709271)
        ·
          refine ⟨293099117740096646501563907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195399411826731097667709271 293099117740096646501563907)
          ·
            refine ⟨439648676610144969752345861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293099117740096646501563907 439648676610144969752345861)
            ·
              refine ⟨82434126864402181828564849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439648676610144969752345861 82434126864402181828564849)
              ·
                refine ⟨61825595148301636371423637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82434126864402181828564849 61825595148301636371423637)
                ·
                  refine ⟨2898074772576639204910483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61825595148301636371423637 2898074772576639204910483)
                  ·
                    refine ⟨4347112158864958807365725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2898074772576639204910483 4347112158864958807365725)
                    ·
                      refine ⟨1630167059574359552762147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347112158864958807365725 1630167059574359552762147)
                      ·
                        rfl

theorem cell23_3174739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 3].length) (baseStart_3174739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174739 prefixEnd_3174739 := by exact prefixLift 3174739
  have htrace : WordTrace (prefixWord ++ tailWord_3174739) baseStart_3174739 baseEnd_3174739 := by
    simpa [prefixWord, tailWord_3174739, baseEnd_3174739] using wordTrace_append hprefix tailTrace_3174739
  have hstable : (prefixWord ++ tailWord_3174739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174739).length < 2 ^ (prefixWord ++ tailWord_3174739).sum := by decide
  have hdescent : baseEnd_3174739 < baseStart_3174739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174773 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3174773 : Nat := 118140960795 + 3174773 * 2 ^ 59
def prefixEnd_3174773 : Nat := 4983230072969 + 3 ^ 40 * 3174773 * 2
def baseEnd_3174773 : Nat := 1630184517916612419736991

theorem tailTrace_3174773 : CollatzResearch.WordTrace tailWord_3174773 prefixEnd_3174773 1630184517916612419736991 := by
  unfold tailWord_3174773
  simp only [CollatzResearch.WordTrace]
  refine ⟨115793484127347103906120973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77195656084898069270747315 115793484127347103906120973)
  ·
    refine ⟨43422556547755163964795365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115793484127347103906120973 43422556547755163964795365)
    ·
      refine ⟨8141729352704093243399131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43422556547755163964795365 8141729352704093243399131)
      ·
        refine ⟨12212594029056139865098697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8141729352704093243399131 12212594029056139865098697)
        ·
          refine ⟨9159445521792104898824023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12212594029056139865098697 9159445521792104898824023)
          ·
            refine ⟨13739168282688157348236035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9159445521792104898824023 13739168282688157348236035)
            ·
              refine ⟨20608752424032236022354053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13739168282688157348236035 20608752424032236022354053)
              ·
                refine ⟨3864141079506044254191385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20608752424032236022354053 3864141079506044254191385)
                ·
                  refine ⟨2898105809629533190643539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3864141079506044254191385 2898105809629533190643539)
                  ·
                    refine ⟨4347158714444299785965309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2898105809629533190643539 4347158714444299785965309)
                    ·
                      refine ⟨1630184517916612419736991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347158714444299785965309 1630184517916612419736991)
                      ·
                        rfl

theorem cell23_3174773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3174773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174773 prefixEnd_3174773 := by exact prefixLift 3174773
  have htrace : WordTrace (prefixWord ++ tailWord_3174773) baseStart_3174773 baseEnd_3174773 := by
    simpa [prefixWord, tailWord_3174773, baseEnd_3174773] using wordTrace_append hprefix tailTrace_3174773
  have hstable : (prefixWord ++ tailWord_3174773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174773).length < 2 ^ (prefixWord ++ tailWord_3174773).sum := by decide
  have hdescent : baseEnd_3174773 < baseStart_3174773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174774 : List Nat := [5, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3174774 : Nat := 118140960795 + 3174774 * 2 ^ 59
def prefixEnd_3174774 : Nat := 4983230072969 + 3 ^ 40 * 3174774 * 2
def baseEnd_3174774 : Nat := 1630185031397266915824487

theorem tailTrace_3174774 : CollatzResearch.WordTrace tailWord_3174774 prefixEnd_3174774 1630185031397266915824487 := by
  unfold tailWord_3174774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237095037521467567306711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77195680400228987384604917 7237095037521467567306711)
  ·
    refine ⟨10855642556282201350960067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7237095037521467567306711 10855642556282201350960067)
    ·
      refine ⟨16283463834423302026440101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10855642556282201350960067 16283463834423302026440101)
      ·
        refine ⟨3053149468954369129957519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16283463834423302026440101 3053149468954369129957519)
        ·
          refine ⟨4579724203431553694936279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053149468954369129957519 4579724203431553694936279)
          ·
            refine ⟨6869586305147330542404419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579724203431553694936279 6869586305147330542404419)
            ·
              refine ⟨10304379457720995813606629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869586305147330542404419 10304379457720995813606629)
              ·
                refine ⟨1932071148322686715051243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10304379457720995813606629 1932071148322686715051243)
                ·
                  refine ⟨2898106722484030072576865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932071148322686715051243 2898106722484030072576865)
                  ·
                    refine ⟨2173580041863022554432649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898106722484030072576865 2173580041863022554432649)
                    ·
                      refine ⟨1630185031397266915824487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173580041863022554432649 1630185031397266915824487)
                      ·
                        rfl

theorem cell23_3174774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3174774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174774 prefixEnd_3174774 := by exact prefixLift 3174774
  have htrace : WordTrace (prefixWord ++ tailWord_3174774) baseStart_3174774 baseEnd_3174774 := by
    simpa [prefixWord, tailWord_3174774, baseEnd_3174774] using wordTrace_append hprefix tailTrace_3174774
  have hstable : (prefixWord ++ tailWord_3174774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174774).length < 2 ^ (prefixWord ++ tailWord_3174774).sum := by decide
  have hdescent : baseEnd_3174774 < baseStart_3174774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174796 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 1, 4, 2]
def baseStart_3174796 : Nat := 118140960795 + 3174796 * 2 ^ 59
def prefixEnd_3174796 : Nat := 4983230072969 + 3 ^ 40 * 3174796 * 2
def baseEnd_3174796 : Nat := 1630196327971665829749385

theorem tailTrace_3174796 : CollatzResearch.WordTrace tailWord_3174796 prefixEnd_3174796 1630196327971665829749385 := by
  unfold tailWord_3174796
  simp only [CollatzResearch.WordTrace]
  refine ⟨57897161503131889417104121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77196215337509185889472161 57897161503131889417104121)
  ·
    refine ⟨43422871127348917062828091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57897161503131889417104121 43422871127348917062828091)
    ·
      refine ⟨65134306691023375594242137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43422871127348917062828091 65134306691023375594242137)
      ·
        refine ⟨48850730018267531695681603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65134306691023375594242137 48850730018267531695681603)
        ·
          refine ⟨73276095027401297543522405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48850730018267531695681603 73276095027401297543522405)
          ·
            refine ⟨13739267817637743289410451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73276095027401297543522405 13739267817637743289410451)
            ·
              refine ⟨20608901726456614934115677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13739267817637743289410451 20608901726456614934115677)
              ·
                refine ⟨7728338147421230600293379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20608901726456614934115677 7728338147421230600293379)
                ·
                  refine ⟨11592507221131845900440069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7728338147421230600293379 11592507221131845900440069)
                  ·
                    refine ⟨2173595103962221106332513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11592507221131845900440069 2173595103962221106332513)
                    ·
                      refine ⟨1630196327971665829749385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2173595103962221106332513 1630196327971665829749385)
                      ·
                        rfl

theorem cell23_3174796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_3174796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174796 prefixEnd_3174796 := by exact prefixLift 3174796
  have htrace : WordTrace (prefixWord ++ tailWord_3174796) baseStart_3174796 baseEnd_3174796 := by
    simpa [prefixWord, tailWord_3174796, baseEnd_3174796] using wordTrace_append hprefix tailTrace_3174796
  have hstable : (prefixWord ++ tailWord_3174796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174796).length < 2 ^ (prefixWord ++ tailWord_3174796).sum := by decide
  have hdescent : baseEnd_3174796 < baseStart_3174796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174846 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3174846 : Nat := 118140960795 + 3174846 * 2 ^ 59
def prefixEnd_3174846 : Nat := 4983230072969 + 3 ^ 40 * 3174846 * 2
def baseEnd_3174846 : Nat := 1630222002004390634124155

theorem tailTrace_3174846 : CollatzResearch.WordTrace tailWord_3174846 prefixEnd_3174846 1630222002004390634124155 := by
  unfold tailWord_3174846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14474518332010329671691049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77197431104055091582352261 14474518332010329671691049)
  ·
    refine ⟨10855888749007747253768287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14474518332010329671691049 10855888749007747253768287)
    ·
      refine ⟨16283833123511620880652431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10855888749007747253768287 16283833123511620880652431)
      ·
        refine ⟨24425749685267431320978647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16283833123511620880652431 24425749685267431320978647)
        ·
          refine ⟨36638624527901146981467971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24425749685267431320978647 36638624527901146981467971)
          ·
            refine ⟨54957936791851720472201957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36638624527901146981467971 54957936791851720472201957)
            ·
              refine ⟨10304613148472197588537867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54957936791851720472201957 10304613148472197588537867)
              ·
                refine ⟨15456919722708296382806801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10304613148472197588537867 15456919722708296382806801)
                ·
                  refine ⟨11592689792031222287105101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15456919722708296382806801 11592689792031222287105101)
                  ·
                    refine ⟨4347258672011708357664413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11592689792031222287105101 4347258672011708357664413)
                    ·
                      refine ⟨1630222002004390634124155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347258672011708357664413 1630222002004390634124155)
                      ·
                        rfl

theorem cell23_3174846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3174846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174846 prefixEnd_3174846 := by exact prefixLift 3174846
  have htrace : WordTrace (prefixWord ++ tailWord_3174846) baseStart_3174846 baseEnd_3174846 := by
    simpa [prefixWord, tailWord_3174846, baseEnd_3174846] using wordTrace_append hprefix tailTrace_3174846
  have hstable : (prefixWord ++ tailWord_3174846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174846).length < 2 ^ (prefixWord ++ tailWord_3174846).sum := by decide
  have hdescent : baseEnd_3174846 < baseStart_3174846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174889 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 3]
def baseStart_3174889 : Nat := 118140960795 + 3174889 * 2 ^ 59
def prefixEnd_3174889 : Nat := 4983230072969 + 3 ^ 40 * 3174889 * 2
def baseEnd_3174889 : Nat := 1630244081672533965886457

theorem tailTrace_3174889 : CollatzResearch.WordTrace tailWord_3174889 prefixEnd_3174889 1630244081672533965886457 := by
  unfold tailWord_3174889
  simp only [CollatzResearch.WordTrace]
  refine ⟨115797714994926855717343721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77198476663284570478229147 115797714994926855717343721)
  ·
    refine ⟨86848286246195141788007791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115797714994926855717343721 86848286246195141788007791)
    ·
      refine ⟨130272429369292712682011687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86848286246195141788007791 130272429369292712682011687)
      ·
        refine ⟨195408644053939069023017531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130272429369292712682011687 195408644053939069023017531)
        ·
          refine ⟨293112966080908603534526297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195408644053939069023017531 293112966080908603534526297)
          ·
            refine ⟨219834724560681452650894723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293112966080908603534526297 219834724560681452650894723)
            ·
              refine ⟨329752086841022178976342085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219834724560681452650894723 329752086841022178976342085)
              ·
                refine ⟨61828516282691658558064141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329752086841022178976342085 61828516282691658558064141)
                ·
                  refine ⟨23185693606009371959274053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61828516282691658558064141 23185693606009371959274053)
                  ·
                    refine ⟨4347317551126757242363885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23185693606009371959274053 4347317551126757242363885)
                    ·
                      refine ⟨1630244081672533965886457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347317551126757242363885 1630244081672533965886457)
                      ·
                        rfl

theorem cell23_3174889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_3174889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174889 prefixEnd_3174889 := by exact prefixLift 3174889
  have htrace : WordTrace (prefixWord ++ tailWord_3174889) baseStart_3174889 baseEnd_3174889 := by
    simpa [prefixWord, tailWord_3174889, baseEnd_3174889] using wordTrace_append hprefix tailTrace_3174889
  have hstable : (prefixWord ++ tailWord_3174889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174889).length < 2 ^ (prefixWord ++ tailWord_3174889).sum := by decide
  have hdescent : baseEnd_3174889 < baseStart_3174889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174923 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 3]
def baseStart_3174923 : Nat := 118140960795 + 3174923 * 2 ^ 59
def prefixEnd_3174923 : Nat := 4983230072969 + 3 ^ 40 * 3174923 * 2
def baseEnd_3174923 : Nat := 1630261540014786832861301

theorem tailTrace_3174923 : CollatzResearch.WordTrace tailWord_3174923 prefixEnd_3174923 1630261540014786832861301 := by
  unfold tailWord_3174923
  simp only [CollatzResearch.WordTrace]
  refine ⟨115798955076803679524081423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77199303384535786349387615 115798955076803679524081423)
  ·
    refine ⟨173698432615205519286122135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115798955076803679524081423 173698432615205519286122135)
    ·
      refine ⟨260547648922808278929183203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173698432615205519286122135 260547648922808278929183203)
      ·
        refine ⟨390821473384212418393774805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260547648922808278929183203 390821473384212418393774805)
        ·
          refine ⟨9159878282442478556104097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 390821473384212418393774805 9159878282442478556104097)
          ·
            refine ⟨6869908711831858917078073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9159878282442478556104097 6869908711831858917078073)
            ·
              refine ⟨5152431533873894187808555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6869908711831858917078073 5152431533873894187808555)
              ·
                refine ⟨7728647300810841281712833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152431533873894187808555 7728647300810841281712833)
                ·
                  refine ⟨5796485475608130961284625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7728647300810841281712833 5796485475608130961284625)
                  ·
                    refine ⟨4347364106706098220963469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5796485475608130961284625 4347364106706098220963469)
                    ·
                      refine ⟨1630261540014786832861301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347364106706098220963469 1630261540014786832861301)
                      ·
                        rfl

theorem cell23_3174923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 3].length) (baseStart_3174923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174923 prefixEnd_3174923 := by exact prefixLift 3174923
  have htrace : WordTrace (prefixWord ++ tailWord_3174923) baseStart_3174923 baseEnd_3174923 := by
    simpa [prefixWord, tailWord_3174923, baseEnd_3174923] using wordTrace_append hprefix tailTrace_3174923
  have hstable : (prefixWord ++ tailWord_3174923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174923).length < 2 ^ (prefixWord ++ tailWord_3174923).sum := by decide
  have hdescent : baseEnd_3174923 < baseStart_3174923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174947 : List Nat := [1, 1, 1, 4, 4, 3, 2, 2, 1, 4]
def baseStart_3174947 : Nat := 118140960795 + 3174947 * 2 ^ 59
def prefixEnd_3174947 : Nat := 4983230072969 + 3 ^ 40 * 3174947 * 2
def baseEnd_3174947 : Nat := 543424621183498246320397

theorem tailTrace_3174947 : CollatzResearch.WordTrace tailWord_3174947 prefixEnd_3174947 543424621183498246320397 := by
  unfold tailWord_3174947
  simp only [CollatzResearch.WordTrace]
  refine ⟨115799830428716731622955095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77199886952477821081970063 115799830428716731622955095)
  ·
    refine ⟨173699745643075097434432643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115799830428716731622955095 173699745643075097434432643)
    ·
      refine ⟨260549618464612646151648965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173699745643075097434432643 260549618464612646151648965)
      ·
        refine ⟨48853053462114871153434181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260549618464612646151648965 48853053462114871153434181)
        ·
          refine ⟨9159947524146538341268909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48853053462114871153434181 9159947524146538341268909)
          ·
            refine ⟨3434980321554951877975841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9159947524146538341268909 3434980321554951877975841)
            ·
              refine ⟨2576235241166213908481881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3434980321554951877975841 2576235241166213908481881)
              ·
                refine ⟨1932176430874660431361411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576235241166213908481881 1932176430874660431361411)
                ·
                  refine ⟨2898264646311990647042117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932176430874660431361411 2898264646311990647042117)
                  ·
                    refine ⟨543424621183498246320397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2898264646311990647042117 543424621183498246320397)
                    ·
                      rfl

theorem cell23_3174947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 1, 4].length) (baseStart_3174947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174947 prefixEnd_3174947 := by exact prefixLift 3174947
  have htrace : WordTrace (prefixWord ++ tailWord_3174947) baseStart_3174947 baseEnd_3174947 := by
    simpa [prefixWord, tailWord_3174947, baseEnd_3174947] using wordTrace_append hprefix tailTrace_3174947
  have hstable : (prefixWord ++ tailWord_3174947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174947).length < 2 ^ (prefixWord ++ tailWord_3174947).sum := by decide
  have hdescent : baseEnd_3174947 < baseStart_3174947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174974 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_3174974 : Nat := 118140960795 + 3174974 * 2 ^ 59
def prefixEnd_3174974 : Nat := 4983230072969 + 3 ^ 40 * 3174974 * 2
def baseEnd_3174974 : Nat := 1630287727528166133323567

theorem tailTrace_3174974 : CollatzResearch.WordTrace tailWord_3174974 prefixEnd_3174974 1630287727528166133323567 := by
  unfold tailWord_3174974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14475101899952364404273497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77200543466412610156125317 14475101899952364404273497)
  ·
    refine ⟨10856326424964273303205123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14475101899952364404273497 10856326424964273303205123)
    ·
      refine ⟨16284489637446409954807685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10856326424964273303205123 16284489637446409954807685)
      ·
        refine ⟨3053341807021201866526441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16284489637446409954807685 3053341807021201866526441)
        ·
          refine ⟨2290006355265901399894831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3053341807021201866526441 2290006355265901399894831)
          ·
            refine ⟨3435009532898852099842247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290006355265901399894831 3435009532898852099842247)
            ·
              refine ⟨5152514299348278149763371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3435009532898852099842247 5152514299348278149763371)
              ·
                refine ⟨7728771449022417224645057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152514299348278149763371 7728771449022417224645057)
                ·
                  refine ⟨5796578586766812918483793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7728771449022417224645057 5796578586766812918483793)
                  ·
                    refine ⟨4347433940075109688862845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5796578586766812918483793 4347433940075109688862845)
                    ·
                      refine ⟨1630287727528166133323567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4347433940075109688862845 1630287727528166133323567)
                      ·
                        rfl

theorem cell23_3174974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_3174974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174974 prefixEnd_3174974 := by exact prefixLift 3174974
  have htrace : WordTrace (prefixWord ++ tailWord_3174974) baseStart_3174974 baseEnd_3174974 := by
    simpa [prefixWord, tailWord_3174974, baseEnd_3174974] using wordTrace_append hprefix tailTrace_3174974
  have hstable : (prefixWord ++ tailWord_3174974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174974).length < 2 ^ (prefixWord ++ tailWord_3174974).sum := by decide
  have hdescent : baseEnd_3174974 < baseStart_3174974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3174976 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_3174976 : Nat := 118140960795 + 3174976 * 2 ^ 59
def prefixEnd_3174976 : Nat := 4983230072969 + 3 ^ 40 * 3174976 * 2
def baseEnd_3174976 : Nat := 1630288754489475125498557

theorem tailTrace_3174976 : CollatzResearch.WordTrace tailWord_3174976 prefixEnd_3174976 1630288754489475125498557 := by
  unfold tailWord_3174976
  simp only [CollatzResearch.WordTrace]
  refine ⟨57900444072805834787880391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77200592097074446383840521 57900444072805834787880391)
  ·
    refine ⟨86850666109208752181820587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57900444072805834787880391 86850666109208752181820587)
    ·
      refine ⟨130275999163813128272730881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86850666109208752181820587 130275999163813128272730881)
      ·
        refine ⟨97706999372859846204548161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130275999163813128272730881 97706999372859846204548161)
        ·
          refine ⟨73280249529644884653411121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97706999372859846204548161 73280249529644884653411121)
          ·
            refine ⟨54960187147233663490058341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73280249529644884653411121 54960187147233663490058341)
            ·
              refine ⟨10305035090106311904385939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54960187147233663490058341 10305035090106311904385939)
              ·
                refine ⟨15457552635159467856578909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10305035090106311904385939 15457552635159467856578909)
                ·
                  refine ⟨5796582238184800446217091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15457552635159467856578909 5796582238184800446217091)
                  ·
                    refine ⟨8694873357277200669325637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5796582238184800446217091 8694873357277200669325637)
                    ·
                      refine ⟨1630288754489475125498557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8694873357277200669325637 1630288754489475125498557)
                      ·
                        rfl

theorem cell23_3174976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_3174976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3174976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3174976 prefixEnd_3174976 := by exact prefixLift 3174976
  have htrace : WordTrace (prefixWord ++ tailWord_3174976) baseStart_3174976 baseEnd_3174976 := by
    simpa [prefixWord, tailWord_3174976, baseEnd_3174976] using wordTrace_append hprefix tailTrace_3174976
  have hstable : (prefixWord ++ tailWord_3174976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3174976).length < 2 ^ (prefixWord ++ tailWord_3174976).sum := by decide
  have hdescent : baseEnd_3174976 < baseStart_3174976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3174976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
