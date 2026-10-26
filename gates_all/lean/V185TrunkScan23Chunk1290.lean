import V185TrunkScan23Chunk1289

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7641273 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 5]
def baseStart_7641273 : Nat := 118140960795 + 7641273 * 2 ^ 59
def prefixEnd_7641273 : Nat := 4983230072969 + 3 ^ 40 * 7641273 * 2
def baseEnd_7641273 : Nat := 3923645861223387217945931

theorem tailTrace_7641273 : CollatzResearch.WordTrace tailWord_7641273 prefixEnd_7641273 3923645861223387217945931 := by
  unfold tailWord_7641273
  simp only [CollatzResearch.WordTrace]
  refine ⟨278700122445980421375120473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185800081630653614250080315 278700122445980421375120473)
  ·
    refine ⟨209025091834485316031340355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278700122445980421375120473 209025091834485316031340355)
    ·
      refine ⟨313537637751727974047010533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209025091834485316031340355 313537637751727974047010533)
      ·
        refine ⟨58788307078448995133814475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313537637751727974047010533 58788307078448995133814475)
        ·
          refine ⟨88182460617673492700721713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58788307078448995133814475 88182460617673492700721713)
          ·
            refine ⟨66136845463255119525541285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88182460617673492700721713 66136845463255119525541285)
            ·
              refine ⟨12400658524360334911038991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66136845463255119525541285 12400658524360334911038991)
              ·
                refine ⟨18600987786540502366558487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12400658524360334911038991 18600987786540502366558487)
                ·
                  refine ⟨27901481679810753549837731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18600987786540502366558487 27901481679810753549837731)
                  ·
                    refine ⟨41852222519716130324756597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27901481679810753549837731 41852222519716130324756597)
                    ·
                      refine ⟨3923645861223387217945931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41852222519716130324756597 3923645861223387217945931)
                      ·
                        rfl

theorem cell23_7641273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_7641273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641273 prefixEnd_7641273 := by exact prefixLift 7641273
  have htrace : WordTrace (prefixWord ++ tailWord_7641273) baseStart_7641273 baseEnd_7641273 := by
    simpa [prefixWord, tailWord_7641273, baseEnd_7641273] using wordTrace_append hprefix tailTrace_7641273
  have hstable : (prefixWord ++ tailWord_7641273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641273).length < 2 ^ (prefixWord ++ tailWord_7641273).sum := by decide
  have hdescent : baseEnd_7641273 < baseStart_7641273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641281 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7641281 : Nat := 118140960795 + 7641281 * 2 ^ 59
def prefixEnd_7641281 : Nat := 4983230072969 + 3 ^ 40 * 7641281 * 2
def baseEnd_7641281 : Nat := 3923649969068623186645895

theorem tailTrace_7641281 : CollatzResearch.WordTrace tailWord_7641281 prefixEnd_7641281 3923649969068623186645895 := by
  unfold tailWord_7641281
  simp only [CollatzResearch.WordTrace]
  refine ⟨278700414229951438741411697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185800276153300959160941131 278700414229951438741411697)
  ·
    refine ⟨209025310672463579056058773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278700414229951438741411697 209025310672463579056058773)
    ·
      refine ⟨9798061437771730268252755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209025310672463579056058773 9798061437771730268252755)
      ·
        refine ⟨14697092156657595402379133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9798061437771730268252755 14697092156657595402379133)
        ·
          refine ⟨5511409558746598275892175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14697092156657595402379133 5511409558746598275892175)
          ·
            refine ⟨8267114338119897413838263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511409558746598275892175 8267114338119897413838263)
            ·
              refine ⟨12400671507179846120757395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267114338119897413838263 12400671507179846120757395)
              ·
                refine ⟨18601007260769769181136093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12400671507179846120757395 18601007260769769181136093)
                ·
                  refine ⟨6975377722788663442926035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18601007260769769181136093 6975377722788663442926035)
                  ·
                    refine ⟨10463066584182995164389053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6975377722788663442926035 10463066584182995164389053)
                    ·
                      refine ⟨3923649969068623186645895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10463066584182995164389053 3923649969068623186645895)
                      ·
                        rfl

theorem cell23_7641281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7641281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641281 prefixEnd_7641281 := by exact prefixLift 7641281
  have htrace : WordTrace (prefixWord ++ tailWord_7641281) baseStart_7641281 baseEnd_7641281 := by
    simpa [prefixWord, tailWord_7641281, baseEnd_7641281] using wordTrace_append hprefix tailTrace_7641281
  have hstable : (prefixWord ++ tailWord_7641281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641281).length < 2 ^ (prefixWord ++ tailWord_7641281).sum := by decide
  have hdescent : baseEnd_7641281 < baseStart_7641281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641303 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_7641303 : Nat := 118140960795 + 7641303 * 2 ^ 59
def prefixEnd_7641303 : Nat := 4983230072969 + 3 ^ 40 * 7641303 * 2
def baseEnd_7641303 : Nat := 3923661265643022100570793

theorem tailTrace_7641303 : CollatzResearch.WordTrace tailWord_7641303 prefixEnd_7641303 3923661265643022100570793 := by
  unfold tailWord_7641303
  simp only [CollatzResearch.WordTrace]
  refine ⟨278701216635871736498712563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185800811090581157665808375 278701216635871736498712563)
  ·
    refine ⟨418051824953807604748068845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278701216635871736498712563 418051824953807604748068845)
    ·
      refine ⟨156769434357677851780525817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418051824953807604748068845 156769434357677851780525817)
      ·
        refine ⟨117577075768258388835394363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156769434357677851780525817 117577075768258388835394363)
        ·
          refine ⟨176365613652387583253091545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117577075768258388835394363 176365613652387583253091545)
          ·
            refine ⟨132274210239290687439818659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176365613652387583253091545 132274210239290687439818659)
            ·
              refine ⟨198411315358936031159727989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132274210239290687439818659 198411315358936031159727989)
              ·
                refine ⟨18601060814900252921224499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198411315358936031159727989 18601060814900252921224499)
                ·
                  refine ⟨27901591222350379381836749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18601060814900252921224499 27901591222350379381836749)
                  ·
                    refine ⟨10463096708381392268188781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27901591222350379381836749 10463096708381392268188781)
                    ·
                      refine ⟨3923661265643022100570793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10463096708381392268188781 3923661265643022100570793)
                      ·
                        rfl

theorem cell23_7641303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_7641303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641303 prefixEnd_7641303 := by exact prefixLift 7641303
  have htrace : WordTrace (prefixWord ++ tailWord_7641303) baseStart_7641303 baseEnd_7641303 := by
    simpa [prefixWord, tailWord_7641303, baseEnd_7641303] using wordTrace_append hprefix tailTrace_7641303
  have hstable : (prefixWord ++ tailWord_7641303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641303).length < 2 ^ (prefixWord ++ tailWord_7641303).sum := by decide
  have hdescent : baseEnd_7641303 < baseStart_7641303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641314 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7641314 : Nat := 118140960795 + 7641314 * 2 ^ 59
def prefixEnd_7641314 : Nat := 4983230072969 + 3 ^ 40 * 7641314 * 2
def baseEnd_7641314 : Nat := 1307888971310073852511081

theorem tailTrace_7641314 : CollatzResearch.WordTrace tailWord_7641314 prefixEnd_7641314 1307888971310073852511081 := by
  unfold tailWord_7641314
  simp only [CollatzResearch.WordTrace]
  refine ⟨69675404459707971344340749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185801078559221256918241997 69675404459707971344340749)
  ·
    refine ⟨26128276672390489254127781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69675404459707971344340749 26128276672390489254127781)
    ·
      refine ⟨4899051876073216735148959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26128276672390489254127781 4899051876073216735148959)
      ·
        refine ⟨7348577814109825102723439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899051876073216735148959 7348577814109825102723439)
        ·
          refine ⟨11022866721164737654085159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7348577814109825102723439 11022866721164737654085159)
          ·
            refine ⟨16534300081747106481127739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11022866721164737654085159 16534300081747106481127739)
            ·
              refine ⟨24801450122620659721691609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534300081747106481127739 24801450122620659721691609)
              ·
                refine ⟨18601087591965494791268707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24801450122620659721691609 18601087591965494791268707)
                ·
                  refine ⟨27901631387948242186903061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18601087591965494791268707 27901631387948242186903061)
                  ·
                    refine ⟨1307888971310073852511081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27901631387948242186903061 1307888971310073852511081)
                    ·
                      rfl

theorem cell23_7641314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7641314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641314 prefixEnd_7641314 := by exact prefixLift 7641314
  have htrace : WordTrace (prefixWord ++ tailWord_7641314) baseStart_7641314 baseEnd_7641314 := by
    simpa [prefixWord, tailWord_7641314, baseEnd_7641314] using wordTrace_append hprefix tailTrace_7641314
  have hstable : (prefixWord ++ tailWord_7641314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641314).length < 2 ^ (prefixWord ++ tailWord_7641314).sum := by decide
  have hdescent : baseEnd_7641314 < baseStart_7641314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641320 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_7641320 : Nat := 118140960795 + 7641320 * 2 ^ 59
def prefixEnd_7641320 : Nat := 4983230072969 + 3 ^ 40 * 7641320 * 2
def baseEnd_7641320 : Nat := 3923669994814148534058215

theorem tailTrace_7641320 : CollatzResearch.WordTrace tailWord_7641320 prefixEnd_7641320 3923669994814148534058215 := by
  unfold tailWord_7641320
  simp only [CollatzResearch.WordTrace]
  refine ⟨139350918338405074201040707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185801224451206765601387609 139350918338405074201040707)
  ·
    refine ⟨209026377507607611301561061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139350918338405074201040707 209026377507607611301561061)
    ·
      refine ⟨39192445782676427119042699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209026377507607611301561061 39192445782676427119042699)
      ·
        refine ⟨58788668674014640678564049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39192445782676427119042699 58788668674014640678564049)
        ·
          refine ⟨44091501505510980508923037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58788668674014640678564049 44091501505510980508923037)
          ·
            refine ⟨16534313064566617690846139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44091501505510980508923037 16534313064566617690846139)
            ·
              refine ⟨24801469596849926536269209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534313064566617690846139 24801469596849926536269209)
              ·
                refine ⟨18601102197637444902201907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24801469596849926536269209 18601102197637444902201907)
                ·
                  refine ⟨27901653296456167353302861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18601102197637444902201907 27901653296456167353302861)
                  ·
                    refine ⟨10463119986171062757488573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27901653296456167353302861 10463119986171062757488573)
                    ·
                      refine ⟨3923669994814148534058215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10463119986171062757488573 3923669994814148534058215)
                      ·
                        rfl

theorem cell23_7641320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_7641320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641320 prefixEnd_7641320 := by exact prefixLift 7641320
  have htrace : WordTrace (prefixWord ++ tailWord_7641320) baseStart_7641320 baseEnd_7641320 := by
    simpa [prefixWord, tailWord_7641320, baseEnd_7641320] using wordTrace_append hprefix tailTrace_7641320
  have hstable : (prefixWord ++ tailWord_7641320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641320).length < 2 ^ (prefixWord ++ tailWord_7641320).sum := by decide
  have hdescent : baseEnd_7641320 < baseStart_7641320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641336 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 3, 8]
def baseStart_7641336 : Nat := 118140960795 + 7641336 * 2 ^ 59
def prefixEnd_7641336 : Nat := 4983230072969 + 3 ^ 40 * 7641336 * 2
def baseEnd_7641336 : Nat := 1307892736834873490486047

theorem tailTrace_7641336 : CollatzResearch.WordTrace tailWord_7641336 prefixEnd_7641336 1307892736834873490486047 := by
  unfold tailWord_7641336
  simp only [CollatzResearch.WordTrace]
  refine ⟨139351210122376091567331931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185801613496501455423109241 139351210122376091567331931)
  ·
    refine ⟨209026815183564137350997897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139351210122376091567331931 209026815183564137350997897)
    ·
      refine ⟨156770111387673103013248423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209026815183564137350997897 156770111387673103013248423)
      ·
        refine ⟨235155167081509654519872635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156770111387673103013248423 235155167081509654519872635)
        ·
          refine ⟨352732750622264481779808953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235155167081509654519872635 352732750622264481779808953)
          ·
            refine ⟨264549562966698361334856715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352732750622264481779808953 264549562966698361334856715)
            ·
              refine ⟨396824344450047542002285073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264549562966698361334856715 396824344450047542002285073)
              ·
                refine ⟨297618258337535656501713805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396824344450047542002285073 297618258337535656501713805)
                ·
                  refine ⟨111606846876575871188142677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297618258337535656501713805 111606846876575871188142677)
                  ·
                    refine ⟨1307892736834873490486047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111606846876575871188142677 1307892736834873490486047)
                    ·
                      rfl

theorem cell23_7641336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_7641336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641336 prefixEnd_7641336 := by exact prefixLift 7641336
  have htrace : WordTrace (prefixWord ++ tailWord_7641336) baseStart_7641336 baseEnd_7641336 := by
    simpa [prefixWord, tailWord_7641336, baseEnd_7641336] using wordTrace_append hprefix tailTrace_7641336
  have hstable : (prefixWord ++ tailWord_7641336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641336).length < 2 ^ (prefixWord ++ tailWord_7641336).sum := by decide
  have hdescent : baseEnd_7641336 < baseStart_7641336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641353 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 2, 6]
def baseStart_7641353 : Nat := 118140960795 + 7641353 * 2 ^ 59
def prefixEnd_7641353 : Nat := 4983230072969 + 3 ^ 40 * 7641353 * 2
def baseEnd_7641353 : Nat := 1307895646558582301648521

theorem tailTrace_7641353 : CollatzResearch.WordTrace tailWord_7641353 prefixEnd_7641353 1307895646558582301648521 := by
  unfold tailWord_7641353
  simp only [CollatzResearch.WordTrace]
  refine ⟨278703040285690595038032713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185802026857127063358688475 278703040285690595038032713)
  ·
    refine ⟨209027280214267946278524535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278703040285690595038032713 209027280214267946278524535)
    ·
      refine ⟨313540920321401919417786803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209027280214267946278524535 313540920321401919417786803)
      ·
        refine ⟨470311380482102879126680205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313540920321401919417786803 470311380482102879126680205)
        ·
          refine ⟨176366767680788579672505077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470311380482102879126680205 176366767680788579672505077)
          ·
            refine ⟨16534384470073929344297351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176366767680788579672505077 16534384470073929344297351)
            ·
              refine ⟨24801576705110894016446027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534384470073929344297351 24801576705110894016446027)
              ·
                refine ⟨37202365057666341024669041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24801576705110894016446027 37202365057666341024669041)
                ·
                  refine ⟨27901773793249755768501781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37202365057666341024669041 27901773793249755768501781)
                  ·
                    refine ⟨1307895646558582301648521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27901773793249755768501781 1307895646558582301648521)
                    ·
                      rfl

theorem cell23_7641353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_7641353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641353 prefixEnd_7641353 := by exact prefixLift 7641353
  have htrace : WordTrace (prefixWord ++ tailWord_7641353) baseStart_7641353 baseEnd_7641353 := by
    simpa [prefixWord, tailWord_7641353, baseEnd_7641353] using wordTrace_append hprefix tailTrace_7641353
  have hstable : (prefixWord ++ tailWord_7641353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641353).length < 2 ^ (prefixWord ++ tailWord_7641353).sum := by decide
  have hdescent : baseEnd_7641353 < baseStart_7641353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641381 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 1, 3, 2]
def baseStart_7641381 : Nat := 118140960795 + 7641381 * 2 ^ 59
def prefixEnd_7641381 : Nat := 4983230072969 + 3 ^ 40 * 7641381 * 2
def baseEnd_7641381 : Nat := 3923701317134072795395435

theorem tailTrace_7641381 : CollatzResearch.WordTrace tailWord_7641381 prefixEnd_7641381 3923701317134072795395435 := by
  unfold tailWord_7641381
  simp only [CollatzResearch.WordTrace]
  refine ⟨278704061529589155820051997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185802707686392770546701331 278704061529589155820051997)
  ·
    refine ⟨104514023073595933432519499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278704061529589155820051997 104514023073595933432519499)
    ·
      refine ⟨156771034610393900148779249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104514023073595933432519499 156771034610393900148779249)
      ·
        refine ⟨117578275957795425111584437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156771034610393900148779249 117578275957795425111584437)
        ·
          refine ⟨11022963371043321104211041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117578275957795425111584437 11022963371043321104211041)
          ·
            refine ⟨8267222528282490828158281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11022963371043321104211041 8267222528282490828158281)
            ·
              refine ⟨6200416896211868121118711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8267222528282490828158281 6200416896211868121118711)
              ·
                refine ⟨9300625344317802181678067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200416896211868121118711 9300625344317802181678067)
                ·
                  refine ⟨13950938016476703272517101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9300625344317802181678067 13950938016476703272517101)
                  ·
                    refine ⟨5231601756178763727193913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13950938016476703272517101 5231601756178763727193913)
                    ·
                      refine ⟨3923701317134072795395435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231601756178763727193913 3923701317134072795395435)
                      ·
                        rfl

theorem cell23_7641381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_7641381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641381 prefixEnd_7641381 := by exact prefixLift 7641381
  have htrace : WordTrace (prefixWord ++ tailWord_7641381) baseStart_7641381 baseEnd_7641381 := by
    simpa [prefixWord, tailWord_7641381, baseEnd_7641381] using wordTrace_append hprefix tailTrace_7641381
  have hstable : (prefixWord ++ tailWord_7641381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641381).length < 2 ^ (prefixWord ++ tailWord_7641381).sum := by decide
  have hdescent : baseEnd_7641381 < baseStart_7641381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641394 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2]
def baseStart_7641394 : Nat := 118140960795 + 7641394 * 2 ^ 59
def prefixEnd_7641394 : Nat := 4983230072969 + 3 ^ 40 * 7641394 * 2
def baseEnd_7641394 : Nat := 3923707992382581244532875

theorem tailTrace_7641394 : CollatzResearch.WordTrace tailWord_7641394 prefixEnd_7641394 3923707992382581244532875 := by
  unfold tailWord_7641394
  simp only [CollatzResearch.WordTrace]
  refine ⟨69676133919635514760068809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185803023785694706026850157 69676133919635514760068809)
  ·
    refine ⟨52257100439726636070051607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69676133919635514760068809 52257100439726636070051607)
    ·
      refine ⟨78385650659589954105077411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52257100439726636070051607 78385650659589954105077411)
      ·
        refine ⟨117578475989384931157616117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78385650659589954105077411 117578475989384931157616117)
        ·
          refine ⟨11022982124004837296026511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117578475989384931157616117 11022982124004837296026511)
          ·
            refine ⟨16534473186007255944039767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11022982124004837296026511 16534473186007255944039767)
            ·
              refine ⟨24801709779010883916059651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534473186007255944039767 24801709779010883916059651)
              ·
                refine ⟨37202564668516325874089477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24801709779010883916059651 37202564668516325874089477)
                ·
                  refine ⟨6975480875346811101391777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37202564668516325874089477 6975480875346811101391777)
                  ·
                    refine ⟨5231610656510108326043833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6975480875346811101391777 5231610656510108326043833)
                    ·
                      refine ⟨3923707992382581244532875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231610656510108326043833 3923707992382581244532875)
                      ·
                        rfl

theorem cell23_7641394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_7641394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641394 prefixEnd_7641394 := by exact prefixLift 7641394
  have htrace : WordTrace (prefixWord ++ tailWord_7641394) baseStart_7641394 baseEnd_7641394 := by
    simpa [prefixWord, tailWord_7641394, baseEnd_7641394] using wordTrace_append hprefix tailTrace_7641394
  have hstable : (prefixWord ++ tailWord_7641394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641394).length < 2 ^ (prefixWord ++ tailWord_7641394).sum := by decide
  have hdescent : baseEnd_7641394 < baseStart_7641394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641400 : List Nat := [2, 1, 2, 1, 3, 1, 4, 4, 5]
def baseStart_7641400 : Nat := 118140960795 + 7641400 * 2 ^ 59
def prefixEnd_7641400 : Nat := 4983230072969 + 3 ^ 40 * 7641400 * 2
def baseEnd_7641400 : Nat := 435967897029612024561983

theorem tailTrace_7641400 : CollatzResearch.WordTrace tailWord_7641400 prefixEnd_7641400 435967897029612024561983 := by
  unfold tailWord_7641400
  simp only [CollatzResearch.WordTrace]
  refine ⟨139352377258260161032496827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185803169677680214709995769 139352377258260161032496827)
  ·
    refine ⟨209028565887390241548745241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139352377258260161032496827 209028565887390241548745241)
    ·
      refine ⟨156771424415542681161558931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209028565887390241548745241 156771424415542681161558931)
      ·
        refine ⟨235157136623314021742338397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156771424415542681161558931 235157136623314021742338397)
        ·
          refine ⟨88183926233742758153376899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235157136623314021742338397 88183926233742758153376899)
          ·
            refine ⟨132275889350614137230065349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88183926233742758153376899 132275889350614137230065349)
            ·
              refine ⟨24801729253240150730637253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132275889350614137230065349 24801729253240150730637253)
              ·
                refine ⟨4650324234982528261994485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24801729253240150730637253 4650324234982528261994485)
                ·
                  refine ⟨435967897029612024561983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4650324234982528261994485 435967897029612024561983)
                  ·
                    rfl

theorem cell23_7641400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 5].length) (baseStart_7641400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641400 prefixEnd_7641400 := by exact prefixLift 7641400
  have htrace : WordTrace (prefixWord ++ tailWord_7641400) baseStart_7641400 baseEnd_7641400 := by
    simpa [prefixWord, tailWord_7641400, baseEnd_7641400] using wordTrace_append hprefix tailTrace_7641400
  have hstable : (prefixWord ++ tailWord_7641400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641400).length < 2 ^ (prefixWord ++ tailWord_7641400).sum := by decide
  have hdescent : baseEnd_7641400 < baseStart_7641400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641462 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7641462 : Nat := 118140960795 + 7641462 * 2 ^ 59
def prefixEnd_7641462 : Nat := 4983230072969 + 3 ^ 40 * 7641462 * 2
def baseEnd_7641462 : Nat := 3923742909067086978482563

theorem tailTrace_7641462 : CollatzResearch.WordTrace tailWord_7641462 prefixEnd_7641462 3923742909067086978482563 := by
  unfold tailWord_7641462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17419188490143481665859415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185804677228197137769167093 17419188490143481665859415)
  ·
    refine ⟨26128782735215222498789123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17419188490143481665859415 26128782735215222498789123)
    ·
      refine ⟨39193174102822833748183685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26128782735215222498789123 39193174102822833748183685)
      ·
        refine ⟨7348720144279281327784441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39193174102822833748183685 7348720144279281327784441)
        ·
          refine ⟨5511540108209460995838331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7348720144279281327784441 5511540108209460995838331)
          ·
            refine ⟨8267310162314191493757497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511540108209460995838331 8267310162314191493757497)
            ·
              refine ⟨6200482621735643620318123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8267310162314191493757497 6200482621735643620318123)
              ·
                refine ⟨9300723932603465430477185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200482621735643620318123 9300723932603465430477185)
                ·
                  refine ⟨6975542949452599072857889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9300723932603465430477185 6975542949452599072857889)
                  ·
                    refine ⟨5231657212089449304643417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6975542949452599072857889 5231657212089449304643417)
                    ·
                      refine ⟨3923742909067086978482563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231657212089449304643417 3923742909067086978482563)
                      ·
                        rfl

theorem cell23_7641462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7641462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641462 prefixEnd_7641462 := by exact prefixLift 7641462
  have htrace : WordTrace (prefixWord ++ tailWord_7641462) baseStart_7641462 baseEnd_7641462 := by
    simpa [prefixWord, tailWord_7641462, baseEnd_7641462] using wordTrace_append hprefix tailTrace_7641462
  have hstable : (prefixWord ++ tailWord_7641462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641462).length < 2 ^ (prefixWord ++ tailWord_7641462).sum := by decide
  have hdescent : baseEnd_7641462 < baseStart_7641462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641463 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_7641463 : Nat := 118140960795 + 7641463 * 2 ^ 59
def prefixEnd_7641463 : Nat := 4983230072969 + 3 ^ 40 * 7641463 * 2
def baseEnd_7641463 : Nat := 3923743422547741474570057

theorem tailTrace_7641463 : CollatzResearch.WordTrace tailWord_7641463 prefixEnd_7641463 3923743422547741474570057 := by
  unfold tailWord_7641463
  simp only [CollatzResearch.WordTrace]
  refine ⟨278707052315292083824537043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185804701543528055883024695 278707052315292083824537043)
  ·
    refine ⟨418060578472938125736805565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278707052315292083824537043 418060578472938125736805565)
    ·
      refine ⟨156772716927351797151302087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418060578472938125736805565 156772716927351797151302087)
      ·
        refine ⟨235159075391027695726953131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156772716927351797151302087 235159075391027695726953131)
        ·
          refine ⟨352738613086541543590429697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235159075391027695726953131 352738613086541543590429697)
          ·
            refine ⟨264553959814906157692822273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352738613086541543590429697 264553959814906157692822273)
            ·
              refine ⟨198415469861179618269616705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264553959814906157692822273 198415469861179618269616705)
              ·
                refine ⟨148811602395884713702212529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198415469861179618269616705 148811602395884713702212529)
                ·
                  refine ⟨111608701796913535276659397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148811602395884713702212529 111608701796913535276659397)
                  ·
                    refine ⟨20926631586921287864373637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111608701796913535276659397 20926631586921287864373637)
                    ·
                      refine ⟨3923743422547741474570057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20926631586921287864373637 3923743422547741474570057)
                      ·
                        rfl

theorem cell23_7641463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_7641463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641463 prefixEnd_7641463 := by exact prefixLift 7641463
  have htrace : WordTrace (prefixWord ++ tailWord_7641463) baseStart_7641463 baseEnd_7641463 := by
    simpa [prefixWord, tailWord_7641463, baseEnd_7641463] using wordTrace_append hprefix tailTrace_7641463
  have hstable : (prefixWord ++ tailWord_7641463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641463).length < 2 ^ (prefixWord ++ tailWord_7641463).sum := by decide
  have hdescent : baseEnd_7641463 < baseStart_7641463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641493 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_7641493 : Nat := 118140960795 + 7641493 * 2 ^ 59
def prefixEnd_7641493 : Nat := 4983230072969 + 3 ^ 40 * 7641493 * 2
def baseEnd_7641493 : Nat := 3923758826967376357194919

theorem tailTrace_7641493 : CollatzResearch.WordTrace tailWord_7641493 prefixEnd_7641493 3923758826967376357194919 := by
  unfold tailWord_7641493
  simp only [CollatzResearch.WordTrace]
  refine ⟨278708146505183398948129133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185805431003455599298752755 278708146505183398948129133)
  ·
    refine ⟨104515554939443774605548425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278708146505183398948129133 104515554939443774605548425)
    ·
      refine ⟨78386666204582830954161319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104515554939443774605548425 78386666204582830954161319)
      ·
        refine ⟨117579999306874246431241979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78386666204582830954161319 117579999306874246431241979)
        ·
          refine ⟨176369998960311369646862969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117579999306874246431241979 176369998960311369646862969)
          ·
            refine ⟨132277499220233527235147227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176369998960311369646862969 132277499220233527235147227)
            ·
              refine ⟨198416248830350290852720841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132277499220233527235147227 198416248830350290852720841)
              ·
                refine ⟨148812186622762718139540631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198416248830350290852720841 148812186622762718139540631)
                ·
                  refine ⟨223218279934144077209310947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148812186622762718139540631 223218279934144077209310947)
                  ·
                    refine ⟨334827419901216115813966421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223218279934144077209310947 334827419901216115813966421)
                    ·
                      refine ⟨3923758826967376357194919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 334827419901216115813966421 3923758826967376357194919)
                      ·
                        rfl

theorem cell23_7641493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_7641493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641493 prefixEnd_7641493 := by exact prefixLift 7641493
  have htrace : WordTrace (prefixWord ++ tailWord_7641493) baseStart_7641493 baseEnd_7641493 := by
    simpa [prefixWord, tailWord_7641493, baseEnd_7641493] using wordTrace_append hprefix tailTrace_7641493
  have hstable : (prefixWord ++ tailWord_7641493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641493).length < 2 ^ (prefixWord ++ tailWord_7641493).sum := by decide
  have hdescent : baseEnd_7641493 < baseStart_7641493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641511 : List Nat := [1, 1, 6, 1, 1, 2, 4, 2, 1, 4]
def baseStart_7641511 : Nat := 118140960795 + 7641511 * 2 ^ 59
def prefixEnd_7641511 : Nat := 4983230072969 + 3 ^ 40 * 7641511 * 2
def baseEnd_7641511 : Nat := 1307922689873052428923279

theorem tailTrace_7641511 : CollatzResearch.WordTrace tailWord_7641511 prefixEnd_7641511 1307922689873052428923279 := by
  unfold tailWord_7641511
  simp only [CollatzResearch.WordTrace]
  refine ⟨278708803019118188022284387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185805868679412125348189591 278708803019118188022284387)
  ·
    refine ⟨418063204528677282033426581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278708803019118188022284387 418063204528677282033426581)
    ·
      refine ⟨19596712712281747595316871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 418063204528677282033426581 19596712712281747595316871)
      ·
        refine ⟨29395069068422621392975307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19596712712281747595316871 29395069068422621392975307)
        ·
          refine ⟨44092603602633932089462961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29395069068422621392975307 44092603602633932089462961)
          ·
            refine ⟨33069452701975449067097221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44092603602633932089462961 33069452701975449067097221)
            ·
              refine ⟨6200522381620396700080729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33069452701975449067097221 6200522381620396700080729)
              ·
                refine ⟨4650391786215297525060547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200522381620396700080729 4650391786215297525060547)
                ·
                  refine ⟨6975587679322946287590821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650391786215297525060547 6975587679322946287590821)
                  ·
                    refine ⟨1307922689873052428923279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6975587679322946287590821 1307922689873052428923279)
                    ·
                      rfl

theorem cell23_7641511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_7641511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641511 prefixEnd_7641511 := by exact prefixLift 7641511
  have htrace : WordTrace (prefixWord ++ tailWord_7641511) baseStart_7641511 baseEnd_7641511 := by
    simpa [prefixWord, tailWord_7641511, baseEnd_7641511] using wordTrace_append hprefix tailTrace_7641511
  have hstable : (prefixWord ++ tailWord_7641511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641511).length < 2 ^ (prefixWord ++ tailWord_7641511).sum := by decide
  have hdescent : baseEnd_7641511 < baseStart_7641511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641513 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_7641513 : Nat := 118140960795 + 7641513 * 2 ^ 59
def prefixEnd_7641513 : Nat := 4983230072969 + 3 ^ 40 * 7641513 * 2
def baseEnd_7641513 : Nat := 3923769096580466278944827

theorem tailTrace_7641513 : CollatzResearch.WordTrace tailWord_7641513 prefixEnd_7641513 3923769096580466278944827 := by
  unfold tailWord_7641513
  simp only [CollatzResearch.WordTrace]
  refine ⟨278708875965110942363857193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185805917310073961575904795 278708875965110942363857193)
  ·
    refine ⟨209031656973833206772892895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278708875965110942363857193 209031656973833206772892895)
    ·
      refine ⟨313547485460749810159339343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209031656973833206772892895 313547485460749810159339343)
      ·
        refine ⟨470321228191124715239009015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313547485460749810159339343 470321228191124715239009015)
        ·
          refine ⟨705481842286687072858513523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470321228191124715239009015 705481842286687072858513523)
          ·
            refine ⟨1058222763430030609287770285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705481842286687072858513523 1058222763430030609287770285)
            ·
              refine ⟨396833536286261478482913857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1058222763430030609287770285 396833536286261478482913857)
              ·
                refine ⟨297625152214696108862185393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396833536286261478482913857 297625152214696108862185393)
                ·
                  refine ⟨223218864161022081646639045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 297625152214696108862185393 223218864161022081646639045)
                  ·
                    refine ⟨41853537030191640308744821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223218864161022081646639045 41853537030191640308744821)
                    ·
                      refine ⟨3923769096580466278944827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41853537030191640308744821 3923769096580466278944827)
                      ·
                        rfl

theorem cell23_7641513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_7641513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641513 prefixEnd_7641513 := by exact prefixLift 7641513
  have htrace : WordTrace (prefixWord ++ tailWord_7641513) baseStart_7641513 baseEnd_7641513 := by
    simpa [prefixWord, tailWord_7641513, baseEnd_7641513] using wordTrace_append hprefix tailTrace_7641513
  have hstable : (prefixWord ++ tailWord_7641513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641513).length < 2 ^ (prefixWord ++ tailWord_7641513).sum := by decide
  have hdescent : baseEnd_7641513 < baseStart_7641513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641544 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 2, 3, 2]
def baseStart_7641544 : Nat := 118140960795 + 7641544 * 2 ^ 59
def prefixEnd_7641544 : Nat := 4983230072969 + 3 ^ 40 * 7641544 * 2
def baseEnd_7641544 : Nat := 3923785014480755657657185

theorem tailTrace_7641544 : CollatzResearch.WordTrace tailWord_7641544 prefixEnd_7641544 3923785014480755657657185 := by
  unfold tailWord_7641544
  simp only [CollatzResearch.WordTrace]
  refine ⟨139355003313999317329117843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185806671085332423105490457 139355003313999317329117843)
  ·
    refine ⟨209032504970998975993676765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139355003313999317329117843 209032504970998975993676765)
    ·
      refine ⟨78387189364124615997628787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209032504970998975993676765 78387189364124615997628787)
      ·
        refine ⟨117580784046186923996443181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78387189364124615997628787 117580784046186923996443181)
        ·
          refine ⟨44092794017320096498666193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117580784046186923996443181 44092794017320096498666193)
          ·
            refine ⟨33069595512990072373999645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44092794017320096498666193 33069595512990072373999645)
            ·
              refine ⟨12401098317371277140249867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33069595512990072373999645 12401098317371277140249867)
              ·
                refine ⟨18601647476056915710374801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12401098317371277140249867 18601647476056915710374801)
                ·
                  refine ⟨13951235607042686782781101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18601647476056915710374801 13951235607042686782781101)
                  ·
                    refine ⟨5231713352641007543542913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13951235607042686782781101 5231713352641007543542913)
                    ·
                      refine ⟨3923785014480755657657185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231713352641007543542913 3923785014480755657657185)
                      ·
                        rfl

theorem cell23_7641544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_7641544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641544 prefixEnd_7641544 := by exact prefixLift 7641544
  have htrace : WordTrace (prefixWord ++ tailWord_7641544) baseStart_7641544 baseEnd_7641544 := by
    simpa [prefixWord, tailWord_7641544, baseEnd_7641544] using wordTrace_append hprefix tailTrace_7641544
  have hstable : (prefixWord ++ tailWord_7641544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641544).length < 2 ^ (prefixWord ++ tailWord_7641544).sum := by decide
  have hdescent : baseEnd_7641544 < baseStart_7641544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641560 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_7641560 : Nat := 118140960795 + 7641560 * 2 ^ 59
def prefixEnd_7641560 : Nat := 4983230072969 + 3 ^ 40 * 7641560 * 2
def baseEnd_7641560 : Nat := 3923793230171227595057111

theorem tailTrace_7641560 : CollatzResearch.WordTrace tailWord_7641560 prefixEnd_7641560 3923793230171227595057111 := by
  unfold tailWord_7641560
  simp only [CollatzResearch.WordTrace]
  refine ⟨139355295097970334695409067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185807060130627112927212089 139355295097970334695409067)
  ·
    refine ⟨209032942646955502043113601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139355295097970334695409067 209032942646955502043113601)
    ·
      refine ⟨156774706985216626532335201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209032942646955502043113601 156774706985216626532335201)
      ·
        refine ⟨117581030238912469899251401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156774706985216626532335201 117581030238912469899251401)
        ·
          refine ⟨88185772679184352424438551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117581030238912469899251401 88185772679184352424438551)
          ·
            refine ⟨132278659018776528636657827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88185772679184352424438551 132278659018776528636657827)
            ·
              refine ⟨198417988528164792954986741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132278659018776528636657827 198417988528164792954986741)
              ·
                refine ⟨18601686424515449339530007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198417988528164792954986741 18601686424515449339530007)
                ·
                  refine ⟨27902529636773174009295011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18601686424515449339530007 27902529636773174009295011)
                  ·
                    refine ⟨41853794455159761013942517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27902529636773174009295011 41853794455159761013942517)
                    ·
                      refine ⟨3923793230171227595057111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41853794455159761013942517 3923793230171227595057111)
                      ·
                        rfl

theorem cell23_7641560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_7641560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641560 prefixEnd_7641560 := by exact prefixLift 7641560
  have htrace : WordTrace (prefixWord ++ tailWord_7641560) baseStart_7641560 baseEnd_7641560 := by
    simpa [prefixWord, tailWord_7641560, baseEnd_7641560] using wordTrace_append hprefix tailTrace_7641560
  have hstable : (prefixWord ++ tailWord_7641560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641560).length < 2 ^ (prefixWord ++ tailWord_7641560).sum := by decide
  have hdescent : baseEnd_7641560 < baseStart_7641560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641567 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 4, 4]
def baseStart_7641567 : Nat := 118140960795 + 7641567 * 2 ^ 59
def prefixEnd_7641567 : Nat := 4983230072969 + 3 ^ 40 * 7641567 * 2
def baseEnd_7641567 : Nat := 1307932274845269689223193

theorem tailTrace_7641567 : CollatzResearch.WordTrace tailWord_7641567 prefixEnd_7641567 1307932274845269689223193 := by
  unfold tailWord_7641567
  simp only [CollatzResearch.WordTrace]
  refine ⟨278710845506915309586322955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185807230337943539724215303 278710845506915309586322955)
  ·
    refine ⟨418066268260372964379484433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278710845506915309586322955 418066268260372964379484433)
    ·
      refine ⟨313549701195279723284613325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418066268260372964379484433 313549701195279723284613325)
      ·
        refine ⟨117581137948229896231729997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313549701195279723284613325 117581137948229896231729997)
        ·
          refine ⟨44092926730586211086898749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117581137948229896231729997 44092926730586211086898749)
          ·
            refine ⟨16534847523969829157587031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44092926730586211086898749 16534847523969829157587031)
            ·
              refine ⟨24802271285954743736380547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534847523969829157587031 24802271285954743736380547)
              ·
                refine ⟨37203406928932115604570821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24802271285954743736380547 37203406928932115604570821)
                ·
                  refine ⟨6975638799174771675857029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37203406928932115604570821 6975638799174771675857029)
                  ·
                    refine ⟨1307932274845269689223193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6975638799174771675857029 1307932274845269689223193)
                    ·
                      rfl

theorem cell23_7641567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_7641567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641567 prefixEnd_7641567 := by exact prefixLift 7641567
  have htrace : WordTrace (prefixWord ++ tailWord_7641567) baseStart_7641567 baseEnd_7641567 := by
    simpa [prefixWord, tailWord_7641567, baseEnd_7641567] using wordTrace_append hprefix tailTrace_7641567
  have hstable : (prefixWord ++ tailWord_7641567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641567).length < 2 ^ (prefixWord ++ tailWord_7641567).sum := by decide
  have hdescent : baseEnd_7641567 < baseStart_7641567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641584 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 2, 4]
def baseStart_7641584 : Nat := 118140960795 + 7641584 * 2 ^ 59
def prefixEnd_7641584 : Nat := 4983230072969 + 3 ^ 40 * 7641584 * 2
def baseEnd_7641584 : Nat := 1307935184568978500385667

theorem tailTrace_7641584 : CollatzResearch.WordTrace tailWord_7641584 prefixEnd_7641584 1307935184568978500385667 := by
  unfold tailWord_7641584
  simp only [CollatzResearch.WordTrace]
  refine ⟨139355732773926860744845903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185807643698569147659794537 139355732773926860744845903)
  ·
    refine ⟨209033599160890291117268855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139355732773926860744845903 209033599160890291117268855)
    ·
      refine ⟨313550398741335436675903283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209033599160890291117268855 313550398741335436675903283)
      ·
        refine ⟨470325598112003155013854925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313550398741335436675903283 470325598112003155013854925)
        ·
          refine ⟨176372099292001183130195597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470325598112003155013854925 176372099292001183130195597)
          ·
            refine ⟨66139537234500443673823349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176372099292001183130195597 66139537234500443673823349)
            ·
              refine ⟨6200581615734416594420939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66139537234500443673823349 6200581615734416594420939)
              ·
                refine ⟨9300872423601624891631409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200581615734416594420939 9300872423601624891631409)
                ·
                  refine ⟨6975654317701218668723557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9300872423601624891631409 6975654317701218668723557)
                  ·
                    refine ⟨1307935184568978500385667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6975654317701218668723557 1307935184568978500385667)
                    ·
                      rfl

theorem cell23_7641584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 4].length) (baseStart_7641584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641584 prefixEnd_7641584 := by exact prefixLift 7641584
  have htrace : WordTrace (prefixWord ++ tailWord_7641584) baseStart_7641584 baseEnd_7641584 := by
    simpa [prefixWord, tailWord_7641584, baseEnd_7641584] using wordTrace_append hprefix tailTrace_7641584
  have hstable : (prefixWord ++ tailWord_7641584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641584).length < 2 ^ (prefixWord ++ tailWord_7641584).sum := by decide
  have hdescent : baseEnd_7641584 < baseStart_7641584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641602 : List Nat := [3, 4, 1, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7641602 : Nat := 118140960795 + 7641602 * 2 ^ 59
def prefixEnd_7641602 : Nat := 4983230072969 + 3 ^ 40 * 7641602 * 2
def baseEnd_7641602 : Nat := 3923814796358716430731919

theorem tailTrace_7641602 : CollatzResearch.WordTrace tailWord_7641602 prefixEnd_7641602 3923814796358716430731919 := by
  unfold tailWord_7641602
  simp only [CollatzResearch.WordTrace]
  refine ⟨69678030515447127640961765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185808081374525673709231373 69678030515447127640961765)
  ·
    refine ⟨13064630721646336432680331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69678030515447127640961765 13064630721646336432680331)
    ·
      refine ⟨19596946082469504649020497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13064630721646336432680331 19596946082469504649020497)
      ·
        refine ⟨14697709561852128486765373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19596946082469504649020497 14697709561852128486765373)
        ·
          refine ⟨5511641085694548182537015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14697709561852128486765373 5511641085694548182537015)
          ·
            refine ⟨8267461628541822273805523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511641085694548182537015 8267461628541822273805523)
            ·
              refine ⟨12401192442812733410708285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267461628541822273805523 12401192442812733410708285)
              ·
                refine ⟨4650447166054775029015607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12401192442812733410708285 4650447166054775029015607)
                ·
                  refine ⟨6975670749082162543523411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650447166054775029015607 6975670749082162543523411)
                  ·
                    refine ⟨10463506123623243815285117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6975670749082162543523411 10463506123623243815285117)
                    ·
                      refine ⟨3923814796358716430731919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10463506123623243815285117 3923814796358716430731919)
                      ·
                        rfl

theorem cell23_7641602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7641602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641602 prefixEnd_7641602 := by exact prefixLift 7641602
  have htrace : WordTrace (prefixWord ++ tailWord_7641602) baseStart_7641602 baseEnd_7641602 := by
    simpa [prefixWord, tailWord_7641602, baseEnd_7641602] using wordTrace_append hprefix tailTrace_7641602
  have hstable : (prefixWord ++ tailWord_7641602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641602).length < 2 ^ (prefixWord ++ tailWord_7641602).sum := by decide
  have hdescent : baseEnd_7641602 < baseStart_7641602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641624 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 4, 1, 3]
def baseStart_7641624 : Nat := 118140960795 + 7641624 * 2 ^ 59
def prefixEnd_7641624 : Nat := 4983230072969 + 3 ^ 40 * 7641624 * 2
def baseEnd_7641624 : Nat := 3923826092933115344656817

theorem tailTrace_7641624 : CollatzResearch.WordTrace tailWord_7641624 prefixEnd_7641624 3923826092933115344656817 := by
  unfold tailWord_7641624
  simp only [CollatzResearch.WordTrace]
  refine ⟨139356462233854404160573963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185808616311805872214098617 139356462233854404160573963)
  ·
    refine ⟨209034693350781606240860945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139356462233854404160573963 209034693350781606240860945)
    ·
      refine ⟨156776020013086204680645709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209034693350781606240860945 156776020013086204680645709)
      ·
        refine ⟨58791007504907326755242141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156776020013086204680645709 58791007504907326755242141)
        ·
          refine ⟨22046627814340247533215803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58791007504907326755242141 22046627814340247533215803)
          ·
            refine ⟨33069941721510371299823705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22046627814340247533215803 33069941721510371299823705)
            ·
              refine ⟨24802456291132778474867779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33069941721510371299823705 24802456291132778474867779)
              ·
                refine ⟨37203684436699167712301669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24802456291132778474867779 37203684436699167712301669)
                ·
                  refine ⟨6975690831881093946056563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37203684436699167712301669 6975690831881093946056563)
                  ·
                    refine ⟨10463536247821640919084845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6975690831881093946056563 10463536247821640919084845)
                    ·
                      refine ⟨3923826092933115344656817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10463536247821640919084845 3923826092933115344656817)
                      ·
                        rfl

theorem cell23_7641624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_7641624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641624 prefixEnd_7641624 := by exact prefixLift 7641624
  have htrace : WordTrace (prefixWord ++ tailWord_7641624) baseStart_7641624 baseEnd_7641624 := by
    simpa [prefixWord, tailWord_7641624, baseEnd_7641624] using wordTrace_append hprefix tailTrace_7641624
  have hstable : (prefixWord ++ tailWord_7641624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641624).length < 2 ^ (prefixWord ++ tailWord_7641624).sum := by decide
  have hdescent : baseEnd_7641624 < baseStart_7641624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641634 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_7641634 : Nat := 118140960795 + 7641634 * 2 ^ 59
def prefixEnd_7641634 : Nat := 4983230072969 + 3 ^ 40 * 7641634 * 2
def baseEnd_7641634 : Nat := 3923831227739660305531771

theorem tailTrace_7641634 : CollatzResearch.WordTrace tailWord_7641634 prefixEnd_7641634 3923831227739660305531771 := by
  unfold tailWord_7641634
  simp only [CollatzResearch.WordTrace]
  refine ⟨69678322299418145007252989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185808859465115053352674637 69678322299418145007252989)
  ·
    refine ⟨26129370862281804377719871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69678322299418145007252989 26129370862281804377719871)
    ·
      refine ⟨39194056293422706566579807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26129370862281804377719871 39194056293422706566579807)
      ·
        refine ⟨58791084440134059849869711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39194056293422706566579807 58791084440134059849869711)
        ·
          refine ⟨88186626660201089774804567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58791084440134059849869711 88186626660201089774804567)
          ·
            refine ⟨132279939990301634662206851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88186626660201089774804567 132279939990301634662206851)
            ·
              refine ⟨198419909985452451993310277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132279939990301634662206851 198419909985452451993310277)
              ·
                refine ⟨37203733122272334748745677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198419909985452451993310277 37203733122272334748745677)
                ·
                  refine ⟨13951399920852125530779629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37203733122272334748745677 13951399920852125530779629)
                  ·
                    refine ⟨5231774970319547074042361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13951399920852125530779629 5231774970319547074042361)
                    ·
                      refine ⟨3923831227739660305531771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231774970319547074042361 3923831227739660305531771)
                      ·
                        rfl

theorem cell23_7641634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_7641634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641634 prefixEnd_7641634 := by exact prefixLift 7641634
  have htrace : WordTrace (prefixWord ++ tailWord_7641634) baseStart_7641634 baseEnd_7641634 := by
    simpa [prefixWord, tailWord_7641634, baseEnd_7641634] using wordTrace_append hprefix tailTrace_7641634
  have hstable : (prefixWord ++ tailWord_7641634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641634).length < 2 ^ (prefixWord ++ tailWord_7641634).sum := by decide
  have hdescent : baseEnd_7641634 < baseStart_7641634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641647 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 7, 4, 2]
def baseStart_7641647 : Nat := 118140960795 + 7641647 * 2 ^ 59
def prefixEnd_7641647 : Nat := 4983230072969 + 3 ^ 40 * 7641647 * 2
def baseEnd_7641647 : Nat := 3923837902988168754669211

theorem tailTrace_7641647 : CollatzResearch.WordTrace tailWord_7641647 prefixEnd_7641647 3923837902988168754669211 := by
  unfold tailWord_7641647
  simp only [CollatzResearch.WordTrace]
  refine ⟨278713763346625483249235195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185809175564416988832823463 278713763346625483249235195)
  ·
    refine ⟨418070645019938224873852793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278713763346625483249235195 418070645019938224873852793)
    ·
      refine ⟨313552983764953668655389595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418070645019938224873852793 313552983764953668655389595)
      ·
        refine ⟨470329475647430502983084393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313552983764953668655389595 470329475647430502983084393)
        ·
          refine ⟨352747106735572877237313295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470329475647430502983084393 352747106735572877237313295)
          ·
            refine ⟨529120660103359315855969943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352747106735572877237313295 529120660103359315855969943)
            ·
              refine ⟨793680990155038973783954915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529120660103359315855969943 793680990155038973783954915)
              ·
                refine ⟨1190521485232558460675932373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793680990155038973783954915 1190521485232558460675932373)
                ·
                  refine ⟨27902847310138088922092165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1190521485232558460675932373 27902847310138088922092165)
                  ·
                    refine ⟨5231783870650891672892281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27902847310138088922092165 5231783870650891672892281)
                    ·
                      refine ⟨3923837902988168754669211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231783870650891672892281 3923837902988168754669211)
                      ·
                        rfl

theorem cell23_7641647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4, 2].length) (baseStart_7641647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641647 prefixEnd_7641647 := by exact prefixLift 7641647
  have htrace : WordTrace (prefixWord ++ tailWord_7641647) baseStart_7641647 baseEnd_7641647 := by
    simpa [prefixWord, tailWord_7641647, baseEnd_7641647] using wordTrace_append hprefix tailTrace_7641647
  have hstable : (prefixWord ++ tailWord_7641647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641647).length < 2 ^ (prefixWord ++ tailWord_7641647).sum := by decide
  have hdescent : baseEnd_7641647 < baseStart_7641647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641664 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 6, 2, 2]
def baseStart_7641664 : Nat := 118140960795 + 7641664 * 2 ^ 59
def prefixEnd_7641664 : Nat := 4983230072969 + 3 ^ 40 * 7641664 * 2
def baseEnd_7641664 : Nat := 3923846632159295188156633

theorem tailTrace_7641664 : CollatzResearch.WordTrace tailWord_7641664 prefixEnd_7641664 3923846632159295188156633 := by
  unfold tailWord_7641664
  simp only [CollatzResearch.WordTrace]
  refine ⟨139357191693781947576302023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185809588925042596768402697 139357191693781947576302023)
  ·
    refine ⟨209035787540672921364453035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139357191693781947576302023 209035787540672921364453035)
    ·
      refine ⟨313553681311009382046679553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209035787540672921364453035 313553681311009382046679553)
      ·
        refine ⟨235165260983257036535009665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313553681311009382046679553 235165260983257036535009665)
        ·
          refine ⟨176373945737442777401257249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235165260983257036535009665 176373945737442777401257249)
          ·
            refine ⟨132280459303082083050942937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176373945737442777401257249 132280459303082083050942937)
            ·
              refine ⟨99210344477311562288207203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132280459303082083050942937 99210344477311562288207203)
              ·
                refine ⟨148815516715967343432310805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99210344477311562288207203 148815516715967343432310805)
                ·
                  refine ⟨6975727346060969223389569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148815516715967343432310805 6975727346060969223389569)
                  ·
                    refine ⟨5231795509545726917542177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6975727346060969223389569 5231795509545726917542177)
                    ·
                      refine ⟨3923846632159295188156633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231795509545726917542177 3923846632159295188156633)
                      ·
                        rfl

theorem cell23_7641664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_7641664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641664 prefixEnd_7641664 := by exact prefixLift 7641664
  have htrace : WordTrace (prefixWord ++ tailWord_7641664) baseStart_7641664 baseEnd_7641664 := by
    simpa [prefixWord, tailWord_7641664, baseEnd_7641664] using wordTrace_append hprefix tailTrace_7641664
  have hstable : (prefixWord ++ tailWord_7641664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641664).length < 2 ^ (prefixWord ++ tailWord_7641664).sum := by decide
  have hdescent : baseEnd_7641664 < baseStart_7641664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641681 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 2, 2, 2]
def baseStart_7641681 : Nat := 118140960795 + 7641681 * 2 ^ 59
def prefixEnd_7641681 : Nat := 4983230072969 + 3 ^ 40 * 7641681 * 2
def baseEnd_7641681 : Nat := 3923855361330421621644055

theorem tailTrace_7641681 : CollatzResearch.WordTrace tailWord_7641681 prefixEnd_7641681 3923855361330421621644055 := by
  unfold tailWord_7641681
  simp only [CollatzResearch.WordTrace]
  refine ⟨278715003428502307055972897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185810002285668204703981931 278715003428502307055972897)
  ·
    refine ⟨209036252571376730291979673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278715003428502307055972897 209036252571376730291979673)
    ·
      refine ⟨156777189428532547718984755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209036252571376730291979673 156777189428532547718984755)
      ·
        refine ⟨235165784142798821578477133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156777189428532547718984755 235165784142798821578477133)
        ·
          refine ⟨88187169053549558091928925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235165784142798821578477133 88187169053549558091928925)
          ·
            refine ⟨33070188395081084284473347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88187169053549558091928925 33070188395081084284473347)
            ·
              refine ⟨49605282592621626426710021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33070188395081084284473347 49605282592621626426710021)
              ·
                refine ⟨9300990486116554955008129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49605282592621626426710021 9300990486116554955008129)
                ·
                  refine ⟨6975742864587416216256097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9300990486116554955008129 6975742864587416216256097)
                  ·
                    refine ⟨5231807148440562162192073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6975742864587416216256097 5231807148440562162192073)
                    ·
                      refine ⟨3923855361330421621644055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231807148440562162192073 3923855361330421621644055)
                      ·
                        rfl

theorem cell23_7641681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_7641681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641681 prefixEnd_7641681 := by exact prefixLift 7641681
  have htrace : WordTrace (prefixWord ++ tailWord_7641681) baseStart_7641681 baseEnd_7641681 := by
    simpa [prefixWord, tailWord_7641681, baseEnd_7641681] using wordTrace_append hprefix tailTrace_7641681
  have hstable : (prefixWord ++ tailWord_7641681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641681).length < 2 ^ (prefixWord ++ tailWord_7641681).sum := by decide
  have hdescent : baseEnd_7641681 < baseStart_7641681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641690 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_7641690 : Nat := 118140960795 + 7641690 * 2 ^ 59
def prefixEnd_7641690 : Nat := 4983230072969 + 3 ^ 40 * 7641690 * 2
def baseEnd_7641690 : Nat := 3923859982656312086431513

theorem tailTrace_7641690 : CollatzResearch.WordTrace tailWord_7641690 prefixEnd_7641690 3923859982656312086431513 := by
  unfold tailWord_7641690
  simp only [CollatzResearch.WordTrace]
  refine ⟨69678832921367425398262631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185810221123646467728700349 69678832921367425398262631)
  ·
    refine ⟨104518249382051138097393947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69678832921367425398262631 104518249382051138097393947)
    ·
      refine ⟨156777374073076707146090921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104518249382051138097393947 156777374073076707146090921)
      ·
        refine ⟨117583030554807530359568191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156777374073076707146090921 117583030554807530359568191)
        ·
          refine ⟨176374545832211295539352287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117583030554807530359568191 176374545832211295539352287)
          ·
            refine ⟨264561818748316943309028431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176374545832211295539352287 264561818748316943309028431)
            ·
              refine ⟨396842728122475414963542647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264561818748316943309028431 396842728122475414963542647)
              ·
                refine ⟨595264092183713122445313971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396842728122475414963542647 595264092183713122445313971)
                ·
                  refine ⟨892896138275569683667970957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595264092183713122445313971 892896138275569683667970957)
                  ·
                    refine ⟨334836051853338631375489109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892896138275569683667970957 334836051853338631375489109)
                    ·
                      refine ⟨3923859982656312086431513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 334836051853338631375489109 3923859982656312086431513)
                      ·
                        rfl

theorem cell23_7641690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_7641690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641690 prefixEnd_7641690 := by exact prefixLift 7641690
  have htrace : WordTrace (prefixWord ++ tailWord_7641690) baseStart_7641690 baseEnd_7641690 := by
    simpa [prefixWord, tailWord_7641690, baseEnd_7641690] using wordTrace_append hprefix tailTrace_7641690
  have hstable : (prefixWord ++ tailWord_7641690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641690).length < 2 ^ (prefixWord ++ tailWord_7641690).sum := by decide
  have hdescent : baseEnd_7641690 < baseStart_7641690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641697 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_7641697 : Nat := 118140960795 + 7641697 * 2 ^ 59
def prefixEnd_7641697 : Nat := 4983230072969 + 3 ^ 40 * 7641697 * 2
def baseEnd_7641697 : Nat := 3923863577020893559043981

theorem tailTrace_7641697 : CollatzResearch.WordTrace tailWord_7641697 prefixEnd_7641697 3923863577020893559043981 := by
  unfold tailWord_7641697
  simp only [CollatzResearch.WordTrace]
  refine ⟨278715586996444341788555345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185810391330962894525703563 278715586996444341788555345)
  ·
    refine ⟨209036690247333256341416509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278715586996444341788555345 209036690247333256341416509)
    ·
      refine ⟨78388758842749971128031191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209036690247333256341416509 78388758842749971128031191)
      ·
        refine ⟨117583138264124956692046787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78388758842749971128031191 117583138264124956692046787)
        ·
          refine ⟨176374707396187435038070181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117583138264124956692046787 176374707396187435038070181)
          ·
            refine ⟨33070257636785144069638159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176374707396187435038070181 33070257636785144069638159)
            ·
              refine ⟨49605386455177716104457239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33070257636785144069638159 49605386455177716104457239)
              ·
                refine ⟨74408079682766574156685859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49605386455177716104457239 74408079682766574156685859)
                ·
                  refine ⟨111612119524149861235028789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74408079682766574156685859 111612119524149861235028789)
                  ·
                    refine ⟨10463636205389049490783949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111612119524149861235028789 10463636205389049490783949)
                    ·
                      refine ⟨3923863577020893559043981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10463636205389049490783949 3923863577020893559043981)
                      ·
                        rfl

theorem cell23_7641697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_7641697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641697 prefixEnd_7641697 := by exact prefixLift 7641697
  have htrace : WordTrace (prefixWord ++ tailWord_7641697) baseStart_7641697 baseEnd_7641697 := by
    simpa [prefixWord, tailWord_7641697, baseEnd_7641697] using wordTrace_append hprefix tailTrace_7641697
  have hstable : (prefixWord ++ tailWord_7641697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641697).length < 2 ^ (prefixWord ++ tailWord_7641697).sum := by decide
  have hdescent : baseEnd_7641697 < baseStart_7641697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641704 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 7]
def baseStart_7641704 : Nat := 118140960795 + 7641704 * 2 ^ 59
def prefixEnd_7641704 : Nat := 4983230072969 + 3 ^ 40 * 7641704 * 2
def baseEnd_7641704 : Nat := 435985241265052781295161

theorem tailTrace_7641704 : CollatzResearch.WordTrace tailWord_7641704 prefixEnd_7641704 435985241265052781295161 := by
  unfold tailWord_7641704
  simp only [CollatzResearch.WordTrace]
  refine ⟨139357921153709490992030083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185810561538279321322706777 139357921153709490992030083)
  ·
    refine ⟨209036881730564236488045125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139357921153709490992030083 209036881730564236488045125)
    ·
      refine ⟨39194415324480794341508461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209036881730564236488045125 39194415324480794341508461)
      ·
        refine ⟨14697905746680297878065673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39194415324480794341508461 14697905746680297878065673)
        ·
          refine ⟨11023429310010223408549255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14697905746680297878065673 11023429310010223408549255)
          ·
            refine ⟨16535143965015335112823883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11023429310010223408549255 16535143965015335112823883)
            ·
              refine ⟨24802715947523002669235825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16535143965015335112823883 24802715947523002669235825)
              ·
                refine ⟨18602036960642252001926869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24802715947523002669235825 18602036960642252001926869)
                ·
                  refine ⟨435985241265052781295161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18602036960642252001926869 435985241265052781295161)
                  ·
                    rfl

theorem cell23_7641704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 7].length) (baseStart_7641704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641704 prefixEnd_7641704 := by exact prefixLift 7641704
  have htrace : WordTrace (prefixWord ++ tailWord_7641704) baseStart_7641704 baseEnd_7641704 := by
    simpa [prefixWord, tailWord_7641704, baseEnd_7641704] using wordTrace_append hprefix tailTrace_7641704
  have hstable : (prefixWord ++ tailWord_7641704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641704).length < 2 ^ (prefixWord ++ tailWord_7641704).sum := by decide
  have hdescent : baseEnd_7641704 < baseStart_7641704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641737 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_7641737 : Nat := 118140960795 + 7641737 * 2 ^ 59
def prefixEnd_7641737 : Nat := 4983230072969 + 3 ^ 40 * 7641737 * 2
def baseEnd_7641737 : Nat := 3923884116247073402543797

theorem tailTrace_7641737 : CollatzResearch.WordTrace tailWord_7641737 prefixEnd_7641737 3923884116247073402543797 := by
  unfold tailWord_7641737
  simp only [CollatzResearch.WordTrace]
  refine ⟨278717045916299428620011465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185811363944199619080007643 278717045916299428620011465)
  ·
    refine ⟨209037784437224571465008599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278717045916299428620011465 209037784437224571465008599)
    ·
      refine ⟨313556676655836857197512899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209037784437224571465008599 313556676655836857197512899)
      ·
        refine ⟨470335014983755285796269349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313556676655836857197512899 470335014983755285796269349)
        ·
          refine ⟨88187815309454116086800503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470335014983755285796269349 88187815309454116086800503)
          ·
            refine ⟨132281722964181174130200755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88187815309454116086800503 132281722964181174130200755)
            ·
              refine ⟨198422584446271761195301133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132281722964181174130200755 198422584446271761195301133)
              ·
                refine ⟨74408469167351910448237925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198422584446271761195301133 74408469167351910448237925)
                ·
                  refine ⟨13951587968878483209044611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74408469167351910448237925 13951587968878483209044611)
                  ·
                    refine ⟨20927381953317724813566917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13951587968878483209044611 20927381953317724813566917)
                    ·
                      refine ⟨3923884116247073402543797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20927381953317724813566917 3923884116247073402543797)
                      ·
                        rfl

theorem cell23_7641737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_7641737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641737 prefixEnd_7641737 := by exact prefixLift 7641737
  have htrace : WordTrace (prefixWord ++ tailWord_7641737) baseStart_7641737 baseEnd_7641737 := by
    simpa [prefixWord, tailWord_7641737, baseEnd_7641737] using wordTrace_append hprefix tailTrace_7641737
  have hstable : (prefixWord ++ tailWord_7641737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641737).length < 2 ^ (prefixWord ++ tailWord_7641737).sum := by decide
  have hdescent : baseEnd_7641737 < baseStart_7641737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641747 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 7, 4]
def baseStart_7641747 : Nat := 118140960795 + 7641747 * 2 ^ 59
def prefixEnd_7641747 : Nat := 4983230072969 + 3 ^ 40 * 7641747 * 2
def baseEnd_7641747 : Nat := 1307963083684539454472917

theorem tailTrace_7641747 : CollatzResearch.WordTrace tailWord_7641747 prefixEnd_7641747 1307963083684539454472917 := by
  unfold tailWord_7641747
  simp only [CollatzResearch.WordTrace]
  refine ⟨278717410646263200327875495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185811607097508800218583663 278717410646263200327875495)
  ·
    refine ⟨418076115969394800491813243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278717410646263200327875495 418076115969394800491813243)
    ·
      refine ⟨627114173954092200737719865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418076115969394800491813243 627114173954092200737719865)
      ·
        refine ⟨470335630465569150553289899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627114173954092200737719865 470335630465569150553289899)
        ·
          refine ⟨705503445698353725829934849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470335630465569150553289899 705503445698353725829934849)
          ·
            refine ⟨529127584273765294372451137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705503445698353725829934849 529127584273765294372451137)
            ·
              refine ⟨396845688205323970779338353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529127584273765294372451137 396845688205323970779338353)
              ·
                refine ⟨297634266153992978084503765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396845688205323970779338353 297634266153992978084503765)
                ·
                  refine ⟨6975803112984210423855557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297634266153992978084503765 6975803112984210423855557)
                  ·
                    refine ⟨1307963083684539454472917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6975803112984210423855557 1307963083684539454472917)
                    ·
                      rfl

theorem cell23_7641747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 4].length) (baseStart_7641747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641747 prefixEnd_7641747 := by exact prefixLift 7641747
  have htrace : WordTrace (prefixWord ++ tailWord_7641747) baseStart_7641747 baseEnd_7641747 := by
    simpa [prefixWord, tailWord_7641747, baseEnd_7641747] using wordTrace_append hprefix tailTrace_7641747
  have hstable : (prefixWord ++ tailWord_7641747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641747).length < 2 ^ (prefixWord ++ tailWord_7641747).sum := by decide
  have hdescent : baseEnd_7641747 < baseStart_7641747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641764 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_7641764 : Nat := 118140960795 + 7641764 * 2 ^ 59
def prefixEnd_7641764 : Nat := 4983230072969 + 3 ^ 40 * 7641764 * 2
def baseEnd_7641764 : Nat := 1307965993408248265635391

theorem tailTrace_7641764 : CollatzResearch.WordTrace tailWord_7641764 prefixEnd_7641764 1307965993408248265635391 := by
  unfold tailWord_7641764
  simp only [CollatzResearch.WordTrace]
  refine ⟨139359015343600806115622173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185812020458134408154162897 139359015343600806115622173)
  ·
    refine ⟨52259630753850302293358315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139359015343600806115622173 52259630753850302293358315)
    ·
      refine ⟨78389446130775453440037473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52259630753850302293358315 78389446130775453440037473)
      ·
        refine ⟨58792084598081590080028105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78389446130775453440037473 58792084598081590080028105)
        ·
          refine ⟨44094063448561192560021079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58792084598081590080028105 44094063448561192560021079)
          ·
            refine ⟨66141095172841788840031619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44094063448561192560021079 66141095172841788840031619)
            ·
              refine ⟨99211642759262683260047429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66141095172841788840031619 99211642759262683260047429)
              ·
                refine ⟨18602183017361753111258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99211642759262683260047429 18602183017361753111258893)
                ·
                  refine ⟨6975818631510657416722085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18602183017361753111258893 6975818631510657416722085)
                  ·
                    refine ⟨1307965993408248265635391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6975818631510657416722085 1307965993408248265635391)
                    ·
                      rfl

theorem cell23_7641764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_7641764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641764 prefixEnd_7641764 := by exact prefixLift 7641764
  have htrace : WordTrace (prefixWord ++ tailWord_7641764) baseStart_7641764 baseEnd_7641764 := by
    simpa [prefixWord, tailWord_7641764, baseEnd_7641764] using wordTrace_append hprefix tailTrace_7641764
  have hstable : (prefixWord ++ tailWord_7641764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641764).length < 2 ^ (prefixWord ++ tailWord_7641764).sum := by decide
  have hdescent : baseEnd_7641764 < baseStart_7641764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641841 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 1, 5]
def baseStart_7641841 : Nat := 118140960795 + 7641841 * 2 ^ 59
def prefixEnd_7641841 : Nat := 4983230072969 + 3 ^ 40 * 7641841 * 2
def baseEnd_7641841 : Nat := 1307979172745046998547773

theorem tailTrace_7641841 : CollatzResearch.WordTrace tailWord_7641841 prefixEnd_7641841 1307979172745046998547773 := by
  unfold tailWord_7641841
  simp only [CollatzResearch.WordTrace]
  refine ⟨278720839107922654381797377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185813892738615102921198251 278720839107922654381797377)
  ·
    refine ⟨209040629330941990786348033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278720839107922654381797377 209040629330941990786348033)
    ·
      refine ⟨156780471998206493089761025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209040629330941990786348033 156780471998206493089761025)
      ·
        refine ⟨117585353998654869817320769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156780471998206493089761025 117585353998654869817320769)
        ·
          refine ⟨88189015498991152362990577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117585353998654869817320769 88189015498991152362990577)
          ·
            refine ⟨66141761624243364272242933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88189015498991152362990577 66141761624243364272242933)
            ·
              refine ⟨6200790152272815400522775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66141761624243364272242933 6200790152272815400522775)
              ·
                refine ⟨9301185228409223100784163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200790152272815400522775 9301185228409223100784163)
                ·
                  refine ⟨13951777842613834651176245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9301185228409223100784163 13951777842613834651176245)
                  ·
                    refine ⟨1307979172745046998547773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13951777842613834651176245 1307979172745046998547773)
                    ·
                      rfl

theorem cell23_7641841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_7641841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641841 prefixEnd_7641841 := by exact prefixLift 7641841
  have htrace : WordTrace (prefixWord ++ tailWord_7641841) baseStart_7641841 baseEnd_7641841 := by
    simpa [prefixWord, tailWord_7641841, baseEnd_7641841] using wordTrace_append hprefix tailTrace_7641841
  have hstable : (prefixWord ++ tailWord_7641841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641841).length < 2 ^ (prefixWord ++ tailWord_7641841).sum := by decide
  have hdescent : baseEnd_7641841 < baseStart_7641841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641845 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 6]
def baseStart_7641845 : Nat := 118140960795 + 7641845 * 2 ^ 59
def prefixEnd_7641845 : Nat := 4983230072969 + 3 ^ 40 * 7641845 * 2
def baseEnd_7641845 : Nat := 435993285795306553332589

theorem tailTrace_7641845 : CollatzResearch.WordTrace tailWord_7641845 prefixEnd_7641845 435993285795306553332589 := by
  unfold tailWord_7641845
  simp only [CollatzResearch.WordTrace]
  refine ⟨278720984999908163064942989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185813989999938775376628659 278720984999908163064942989)
  ·
    refine ⟨104520369374965561149353621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278720984999908163064942989 104520369374965561149353621)
    ·
      refine ⟨4899392314451510678875951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104520369374965561149353621 4899392314451510678875951)
      ·
        refine ⟨7349088471677266018313927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899392314451510678875951 7349088471677266018313927)
        ·
          refine ⟨11023632707515899027470891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7349088471677266018313927 11023632707515899027470891)
          ·
            refine ⟨16535449061273848541206337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11023632707515899027470891 16535449061273848541206337)
            ·
              refine ⟨12401586795955386405904753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16535449061273848541206337 12401586795955386405904753)
              ·
                refine ⟨9301190096966539804428565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12401586795955386405904753 9301190096966539804428565)
                ·
                  refine ⟨435993285795306553332589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9301190096966539804428565 435993285795306553332589)
                  ·
                    rfl

theorem cell23_7641845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_7641845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641845 prefixEnd_7641845 := by exact prefixLift 7641845
  have htrace : WordTrace (prefixWord ++ tailWord_7641845) baseStart_7641845 baseEnd_7641845 := by
    simpa [prefixWord, tailWord_7641845, baseEnd_7641845] using wordTrace_append hprefix tailTrace_7641845
  have hstable : (prefixWord ++ tailWord_7641845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641845).length < 2 ^ (prefixWord ++ tailWord_7641845).sum := by decide
  have hdescent : baseEnd_7641845 < baseStart_7641845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641861 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 7, 2, 2]
def baseStart_7641861 : Nat := 118140960795 + 7641861 * 2 ^ 59
def prefixEnd_7641861 : Nat := 4983230072969 + 3 ^ 40 * 7641861 * 2
def baseEnd_7641861 : Nat := 3923947787848230917393227

theorem tailTrace_7641861 : CollatzResearch.WordTrace tailWord_7641861 prefixEnd_7641861 3923947787848230917393227 := by
  unfold tailWord_7641861
  simp only [CollatzResearch.WordTrace]
  refine ⟨278721568567850197797525437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185814379045233465198350291 278721568567850197797525437)
  ·
    refine ⟨104520588212943824174072039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278721568567850197797525437 104520588212943824174072039)
    ·
      refine ⟨156780882319415736261108059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104520588212943824174072039 156780882319415736261108059)
      ·
        refine ⟨235171323479123604391662089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156780882319415736261108059 235171323479123604391662089)
        ·
          refine ⟨176378492609342703293746567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235171323479123604391662089 176378492609342703293746567)
          ·
            refine ⟨264567738914014054940619851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176378492609342703293746567 264567738914014054940619851)
            ·
              refine ⟨396851608371021082410929777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264567738914014054940619851 396851608371021082410929777)
              ·
                refine ⟨297638706278265811808197333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396851608371021082410929777 297638706278265811808197333)
                ·
                  refine ⟨6975907178396854964254625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297638706278265811808197333 6975907178396854964254625)
                  ·
                    refine ⟨5231930383797641223190969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6975907178396854964254625 5231930383797641223190969)
                    ·
                      refine ⟨3923947787848230917393227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231930383797641223190969 3923947787848230917393227)
                      ·
                        rfl

theorem cell23_7641861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_7641861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641861 prefixEnd_7641861 := by exact prefixLift 7641861
  have htrace : WordTrace (prefixWord ++ tailWord_7641861) baseStart_7641861 baseEnd_7641861 := by
    simpa [prefixWord, tailWord_7641861, baseEnd_7641861] using wordTrace_append hprefix tailTrace_7641861
  have hstable : (prefixWord ++ tailWord_7641861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641861).length < 2 ^ (prefixWord ++ tailWord_7641861).sum := by decide
  have hdescent : baseEnd_7641861 < baseStart_7641861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641897 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 4, 7]
def baseStart_7641897 : Nat := 118140960795 + 7641897 * 2 ^ 59
def prefixEnd_7641897 : Nat := 4983230072969 + 3 ^ 40 * 7641897 * 2
def baseEnd_7641897 : Nat := 1307988757717264258847687

theorem tailTrace_7641897 : CollatzResearch.WordTrace tailWord_7641897 prefixEnd_7641897 1307988757717264258847687 := by
  unfold tailWord_7641897
  simp only [CollatzResearch.WordTrace]
  refine ⟨278722881595719775945835945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185815254397146517297223963 278722881595719775945835945)
  ·
    refine ⟨209042161196789831959376959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278722881595719775945835945 209042161196789831959376959)
    ·
      refine ⟨313563241795184747939065439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209042161196789831959376959 313563241795184747939065439)
      ·
        refine ⟨470344862692777121908598159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313563241795184747939065439 470344862692777121908598159)
        ·
          refine ⟨705517294039165682862897239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470344862692777121908598159 705517294039165682862897239)
          ·
            refine ⟨1058275941058748524294345859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705517294039165682862897239 1058275941058748524294345859)
            ·
              refine ⟨1587413911588122786441518789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058275941058748524294345859 1587413911588122786441518789)
              ·
                refine ⟨297640108422773022457784773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1587413911588122786441518789 297640108422773022457784773)
                ·
                  refine ⟨55807520329269941710834645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297640108422773022457784773 55807520329269941710834645)
                  ·
                    refine ⟨1307988757717264258847687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55807520329269941710834645 1307988757717264258847687)
                    ·
                      rfl

theorem cell23_7641897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_7641897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641897 prefixEnd_7641897 := by exact prefixLift 7641897
  have htrace : WordTrace (prefixWord ++ tailWord_7641897) baseStart_7641897 baseEnd_7641897 := by
    simpa [prefixWord, tailWord_7641897, baseEnd_7641897] using wordTrace_append hprefix tailTrace_7641897
  have hstable : (prefixWord ++ tailWord_7641897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641897).length < 2 ^ (prefixWord ++ tailWord_7641897).sum := by decide
  have hdescent : baseEnd_7641897 < baseStart_7641897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641911 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_7641911 : Nat := 118140960795 + 7641911 * 2 ^ 59
def prefixEnd_7641911 : Nat := 4983230072969 + 3 ^ 40 * 7641911 * 2
def baseEnd_7641911 : Nat := 3923973461880955721767997

theorem tailTrace_7641911 : CollatzResearch.WordTrace tailWord_7641911 prefixEnd_7641911 3923973461880955721767997 := by
  unfold tailWord_7641911
  simp only [CollatzResearch.WordTrace]
  refine ⟨278723392217669056336845587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185815594811779370891230391 278723392217669056336845587)
  ·
    refine ⟨418085088326503584505268381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278723392217669056336845587 418085088326503584505268381)
    ·
      refine ⟨156781908122438844189475643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418085088326503584505268381 156781908122438844189475643)
      ·
        refine ⟨235172862183658266284213465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156781908122438844189475643 235172862183658266284213465)
        ·
          refine ⟨176379646637743699713160099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235172862183658266284213465 176379646637743699713160099)
          ·
            refine ⟨264569469956615549569740149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176379646637743699713160099 264569469956615549569740149)
            ·
              refine ⟨24803387808432707772163139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264569469956615549569740149 24803387808432707772163139)
              ·
                refine ⟨37205081712649061658244709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24803387808432707772163139 37205081712649061658244709)
                ·
                  refine ⟨6975952821121699060920883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37205081712649061658244709 6975952821121699060920883)
                  ·
                    refine ⟨10463929231682548591381325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6975952821121699060920883 10463929231682548591381325)
                    ·
                      refine ⟨3923973461880955721767997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10463929231682548591381325 3923973461880955721767997)
                      ·
                        rfl

theorem cell23_7641911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_7641911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641911 prefixEnd_7641911 := by exact prefixLift 7641911
  have htrace : WordTrace (prefixWord ++ tailWord_7641911) baseStart_7641911 baseEnd_7641911 := by
    simpa [prefixWord, tailWord_7641911, baseEnd_7641911] using wordTrace_append hprefix tailTrace_7641911
  have hstable : (prefixWord ++ tailWord_7641911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641911).length < 2 ^ (prefixWord ++ tailWord_7641911).sum := by decide
  have hdescent : baseEnd_7641911 < baseStart_7641911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641934 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7641934 : Nat := 118140960795 + 7641934 * 2 ^ 59
def prefixEnd_7641934 : Nat := 4983230072969 + 3 ^ 40 * 7641934 * 2
def baseEnd_7641934 : Nat := 3923985271936009131780391

theorem tailTrace_7641934 : CollatzResearch.WordTrace tailWord_7641934 prefixEnd_7641934 3923985271936009131780391 := by
  unfold tailWord_7641934
  simp only [CollatzResearch.WordTrace]
  refine ⟨34840528887073216408116607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185816154064390487509955237 34840528887073216408116607)
  ·
    refine ⟨52260793330609824612174911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34840528887073216408116607 52260793330609824612174911)
    ·
      refine ⟨78391189995914736918262367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52260793330609824612174911 78391189995914736918262367)
      ·
        refine ⟨117586784993872105377393551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78391189995914736918262367 117586784993872105377393551)
        ·
          refine ⟨176380177490808158066090327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117586784993872105377393551 176380177490808158066090327)
          ·
            refine ⟨264570266236212237099135491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176380177490808158066090327 264570266236212237099135491)
            ·
              refine ⟨396855399354318355648703237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264570266236212237099135491 396855399354318355648703237)
              ·
                refine ⟨74410387378934691684131857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396855399354318355648703237 74410387378934691684131857)
                ·
                  refine ⟨55807790534201018763098893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74410387378934691684131857 55807790534201018763098893)
                  ·
                    refine ⟨20927921450325382036162085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55807790534201018763098893 20927921450325382036162085)
                    ·
                      refine ⟨3923985271936009131780391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20927921450325382036162085 3923985271936009131780391)
                      ·
                        rfl

theorem cell23_7641934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7641934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641934 prefixEnd_7641934 := by exact prefixLift 7641934
  have htrace : WordTrace (prefixWord ++ tailWord_7641934) baseStart_7641934 baseEnd_7641934 := by
    simpa [prefixWord, tailWord_7641934, baseEnd_7641934] using wordTrace_append hprefix tailTrace_7641934
  have hstable : (prefixWord ++ tailWord_7641934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641934).length < 2 ^ (prefixWord ++ tailWord_7641934).sum := by decide
  have hdescent : baseEnd_7641934 < baseStart_7641934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641951 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 3, 4, 2]
def baseStart_7641951 : Nat := 118140960795 + 7641951 * 2 ^ 59
def prefixEnd_7641951 : Nat := 4983230072969 + 3 ^ 40 * 7641951 * 2
def baseEnd_7641951 : Nat := 3923994001107135565267813

theorem tailTrace_7641951 : CollatzResearch.WordTrace tailWord_7641951 prefixEnd_7641951 3923994001107135565267813 := by
  unfold tailWord_7641951
  simp only [CollatzResearch.WordTrace]
  refine ⟨278724851137524143168301707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185816567425016095445534471 278724851137524143168301707)
  ·
    refine ⟨418087276706286214752452561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278724851137524143168301707 418087276706286214752452561)
    ·
      refine ⟨313565457529714661064339421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418087276706286214752452561 313565457529714661064339421)
      ·
        refine ⟨117587046573642997899127283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313565457529714661064339421 117587046573642997899127283)
        ·
          refine ⟨176380569860464496848690925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117587046573642997899127283 176380569860464496848690925)
          ·
            refine ⟨66142713697674186318259097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176380569860464496848690925 66142713697674186318259097)
            ·
              refine ⟨49607035273255639738694323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66142713697674186318259097 49607035273255639738694323)
              ·
                refine ⟨74410552909883459608041485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49607035273255639738694323 74410552909883459608041485)
                ·
                  refine ⟨27903957341206297353015557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74410552909883459608041485 27903957341206297353015557)
                  ·
                    refine ⟨5231992001476180753690417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27903957341206297353015557 5231992001476180753690417)
                    ·
                      refine ⟨3923994001107135565267813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5231992001476180753690417 3923994001107135565267813)
                      ·
                        rfl

theorem cell23_7641951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_7641951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641951 prefixEnd_7641951 := by exact prefixLift 7641951
  have htrace : WordTrace (prefixWord ++ tailWord_7641951) baseStart_7641951 baseEnd_7641951 := by
    simpa [prefixWord, tailWord_7641951, baseEnd_7641951] using wordTrace_append hprefix tailTrace_7641951
  have hstable : (prefixWord ++ tailWord_7641951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641951).length < 2 ^ (prefixWord ++ tailWord_7641951).sum := by decide
  have hdescent : baseEnd_7641951 < baseStart_7641951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7641968 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 4, 2, 2]
def baseStart_7641968 : Nat := 118140960795 + 7641968 * 2 ^ 59
def prefixEnd_7641968 : Nat := 4983230072969 + 3 ^ 40 * 7641968 * 2
def baseEnd_7641968 : Nat := 3924002730278261998755235

theorem tailTrace_7641968 : CollatzResearch.WordTrace tailWord_7641968 prefixEnd_7641968 3924002730278261998755235 := by
  unfold tailWord_7641968
  simp only [CollatzResearch.WordTrace]
  refine ⟨139362735589231277535835279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185816980785641703381113705 139362735589231277535835279)
  ·
    refine ⟨209044103383846916303752919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139362735589231277535835279 209044103383846916303752919)
    ·
      refine ⟨313566155075770374455629379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209044103383846916303752919 313566155075770374455629379)
      ·
        refine ⟨470349232613655561683444069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313566155075770374455629379 470349232613655561683444069)
        ·
          refine ⟨88190481115060417815645763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470349232613655561683444069 88190481115060417815645763)
          ·
            refine ⟨132285721672590626723468645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88190481115060417815645763 132285721672590626723468645)
            ·
              refine ⟨24803572813610742510650371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132285721672590626723468645 24803572813610742510650371)
              ·
                refine ⟨37205359220416113765975557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24803572813610742510650371 37205359220416113765975557)
                ·
                  refine ⟨6976004853828021331120417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37205359220416113765975557 6976004853828021331120417)
                  ·
                    refine ⟨5232003640371015998340313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6976004853828021331120417 5232003640371015998340313)
                    ·
                      refine ⟨3924002730278261998755235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232003640371015998340313 3924002730278261998755235)
                      ·
                        rfl

theorem cell23_7641968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 2, 2].length) (baseStart_7641968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7641968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7641968 prefixEnd_7641968 := by exact prefixLift 7641968
  have htrace : WordTrace (prefixWord ++ tailWord_7641968) baseStart_7641968 baseEnd_7641968 := by
    simpa [prefixWord, tailWord_7641968, baseEnd_7641968] using wordTrace_append hprefix tailTrace_7641968
  have hstable : (prefixWord ++ tailWord_7641968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7641968).length < 2 ^ (prefixWord ++ tailWord_7641968).sum := by decide
  have hdescent : baseEnd_7641968 < baseStart_7641968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7641968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642006 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7642006 : Nat := 118140960795 + 7642006 * 2 ^ 59
def prefixEnd_7642006 : Nat := 4983230072969 + 3 ^ 40 * 7642006 * 2
def baseEnd_7642006 : Nat := 3924022242543132850080061

theorem tailTrace_7642006 : CollatzResearch.WordTrace tailWord_7642006 prefixEnd_7642006 3924022242543132850080061 := by
  unfold tailWord_7642006
  simp only [CollatzResearch.WordTrace]
  refine ⟨17420428572020305472597117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185817904768216591707702581 17420428572020305472597117)
  ·
    refine ⟨6532660714507614552223919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17420428572020305472597117 6532660714507614552223919)
    ·
      refine ⟨9798991071761421828335879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532660714507614552223919 9798991071761421828335879)
      ·
        refine ⟨14698486607642132742503819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9798991071761421828335879 14698486607642132742503819)
        ·
          refine ⟨22047729911463199113755729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14698486607642132742503819 22047729911463199113755729)
          ·
            refine ⟨16535797433597399335316797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22047729911463199113755729 16535797433597399335316797)
            ·
              refine ⟨6200924037599024750743799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16535797433597399335316797 6200924037599024750743799)
              ·
                refine ⟨9301386056398537126115699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200924037599024750743799 9301386056398537126115699)
                ·
                  refine ⟨13952079084597805689173549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9301386056398537126115699 13952079084597805689173549)
                  ·
                    refine ⟨5232029656724177133440081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13952079084597805689173549 5232029656724177133440081)
                    ·
                      refine ⟨3924022242543132850080061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232029656724177133440081 3924022242543132850080061)
                      ·
                        rfl

theorem cell23_7642006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7642006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642006 prefixEnd_7642006 := by exact prefixLift 7642006
  have htrace : WordTrace (prefixWord ++ tailWord_7642006) baseStart_7642006 baseEnd_7642006 := by
    simpa [prefixWord, tailWord_7642006, baseEnd_7642006] using wordTrace_append hprefix tailTrace_7642006
  have hstable : (prefixWord ++ tailWord_7642006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642006).length < 2 ^ (prefixWord ++ tailWord_7642006).sum := by decide
  have hdescent : baseEnd_7642006 < baseStart_7642006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642034 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_7642034 : Nat := 118140960795 + 7642034 * 2 ^ 59
def prefixEnd_7642034 : Nat := 4983230072969 + 3 ^ 40 * 7642034 * 2
def baseEnd_7642034 : Nat := 1308012206667152913509977

theorem tailTrace_7642034 : CollatzResearch.WordTrace tailWord_7642034 prefixEnd_7642034 1308012206667152913509977 := by
  unfold tailWord_7642034
  simp only [CollatzResearch.WordTrace]
  refine ⟨69681969599055862085893289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185818585597482298895715437 69681969599055862085893289)
  ·
    refine ⟨52261477199291896564419967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69681969599055862085893289 52261477199291896564419967)
    ·
      refine ⟨78392215798937844846629951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52261477199291896564419967 78392215798937844846629951)
      ·
        refine ⟨117588323698406767269944927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78392215798937844846629951 117588323698406767269944927)
        ·
          refine ⟨176382485547610150904917391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117588323698406767269944927 176382485547610150904917391)
          ·
            refine ⟨264573728321415226357376087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176382485547610150904917391 264573728321415226357376087)
            ·
              refine ⟨396860592482122839536064131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264573728321415226357376087 396860592482122839536064131)
              ·
                refine ⟨595290888723184259304096197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396860592482122839536064131 595290888723184259304096197)
                ·
                  refine ⟨111617041635597048619518037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595290888723184259304096197 111617041635597048619518037)
                  ·
                    refine ⟨1308012206667152913509977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111617041635597048619518037 1308012206667152913509977)
                    ·
                      rfl

theorem cell23_7642034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_7642034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642034 prefixEnd_7642034 := by exact prefixLift 7642034
  have htrace : WordTrace (prefixWord ++ tailWord_7642034) baseStart_7642034 baseEnd_7642034 := by
    simpa [prefixWord, tailWord_7642034, baseEnd_7642034] using wordTrace_append hprefix tailTrace_7642034
  have hstable : (prefixWord ++ tailWord_7642034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642034).length < 2 ^ (prefixWord ++ tailWord_7642034).sum := by decide
  have hdescent : baseEnd_7642034 < baseStart_7642034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642051 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 3, 4]
def baseStart_7642051 : Nat := 118140960795 + 7642051 * 2 ^ 59
def prefixEnd_7642051 : Nat := 4983230072969 + 3 ^ 40 * 7642051 * 2
def baseEnd_7642051 : Nat := 1308015116390861724672451

theorem tailTrace_7642051 : CollatzResearch.WordTrace tailWord_7642051 prefixEnd_7642051 1308015116390861724672451 := by
  unfold tailWord_7642051
  simp only [CollatzResearch.WordTrace]
  refine ⟨278728498437161860246942007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185818998958107906831294671 278728498437161860246942007)
  ·
    refine ⟨418092747655742790370413011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278728498437161860246942007 418092747655742790370413011)
    ·
      refine ⟨627139121483614185555619517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418092747655742790370413011 627139121483614185555619517)
      ·
        refine ⟨235177170556355319583357319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627139121483614185555619517 235177170556355319583357319)
        ·
          refine ⟨352765755834532979375035979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235177170556355319583357319 352765755834532979375035979)
          ·
            refine ⟨529148633751799469062553969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352765755834532979375035979 529148633751799469062553969)
            ·
              refine ⟨396861475313849601796915477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529148633751799469062553969 396861475313849601796915477)
              ·
                refine ⟨18602881655336700084230413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396861475313849601796915477 18602881655336700084230413)
                ·
                  refine ⟨6976080620751262531586405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18602881655336700084230413 6976080620751262531586405)
                  ·
                    refine ⟨1308015116390861724672451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976080620751262531586405 1308015116390861724672451)
                    ·
                      rfl

theorem cell23_7642051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 4].length) (baseStart_7642051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642051 prefixEnd_7642051 := by exact prefixLift 7642051
  have htrace : WordTrace (prefixWord ++ tailWord_7642051) baseStart_7642051 baseEnd_7642051 := by
    simpa [prefixWord, tailWord_7642051, baseEnd_7642051] using wordTrace_append hprefix tailTrace_7642051
  have hstable : (prefixWord ++ tailWord_7642051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642051).length < 2 ^ (prefixWord ++ tailWord_7642051).sum := by decide
  have hdescent : baseEnd_7642051 < baseStart_7642051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642064 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 8]
def baseStart_7642064 : Nat := 118140960795 + 7642064 * 2 ^ 59
def prefixEnd_7642064 : Nat := 4983230072969 + 3 ^ 40 * 7642064 * 2
def baseEnd_7642064 : Nat := 436005780491232624794977

theorem tailTrace_7642064 : CollatzResearch.WordTrace tailWord_7642064 prefixEnd_7642064 436005780491232624794977 := by
  unfold tailWord_7642064
  simp only [CollatzResearch.WordTrace]
  refine ⟨139364486293057381733582623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185819315057409842311443497 139364486293057381733582623)
  ·
    refine ⟨209046729439586072600373935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139364486293057381733582623 209046729439586072600373935)
    ·
      refine ⟨313570094159379108900560903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209046729439586072600373935 313570094159379108900560903)
      ·
        refine ⟨470355141239068663350841355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313570094159379108900560903 470355141239068663350841355)
        ·
          refine ⟨705532711858602995026262033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470355141239068663350841355 705532711858602995026262033)
          ·
            refine ⟨529149533893952246269696525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 705532711858602995026262033 529149533893952246269696525)
            ·
              refine ⟨198431075210232092351136197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529149533893952246269696525 198431075210232092351136197)
              ·
                refine ⟨37205826601918517315838037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198431075210232092351136197 37205826601918517315838037)
                ·
                  refine ⟨436005780491232624794977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37205826601918517315838037 436005780491232624794977)
                  ·
                    rfl

theorem cell23_7642064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_7642064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642064 prefixEnd_7642064 := by exact prefixLift 7642064
  have htrace : WordTrace (prefixWord ++ tailWord_7642064) baseStart_7642064 baseEnd_7642064 := by
    simpa [prefixWord, tailWord_7642064, baseEnd_7642064] using wordTrace_append hprefix tailTrace_7642064
  have hstable : (prefixWord ++ tailWord_7642064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642064).length < 2 ^ (prefixWord ++ tailWord_7642064).sum := by decide
  have hdescent : baseEnd_7642064 < baseStart_7642064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642131 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 4]
def baseStart_7642131 : Nat := 118140960795 + 7642131 * 2 ^ 59
def prefixEnd_7642131 : Nat := 4983230072969 + 3 ^ 40 * 7642131 * 2
def baseEnd_7642131 : Nat := 3924086427624944861016985

theorem tailTrace_7642131 : CollatzResearch.WordTrace tailWord_7642131 prefixEnd_7642131 3924086427624944861016985 := by
  unfold tailWord_7642131
  simp only [CollatzResearch.WordTrace]
  refine ⟨278731416276872033909854247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185820944184581355939902831 278731416276872033909854247)
  ·
    refine ⟨418097124415308050864781371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278731416276872033909854247 418097124415308050864781371)
    ·
      refine ⟨627145686622962076297172057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418097124415308050864781371 627145686622962076297172057)
      ·
        refine ⟨470359264967221557222879043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627145686622962076297172057 470359264967221557222879043)
        ·
          refine ⟨705538897450832335834318565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470359264967221557222879043 705538897450832335834318565)
          ·
            refine ⟨132288543272031062968934731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 705538897450832335834318565 132288543272031062968934731)
            ·
              refine ⟨198432814908046594453402097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132288543272031062968934731 198432814908046594453402097)
              ·
                refine ⟨148824611181034945840051573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198432814908046594453402097 148824611181034945840051573)
                ·
                  refine ⟨13952307298222026172504835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148824611181034945840051573 13952307298222026172504835)
                  ·
                    refine ⟨20928460947333039258757253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13952307298222026172504835 20928460947333039258757253)
                    ·
                      refine ⟨3924086427624944861016985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20928460947333039258757253 3924086427624944861016985)
                      ·
                        rfl

theorem cell23_7642131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_7642131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642131 prefixEnd_7642131 := by exact prefixLift 7642131
  have htrace : WordTrace (prefixWord ++ tailWord_7642131) baseStart_7642131 baseEnd_7642131 := by
    simpa [prefixWord, tailWord_7642131, baseEnd_7642131] using wordTrace_append hprefix tailTrace_7642131
  have hstable : (prefixWord ++ tailWord_7642131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642131).length < 2 ^ (prefixWord ++ tailWord_7642131).sum := by decide
  have hdescent : baseEnd_7642131 < baseStart_7642131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642135 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 4, 3, 2]
def baseStart_7642135 : Nat := 118140960795 + 7642135 * 2 ^ 59
def prefixEnd_7642135 : Nat := 4983230072969 + 3 ^ 40 * 7642135 * 2
def baseEnd_7642135 : Nat := 3924088481547562845366967

theorem tailTrace_7642135 : CollatzResearch.WordTrace tailWord_7642135 prefixEnd_7642135 3924088481547562845366967 := by
  unfold tailWord_7642135
  simp only [CollatzResearch.WordTrace]
  refine ⟨278731562168857542592999859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185821041445905028395333239 278731562168857542592999859)
  ·
    refine ⟨418097343253286313889499789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278731562168857542592999859 418097343253286313889499789)
    ·
      refine ⟨156786503719982367708562421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418097343253286313889499789 156786503719982367708562421)
      ·
        refine ⟨14698734723748346972677727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156786503719982367708562421 14698734723748346972677727)
        ·
          refine ⟨22048102085622520459016591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14698734723748346972677727 22048102085622520459016591)
          ·
            refine ⟨33072153128433780688524887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22048102085622520459016591 33072153128433780688524887)
            ·
              refine ⟨49608229692650671032787331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33072153128433780688524887 49608229692650671032787331)
              ·
                refine ⟨74412344538976006549180997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49608229692650671032787331 74412344538976006549180997)
                ·
                  refine ⟨13952314601058001227971437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74412344538976006549180997 13952314601058001227971437)
                  ·
                    refine ⟨5232117975396750460489289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13952314601058001227971437 5232117975396750460489289)
                    ·
                      refine ⟨3924088481547562845366967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232117975396750460489289 3924088481547562845366967)
                      ·
                        rfl

theorem cell23_7642135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_7642135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642135 prefixEnd_7642135 := by exact prefixLift 7642135
  have htrace : WordTrace (prefixWord ++ tailWord_7642135) baseStart_7642135 baseEnd_7642135 := by
    simpa [prefixWord, tailWord_7642135, baseEnd_7642135] using wordTrace_append hprefix tailTrace_7642135
  have hstable : (prefixWord ++ tailWord_7642135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642135).length < 2 ^ (prefixWord ++ tailWord_7642135).sum := by decide
  have hdescent : baseEnd_7642135 < baseStart_7642135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642158 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_7642158 : Nat := 118140960795 + 7642158 * 2 ^ 59
def prefixEnd_7642158 : Nat := 4983230072969 + 3 ^ 40 * 7642158 * 2
def baseEnd_7642158 : Nat := 1308033430534205418459787

theorem tailTrace_7642158 : CollatzResearch.WordTrace tailWord_7642158 prefixEnd_7642158 1308033430534205418459787 := by
  unfold tailWord_7642158
  simp only [CollatzResearch.WordTrace]
  refine ⟨34841550130971777190135891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185821600698516145014058085 34841550130971777190135891)
  ·
    refine ⟨52262325196457665785203837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34841550130971777190135891 52262325196457665785203837)
    ·
      refine ⟨19598371948671624669451439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52262325196457665785203837 19598371948671624669451439)
      ·
        refine ⟨29397557923007437004177159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19598371948671624669451439 29397557923007437004177159)
        ·
          refine ⟨44096336884511155506265739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29397557923007437004177159 44096336884511155506265739)
          ·
            refine ⟨66144505326766733259398609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44096336884511155506265739 66144505326766733259398609)
            ·
              refine ⟨49608378995075049944548957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66144505326766733259398609 49608378995075049944548957)
              ·
                refine ⟨18603142123153143729205859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49608378995075049944548957 18603142123153143729205859)
                ·
                  refine ⟨27904713184729715593808789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18603142123153143729205859 27904713184729715593808789)
                  ·
                    refine ⟨1308033430534205418459787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27904713184729715593808789 1308033430534205418459787)
                    ·
                      rfl

theorem cell23_7642158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_7642158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642158 prefixEnd_7642158 := by exact prefixLift 7642158
  have htrace : WordTrace (prefixWord ++ tailWord_7642158) baseStart_7642158 baseEnd_7642158 := by
    simpa [prefixWord, tailWord_7642158, baseEnd_7642158] using wordTrace_append hprefix tailTrace_7642158
  have hstable : (prefixWord ++ tailWord_7642158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642158).length < 2 ^ (prefixWord ++ tailWord_7642158).sum := by decide
  have hdescent : baseEnd_7642158 < baseStart_7642158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642161 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_7642161 : Nat := 118140960795 + 7642161 * 2 ^ 59
def prefixEnd_7642161 : Nat := 4983230072969 + 3 ^ 40 * 7642161 * 2
def baseEnd_7642161 : Nat := 3924101832044579743641847

theorem tailTrace_7642161 : CollatzResearch.WordTrace tailWord_7642161 prefixEnd_7642161 3924101832044579743641847 := by
  unfold tailWord_7642161
  simp only [CollatzResearch.WordTrace]
  refine ⟨278732510466763349033446337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185821673644508899355630891 278732510466763349033446337)
  ·
    refine ⟨209049382850072511775084753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278732510466763349033446337 209049382850072511775084753)
    ·
      refine ⟨156787037137554383831313565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209049382850072511775084753 156787037137554383831313565)
      ·
        refine ⟨58795138926582893936742587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156787037137554383831313565 58795138926582893936742587)
        ·
          refine ⟨88192708389874340905113881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58795138926582893936742587 88192708389874340905113881)
          ·
            refine ⟨66144531292405755678835411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88192708389874340905113881 66144531292405755678835411)
            ·
              refine ⟨99216796938608633518253117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66144531292405755678835411 99216796938608633518253117)
              ·
                refine ⟨37206298851978237569344919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99216796938608633518253117 37206298851978237569344919)
                ·
                  refine ⟨55809448277967356354017379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37206298851978237569344919 55809448277967356354017379)
                  ·
                    refine ⟨83714172416951034531026069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55809448277967356354017379 83714172416951034531026069)
                    ·
                      refine ⟨3924101832044579743641847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83714172416951034531026069 3924101832044579743641847)
                      ·
                        rfl

theorem cell23_7642161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_7642161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642161 prefixEnd_7642161 := by exact prefixLift 7642161
  have htrace : WordTrace (prefixWord ++ tailWord_7642161) baseStart_7642161 baseEnd_7642161 := by
    simpa [prefixWord, tailWord_7642161, baseEnd_7642161] using wordTrace_append hprefix tailTrace_7642161
  have hstable : (prefixWord ++ tailWord_7642161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642161).length < 2 ^ (prefixWord ++ tailWord_7642161).sum := by decide
  have hdescent : baseEnd_7642161 < baseStart_7642161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642165 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_7642165 : Nat := 118140960795 + 7642165 * 2 ^ 59
def prefixEnd_7642165 : Nat := 4983230072969 + 3 ^ 40 * 7642165 * 2
def baseEnd_7642165 : Nat := 3924103885967197727991829

theorem tailTrace_7642165 : CollatzResearch.WordTrace tailWord_7642165 prefixEnd_7642165 3924103885967197727991829 := by
  unfold tailWord_7642165
  simp only [CollatzResearch.WordTrace]
  refine ⟨278732656358748857716591949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185821770905832571811061299 278732656358748857716591949)
  ·
    refine ⟨104524746134530821643721981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278732656358748857716591949 104524746134530821643721981)
    ·
      refine ⟨39196779800449058116395743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104524746134530821643721981 39196779800449058116395743)
      ·
        refine ⟨58795169700673587174593615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39196779800449058116395743 58795169700673587174593615)
        ·
          refine ⟨88192754551010380761890423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58795169700673587174593615 88192754551010380761890423)
          ·
            refine ⟨132289131826515571142835635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88192754551010380761890423 132289131826515571142835635)
            ·
              refine ⟨198433697739773356714253453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132289131826515571142835635 198433697739773356714253453)
              ·
                refine ⟨74412636652415008767845045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198433697739773356714253453 74412636652415008767845045)
                ·
                  refine ⟨6976184686163907071985473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74412636652415008767845045 6976184686163907071985473)
                  ·
                    refine ⟨5232138514622930303989105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6976184686163907071985473 5232138514622930303989105)
                    ·
                      refine ⟨3924103885967197727991829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232138514622930303989105 3924103885967197727991829)
                      ·
                        rfl

theorem cell23_7642165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_7642165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642165 prefixEnd_7642165 := by exact prefixLift 7642165
  have htrace : WordTrace (prefixWord ++ tailWord_7642165) baseStart_7642165 baseEnd_7642165 := by
    simpa [prefixWord, tailWord_7642165, baseEnd_7642165] using wordTrace_append hprefix tailTrace_7642165
  have hstable : (prefixWord ++ tailWord_7642165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642165).length < 2 ^ (prefixWord ++ tailWord_7642165).sum := by decide
  have hdescent : baseEnd_7642165 < baseStart_7642165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642211 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7642211 : Nat := 118140960795 + 7642211 * 2 ^ 59
def prefixEnd_7642211 : Nat := 4983230072969 + 3 ^ 40 * 7642211 * 2
def baseEnd_7642211 : Nat := 3924127506077304548016617

theorem tailTrace_7642211 : CollatzResearch.WordTrace tailWord_7642211 prefixEnd_7642211 3924127506077304548016617 := by
  unfold tailWord_7642211
  simp only [CollatzResearch.WordTrace]
  refine ⟨278734334116582207572766487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185822889411054805048510991 278734334116582207572766487)
  ·
    refine ⟨418101501174873311359149731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278734334116582207572766487 418101501174873311359149731)
    ·
      refine ⟨627152251762309967038724597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418101501174873311359149731 627152251762309967038724597)
      ·
        refine ⟨58795523602716559409880431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 627152251762309967038724597 58795523602716559409880431)
        ·
          refine ⟨88193285404074839114820647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58795523602716559409880431 88193285404074839114820647)
          ·
            refine ⟨132289928106112258672230971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88193285404074839114820647 132289928106112258672230971)
            ·
              refine ⟨198434892159168388008346457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132289928106112258672230971 198434892159168388008346457)
              ·
                refine ⟨148826169119376291006259843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198434892159168388008346457 148826169119376291006259843)
                ·
                  refine ⟨223239253679064436509389765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148826169119376291006259843 223239253679064436509389765)
                  ·
                    refine ⟨41857360064824581845510581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 223239253679064436509389765 41857360064824581845510581)
                    ·
                      refine ⟨3924127506077304548016617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41857360064824581845510581 3924127506077304548016617)
                      ·
                        rfl

theorem cell23_7642211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7642211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642211 prefixEnd_7642211 := by exact prefixLift 7642211
  have htrace : WordTrace (prefixWord ++ tailWord_7642211) baseStart_7642211 baseEnd_7642211 := by
    simpa [prefixWord, tailWord_7642211, baseEnd_7642211] using wordTrace_append hprefix tailTrace_7642211
  have hstable : (prefixWord ++ tailWord_7642211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642211).length < 2 ^ (prefixWord ++ tailWord_7642211).sum := by decide
  have hdescent : baseEnd_7642211 < baseStart_7642211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642215 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_7642215 : Nat := 118140960795 + 7642215 * 2 ^ 59
def prefixEnd_7642215 : Nat := 4983230072969 + 3 ^ 40 * 7642215 * 2
def baseEnd_7642215 : Nat := 3924129559999922532366599

theorem tailTrace_7642215 : CollatzResearch.WordTrace tailWord_7642215 prefixEnd_7642215 3924129559999922532366599 := by
  unfold tailWord_7642215
  simp only [CollatzResearch.WordTrace]
  refine ⟨278734480008567716255912099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185822986672378477503941399 278734480008567716255912099)
  ·
    refine ⟨418101720012851574383868149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278734480008567716255912099 418101720012851574383868149)
    ·
      refine ⟨39197036251204835098487639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 418101720012851574383868149 39197036251204835098487639)
      ·
        refine ⟨58795554376807252647731459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39197036251204835098487639 58795554376807252647731459)
        ·
          refine ⟨88193331565210878971597189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58795554376807252647731459 88193331565210878971597189)
          ·
            refine ⟨16536249668477039807174473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88193331565210878971597189 16536249668477039807174473)
            ·
              refine ⟨12402187251357779855380855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16536249668477039807174473 12402187251357779855380855)
              ·
                refine ⟨18603280877036669783071283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12402187251357779855380855 18603280877036669783071283)
                ·
                  refine ⟨27904921315555004674606925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18603280877036669783071283 27904921315555004674606925)
                  ·
                    refine ⟨10464345493333126752977597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27904921315555004674606925 10464345493333126752977597)
                    ·
                      refine ⟨3924129559999922532366599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10464345493333126752977597 3924129559999922532366599)
                      ·
                        rfl

theorem cell23_7642215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_7642215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642215 prefixEnd_7642215 := by exact prefixLift 7642215
  have htrace : WordTrace (prefixWord ++ tailWord_7642215) baseStart_7642215 baseEnd_7642215 := by
    simpa [prefixWord, tailWord_7642215, baseEnd_7642215] using wordTrace_append hprefix tailTrace_7642215
  have hstable : (prefixWord ++ tailWord_7642215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642215).length < 2 ^ (prefixWord ++ tailWord_7642215).sum := by decide
  have hdescent : baseEnd_7642215 < baseStart_7642215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642231 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 1, 8]
def baseStart_7642231 : Nat := 118140960795 + 7642231 * 2 ^ 59
def prefixEnd_7642231 : Nat := 4983230072969 + 3 ^ 40 * 7642231 * 2
def baseEnd_7642231 : Nat := 1308045925230131489922175

theorem tailTrace_7642231 : CollatzResearch.WordTrace tailWord_7642231 prefixEnd_7642231 1308045925230131489922175 := by
  unfold tailWord_7642231
  simp only [CollatzResearch.WordTrace]
  refine ⟨278735063576509750988494547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185823375717673167325663031 278735063576509750988494547)
  ·
    refine ⟨418102595364764626482741821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278735063576509750988494547 418102595364764626482741821)
    ·
      refine ⟨156788473261786734931028183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418102595364764626482741821 156788473261786734931028183)
      ·
        refine ⟨235182709892680102396542275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156788473261786734931028183 235182709892680102396542275)
        ·
          refine ⟨352774064839020153594813413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235182709892680102396542275 352774064839020153594813413)
          ·
            refine ⟨66145137157316278799027515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352774064839020153594813413 66145137157316278799027515)
            ·
              refine ⟨99217705735974418198541273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66145137157316278799027515 99217705735974418198541273)
              ·
                refine ⟨74413279301980813648905955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99217705735974418198541273 74413279301980813648905955)
                ·
                  refine ⟨111619918952971220473358933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74413279301980813648905955 111619918952971220473358933)
                  ·
                    refine ⟨1308045925230131489922175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111619918952971220473358933 1308045925230131489922175)
                    ·
                      rfl

theorem cell23_7642231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_7642231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642231 prefixEnd_7642231 := by exact prefixLift 7642231
  have htrace : WordTrace (prefixWord ++ tailWord_7642231) baseStart_7642231 baseEnd_7642231 := by
    simpa [prefixWord, tailWord_7642231, baseEnd_7642231] using wordTrace_append hprefix tailTrace_7642231
  have hstable : (prefixWord ++ tailWord_7642231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642231).length < 2 ^ (prefixWord ++ tailWord_7642231).sum := by decide
  have hdescent : baseEnd_7642231 < baseStart_7642231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642281 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_7642281 : Nat := 118140960795 + 7642281 * 2 ^ 59
def prefixEnd_7642281 : Nat := 4983230072969 + 3 ^ 40 * 7642281 * 2
def baseEnd_7642281 : Nat := 3924163449723119274141295

theorem tailTrace_7642281 : CollatzResearch.WordTrace tailWord_7642281 prefixEnd_7642281 3924163449723119274141295 := by
  unfold tailWord_7642281
  simp only [CollatzResearch.WordTrace]
  refine ⟨278736887226328609527814697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185824591484219073018543131 278736887226328609527814697)
  ·
    refine ⟨209052665419746457145861023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278736887226328609527814697 209052665419746457145861023)
    ·
      refine ⟨313578998129619685718791535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209052665419746457145861023 313578998129619685718791535)
      ·
        refine ⟨470368497194429528578187303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313578998129619685718791535 470368497194429528578187303)
        ·
          refine ⟨705552745791644292867280955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470368497194429528578187303 705552745791644292867280955)
          ·
            refine ⟨1058329118687466439300921433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705552745791644292867280955 1058329118687466439300921433)
            ·
              refine ⟨793746839015599829475691075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058329118687466439300921433 793746839015599829475691075)
              ·
                refine ⟨1190620258523399744213536613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793746839015599829475691075 1190620258523399744213536613)
                ·
                  refine ⟨223241298473137452040038115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1190620258523399744213536613 223241298473137452040038115)
                  ·
                    refine ⟨334861947709706178060057173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223241298473137452040038115 334861947709706178060057173)
                    ·
                      refine ⟨3924163449723119274141295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 334861947709706178060057173 3924163449723119274141295)
                      ·
                        rfl

theorem cell23_7642281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_7642281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642281 prefixEnd_7642281 := by exact prefixLift 7642281
  have htrace : WordTrace (prefixWord ++ tailWord_7642281) baseStart_7642281 baseEnd_7642281 := by
    simpa [prefixWord, tailWord_7642281, baseEnd_7642281] using wordTrace_append hprefix tailTrace_7642281
  have hstable : (prefixWord ++ tailWord_7642281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642281).length < 2 ^ (prefixWord ++ tailWord_7642281).sum := by decide
  have hdescent : baseEnd_7642281 < baseStart_7642281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642399 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 3]
def baseStart_7642399 : Nat := 118140960795 + 7642399 * 2 ^ 59
def prefixEnd_7642399 : Nat := 4983230072969 + 3 ^ 40 * 7642399 * 2
def baseEnd_7642399 : Nat := 3924224040440349812465753

theorem tailTrace_7642399 : CollatzResearch.WordTrace tailWord_7642399 prefixEnd_7642399 3924224040440349812465753 := by
  unfold tailWord_7642399
  simp only [CollatzResearch.WordTrace]
  refine ⟨278741191039901115680610251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185827460693267410453740167 278741191039901115680610251)
  ·
    refine ⟨418111786559851673520915377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278741191039901115680610251 418111786559851673520915377)
    ·
      refine ⟨313583839919888755140686533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418111786559851673520915377 313583839919888755140686533)
      ·
        refine ⟨58796969984979141588878725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313583839919888755140686533 58796969984979141588878725)
        ·
          refine ⟨11024431872183589047914761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58796969984979141588878725 11024431872183589047914761)
          ·
            refine ⟨8268323904137691785936071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11024431872183589047914761 8268323904137691785936071)
            ·
              refine ⟨12402485856206537678904107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268323904137691785936071 12402485856206537678904107)
              ·
                refine ⟨18603728784309806518356161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12402485856206537678904107 18603728784309806518356161)
                ·
                  refine ⟨13952796588232354888767121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18603728784309806518356161 13952796588232354888767121)
                  ·
                    refine ⟨10464597441174266166575341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13952796588232354888767121 10464597441174266166575341)
                    ·
                      refine ⟨3924224040440349812465753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10464597441174266166575341 3924224040440349812465753)
                      ·
                        rfl

theorem cell23_7642399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_7642399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642399 prefixEnd_7642399 := by exact prefixLift 7642399
  have htrace : WordTrace (prefixWord ++ tailWord_7642399) baseStart_7642399 baseEnd_7642399 := by
    simpa [prefixWord, tailWord_7642399, baseEnd_7642399] using wordTrace_append hprefix tailTrace_7642399
  have hstable : (prefixWord ++ tailWord_7642399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642399).length < 2 ^ (prefixWord ++ tailWord_7642399).sum := by decide
  have hdescent : baseEnd_7642399 < baseStart_7642399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642452 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_7642452 : Nat := 118140960795 + 7642452 * 2 ^ 59
def prefixEnd_7642452 : Nat := 4983230072969 + 3 ^ 40 * 7642452 * 2
def baseEnd_7642452 : Nat := 3924251254915038105103009

theorem tailTrace_7642452 : CollatzResearch.WordTrace tailWord_7642452 prefixEnd_7642452 3924251254915038105103009 := by
  unfold tailWord_7642452
  simp only [CollatzResearch.WordTrace]
  refine ⟨139371562054354552866144805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185828749405806070488193073 139371562054354552866144805)
  ·
    refine ⟨26132167885191478662402151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139371562054354552866144805 26132167885191478662402151)
    ·
      refine ⟨39198251827787217993603227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26132167885191478662402151 39198251827787217993603227)
      ·
        refine ⟨58797377741680826990404841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39198251827787217993603227 58797377741680826990404841)
        ·
          refine ⟨44098033306260620242803631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58797377741680826990404841 44098033306260620242803631)
          ·
            refine ⟨66147049959390930364205447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44098033306260620242803631 66147049959390930364205447)
            ·
              refine ⟨99220574939086395546308171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66147049959390930364205447 99220574939086395546308171)
              ·
                refine ⟨148830862408629593319462257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99220574939086395546308171 148830862408629593319462257)
                ·
                  refine ⟨111623146806472194989596693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148830862408629593319462257 111623146806472194989596693)
                  ·
                    refine ⟨5232335006553384140137345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111623146806472194989596693 5232335006553384140137345)
                    ·
                      refine ⟨3924251254915038105103009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232335006553384140137345 3924251254915038105103009)
                      ·
                        rfl

theorem cell23_7642452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_7642452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642452 prefixEnd_7642452 := by exact prefixLift 7642452
  have htrace : WordTrace (prefixWord ++ tailWord_7642452) baseStart_7642452 baseEnd_7642452 := by
    simpa [prefixWord, tailWord_7642452, baseEnd_7642452] using wordTrace_append hprefix tailTrace_7642452
  have hstable : (prefixWord ++ tailWord_7642452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642452).length < 2 ^ (prefixWord ++ tailWord_7642452).sum := by decide
  have hdescent : baseEnd_7642452 < baseStart_7642452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642465 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7642465 : Nat := 118140960795 + 7642465 * 2 ^ 59
def prefixEnd_7642465 : Nat := 4983230072969 + 3 ^ 40 * 7642465 * 2
def baseEnd_7642465 : Nat := 3924257930163546554240449

theorem tailTrace_7642465 : CollatzResearch.WordTrace tailWord_7642465 prefixEnd_7642465 3924257930163546554240449 := by
  unfold tailWord_7642465
  simp only [CollatzResearch.WordTrace]
  refine ⟨278743598257662008952512849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185829065505108005968341899 278743598257662008952512849)
  ·
    refine ⟨209057698693246506714384637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278743598257662008952512849 209057698693246506714384637)
    ·
      refine ⟨78396637009967440017894239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209057698693246506714384637 78396637009967440017894239)
      ·
        refine ⟨117594955514951160026841359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78396637009967440017894239 117594955514951160026841359)
        ·
          refine ⟨176392433272426740040262039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117594955514951160026841359 176392433272426740040262039)
          ·
            refine ⟨264588649908640110060393059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176392433272426740040262039 264588649908640110060393059)
            ·
              refine ⟨396882974862960165090589589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264588649908640110060393059 396882974862960165090589589)
              ·
                refine ⟨18603889446701257738621387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396882974862960165090589589 18603889446701257738621387)
                ·
                  refine ⟨27905834170051886607932081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18603889446701257738621387 27905834170051886607932081)
                  ·
                    refine ⟨20929375627538914955949061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27905834170051886607932081 20929375627538914955949061)
                    ·
                      refine ⟨3924257930163546554240449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20929375627538914955949061 3924257930163546554240449)
                      ·
                        rfl

theorem cell23_7642465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7642465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642465 prefixEnd_7642465 := by exact prefixLift 7642465
  have htrace : WordTrace (prefixWord ++ tailWord_7642465) baseStart_7642465 baseEnd_7642465 := by
    simpa [prefixWord, tailWord_7642465, baseEnd_7642465] using wordTrace_append hprefix tailTrace_7642465
  have hstable : (prefixWord ++ tailWord_7642465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642465).length < 2 ^ (prefixWord ++ tailWord_7642465).sum := by decide
  have hdescent : baseEnd_7642465 < baseStart_7642465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642580 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_7642580 : Nat := 118140960795 + 7642580 * 2 ^ 59
def prefixEnd_7642580 : Nat := 4983230072969 + 3 ^ 40 * 7642580 * 2
def baseEnd_7642580 : Nat := 3924316980438813604302421

theorem tailTrace_7642580 : CollatzResearch.WordTrace tailWord_7642580 prefixEnd_7642580 3924316980438813604302421 := by
  unfold tailWord_7642580
  simp only [CollatzResearch.WordTrace]
  refine ⟨139373896326122691796474597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185831861768163589061966129 139373896326122691796474597)
  ·
    refine ⟨26132605561148004711838987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139373896326122691796474597 26132605561148004711838987)
    ·
      refine ⟨39198908341722007067758481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26132605561148004711838987 39198908341722007067758481)
      ·
        refine ⟨29399181256291505300818861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39198908341722007067758481 29399181256291505300818861)
        ·
          refine ⟨11024692971109314487807073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29399181256291505300818861 11024692971109314487807073)
          ·
            refine ⟨8268519728331985865855305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11024692971109314487807073 8268519728331985865855305)
            ·
              refine ⟨6201389796248989399391479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268519728331985865855305 6201389796248989399391479)
              ·
                refine ⟨9302084694373484099087219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201389796248989399391479 9302084694373484099087219)
                ·
                  refine ⟨13953127041560226148630829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9302084694373484099087219 13953127041560226148630829)
                  ·
                    refine ⟨5232422640585084805736561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13953127041560226148630829 5232422640585084805736561)
                    ·
                      refine ⟨3924316980438813604302421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232422640585084805736561 3924316980438813604302421)
                      ·
                        rfl

theorem cell23_7642580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_7642580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642580 prefixEnd_7642580 := by exact prefixLift 7642580
  have htrace : WordTrace (prefixWord ++ tailWord_7642580) baseStart_7642580 baseEnd_7642580 := by
    simpa [prefixWord, tailWord_7642580, baseEnd_7642580] using wordTrace_append hprefix tailTrace_7642580
  have hstable : (prefixWord ++ tailWord_7642580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642580).length < 2 ^ (prefixWord ++ tailWord_7642580).sum := by decide
  have hdescent : baseEnd_7642580 < baseStart_7642580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642593 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_7642593 : Nat := 118140960795 + 7642593 * 2 ^ 59
def prefixEnd_7642593 : Nat := 4983230072969 + 3 ^ 40 * 7642593 * 2
def baseEnd_7642593 : Nat := 3924323655687322053439861

theorem tailTrace_7642593 : CollatzResearch.WordTrace tailWord_7642593 prefixEnd_7642593 3924323655687322053439861 := by
  unfold tailWord_7642593
  simp only [CollatzResearch.WordTrace]
  refine ⟨278748266801198286813172433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185832177867465524542114955 278748266801198286813172433)
  ·
    refine ⟨209061200100898715109879325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278748266801198286813172433 209061200100898715109879325)
    ·
      refine ⟨78397950037837018166204747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209061200100898715109879325 78397950037837018166204747)
      ·
        refine ⟨117596925056755527249307121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78397950037837018166204747 117596925056755527249307121)
        ·
          refine ⟨88197693792566645436980341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117596925056755527249307121 88197693792566645436980341)
          ·
            refine ⟨8268533793053123009716907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88197693792566645436980341 8268533793053123009716907)
            ·
              refine ⟨12402800689579684514575361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268533793053123009716907 12402800689579684514575361)
              ·
                refine ⟨9302100517184763385931521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12402800689579684514575361 9302100517184763385931521)
                ·
                  refine ⟨6976575387888572539448641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9302100517184763385931521 6976575387888572539448641)
                  ·
                    refine ⟨5232431540916429404586481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6976575387888572539448641 5232431540916429404586481)
                    ·
                      refine ⟨3924323655687322053439861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232431540916429404586481 3924323655687322053439861)
                      ·
                        rfl

theorem cell23_7642593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_7642593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642593 prefixEnd_7642593 := by exact prefixLift 7642593
  have htrace : WordTrace (prefixWord ++ tailWord_7642593) baseStart_7642593 baseEnd_7642593 := by
    simpa [prefixWord, tailWord_7642593, baseEnd_7642593] using wordTrace_append hprefix tailTrace_7642593
  have hstable : (prefixWord ++ tailWord_7642593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642593).length < 2 ^ (prefixWord ++ tailWord_7642593).sum := by decide
  have hdescent : baseEnd_7642593 < baseStart_7642593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642599 : List Nat := [1, 1, 5, 2, 1, 2, 2, 4, 5]
def baseStart_7642599 : Nat := 118140960795 + 7642599 * 2 ^ 59
def prefixEnd_7642599 : Nat := 4983230072969 + 3 ^ 40 * 7642599 * 2
def baseEnd_7642599 : Nat := 436036304063472114440537

theorem tailTrace_7642599 : CollatzResearch.WordTrace tailWord_7642599 prefixEnd_7642599 436036304063472114440537 := by
  unfold tailWord_7642599
  simp only [CollatzResearch.WordTrace]
  refine ⟨278748485639176549837890851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185832323759451033225260567 278748485639176549837890851)
  ·
    refine ⟨418122728458764824756836277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278748485639176549837890851 418122728458764824756836277)
    ·
      refine ⟨39199005793009202320953401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 418122728458764824756836277 39199005793009202320953401)
      ·
        refine ⟨29399254344756901740715051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39199005793009202320953401 29399254344756901740715051)
        ·
          refine ⟨44098881517135352611072577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29399254344756901740715051 44098881517135352611072577)
          ·
            refine ⟨33074161137851514458304433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44098881517135352611072577 33074161137851514458304433)
            ·
              refine ⟨24805620853388635843728325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33074161137851514458304433 24805620853388635843728325)
              ·
                refine ⟨4651053910010369220699061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24805620853388635843728325 4651053910010369220699061)
                ·
                  refine ⟨436036304063472114440537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4651053910010369220699061 436036304063472114440537)
                  ·
                    rfl

theorem cell23_7642599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 5].length) (baseStart_7642599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642599 prefixEnd_7642599 := by exact prefixLift 7642599
  have htrace : WordTrace (prefixWord ++ tailWord_7642599) baseStart_7642599 baseEnd_7642599 := by
    simpa [prefixWord, tailWord_7642599, baseEnd_7642599] using wordTrace_append hprefix tailTrace_7642599
  have hstable : (prefixWord ++ tailWord_7642599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642599).length < 2 ^ (prefixWord ++ tailWord_7642599).sum := by decide
  have hdescent : baseEnd_7642599 < baseStart_7642599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642610 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7642610 : Nat := 118140960795 + 7642610 * 2 ^ 59
def prefixEnd_7642610 : Nat := 4983230072969 + 3 ^ 40 * 7642610 * 2
def baseEnd_7642610 : Nat := 3924332384858448486927283

theorem tailTrace_7642610 : CollatzResearch.WordTrace tailWord_7642610 prefixEnd_7642610 3924332384858448486927283 := by
  unfold tailWord_7642610
  simp only [CollatzResearch.WordTrace]
  refine ⟨69687221710534174679135321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185832591228091132477694189 69687221710534174679135321)
  ·
    refine ⟨52265416282900631009351491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69687221710534174679135321 52265416282900631009351491)
    ·
      refine ⟨78398124424350946514027237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52265416282900631009351491 78398124424350946514027237)
      ·
        refine ⟨14699648329565802471380107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78398124424350946514027237 14699648329565802471380107)
        ·
          refine ⟨22049472494348703707070161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14699648329565802471380107 22049472494348703707070161)
          ·
            refine ⟨16537104370761527780302621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22049472494348703707070161 16537104370761527780302621)
            ·
              refine ⟨6201414139035572917613483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16537104370761527780302621 6201414139035572917613483)
              ·
                refine ⟨9302121208553359376420225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201414139035572917613483 9302121208553359376420225)
                ·
                  refine ⟨6976590906415019532315169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9302121208553359376420225 6976590906415019532315169)
                  ·
                    refine ⟨5232443179811264649236377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6976590906415019532315169 5232443179811264649236377)
                    ·
                      refine ⟨3924332384858448486927283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232443179811264649236377 3924332384858448486927283)
                      ·
                        rfl

theorem cell23_7642610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7642610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642610 prefixEnd_7642610 := by exact prefixLift 7642610
  have htrace : WordTrace (prefixWord ++ tailWord_7642610) baseStart_7642610 baseEnd_7642610 := by
    simpa [prefixWord, tailWord_7642610, baseEnd_7642610] using wordTrace_append hprefix tailTrace_7642610
  have hstable : (prefixWord ++ tailWord_7642610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642610).length < 2 ^ (prefixWord ++ tailWord_7642610).sum := by decide
  have hdescent : baseEnd_7642610 < baseStart_7642610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642632 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_7642632 : Nat := 118140960795 + 7642632 * 2 ^ 59
def prefixEnd_7642632 : Nat := 4983230072969 + 3 ^ 40 * 7642632 * 2
def baseEnd_7642632 : Nat := 3924343681432847400852181

theorem tailTrace_7642632 : CollatzResearch.WordTrace tailWord_7642632 prefixEnd_7642632 3924343681432847400852181 := by
  unfold tailWord_7642632
  simp only [CollatzResearch.WordTrace]
  refine ⟨139374844624028498236921075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185833126165371330982561433 139374844624028498236921075)
  ·
    refine ⟨209062266936042747355381613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139374844624028498236921075 209062266936042747355381613)
    ·
      refine ⟨78398350101016030258268105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209062266936042747355381613 78398350101016030258268105)
      ·
        refine ⟨58798762575762022693701079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78398350101016030258268105 58798762575762022693701079)
        ·
          refine ⟨88198143863643034040551619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58798762575762022693701079 88198143863643034040551619)
          ·
            refine ⟨132297215795464551060827429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88198143863643034040551619 132297215795464551060827429)
            ·
              refine ⟨24805727961649603323905143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132297215795464551060827429 24805727961649603323905143)
              ·
                refine ⟨37208591942474404985857715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24805727961649603323905143 37208591942474404985857715)
                ·
                  refine ⟨55812887913711607478786573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37208591942474404985857715 55812887913711607478786573)
                  ·
                    refine ⟨20929832967641852804544965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55812887913711607478786573 20929832967641852804544965)
                    ·
                      refine ⟨3924343681432847400852181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20929832967641852804544965 3924343681432847400852181)
                      ·
                        rfl

theorem cell23_7642632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_7642632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642632 prefixEnd_7642632 := by exact prefixLift 7642632
  have htrace : WordTrace (prefixWord ++ tailWord_7642632) baseStart_7642632 baseEnd_7642632 := by
    simpa [prefixWord, tailWord_7642632, baseEnd_7642632] using wordTrace_append hprefix tailTrace_7642632
  have hstable : (prefixWord ++ tailWord_7642632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642632).length < 2 ^ (prefixWord ++ tailWord_7642632).sum := by decide
  have hdescent : baseEnd_7642632 < baseStart_7642632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642709 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_7642709 : Nat := 118140960795 + 7642709 * 2 ^ 59
def prefixEnd_7642709 : Nat := 4983230072969 + 3 ^ 40 * 7642709 * 2
def baseEnd_7642709 : Nat := 3924383219443243599589327

theorem tailTrace_7642709 : CollatzResearch.WordTrace tailWord_7642709 prefixEnd_7642709 3924383219443243599589327 := by
  unfold tailWord_7642709
  simp only [CollatzResearch.WordTrace]
  refine ⟨278752497668778038624395181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185834998445852025749596787 278752497668778038624395181)
  ·
    refine ⟨104532186625791764484148193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278752497668778038624395181 104532186625791764484148193)
    ·
      refine ⟨78399139969343823363111145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104532186625791764484148193 78399139969343823363111145)
      ·
        refine ⟨58799354977007867522333359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78399139969343823363111145 58799354977007867522333359)
        ·
          refine ⟨88199032465511801283500039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58799354977007867522333359 88199032465511801283500039)
          ·
            refine ⟨132298548698267701925250059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88199032465511801283500039 132298548698267701925250059)
            ·
              refine ⟨198447823047401552887875089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132298548698267701925250059 198447823047401552887875089)
              ·
                refine ⟨148835867285551164665906317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198447823047401552887875089 148835867285551164665906317)
                ·
                  refine ⟨55813450232081686749714869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148835867285551164665906317 55813450232081686749714869)
                  ·
                    refine ⟨5232510959257658132785769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55813450232081686749714869 5232510959257658132785769)
                    ·
                      refine ⟨3924383219443243599589327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232510959257658132785769 3924383219443243599589327)
                      ·
                        rfl

theorem cell23_7642709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_7642709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642709 prefixEnd_7642709 := by exact prefixLift 7642709
  have htrace : WordTrace (prefixWord ++ tailWord_7642709) baseStart_7642709 baseEnd_7642709 := by
    simpa [prefixWord, tailWord_7642709, baseEnd_7642709] using wordTrace_append hprefix tailTrace_7642709
  have hstable : (prefixWord ++ tailWord_7642709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642709).length < 2 ^ (prefixWord ++ tailWord_7642709).sum := by decide
  have hdescent : baseEnd_7642709 < baseStart_7642709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642733 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_7642733 : Nat := 118140960795 + 7642733 * 2 ^ 59
def prefixEnd_7642733 : Nat := 4983230072969 + 3 ^ 40 * 7642733 * 2
def baseEnd_7642733 : Nat := 3924395542978951505689217

theorem tailTrace_7642733 : CollatzResearch.WordTrace tailWord_7642733 prefixEnd_7642733 3924395542978951505689217 := by
  unfold tailWord_7642733
  simp only [CollatzResearch.WordTrace]
  refine ⟨278753373020691090723268853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185835582013794060482179235 278753373020691090723268853)
  ·
    refine ⟨26133128720689789755306455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278753373020691090723268853 26133128720689789755306455)
    ·
      refine ⟨39199693081034684632959683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26133128720689789755306455 39199693081034684632959683)
      ·
        refine ⟨58799539621552026949439525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39199693081034684632959683 58799539621552026949439525)
        ·
          refine ⟨11024913679041005053019911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58799539621552026949439525 11024913679041005053019911)
          ·
            refine ⟨16537370518561507579529867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11024913679041005053019911 16537370518561507579529867)
            ·
              refine ⟨24806055777842261369294801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16537370518561507579529867 24806055777842261369294801)
              ·
                refine ⟨18604541833381696026971101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24806055777842261369294801 18604541833381696026971101)
                ·
                  refine ⟨6976703187518136010114163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18604541833381696026971101 6976703187518136010114163)
                  ·
                    refine ⟨10465054781277204015171245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6976703187518136010114163 10465054781277204015171245)
                    ·
                      refine ⟨3924395542978951505689217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10465054781277204015171245 3924395542978951505689217)
                      ·
                        rfl

theorem cell23_7642733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_7642733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642733 prefixEnd_7642733 := by exact prefixLift 7642733
  have htrace : WordTrace (prefixWord ++ tailWord_7642733) baseStart_7642733 baseEnd_7642733 := by
    simpa [prefixWord, tailWord_7642733, baseEnd_7642733] using wordTrace_append hprefix tailTrace_7642733
  have hstable : (prefixWord ++ tailWord_7642733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642733).length < 2 ^ (prefixWord ++ tailWord_7642733).sum := by decide
  have hdescent : baseEnd_7642733 < baseStart_7642733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642749 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_7642749 : Nat := 118140960795 + 7642749 * 2 ^ 59
def prefixEnd_7642749 : Nat := 4983230072969 + 3 ^ 40 * 7642749 * 2
def baseEnd_7642749 : Nat := 1308134586223141147696381

theorem tailTrace_7642749 : CollatzResearch.WordTrace tailWord_7642749 prefixEnd_7642749 1308134586223141147696381 := by
  unfold tailWord_7642749
  simp only [CollatzResearch.WordTrace]
  refine ⟨278753956588633125455851301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185835971059088750303900867 278753956588633125455851301)
  ·
    refine ⟨52266366860368711022972119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278753956588633125455851301 52266366860368711022972119)
    ·
      refine ⟨78399550290553066534458179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52266366860368711022972119 78399550290553066534458179)
      ·
        refine ⟨117599325435829599801687269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78399550290553066534458179 117599325435829599801687269)
        ·
          refine ⟨22049873519218049962816363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117599325435829599801687269 22049873519218049962816363)
          ·
            refine ⟨33074810278827074944224545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22049873519218049962816363 33074810278827074944224545)
            ·
              refine ⟨24806107709120306208168409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33074810278827074944224545 24806107709120306208168409)
              ·
                refine ⟨18604580781840229656126307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24806107709120306208168409 18604580781840229656126307)
                ·
                  refine ⟨27906871172760344484189461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18604580781840229656126307 27906871172760344484189461)
                  ·
                    refine ⟨1308134586223141147696381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27906871172760344484189461 1308134586223141147696381)
                    ·
                      rfl

theorem cell23_7642749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_7642749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642749 prefixEnd_7642749 := by exact prefixLift 7642749
  have htrace : WordTrace (prefixWord ++ tailWord_7642749) baseStart_7642749 baseEnd_7642749 := by
    simpa [prefixWord, tailWord_7642749, baseEnd_7642749] using wordTrace_append hprefix tailTrace_7642749
  have hstable : (prefixWord ++ tailWord_7642749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642749).length < 2 ^ (prefixWord ++ tailWord_7642749).sum := by decide
  have hdescent : baseEnd_7642749 < baseStart_7642749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642753 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 1, 5]
def baseStart_7642753 : Nat := 118140960795 + 7642753 * 2 ^ 59
def prefixEnd_7642753 : Nat := 4983230072969 + 3 ^ 40 * 7642753 * 2
def baseEnd_7642753 : Nat := 1308135270864013809146375

theorem tailTrace_7642753 : CollatzResearch.WordTrace tailWord_7642753 prefixEnd_7642753 1308135270864013809146375 := by
  unfold tailWord_7642753
  simp only [CollatzResearch.WordTrace]
  refine ⟨278754102480618634138996913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185836068320412422759331275 278754102480618634138996913)
  ·
    refine ⟨209065576860463975604247685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278754102480618634138996913 209065576860463975604247685)
    ·
      refine ⟨39199795661336995425796441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209065576860463975604247685 39199795661336995425796441)
      ·
        refine ⟨29399846746002746569347331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39199795661336995425796441 29399846746002746569347331)
        ·
          refine ⟨44099770119004119854020997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29399846746002746569347331 44099770119004119854020997)
          ·
            refine ⟨8268706897313272472628937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44099770119004119854020997 8268706897313272472628937)
            ·
              refine ⟨6201530172984954354471703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268706897313272472628937 6201530172984954354471703)
              ·
                refine ⟨9302295259477431531707555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201530172984954354471703 9302295259477431531707555)
                ·
                  refine ⟨13953442889216147297561333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9302295259477431531707555 13953442889216147297561333)
                  ·
                    refine ⟨1308135270864013809146375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13953442889216147297561333 1308135270864013809146375)
                    ·
                      rfl

theorem cell23_7642753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_7642753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642753 prefixEnd_7642753 := by exact prefixLift 7642753
  have htrace : WordTrace (prefixWord ++ tailWord_7642753) baseStart_7642753 baseEnd_7642753 := by
    simpa [prefixWord, tailWord_7642753, baseEnd_7642753] using wordTrace_append hprefix tailTrace_7642753
  have hstable : (prefixWord ++ tailWord_7642753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642753).length < 2 ^ (prefixWord ++ tailWord_7642753).sum := by decide
  have hdescent : baseEnd_7642753 < baseStart_7642753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642766 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_7642766 : Nat := 118140960795 + 7642766 * 2 ^ 59
def prefixEnd_7642766 : Nat := 4983230072969 + 3 ^ 40 * 7642766 * 2
def baseEnd_7642766 : Nat := 1308137495946849958858855

theorem tailTrace_7642766 : CollatzResearch.WordTrace tailWord_7642766 prefixEnd_7642766 1308137495946849958858855 := by
  unfold tailWord_7642766
  simp only [CollatzResearch.WordTrace]
  refine ⟨34844322078696442169902519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185836384419714358239480101 34844322078696442169902519)
  ·
    refine ⟨52266483118044663254853779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34844322078696442169902519 52266483118044663254853779)
    ·
      refine ⟨78399724677066994882280669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52266483118044663254853779 78399724677066994882280669)
      ·
        refine ⟨29399896753900123080855251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78399724677066994882280669 29399896753900123080855251)
        ·
          refine ⟨44099845130850184621282877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29399896753900123080855251 44099845130850184621282877)
          ·
            refine ⟨16537441924068819232981079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44099845130850184621282877 16537441924068819232981079)
            ·
              refine ⟨24806162886103228849471619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16537441924068819232981079 24806162886103228849471619)
              ·
                refine ⟨37209244329154843274207429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24806162886103228849471619 37209244329154843274207429)
                ·
                  refine ⟨6976733311716533113913893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37209244329154843274207429 6976733311716533113913893)
                  ·
                    refine ⟨1308137495946849958858855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976733311716533113913893 1308137495946849958858855)
                    ·
                      rfl

theorem cell23_7642766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_7642766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642766 prefixEnd_7642766 := by exact prefixLift 7642766
  have htrace : WordTrace (prefixWord ++ tailWord_7642766) baseStart_7642766 baseEnd_7642766 := by
    simpa [prefixWord, tailWord_7642766, baseEnd_7642766] using wordTrace_append hprefix tailTrace_7642766
  have hstable : (prefixWord ++ tailWord_7642766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642766).length < 2 ^ (prefixWord ++ tailWord_7642766).sum := by decide
  have hdescent : baseEnd_7642766 < baseStart_7642766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642783 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 1, 6]
def baseStart_7642783 : Nat := 118140960795 + 7642783 * 2 ^ 59
def prefixEnd_7642783 : Nat := 4983230072969 + 3 ^ 40 * 7642783 * 2
def baseEnd_7642783 : Nat := 1308140405670558770021329

theorem tailTrace_7642783 : CollatzResearch.WordTrace tailWord_7642783 prefixEnd_7642783 1308140405670558770021329 := by
  unfold tailWord_7642783
  simp only [CollatzResearch.WordTrace]
  refine ⟨278755196670509949262589003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185836797780339966175059335 278755196670509949262589003)
  ·
    refine ⟨418132795005764923893883505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278755196670509949262589003 418132795005764923893883505)
    ·
      refine ⟨313599596254323692920412629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418132795005764923893883505 313599596254323692920412629)
      ·
        refine ⟨7349990537210711552822171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 313599596254323692920412629 7349990537210711552822171)
        ·
          refine ⟨11024985805816067329233257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7349990537210711552822171 11024985805816067329233257)
          ·
            refine ⟨8268739354362050496924943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11024985805816067329233257 8268739354362050496924943)
            ·
              refine ⟨12403109031543075745387415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268739354362050496924943 12403109031543075745387415)
              ·
                refine ⟨18604663547314613618081123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12403109031543075745387415 18604663547314613618081123)
                ·
                  refine ⟨27906995320971920427121685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18604663547314613618081123 27906995320971920427121685)
                  ·
                    refine ⟨1308140405670558770021329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27906995320971920427121685 1308140405670558770021329)
                    ·
                      rfl

theorem cell23_7642783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_7642783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642783 prefixEnd_7642783 := by exact prefixLift 7642783
  have htrace : WordTrace (prefixWord ++ tailWord_7642783) baseStart_7642783 baseEnd_7642783 := by
    simpa [prefixWord, tailWord_7642783, baseEnd_7642783] using wordTrace_append hprefix tailTrace_7642783
  have hstable : (prefixWord ++ tailWord_7642783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642783).length < 2 ^ (prefixWord ++ tailWord_7642783).sum := by decide
  have hdescent : baseEnd_7642783 < baseStart_7642783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642807 : List Nat := [1, 1, 3, 1, 5, 3, 1, 3, 1, 2, 2]
def baseStart_7642807 : Nat := 118140960795 + 7642807 * 2 ^ 59
def prefixEnd_7642807 : Nat := 4983230072969 + 3 ^ 40 * 7642807 * 2
def baseEnd_7642807 : Nat := 3924433540547384216163877

theorem tailTrace_7642807 : CollatzResearch.WordTrace tailWord_7642807 prefixEnd_7642807 3924433540547384216163877 := by
  unfold tailWord_7642807
  simp only [CollatzResearch.WordTrace]
  refine ⟨278756072022423001361462675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185837381348282000907641783 278756072022423001361462675)
  ·
    refine ⟨418134108033634502042194013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278756072022423001361462675 418134108033634502042194013)
    ·
      refine ⟨156800290512612938265822755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418134108033634502042194013 156800290512612938265822755)
      ·
        refine ⟨235200435768919407398734133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156800290512612938265822755 235200435768919407398734133)
        ·
          refine ⟨22050040853336194443631325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235200435768919407398734133 22050040853336194443631325)
          ·
            refine ⟨8268765320001072916361747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22050040853336194443631325 8268765320001072916361747)
            ·
              refine ⟨12403147980001609374542621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268765320001072916361747 12403147980001609374542621)
              ·
                refine ⟨4651180492500603515453483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12403147980001609374542621 4651180492500603515453483)
                ·
                  refine ⟨6976770738750905273180225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651180492500603515453483 6976770738750905273180225)
                  ·
                    refine ⟨5232578054063178954885169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6976770738750905273180225 5232578054063178954885169)
                    ·
                      refine ⟨3924433540547384216163877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232578054063178954885169 3924433540547384216163877)
                      ·
                        rfl

theorem cell23_7642807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_7642807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642807 prefixEnd_7642807 := by exact prefixLift 7642807
  have htrace : WordTrace (prefixWord ++ tailWord_7642807) baseStart_7642807 baseEnd_7642807 := by
    simpa [prefixWord, tailWord_7642807, baseEnd_7642807] using wordTrace_append hprefix tailTrace_7642807
  have hstable : (prefixWord ++ tailWord_7642807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642807).length < 2 ^ (prefixWord ++ tailWord_7642807).sum := by decide
  have hdescent : baseEnd_7642807 < baseStart_7642807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642916 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_7642916 : Nat := 118140960795 + 7642916 * 2 ^ 59
def prefixEnd_7642916 : Nat := 4983230072969 + 3 ^ 40 * 7642916 * 2
def baseEnd_7642916 : Nat := 1308163169979574763233625

theorem tailTrace_7642916 : CollatzResearch.WordTrace tailWord_7642916 prefixEnd_7642916 1308163169979574763233625 := by
  unfold tailWord_7642916
  simp only [CollatzResearch.WordTrace]
  refine ⟨139380023789514056488590301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185840031719352075318120401 139380023789514056488590301)
  ·
    refine ⟨52267508921067771183221363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139380023789514056488590301 52267508921067771183221363)
    ·
      refine ⟨78401263381601656774832045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52267508921067771183221363 78401263381601656774832045)
      ·
        refine ⟨29400473768100621290562017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78401263381601656774832045 29400473768100621290562017)
        ·
          refine ⟨22050355326075465967921513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29400473768100621290562017 22050355326075465967921513)
          ·
            refine ⟨16537766494556599475941135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22050355326075465967921513 16537766494556599475941135)
            ·
              refine ⟨24806649741834899213911703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16537766494556599475941135 24806649741834899213911703)
              ·
                refine ⟨37209974612752348820867555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24806649741834899213911703 37209974612752348820867555)
                ·
                  refine ⟨55814961919128523231301333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37209974612752348820867555 55814961919128523231301333)
                  ·
                    refine ⟨1308163169979574763233625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55814961919128523231301333 1308163169979574763233625)
                    ·
                      rfl

theorem cell23_7642916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_7642916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642916 prefixEnd_7642916 := by exact prefixLift 7642916
  have htrace : WordTrace (prefixWord ++ tailWord_7642916) baseStart_7642916 baseEnd_7642916 := by
    simpa [prefixWord, tailWord_7642916, baseEnd_7642916] using wordTrace_append hprefix tailTrace_7642916
  have hstable : (prefixWord ++ tailWord_7642916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642916).length < 2 ^ (prefixWord ++ tailWord_7642916).sum := by decide
  have hdescent : baseEnd_7642916 < baseStart_7642916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642949 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_7642949 : Nat := 118140960795 + 7642949 * 2 ^ 59
def prefixEnd_7642949 : Nat := 4983230072969 + 3 ^ 40 * 7642949 * 2
def baseEnd_7642949 : Nat := 3924506454800322660588223

theorem tailTrace_7642949 : CollatzResearch.WordTrace tailWord_7642949 prefixEnd_7642949 3924506454800322660588223 := by
  unfold tailWord_7642949
  simp only [CollatzResearch.WordTrace]
  refine ⟨278761251187908559613131901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185840834125272373075421267 278761251187908559613131901)
  ·
    refine ⟨104535469195465709854924463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278761251187908559613131901 104535469195465709854924463)
    ·
      refine ⟨156803203793198564782386695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104535469195465709854924463 156803203793198564782386695)
      ·
        refine ⟨235204805689797847173580043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156803203793198564782386695 235204805689797847173580043)
        ·
          refine ⟨352807208534696770760370065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235204805689797847173580043 352807208534696770760370065)
          ·
            refine ⟨264605406401022578070277549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352807208534696770760370065 264605406401022578070277549)
            ·
              refine ⟨99227027400383466776354081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264605406401022578070277549 99227027400383466776354081)
              ·
                refine ⟨74420270550287600082265561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99227027400383466776354081 74420270550287600082265561)
                ·
                  refine ⟨55815202912715700061699171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74420270550287600082265561 55815202912715700061699171)
                  ·
                    refine ⟨83722804369073550092548757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55815202912715700061699171 83722804369073550092548757)
                    ·
                      refine ⟨3924506454800322660588223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83722804369073550092548757 3924506454800322660588223)
                      ·
                        rfl

theorem cell23_7642949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_7642949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642949 prefixEnd_7642949 := by exact prefixLift 7642949
  have htrace : WordTrace (prefixWord ++ tailWord_7642949) baseStart_7642949 baseEnd_7642949 := by
    simpa [prefixWord, tailWord_7642949, baseEnd_7642949] using wordTrace_append hprefix tailTrace_7642949
  have hstable : (prefixWord ++ tailWord_7642949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642949).length < 2 ^ (prefixWord ++ tailWord_7642949).sum := by decide
  have hdescent : baseEnd_7642949 < baseStart_7642949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642990 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7642990 : Nat := 118140960795 + 7642990 * 2 ^ 59
def prefixEnd_7642990 : Nat := 4983230072969 + 3 ^ 40 * 7642990 * 2
def baseEnd_7642990 : Nat := 3924527507507157000175535

theorem tailTrace_7642990 : CollatzResearch.WordTrace tailWord_7642990 prefixEnd_7642990 3924527507507157000175535 := by
  unfold tailWord_7642990
  simp only [CollatzResearch.WordTrace]
  refine ⟨34845343322595002951921803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185841831053840015743582949 34845343322595002951921803)
  ·
    refine ⟨52268014983892504427882705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34845343322595002951921803 52268014983892504427882705)
    ·
      refine ⟨39201011237919378320912029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52268014983892504427882705 39201011237919378320912029)
      ·
        refine ⟨14700379214219766870342011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39201011237919378320912029 14700379214219766870342011)
        ·
          refine ⟨22050568821329650305513017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14700379214219766870342011 22050568821329650305513017)
          ·
            refine ⟨16537926615997237729134763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22050568821329650305513017 16537926615997237729134763)
            ·
              refine ⟨24806889923995856593702145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16537926615997237729134763 24806889923995856593702145)
              ·
                refine ⟨18605167442996892445276609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24806889923995856593702145 18605167442996892445276609)
                ·
                  refine ⟨13953875582247669333957457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18605167442996892445276609 13953875582247669333957457)
                  ·
                    refine ⟨10465406686685752000468093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13953875582247669333957457 10465406686685752000468093)
                    ·
                      refine ⟨3924527507507157000175535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10465406686685752000468093 3924527507507157000175535)
                      ·
                        rfl

theorem cell23_7642990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7642990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642990 prefixEnd_7642990 := by exact prefixLift 7642990
  have htrace : WordTrace (prefixWord ++ tailWord_7642990) baseStart_7642990 baseEnd_7642990 := by
    simpa [prefixWord, tailWord_7642990, baseEnd_7642990] using wordTrace_append hprefix tailTrace_7642990
  have hstable : (prefixWord ++ tailWord_7642990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642990).length < 2 ^ (prefixWord ++ tailWord_7642990).sum := by decide
  have hdescent : baseEnd_7642990 < baseStart_7642990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642997 : List Nat := [1, 3, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_7642997 : Nat := 118140960795 + 7642997 * 2 ^ 59
def prefixEnd_7642997 : Nat := 4983230072969 + 3 ^ 40 * 7642997 * 2
def baseEnd_7642997 : Nat := 1308177033957246157596001

theorem tailTrace_7642997 : CollatzResearch.WordTrace tailWord_7642997 prefixEnd_7642997 1308177033957246157596001 := by
  unfold tailWord_7642997
  simp only [CollatzResearch.WordTrace]
  refine ⟨278763001891734663810879245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185842001261156442540586163 278763001891734663810879245)
  ·
    refine ⟨104536125709400498929079717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278763001891734663810879245 104536125709400498929079717)
    ·
      refine ⟨19600523570512593549202447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104536125709400498929079717 19600523570512593549202447)
      ·
        refine ⟨29400785355768890323803671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19600523570512593549202447 29400785355768890323803671)
        ·
          refine ⟨44101178033653335485705507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29400785355768890323803671 44101178033653335485705507)
          ·
            refine ⟨66151767050480003228558261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44101178033653335485705507 66151767050480003228558261)
            ·
              refine ⟨6201728160982500302677337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66151767050480003228558261 6201728160982500302677337)
              ·
                refine ⟨4651296120736875227008003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201728160982500302677337 4651296120736875227008003)
                ·
                  refine ⟨6976944181105312840512005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651296120736875227008003 6976944181105312840512005)
                  ·
                    refine ⟨1308177033957246157596001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976944181105312840512005 1308177033957246157596001)
                    ·
                      rfl

theorem cell23_7642997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_7642997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642997 prefixEnd_7642997 := by exact prefixLift 7642997
  have htrace : WordTrace (prefixWord ++ tailWord_7642997) baseStart_7642997 baseEnd_7642997 := by
    simpa [prefixWord, tailWord_7642997, baseEnd_7642997] using wordTrace_append hprefix tailTrace_7642997
  have hstable : (prefixWord ++ tailWord_7642997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642997).length < 2 ^ (prefixWord ++ tailWord_7642997).sum := by decide
  have hdescent : baseEnd_7642997 < baseStart_7642997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7642999 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_7642999 : Nat := 118140960795 + 7642999 * 2 ^ 59
def prefixEnd_7642999 : Nat := 4983230072969 + 3 ^ 40 * 7642999 * 2
def baseEnd_7642999 : Nat := 3924532128833047464962993

theorem tailTrace_7642999 : CollatzResearch.WordTrace tailWord_7642999 prefixEnd_7642999 3924532128833047464962993 := by
  unfold tailWord_7642999
  simp only [CollatzResearch.WordTrace]
  refine ⟨278763074837727418152452051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185842049891818278768301367 278763074837727418152452051)
  ·
    refine ⟨418144612256591127228678077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278763074837727418152452051 418144612256591127228678077)
    ·
      refine ⟨156804229596221672710754279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418144612256591127228678077 156804229596221672710754279)
      ·
        refine ⟨235206344394332509066131419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156804229596221672710754279 235206344394332509066131419)
        ·
          refine ⟨352809516591498763599197129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235206344394332509066131419 352809516591498763599197129)
          ·
            refine ⟨264607137443624072699397847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352809516591498763599197129 264607137443624072699397847)
            ·
              refine ⟨396910706165436109049096771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264607137443624072699397847 396910706165436109049096771)
              ·
                refine ⟨595366059248154163573645157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396910706165436109049096771 595366059248154163573645157)
                ·
                  refine ⟨111631136109028905670058467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595366059248154163573645157 111631136109028905670058467)
                  ·
                    refine ⟨167446704163543358505087701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111631136109028905670058467 167446704163543358505087701)
                    ·
                      refine ⟨3924532128833047464962993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167446704163543358505087701 3924532128833047464962993)
                      ·
                        rfl

theorem cell23_7642999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_7642999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7642999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7642999 prefixEnd_7642999 := by exact prefixLift 7642999
  have htrace : WordTrace (prefixWord ++ tailWord_7642999) baseStart_7642999 baseEnd_7642999 := by
    simpa [prefixWord, tailWord_7642999, baseEnd_7642999] using wordTrace_append hprefix tailTrace_7642999
  have hstable : (prefixWord ++ tailWord_7642999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7642999).length < 2 ^ (prefixWord ++ tailWord_7642999).sum := by decide
  have hdescent : baseEnd_7642999 < baseStart_7642999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7642999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643013 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 4, 3, 2]
def baseStart_7643013 : Nat := 118140960795 + 7643013 * 2 ^ 59
def prefixEnd_7643013 : Nat := 4983230072969 + 3 ^ 40 * 7643013 * 2
def baseEnd_7643013 : Nat := 3924539317562210410187929

theorem tailTrace_7643013 : CollatzResearch.WordTrace tailWord_7643013 prefixEnd_7643013 3924539317562210410187929 := by
  unfold tailWord_7643013
  simp only [CollatzResearch.WordTrace]
  refine ⟨278763585459676698543461693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185842390306451132362307795 278763585459676698543461693)
  ·
    refine ⟨104536344547378761953798135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278763585459676698543461693 104536344547378761953798135)
    ·
      refine ⟨156804516821068142930697203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104536344547378761953798135 156804516821068142930697203)
      ·
        refine ⟨235206775231602214396045805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156804516821068142930697203 235206775231602214396045805)
        ·
          refine ⟨88202540711850830398517177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235206775231602214396045805 88202540711850830398517177)
          ·
            refine ⟨66151905533888122798887883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88202540711850830398517177 66151905533888122798887883)
            ·
              refine ⟨99227858300832184198331825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66151905533888122798887883 99227858300832184198331825)
              ·
                refine ⟨74420893725624138148748869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99227858300832184198331825 74420893725624138148748869)
                ·
                  refine ⟨13953917573554525902890413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74420893725624138148748869 13953917573554525902890413)
                  ·
                    refine ⟨5232719090082947213583905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13953917573554525902890413 5232719090082947213583905)
                    ·
                      refine ⟨3924539317562210410187929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232719090082947213583905 3924539317562210410187929)
                      ·
                        rfl

theorem cell23_7643013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_7643013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643013 prefixEnd_7643013 := by exact prefixLift 7643013
  have htrace : WordTrace (prefixWord ++ tailWord_7643013) baseStart_7643013 baseEnd_7643013 := by
    simpa [prefixWord, tailWord_7643013, baseEnd_7643013] using wordTrace_append hprefix tailTrace_7643013
  have hstable : (prefixWord ++ tailWord_7643013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643013).length < 2 ^ (prefixWord ++ tailWord_7643013).sum := by decide
  have hdescent : baseEnd_7643013 < baseStart_7643013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643048 : List Nat := [2, 1, 6, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7643048 : Nat := 118140960795 + 7643048 * 2 ^ 59
def prefixEnd_7643048 : Nat := 4983230072969 + 3 ^ 40 * 7643048 * 2
def baseEnd_7643048 : Nat := 1308185763128372591083423

theorem tailTrace_7643048 : CollatzResearch.WordTrace tailWord_7643048 prefixEnd_7643048 1308185763128372591083423 := by
  unfold tailWord_7643048
  simp only [CollatzResearch.WordTrace]
  refine ⟨139382431007274949760492899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185843241343033266347323865 139382431007274949760492899)
  ·
    refine ⟨209073646510912424640739349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139382431007274949760492899 209073646510912424640739349)
    ·
      refine ⟨9800327180199019905034657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209073646510912424640739349 9800327180199019905034657)
      ·
        refine ⟨7350245385149264928775993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9800327180199019905034657 7350245385149264928775993)
        ·
          refine ⟨5512684038861948696581995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7350245385149264928775993 5512684038861948696581995)
          ·
            refine ⟨8269026058292923044872993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512684038861948696581995 8269026058292923044872993)
            ·
              refine ⟨6201769543719692283654745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8269026058292923044872993 6201769543719692283654745)
              ·
                refine ⟨4651327157789769212741059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201769543719692283654745 4651327157789769212741059)
                ·
                  refine ⟨6976990736684653819111589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651327157789769212741059 6976990736684653819111589)
                  ·
                    refine ⟨1308185763128372591083423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976990736684653819111589 1308185763128372591083423)
                    ·
                      rfl

theorem cell23_7643048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7643048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643048 prefixEnd_7643048 := by exact prefixLift 7643048
  have htrace : WordTrace (prefixWord ++ tailWord_7643048) baseStart_7643048 baseEnd_7643048 := by
    simpa [prefixWord, tailWord_7643048, baseEnd_7643048] using wordTrace_append hprefix tailTrace_7643048
  have hstable : (prefixWord ++ tailWord_7643048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643048).length < 2 ^ (prefixWord ++ tailWord_7643048).sum := by decide
  have hdescent : baseEnd_7643048 < baseStart_7643048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643070 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_7643070 : Nat := 118140960795 + 7643070 * 2 ^ 59
def prefixEnd_7643070 : Nat := 4983230072969 + 3 ^ 40 * 7643070 * 2
def baseEnd_7643070 : Nat := 1308189528653172229058389

theorem tailTrace_7643070 : CollatzResearch.WordTrace tailWord_7643070 prefixEnd_7643070 1308189528653172229058389 := by
  unfold tailWord_7643070
  simp only [CollatzResearch.WordTrace]
  refine ⟨34845708052558774659785833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185843776280313464852191109 34845708052558774659785833)
  ·
    refine ⟨26134281039419080994839375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34845708052558774659785833 26134281039419080994839375)
    ·
      refine ⟨39201421559128621492259063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26134281039419080994839375 39201421559128621492259063)
      ·
        refine ⟨58802132338692932238388595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39201421559128621492259063 58802132338692932238388595)
        ·
          refine ⟨88203198508039398357582893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58802132338692932238388595 88203198508039398357582893)
          ·
            refine ⟨33076199440514774384093585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88203198508039398357582893 33076199440514774384093585)
            ·
              refine ⟨24807149580386080788070189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33076199440514774384093585 24807149580386080788070189)
              ·
                refine ⟨9302681092644780295526321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24807149580386080788070189 9302681092644780295526321)
                ·
                  refine ⟨6977010819483585221644741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9302681092644780295526321 6977010819483585221644741)
                  ·
                    refine ⟨1308189528653172229058389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977010819483585221644741 1308189528653172229058389)
                    ·
                      rfl

theorem cell23_7643070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_7643070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643070 prefixEnd_7643070 := by exact prefixLift 7643070
  have htrace : WordTrace (prefixWord ++ tailWord_7643070) baseStart_7643070 baseEnd_7643070 := by
    simpa [prefixWord, tailWord_7643070, baseEnd_7643070] using wordTrace_append hprefix tailTrace_7643070
  have hstable : (prefixWord ++ tailWord_7643070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643070).length < 2 ^ (prefixWord ++ tailWord_7643070).sum := by decide
  have hdescent : baseEnd_7643070 < baseStart_7643070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643116 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_7643116 : Nat := 118140960795 + 7643116 * 2 ^ 59
def prefixEnd_7643116 : Nat := 4983230072969 + 3 ^ 40 * 7643116 * 2
def baseEnd_7643116 : Nat := 3924592206069623507199955

theorem tailTrace_7643116 : CollatzResearch.WordTrace tailWord_7643116 prefixEnd_7643116 3924592206069623507199955 := by
  unfold tailWord_7643116
  simp only [CollatzResearch.WordTrace]
  refine ⟨139383671089151773567230601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185844894785535698089640801 139383671089151773567230601)
  ·
    refine ⟨104537753316863830175422951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139383671089151773567230601 104537753316863830175422951)
    ·
      refine ⟨156806629975295745263134427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104537753316863830175422951 156806629975295745263134427)
      ·
        refine ⟨235209944962943617894701641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156806629975295745263134427 235209944962943617894701641)
        ·
          refine ⟨176407458722207713421026231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235209944962943617894701641 176407458722207713421026231)
          ·
            refine ⟨264611188083311570131539347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176407458722207713421026231 264611188083311570131539347)
            ·
              refine ⟨396916782124967355197309021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264611188083311570131539347 396916782124967355197309021)
              ·
                refine ⟨148843793296862758198990883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 396916782124967355197309021 148843793296862758198990883)
                ·
                  refine ⟨223265689945294137298486325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148843793296862758198990883 223265689945294137298486325)
                  ·
                    refine ⟨20931158432371325371733093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 223265689945294137298486325 20931158432371325371733093)
                    ·
                      refine ⟨3924592206069623507199955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20931158432371325371733093 3924592206069623507199955)
                      ·
                        rfl

theorem cell23_7643116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_7643116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643116 prefixEnd_7643116 := by exact prefixLift 7643116
  have htrace : WordTrace (prefixWord ++ tailWord_7643116) baseStart_7643116 baseEnd_7643116 := by
    simpa [prefixWord, tailWord_7643116, baseEnd_7643116] using wordTrace_append hprefix tailTrace_7643116
  have hstable : (prefixWord ++ tailWord_7643116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643116).length < 2 ^ (prefixWord ++ tailWord_7643116).sum := by decide
  have hdescent : baseEnd_7643116 < baseStart_7643116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643137 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_7643137 : Nat := 118140960795 + 7643137 * 2 ^ 59
def prefixEnd_7643137 : Nat := 4983230072969 + 3 ^ 40 * 7643137 * 2
def baseEnd_7643137 : Nat := 3924602989163367925037359

theorem tailTrace_7643137 : CollatzResearch.WordTrace tailWord_7643137 prefixEnd_7643137 3924602989163367925037359 := by
  unfold tailWord_7643137
  simp only [CollatzResearch.WordTrace]
  refine ⟨278768108111227467720975665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185845405407484978480650443 278768108111227467720975665)
  ·
    refine ⟨209076081083420600790731749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278768108111227467720975665 209076081083420600790731749)
    ·
      refine ⟨39201765203141362648262203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209076081083420600790731749 39201765203141362648262203)
      ·
        refine ⟨58802647804712043972393305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39201765203141362648262203 58802647804712043972393305)
        ·
          refine ⟨44101985853534032979294979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58802647804712043972393305 44101985853534032979294979)
          ·
            refine ⟨66152978780301049468942469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44101985853534032979294979 66152978780301049468942469)
            ·
              refine ⟨12403683521306446775426713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66152978780301049468942469 12403683521306446775426713)
              ·
                refine ⟨9302762640979835081570035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12403683521306446775426713 9302762640979835081570035)
                ·
                  refine ⟨13954143961469752622355053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9302762640979835081570035 13954143961469752622355053)
                  ·
                    refine ⟨5232803985551157233383145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13954143961469752622355053 5232803985551157233383145)
                    ·
                      refine ⟨3924602989163367925037359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232803985551157233383145 3924602989163367925037359)
                      ·
                        rfl

theorem cell23_7643137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_7643137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643137 prefixEnd_7643137 := by exact prefixLift 7643137
  have htrace : WordTrace (prefixWord ++ tailWord_7643137) baseStart_7643137 baseEnd_7643137 := by
    simpa [prefixWord, tailWord_7643137, baseEnd_7643137] using wordTrace_append hprefix tailTrace_7643137
  have hstable : (prefixWord ++ tailWord_7643137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643137).length < 2 ^ (prefixWord ++ tailWord_7643137).sum := by decide
  have hdescent : baseEnd_7643137 < baseStart_7643137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643150 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_7643150 : Nat := 118140960795 + 7643150 * 2 ^ 59
def prefixEnd_7643150 : Nat := 4983230072969 + 3 ^ 40 * 7643150 * 2
def baseEnd_7643150 : Nat := 3924609664411876374174799

theorem tailTrace_7643150 : CollatzResearch.WordTrace tailWord_7643150 prefixEnd_7643150 3924609664411876374174799 := by
  unfold tailWord_7643150
  simp only [CollatzResearch.WordTrace]
  refine ⟨34846072782522546367649863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185845721506786913960799269 34846072782522546367649863)
  ·
    refine ⟨52269109173783819551474795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34846072782522546367649863 52269109173783819551474795)
    ·
      refine ⟨78403663760675729327212193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52269109173783819551474795 78403663760675729327212193)
      ·
        refine ⟨58802747820506796995409145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78403663760675729327212193 58802747820506796995409145)
        ·
          refine ⟨44102060865380097746556859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58802747820506796995409145 44102060865380097746556859)
          ·
            refine ⟨66153091298070146619835289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44102060865380097746556859 66153091298070146619835289)
            ·
              refine ⟨49614818473552609964876467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66153091298070146619835289 49614818473552609964876467)
              ·
                refine ⟨74422227710328914947314701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49614818473552609964876467 74422227710328914947314701)
                ·
                  refine ⟨27908335391373343105243013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74422227710328914947314701 27908335391373343105243013)
                  ·
                    refine ⟨5232812885882501832233065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27908335391373343105243013 5232812885882501832233065)
                    ·
                      refine ⟨3924609664411876374174799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232812885882501832233065 3924609664411876374174799)
                      ·
                        rfl

theorem cell23_7643150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_7643150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643150 prefixEnd_7643150 := by exact prefixLift 7643150
  have htrace : WordTrace (prefixWord ++ tailWord_7643150) baseStart_7643150 baseEnd_7643150 := by
    simpa [prefixWord, tailWord_7643150, baseEnd_7643150] using wordTrace_append hprefix tailTrace_7643150
  have hstable : (prefixWord ++ tailWord_7643150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643150).length < 2 ^ (prefixWord ++ tailWord_7643150).sum := by decide
  have hdescent : baseEnd_7643150 < baseStart_7643150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643167 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 2, 2, 2]
def baseStart_7643167 : Nat := 118140960795 + 7643167 * 2 ^ 59
def prefixEnd_7643167 : Nat := 4983230072969 + 3 ^ 40 * 7643167 * 2
def baseEnd_7643167 : Nat := 3924618393583002807662221

theorem tailTrace_7643167 : CollatzResearch.WordTrace tailWord_7643167 prefixEnd_7643167 3924618393583002807662221 := by
  unfold tailWord_7643167
  simp only [CollatzResearch.WordTrace]
  refine ⟨278769202301118782844567755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185846134867412521896378503 278769202301118782844567755)
  ·
    refine ⟨418153803451678174266851633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278769202301118782844567755 418153803451678174266851633)
    ·
      refine ⟨313615352588758630700138725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418153803451678174266851633 313615352588758630700138725)
      ·
        refine ⟨58802878610392243256276011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313615352588758630700138725 58802878610392243256276011)
        ·
          refine ⟨88204317915588364884414017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58802878610392243256276011 88204317915588364884414017)
          ·
            refine ⟨66153238436691273663310513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88204317915588364884414017 66153238436691273663310513)
            ·
              refine ⟨49614928827518455247482885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66153238436691273663310513 49614928827518455247482885)
              ·
                refine ⟨9302799155159710358903041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49614928827518455247482885 9302799155159710358903041)
                ·
                  refine ⟨6977099366369782769177281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9302799155159710358903041 6977099366369782769177281)
                  ·
                    refine ⟨5232824524777337076882961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6977099366369782769177281 5232824524777337076882961)
                    ·
                      refine ⟨3924618393583002807662221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232824524777337076882961 3924618393583002807662221)
                      ·
                        rfl

theorem cell23_7643167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_7643167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643167 prefixEnd_7643167 := by exact prefixLift 7643167
  have htrace : WordTrace (prefixWord ++ tailWord_7643167) baseStart_7643167 baseEnd_7643167 := by
    simpa [prefixWord, tailWord_7643167, baseEnd_7643167] using wordTrace_append hprefix tailTrace_7643167
  have hstable : (prefixWord ++ tailWord_7643167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643167).length < 2 ^ (prefixWord ++ tailWord_7643167).sum := by decide
  have hdescent : baseEnd_7643167 < baseStart_7643167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643173 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 7]
def baseStart_7643173 : Nat := 118140960795 + 7643173 * 2 ^ 59
def prefixEnd_7643173 : Nat := 4983230072969 + 3 ^ 40 * 7643173 * 2
def baseEnd_7643173 : Nat := 436069052718547753798577

theorem tailTrace_7643173 : CollatzResearch.WordTrace tailWord_7643173 prefixEnd_7643173 436069052718547753798577 := by
  unfold tailWord_7643173
  simp only [CollatzResearch.WordTrace]
  refine ⟨278769421139097045869286173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185846280759398030579524115 278769421139097045869286173)
  ·
    refine ⟨104538532927161392200982315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278769421139097045869286173 104538532927161392200982315)
    ·
      refine ⟨156807799390742088301473473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104538532927161392200982315 156807799390742088301473473)
      ·
        refine ⟨117605849543056566226105105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156807799390742088301473473 117605849543056566226105105)
        ·
          refine ⟨88204387157292424669578829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117605849543056566226105105 88204387157292424669578829)
          ·
            refine ⟨33076645183984659251092061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88204387157292424669578829 33076645183984659251092061)
            ·
              refine ⟨12403741943994247219159523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33076645183984659251092061 12403741943994247219159523)
              ·
                refine ⟨18605612915991370828739285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12403741943994247219159523 18605612915991370828739285)
                ·
                  refine ⟨436069052718547753798577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18605612915991370828739285 436069052718547753798577)
                  ·
                    rfl

theorem cell23_7643173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_7643173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643173 prefixEnd_7643173 := by exact prefixLift 7643173
  have htrace : WordTrace (prefixWord ++ tailWord_7643173) baseStart_7643173 baseEnd_7643173 := by
    simpa [prefixWord, tailWord_7643173, baseEnd_7643173] using wordTrace_append hprefix tailTrace_7643173
  have hstable : (prefixWord ++ tailWord_7643173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643173).length < 2 ^ (prefixWord ++ tailWord_7643173).sum := by decide
  have hdescent : baseEnd_7643173 < baseStart_7643173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643184 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 2, 2, 2]
def baseStart_7643184 : Nat := 118140960795 + 7643184 * 2 ^ 59
def prefixEnd_7643184 : Nat := 4983230072969 + 3 ^ 40 * 7643184 * 2
def baseEnd_7643184 : Nat := 3924627122754129241149643

theorem tailTrace_7643184 : CollatzResearch.WordTrace tailWord_7643184 prefixEnd_7643184 3924627122754129241149643 := by
  unfold tailWord_7643184
  simp only [CollatzResearch.WordTrace]
  refine ⟨139384911171028597373968303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185846548228038129831957737 139384911171028597373968303)
  ·
    refine ⟨209077366756542896060952455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139384911171028597373968303 209077366756542896060952455)
    ·
      refine ⟨313616050134814344091428683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209077366756542896060952455 313616050134814344091428683)
      ·
        refine ⟨470424075202221516137143025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313616050134814344091428683 470424075202221516137143025)
        ·
          refine ⟨352818056401666137102857269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470424075202221516137143025 352818056401666137102857269)
          ·
            refine ⟨33076692787656200353392869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352818056401666137102857269 33076692787656200353392869)
            ·
              refine ⟨6201879897685537566261163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33076692787656200353392869 6201879897685537566261163)
              ·
                refine ⟨9302819846528306349391745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201879897685537566261163 9302819846528306349391745)
                ·
                  refine ⟨6977114884896229762043809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9302819846528306349391745 6977114884896229762043809)
                  ·
                    refine ⟨5232836163672172321532857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6977114884896229762043809 5232836163672172321532857)
                    ·
                      refine ⟨3924627122754129241149643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232836163672172321532857 3924627122754129241149643)
                      ·
                        rfl

theorem cell23_7643184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 2, 2].length) (baseStart_7643184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643184 prefixEnd_7643184 := by exact prefixLift 7643184
  have htrace : WordTrace (prefixWord ++ tailWord_7643184) baseStart_7643184 baseEnd_7643184 := by
    simpa [prefixWord, tailWord_7643184, baseEnd_7643184] using wordTrace_append hprefix tailTrace_7643184
  have hstable : (prefixWord ++ tailWord_7643184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643184).length < 2 ^ (prefixWord ++ tailWord_7643184).sum := by decide
  have hdescent : baseEnd_7643184 < baseStart_7643184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643188 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7643188 : Nat := 118140960795 + 7643188 * 2 ^ 59
def prefixEnd_7643188 : Nat := 4983230072969 + 3 ^ 40 * 7643188 * 2
def baseEnd_7643188 : Nat := 3924629176676747225499625

theorem tailTrace_7643188 : CollatzResearch.WordTrace tailWord_7643188 prefixEnd_7643188 3924629176676747225499625 := by
  unfold tailWord_7643188
  simp only [CollatzResearch.WordTrace]
  refine ⟨139384984117021351715541109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185846645489361802287388145 139384984117021351715541109)
  ·
    refine ⟨13067342260970751723331979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139384984117021351715541109 13067342260970751723331979)
    ·
      refine ⟨19601013391456127584997969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13067342260970751723331979 19601013391456127584997969)
      ·
        refine ⟨14700760043592095688748477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19601013391456127584997969 14700760043592095688748477)
        ·
          refine ⟨5512785016347035883280679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14700760043592095688748477 5512785016347035883280679)
          ·
            refine ⟨8269177524520553824921019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512785016347035883280679 8269177524520553824921019)
            ·
              refine ⟨12403766286780830737381529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8269177524520553824921019 12403766286780830737381529)
              ·
                refine ⟨9302824715085623053036147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12403766286780830737381529 9302824715085623053036147)
                ·
                  refine ⟨13954237072628434579554221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9302824715085623053036147 13954237072628434579554221)
                  ·
                    refine ⟨5232838902235662967332833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13954237072628434579554221 5232838902235662967332833)
                    ·
                      refine ⟨3924629176676747225499625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5232838902235662967332833 3924629176676747225499625)
                      ·
                        rfl

theorem cell23_7643188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7643188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643188 prefixEnd_7643188 := by exact prefixLift 7643188
  have htrace : WordTrace (prefixWord ++ tailWord_7643188) baseStart_7643188 baseEnd_7643188 := by
    simpa [prefixWord, tailWord_7643188, baseEnd_7643188] using wordTrace_append hprefix tailTrace_7643188
  have hstable : (prefixWord ++ tailWord_7643188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643188).length < 2 ^ (prefixWord ++ tailWord_7643188).sum := by decide
  have hdescent : baseEnd_7643188 < baseStart_7643188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643250 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_7643250 : Nat := 118140960795 + 7643250 * 2 ^ 59
def prefixEnd_7643250 : Nat := 4983230072969 + 3 ^ 40 * 7643250 * 2
def baseEnd_7643250 : Nat := 1308220337492441994308113

theorem tailTrace_7643250 : CollatzResearch.WordTrace tailWord_7643250 prefixEnd_7643250 1308220337492441994308113 := by
  unfold tailWord_7643250
  simp only [CollatzResearch.WordTrace]
  refine ⟨69693057389954522004959801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185848153039878725346559469 69693057389954522004959801)
  ·
    refine ⟨52269793042465891503719851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69693057389954522004959801 52269793042465891503719851)
    ·
      refine ⟨78404689563698837255579777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52269793042465891503719851 78404689563698837255579777)
      ·
        refine ⟨58803517172774127941684833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78404689563698837255579777 58803517172774127941684833)
        ·
          refine ⟨44102637879580595956263625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58803517172774127941684833 44102637879580595956263625)
          ·
            refine ⟨33076978409685446967197719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44102637879580595956263625 33076978409685446967197719)
            ·
              refine ⟨49615467614528170450796579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33076978409685446967197719 49615467614528170450796579)
              ·
                refine ⟨74423201421792255676194869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49615467614528170450796579 74423201421792255676194869)
                ·
                  refine ⟨6977175133293023969643269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74423201421792255676194869 6977175133293023969643269)
                  ·
                    refine ⟨1308220337492441994308113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977175133293023969643269 1308220337492441994308113)
                    ·
                      rfl

theorem cell23_7643250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_7643250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643250 prefixEnd_7643250 := by exact prefixLift 7643250
  have htrace : WordTrace (prefixWord ++ tailWord_7643250) baseStart_7643250 baseEnd_7643250 := by
    simpa [prefixWord, tailWord_7643250, baseEnd_7643250] using wordTrace_append hprefix tailTrace_7643250
  have hstable : (prefixWord ++ tailWord_7643250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643250).length < 2 ^ (prefixWord ++ tailWord_7643250).sum := by decide
  have hdescent : baseEnd_7643250 < baseStart_7643250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643257 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 4]
def baseStart_7643257 : Nat := 118140960795 + 7643257 * 2 ^ 59
def prefixEnd_7643257 : Nat := 4983230072969 + 3 ^ 40 * 7643257 * 2
def baseEnd_7643257 : Nat := 3924664606841907455536807

theorem tailTrace_7643257 : CollatzResearch.WordTrace tailWord_7643257 prefixEnd_7643257 3924664606841907455536807 := by
  unfold tailWord_7643257
  simp only [CollatzResearch.WordTrace]
  refine ⟨278772484870792728215344025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185848323247195152143562683 278772484870792728215344025)
  ·
    refine ⟨209079363653094546161508019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278772484870792728215344025 209079363653094546161508019)
    ·
      refine ⟨313619045479641819242262029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209079363653094546161508019 313619045479641819242262029)
      ·
        refine ⟨117607142054865682215848261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313619045479641819242262029 117607142054865682215848261)
        ·
          refine ⟨22051339135287315415471549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117607142054865682215848261 22051339135287315415471549)
          ·
            refine ⟨8269252175732743280801831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22051339135287315415471549 8269252175732743280801831)
            ·
              refine ⟨12403878263599114921202747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8269252175732743280801831 12403878263599114921202747)
              ·
                refine ⟨18605817395398672381804121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12403878263599114921202747 18605817395398672381804121)
                ·
                  refine ⟨13954363046549004286353091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18605817395398672381804121 13954363046549004286353091)
                  ·
                    refine ⟨20931544569823506429529637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13954363046549004286353091 20931544569823506429529637)
                    ·
                      refine ⟨3924664606841907455536807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20931544569823506429529637 3924664606841907455536807)
                      ·
                        rfl

theorem cell23_7643257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_7643257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643257 prefixEnd_7643257 := by exact prefixLift 7643257
  have htrace : WordTrace (prefixWord ++ tailWord_7643257) baseStart_7643257 baseEnd_7643257 := by
    simpa [prefixWord, tailWord_7643257, baseEnd_7643257] using wordTrace_append hprefix tailTrace_7643257
  have hstable : (prefixWord ++ tailWord_7643257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643257).length < 2 ^ (prefixWord ++ tailWord_7643257).sum := by decide
  have hdescent : baseEnd_7643257 < baseStart_7643257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643260 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_7643260 : Nat := 118140960795 + 7643260 * 2 ^ 59
def prefixEnd_7643260 : Nat := 4983230072969 + 3 ^ 40 * 7643260 * 2
def baseEnd_7643260 : Nat := 3924666147283870943799293

theorem tailTrace_7643260 : CollatzResearch.WordTrace tailWord_7643260 prefixEnd_7643260 3924666147283870943799293 := by
  unfold tailWord_7643260
  simp only [CollatzResearch.WordTrace]
  refine ⟨139386297144890929863851617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185848396193187906485135489 139386297144890929863851617)
  ·
    refine ⟨104539722858668197397888713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139386297144890929863851617 104539722858668197397888713)
    ·
      refine ⟨78404792144001148048416535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104539722858668197397888713 78404792144001148048416535)
      ·
        refine ⟨117607188216001722072624803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78404792144001148048416535 117607188216001722072624803)
        ·
          refine ⟨176410782324002583108937205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117607188216001722072624803 176410782324002583108937205)
          ·
            refine ⟨16538510842875242166462863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176410782324002583108937205 16538510842875242166462863)
            ·
              refine ⟨24807766264312863249694295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16538510842875242166462863 24807766264312863249694295)
              ·
                refine ⟨37211649396469294874541443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24807766264312863249694295 37211649396469294874541443)
                ·
                  refine ⟨55817474094703942311812165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37211649396469294874541443 55817474094703942311812165)
                  ·
                    refine ⟨10465776392756989183464781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55817474094703942311812165 10465776392756989183464781)
                    ·
                      refine ⟨3924666147283870943799293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10465776392756989183464781 3924666147283870943799293)
                      ·
                        rfl

theorem cell23_7643260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_7643260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643260 prefixEnd_7643260 := by exact prefixLift 7643260
  have htrace : WordTrace (prefixWord ++ tailWord_7643260) baseStart_7643260 baseEnd_7643260 := by
    simpa [prefixWord, tailWord_7643260, baseEnd_7643260] using wordTrace_append hprefix tailTrace_7643260
  have hstable : (prefixWord ++ tailWord_7643260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643260).length < 2 ^ (prefixWord ++ tailWord_7643260).sum := by decide
  have hdescent : baseEnd_7643260 < baseStart_7643260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643267 : List Nat := [1, 1, 1, 3, 3, 3, 1, 5, 1, 4]
def baseStart_7643267 : Nat := 118140960795 + 7643267 * 2 ^ 59
def prefixEnd_7643267 : Nat := 4983230072969 + 3 ^ 40 * 7643267 * 2
def baseEnd_7643267 : Nat := 1308223247216150805470587

theorem tailTrace_7643267 : CollatzResearch.WordTrace tailWord_7643267 prefixEnd_7643267 1308223247216150805470587 := by
  unfold tailWord_7643267
  simp only [CollatzResearch.WordTrace]
  refine ⟨278772849600756499923208055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185848566400504333282138703 278772849600756499923208055)
  ·
    refine ⟨418159274401134749884812083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278772849600756499923208055 418159274401134749884812083)
    ·
      refine ⟨627238911601702124827218125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418159274401134749884812083 627238911601702124827218125)
      ·
        refine ⟨235214591850638296810206797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627238911601702124827218125 235214591850638296810206797)
        ·
          refine ⟨88205471943989361303827549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235214591850638296810206797 88205471943989361303827549)
          ·
            refine ⟨33077051978996010488935331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88205471943989361303827549 33077051978996010488935331)
            ·
              refine ⟨49615577968494015733402997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33077051978996010488935331 49615577968494015733402997)
              ·
                refine ⟨4651460434546313975006531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49615577968494015733402997 4651460434546313975006531)
                ·
                  refine ⟨6977190651819470962509797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651460434546313975006531 6977190651819470962509797)
                  ·
                    refine ⟨1308223247216150805470587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977190651819470962509797 1308223247216150805470587)
                    ·
                      rfl

theorem cell23_7643267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 4].length) (baseStart_7643267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643267 prefixEnd_7643267 := by exact prefixLift 7643267
  have htrace : WordTrace (prefixWord ++ tailWord_7643267) baseStart_7643267 baseEnd_7643267 := by
    simpa [prefixWord, tailWord_7643267, baseEnd_7643267] using wordTrace_append hprefix tailTrace_7643267
  have hstable : (prefixWord ++ tailWord_7643267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643267).length < 2 ^ (prefixWord ++ tailWord_7643267).sum := by decide
  have hdescent : baseEnd_7643267 < baseStart_7643267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643297 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 6]
def baseStart_7643297 : Nat := 118140960795 + 7643297 * 2 ^ 59
def prefixEnd_7643297 : Nat := 4983230072969 + 3 ^ 40 * 7643297 * 2
def baseEnd_7643297 : Nat := 436076127340898588781847

theorem tailTrace_7643297 : CollatzResearch.WordTrace tailWord_7643297 prefixEnd_7643297 436076127340898588781847 := by
  unfold tailWord_7643297
  simp only [CollatzResearch.WordTrace]
  refine ⟨278773943790647815046800145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185849295860431876697866763 278773943790647815046800145)
  ·
    refine ⟨209080457842985861285100109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278773943790647815046800145 209080457842985861285100109)
    ·
      refine ⟨78405171691119697981912541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209080457842985861285100109 78405171691119697981912541)
      ·
        refine ⟨29401939384169886743217203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78405171691119697981912541 29401939384169886743217203)
        ·
          refine ⟨44102909076254830114825805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29401939384169886743217203 44102909076254830114825805)
          ·
            refine ⟨16538590903595561293059677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44102909076254830114825805 16538590903595561293059677)
            ·
              refine ⟨6201971588848335484897379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16538590903595561293059677 6201971588848335484897379)
              ·
                refine ⟨9302957383272503227346069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201971588848335484897379 9302957383272503227346069)
                ·
                  refine ⟨436076127340898588781847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9302957383272503227346069 436076127340898588781847)
                  ·
                    rfl

theorem cell23_7643297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 6].length) (baseStart_7643297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643297 prefixEnd_7643297 := by exact prefixLift 7643297
  have htrace : WordTrace (prefixWord ++ tailWord_7643297) baseStart_7643297 baseEnd_7643297 := by
    simpa [prefixWord, tailWord_7643297, baseEnd_7643297] using wordTrace_append hprefix tailTrace_7643297
  have hstable : (prefixWord ++ tailWord_7643297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643297).length < 2 ^ (prefixWord ++ tailWord_7643297).sum := by decide
  have hdescent : baseEnd_7643297 < baseStart_7643297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643323 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 3, 6]
def baseStart_7643323 : Nat := 118140960795 + 7643323 * 2 ^ 59
def prefixEnd_7643323 : Nat := 4983230072969 + 3 ^ 40 * 7643323 * 2
def baseEnd_7643323 : Nat := 1308232832188368065770501

theorem tailTrace_7643323 : CollatzResearch.WordTrace tailWord_7643323 prefixEnd_7643323 1308232832188368065770501 := by
  unfold tailWord_7643323
  simp only [CollatzResearch.WordTrace]
  refine ⟨278774892088553621487246623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185849928059035747658164415 278774892088553621487246623)
  ·
    refine ⟨418162338132830432230869935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278774892088553621487246623 418162338132830432230869935)
    ·
      refine ⟨627243507199245648346304903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418162338132830432230869935 627243507199245648346304903)
      ·
        refine ⟨940865260798868472519457355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627243507199245648346304903 940865260798868472519457355)
        ·
          refine ⟨1411297891198302708779186033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940865260798868472519457355 1411297891198302708779186033)
          ·
            refine ⟨1058473418398727031584389525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411297891198302708779186033 1058473418398727031584389525)
            ·
              refine ⟨49615941487440329605518259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1058473418398727031584389525 49615941487440329605518259)
              ·
                refine ⟨74423912231160494408277389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49615941487440329605518259 74423912231160494408277389)
                ·
                  refine ⟨27908967086685185403104021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74423912231160494408277389 27908967086685185403104021)
                  ·
                    refine ⟨1308232832188368065770501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27908967086685185403104021 1308232832188368065770501)
                    ·
                      rfl

theorem cell23_7643323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 6].length) (baseStart_7643323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643323 prefixEnd_7643323 := by exact prefixLift 7643323
  have htrace : WordTrace (prefixWord ++ tailWord_7643323) baseStart_7643323 baseEnd_7643323 := by
    simpa [prefixWord, tailWord_7643323, baseEnd_7643323] using wordTrace_append hprefix tailTrace_7643323
  have hstable : (prefixWord ++ tailWord_7643323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643323).length < 2 ^ (prefixWord ++ tailWord_7643323).sum := by decide
  have hdescent : baseEnd_7643323 < baseStart_7643323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643343 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_7643343 : Nat := 118140960795 + 7643343 * 2 ^ 59
def prefixEnd_7643343 : Nat := 4983230072969 + 3 ^ 40 * 7643343 * 2
def baseEnd_7643343 : Nat := 3924708766178194119061411

theorem tailTrace_7643343 : CollatzResearch.WordTrace tailWord_7643343 prefixEnd_7643343 3924708766178194119061411 := by
  unfold tailWord_7643343
  simp only [CollatzResearch.WordTrace]
  refine ⟨278775621548481164902974683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185850414365654109935316455 278775621548481164902974683)
  ·
    refine ⟨418163432322721747354462025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278775621548481164902974683 418163432322721747354462025)
    ·
      refine ⟨313622574242041310515846519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418163432322721747354462025 313622574242041310515846519)
      ·
        refine ⟨470433861363061965773769779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313622574242041310515846519 470433861363061965773769779)
        ·
          refine ⟨705650792044592948660654669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470433861363061965773769779 705650792044592948660654669)
          ·
            refine ⟨264619047016722355747745501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705650792044592948660654669 264619047016722355747745501)
            ·
              refine ⟨99232142631270883405404563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264619047016722355747745501 99232142631270883405404563)
              ·
                refine ⟨148848213946906325108106845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99232142631270883405404563 148848213946906325108106845)
                ·
                  refine ⟨55818080230089871915540067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148848213946906325108106845 55818080230089871915540067)
                  ·
                    refine ⟨83727120345134807873310101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55818080230089871915540067 83727120345134807873310101)
                    ·
                      refine ⟨3924708766178194119061411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83727120345134807873310101 3924708766178194119061411)
                      ·
                        rfl

theorem cell23_7643343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_7643343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643343 prefixEnd_7643343 := by exact prefixLift 7643343
  have htrace : WordTrace (prefixWord ++ tailWord_7643343) baseStart_7643343 baseEnd_7643343 := by
    simpa [prefixWord, tailWord_7643343, baseEnd_7643343] using wordTrace_append hprefix tailTrace_7643343
  have hstable : (prefixWord ++ tailWord_7643343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643343).length < 2 ^ (prefixWord ++ tailWord_7643343).sum := by decide
  have hdescent : baseEnd_7643343 < baseStart_7643343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643353 : List Nat := [1, 2, 1, 2, 3, 1, 3, 10]
def baseStart_7643353 : Nat := 118140960795 + 7643353 * 2 ^ 59
def prefixEnd_7643353 : Nat := 4983230072969 + 3 ^ 40 * 7643353 * 2
def baseEnd_7643353 : Nat := 145359774110545891849495

theorem tailTrace_7643353 : CollatzResearch.WordTrace tailWord_7643353 prefixEnd_7643353 145359774110545891849495 := by
  unfold tailWord_7643353
  simp only [CollatzResearch.WordTrace]
  refine ⟨278775986278444936610838713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185850657518963291073892475 278775986278444936610838713)
  ·
    refine ⟨209081989708833702458129035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278775986278444936610838713 209081989708833702458129035)
    ·
      refine ⟨313622984563250553687193553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209081989708833702458129035 313622984563250553687193553)
      ·
        refine ⟨235217238422437915265395165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313622984563250553687193553 235217238422437915265395165)
        ·
          refine ⟨88206464408414218224523187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235217238422437915265395165 88206464408414218224523187)
          ·
            refine ⟨132309696612621327336784781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88206464408414218224523187 132309696612621327336784781)
            ·
              refine ⟨49616136229732997751294293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132309696612621327336784781 49616136229732997751294293)
              ·
                refine ⟨145359774110545891849495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49616136229732997751294293 145359774110545891849495)
                ·
                  rfl

theorem cell23_7643353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 10].length) (baseStart_7643353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643353 prefixEnd_7643353 := by exact prefixLift 7643353
  have htrace : WordTrace (prefixWord ++ tailWord_7643353) baseStart_7643353 baseEnd_7643353 := by
    simpa [prefixWord, tailWord_7643353, baseEnd_7643353] using wordTrace_append hprefix tailTrace_7643353
  have hstable : (prefixWord ++ tailWord_7643353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643353).length < 2 ^ (prefixWord ++ tailWord_7643353).sum := by decide
  have hdescent : baseEnd_7643353 < baseStart_7643353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643360 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_7643360 : Nat := 118140960795 + 7643360 * 2 ^ 59
def prefixEnd_7643360 : Nat := 4983230072969 + 3 ^ 40 * 7643360 * 2
def baseEnd_7643360 : Nat := 3924717495349320552548833

theorem tailTrace_7643360 : CollatzResearch.WordTrace tailWord_7643360 prefixEnd_7643360 3924717495349320552548833 := by
  unfold tailWord_7643360
  simp only [CollatzResearch.WordTrace]
  refine ⟨139388120794709788403171767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185850827726279717870895689 139388120794709788403171767)
  ·
    refine ⟨209082181192064682604757651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139388120794709788403171767 209082181192064682604757651)
    ·
      refine ⟨313623271788097023907136477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209082181192064682604757651 313623271788097023907136477)
      ·
        refine ⟨117608726920536383965176179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313623271788097023907136477 117608726920536383965176179)
        ·
          refine ⟨176413090380804575947764269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117608726920536383965176179 176413090380804575947764269)
          ·
            refine ⟨66154908892801715980411601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176413090380804575947764269 66154908892801715980411601)
            ·
              refine ⟨49616181669601286985308701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66154908892801715980411601 49616181669601286985308701)
              ·
                refine ⟨18606068126100482619490763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49616181669601286985308701 18606068126100482619490763)
                ·
                  refine ⟨27909102189150723929236145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18606068126100482619490763 27909102189150723929236145)
                  ·
                    refine ⟨20931826641863042946927109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27909102189150723929236145 20931826641863042946927109)
                    ·
                      refine ⟨3924717495349320552548833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20931826641863042946927109 3924717495349320552548833)
                      ·
                        rfl

theorem cell23_7643360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_7643360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643360 prefixEnd_7643360 := by exact prefixLift 7643360
  have htrace : WordTrace (prefixWord ++ tailWord_7643360) baseStart_7643360 baseEnd_7643360 := by
    simpa [prefixWord, tailWord_7643360, baseEnd_7643360] using wordTrace_append hprefix tailTrace_7643360
  have hstable : (prefixWord ++ tailWord_7643360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643360).length < 2 ^ (prefixWord ++ tailWord_7643360).sum := by decide
  have hdescent : baseEnd_7643360 < baseStart_7643360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643383 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 9]
def baseStart_7643383 : Nat := 118140960795 + 7643383 * 2 ^ 59
def prefixEnd_7643383 : Nat := 4983230072969 + 3 ^ 40 * 7643383 * 2
def baseEnd_7643383 : Nat := 1308243101801457987520409

theorem tailTrace_7643383 : CollatzResearch.WordTrace tailWord_7643383 prefixEnd_7643383 1308243101801457987520409 := by
  unfold tailWord_7643383
  simp only [CollatzResearch.WordTrace]
  refine ⟨278777080468336251734430803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185851386978890834489620535 278777080468336251734430803)
  ·
    refine ⟨418165620702504377601646205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278777080468336251734430803 418165620702504377601646205)
    ·
      refine ⟨156812107763439141600617327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418165620702504377601646205 156812107763439141600617327)
      ·
        refine ⟨235218161645158712400925991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156812107763439141600617327 235218161645158712400925991)
        ·
          refine ⟨352827242467738068601388987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235218161645158712400925991 352827242467738068601388987)
          ·
            refine ⟨529240863701607102902083481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352827242467738068601388987 529240863701607102902083481)
            ·
              refine ⟨396930647776205327176562611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529240863701607102902083481 396930647776205327176562611)
              ·
                refine ⟨595395971664307990764843917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396930647776205327176562611 595395971664307990764843917)
                ·
                  refine ⟨223273489374115496536816469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 595395971664307990764843917 223273489374115496536816469)
                  ·
                    refine ⟨1308243101801457987520409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 223273489374115496536816469 1308243101801457987520409)
                    ·
                      rfl

theorem cell23_7643383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_7643383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643383 prefixEnd_7643383 := by exact prefixLift 7643383
  have htrace : WordTrace (prefixWord ++ tailWord_7643383) baseStart_7643383 baseEnd_7643383 := by
    simpa [prefixWord, tailWord_7643383, baseEnd_7643383] using wordTrace_append hprefix tailTrace_7643383
  have hstable : (prefixWord ++ tailWord_7643383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643383).length < 2 ^ (prefixWord ++ tailWord_7643383).sum := by decide
  have hdescent : baseEnd_7643383 < baseStart_7643383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643400 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 2, 7]
def baseStart_7643400 : Nat := 118140960795 + 7643400 * 2 ^ 59
def prefixEnd_7643400 : Nat := 4983230072969 + 3 ^ 40 * 7643400 * 2
def baseEnd_7643400 : Nat := 1308246011525166798682883

theorem tailTrace_7643400 : CollatzResearch.WordTrace tailWord_7643400 prefixEnd_7643400 1308246011525166798682883 := by
  unfold tailWord_7643400
  simp only [CollatzResearch.WordTrace]
  refine ⟨139388850254637331818899827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185851800339516442425199769 139388850254637331818899827)
  ·
    refine ⟨209083275381955997728349741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139388850254637331818899827 209083275381955997728349741)
    ·
      refine ⟨78406228268233499148131153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209083275381955997728349741 78406228268233499148131153)
      ·
        refine ⟨58804671201175124361098365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78406228268233499148131153 58804671201175124361098365)
        ·
          refine ⟨22051751700440671635411887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58804671201175124361098365 22051751700440671635411887)
          ·
            refine ⟨33077627550661007453117831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22051751700440671635411887 33077627550661007453117831)
            ·
              refine ⟨49616441325991511179676747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33077627550661007453117831 49616441325991511179676747)
              ·
                refine ⟨74424661988987266769515121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49616441325991511179676747 74424661988987266769515121)
                ·
                  refine ⟨55818496491740450077136341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74424661988987266769515121 55818496491740450077136341)
                  ·
                    refine ⟨1308246011525166798682883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55818496491740450077136341 1308246011525166798682883)
                    ·
                      rfl

theorem cell23_7643400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_7643400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643400 prefixEnd_7643400 := by exact prefixLift 7643400
  have htrace : WordTrace (prefixWord ++ tailWord_7643400) baseStart_7643400 baseEnd_7643400 := by
    simpa [prefixWord, tailWord_7643400, baseEnd_7643400] using wordTrace_append hprefix tailTrace_7643400
  have hstable : (prefixWord ++ tailWord_7643400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643400).length < 2 ^ (prefixWord ++ tailWord_7643400).sum := by decide
  have hdescent : baseEnd_7643400 < baseStart_7643400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643420 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_7643420 : Nat := 118140960795 + 7643420 * 2 ^ 59
def prefixEnd_7643420 : Nat := 4983230072969 + 3 ^ 40 * 7643420 * 2
def baseEnd_7643420 : Nat := 3924748304188590317798557

theorem tailTrace_7643420 : CollatzResearch.WordTrace tailWord_7643420 prefixEnd_7643420 3924748304188590317798557 := by
  unfold tailWord_7643420
  simp only [CollatzResearch.WordTrace]
  refine ⟨139389214984601103526763857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185852286646134804702351809 139389214984601103526763857)
  ·
    refine ⟨104541911238450827645072893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139389214984601103526763857 104541911238450827645072893)
    ·
      refine ⟨39203216714419060366902335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104541911238450827645072893 39203216714419060366902335)
      ·
        refine ⟨58804825071628590550353503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39203216714419060366902335 58804825071628590550353503)
        ·
          refine ⟨88207237607442885825530255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58804825071628590550353503 88207237607442885825530255)
          ·
            refine ⟨132310856411164328738295383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88207237607442885825530255 132310856411164328738295383)
            ·
              refine ⟨198466284616746493107443075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132310856411164328738295383 198466284616746493107443075)
              ·
                refine ⟨297699426925119739661164613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198466284616746493107443075 297699426925119739661164613)
                ·
                  refine ⟨55818642548459951186468365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297699426925119739661164613 55818642548459951186468365)
                  ·
                    refine ⟨20931990955672481694925637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55818642548459951186468365 20931990955672481694925637)
                    ·
                      refine ⟨3924748304188590317798557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20931990955672481694925637 3924748304188590317798557)
                      ·
                        rfl

theorem cell23_7643420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_7643420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643420 prefixEnd_7643420 := by exact prefixLift 7643420
  have htrace : WordTrace (prefixWord ++ tailWord_7643420) baseStart_7643420 baseEnd_7643420 := by
    simpa [prefixWord, tailWord_7643420, baseEnd_7643420] using wordTrace_append hprefix tailTrace_7643420
  have hstable : (prefixWord ++ tailWord_7643420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643420).length < 2 ^ (prefixWord ++ tailWord_7643420).sum := by decide
  have hdescent : baseEnd_7643420 < baseStart_7643420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643424 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 3, 3, 2]
def baseStart_7643424 : Nat := 118140960795 + 7643424 * 2 ^ 59
def prefixEnd_7643424 : Nat := 4983230072969 + 3 ^ 40 * 7643424 * 2
def baseEnd_7643424 : Nat := 3924750358111208302148539

theorem tailTrace_7643424 : CollatzResearch.WordTrace tailWord_7643424 prefixEnd_7643424 3924750358111208302148539 := by
  unfold tailWord_7643424
  simp only [CollatzResearch.WordTrace]
  refine ⟨139389287930593857868336663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185852383907458477157782217 139389287930593857868336663)
  ·
    refine ⟨209083931895890786802504995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139389287930593857868336663 209083931895890786802504995)
    ·
      refine ⟨313625897843836180203757493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209083931895890786802504995 313625897843836180203757493)
      ·
        refine ⟨29402427922859641894102265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313625897843836180203757493 29402427922859641894102265)
        ·
          refine ⟨22051820942144731420576699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29402427922859641894102265 22051820942144731420576699)
          ·
            refine ⟨33077731413217097130865049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22051820942144731420576699 33077731413217097130865049)
            ·
              refine ⟨24808298559912822848148787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33077731413217097130865049 24808298559912822848148787)
              ·
                refine ⟨37212447839869234272223181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24808298559912822848148787 37212447839869234272223181)
                ·
                  refine ⟨13954667939950962852083693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37212447839869234272223181 13954667939950962852083693)
                  ·
                    refine ⟨5233000477481611069531385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13954667939950962852083693 5233000477481611069531385)
                    ·
                      refine ⟨3924750358111208302148539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233000477481611069531385 3924750358111208302148539)
                      ·
                        rfl

theorem cell23_7643424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_7643424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643424 prefixEnd_7643424 := by exact prefixLift 7643424
  have htrace : WordTrace (prefixWord ++ tailWord_7643424) baseStart_7643424 baseEnd_7643424 := by
    simpa [prefixWord, tailWord_7643424, baseEnd_7643424] using wordTrace_append hprefix tailTrace_7643424
  have hstable : (prefixWord ++ tailWord_7643424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643424).length < 2 ^ (prefixWord ++ tailWord_7643424).sum := by decide
  have hdescent : baseEnd_7643424 < baseStart_7643424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643440 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3]
def baseStart_7643440 : Nat := 118140960795 + 7643440 * 2 ^ 59
def prefixEnd_7643440 : Nat := 4983230072969 + 3 ^ 40 * 7643440 * 2
def baseEnd_7643440 : Nat := 3924758573801680239548465

theorem tailTrace_7643440 : CollatzResearch.WordTrace tailWord_7643440 prefixEnd_7643440 3924758573801680239548465 := by
  unfold tailWord_7643440
  simp only [CollatzResearch.WordTrace]
  refine ⟨139389579714564875234627887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185852772952753166979503849 139389579714564875234627887)
  ·
    refine ⟨209084369571847312851941831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139389579714564875234627887 209084369571847312851941831)
    ·
      refine ⟨313626554357770969277912747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209084369571847312851941831 313626554357770969277912747)
      ·
        refine ⟨470439831536656453916869121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313626554357770969277912747 470439831536656453916869121)
        ·
          refine ⟨352829873652492340437651841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470439831536656453916869121 352829873652492340437651841)
          ·
            refine ⟨264622405239369255328238881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352829873652492340437651841 264622405239369255328238881)
            ·
              refine ⟨198466803929526941496179161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264622405239369255328238881 198466803929526941496179161)
              ·
                refine ⟨148850102947145206122134371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198466803929526941496179161 148850102947145206122134371)
                ·
                  refine ⟨223275154420717809183201557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148850102947145206122134371 223275154420717809183201557)
                  ·
                    refine ⟨10466022863471147305462573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 223275154420717809183201557 10466022863471147305462573)
                    ·
                      refine ⟨3924758573801680239548465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10466022863471147305462573 3924758573801680239548465)
                      ·
                        rfl

theorem cell23_7643440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_7643440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643440 prefixEnd_7643440 := by exact prefixLift 7643440
  have htrace : WordTrace (prefixWord ++ tailWord_7643440) baseStart_7643440 baseEnd_7643440 := by
    simpa [prefixWord, tailWord_7643440, baseEnd_7643440] using wordTrace_append hprefix tailTrace_7643440
  have hstable : (prefixWord ++ tailWord_7643440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643440).length < 2 ^ (prefixWord ++ tailWord_7643440).sum := by decide
  have hdescent : baseEnd_7643440 < baseStart_7643440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643441 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 1, 3, 2]
def baseStart_7643441 : Nat := 118140960795 + 7643441 * 2 ^ 59
def prefixEnd_7643441 : Nat := 4983230072969 + 3 ^ 40 * 7643441 * 2
def baseEnd_7643441 : Nat := 3924759087282334735635961

theorem tailTrace_7643441 : CollatzResearch.WordTrace tailWord_7643441 prefixEnd_7643441 3924759087282334735635961 := by
  unfold tailWord_7643441
  simp only [CollatzResearch.WordTrace]
  refine ⟨278779195902126127640042177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185852797268084085093361451 278779195902126127640042177)
  ·
    refine ⟨209084396926594595730031633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278779195902126127640042177 209084396926594595730031633)
    ·
      refine ⟨156813297694945946797523725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209084396926594595730031633 156813297694945946797523725)
      ·
        refine ⟨58804986635604730049071397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156813297694945946797523725 58804986635604730049071397)
        ·
          refine ⟨11025934994175886884200887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58804986635604730049071397 11025934994175886884200887)
          ·
            refine ⟨16538902491263830326301331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11025934994175886884200887 16538902491263830326301331)
            ·
              refine ⟨24808353736895745489451997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16538902491263830326301331 24808353736895745489451997)
              ·
                refine ⟨9303132651335904558544499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24808353736895745489451997 9303132651335904558544499)
                ·
                  refine ⟨13954698977003856837816749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9303132651335904558544499 13954698977003856837816749)
                  ·
                    refine ⟨5233012116376446314181281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13954698977003856837816749 5233012116376446314181281)
                    ·
                      refine ⟨3924759087282334735635961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233012116376446314181281 3924759087282334735635961)
                      ·
                        rfl

theorem cell23_7643441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_7643441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643441 prefixEnd_7643441 := by exact prefixLift 7643441
  have htrace : WordTrace (prefixWord ++ tailWord_7643441) baseStart_7643441 baseEnd_7643441 := by
    simpa [prefixWord, tailWord_7643441, baseEnd_7643441] using wordTrace_append hprefix tailTrace_7643441
  have hstable : (prefixWord ++ tailWord_7643441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643441).length < 2 ^ (prefixWord ++ tailWord_7643441).sum := by decide
  have hdescent : baseEnd_7643441 < baseStart_7643441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643517 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_7643517 : Nat := 118140960795 + 7643517 * 2 ^ 59
def prefixEnd_7643517 : Nat := 4983230072969 + 3 ^ 40 * 7643517 * 2
def baseEnd_7643517 : Nat := 3924798111812076438285611

theorem tailTrace_7643517 : CollatzResearch.WordTrace tailWord_7643517 prefixEnd_7643517 3924798111812076438285611 := by
  unfold tailWord_7643517
  simp only [CollatzResearch.WordTrace]
  refine ⟨278781967849850792619808805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185854645233233861746539203 278781967849850792619808805)
  ·
    refine ⟨52271618971847023616214151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278781967849850792619808805 52271618971847023616214151)
    ·
      refine ⟨78407428457770535424321227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52271618971847023616214151 78407428457770535424321227)
      ·
        refine ⟨117611142686655803136481841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78407428457770535424321227 117611142686655803136481841)
        ·
          refine ⟨88208357014991852352361381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117611142686655803136481841 88208357014991852352361381)
          ·
            refine ⟨16539066940310972316067759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88208357014991852352361381 16539066940310972316067759)
            ·
              refine ⟨24808600410466458474101639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16539066940310972316067759 24808600410466458474101639)
              ·
                refine ⟨37212900615699687711152459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24808600410466458474101639 37212900615699687711152459)
                ·
                  refine ⟨55819350923549531566728689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37212900615699687711152459 55819350923549531566728689)
                  ·
                    refine ⟨41864513192662148675046517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55819350923549531566728689 41864513192662148675046517)
                    ·
                      refine ⟨3924798111812076438285611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41864513192662148675046517 3924798111812076438285611)
                      ·
                        rfl

theorem cell23_7643517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_7643517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643517 prefixEnd_7643517 := by exact prefixLift 7643517
  have htrace : WordTrace (prefixWord ++ tailWord_7643517) baseStart_7643517 baseEnd_7643517 := by
    simpa [prefixWord, tailWord_7643517, baseEnd_7643517] using wordTrace_append hprefix tailTrace_7643517
  have hstable : (prefixWord ++ tailWord_7643517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643517).length < 2 ^ (prefixWord ++ tailWord_7643517).sum := by decide
  have hdescent : baseEnd_7643517 < baseStart_7643517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643527 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_7643527 : Nat := 118140960795 + 7643527 * 2 ^ 59
def prefixEnd_7643527 : Nat := 4983230072969 + 3 ^ 40 * 7643527 * 2
def baseEnd_7643527 : Nat := 3924803246618621399160565

theorem tailTrace_7643527 : CollatzResearch.WordTrace tailWord_7643527 prefixEnd_7643527 3924803246618621399160565 := by
  unfold tailWord_7643527
  simp only [CollatzResearch.WordTrace]
  refine ⟨278782332579814564327672835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185854888386543042885115223 278782332579814564327672835)
  ·
    refine ⟨418173498869721846491509253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278782332579814564327672835 418173498869721846491509253)
    ·
      refine ⟨78407531038072846217157985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418173498869721846491509253 78407531038072846217157985)
      ·
        refine ⟨58805648278554634662868489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78407531038072846217157985 58805648278554634662868489)
        ·
          refine ⟨44104236208915975997151367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58805648278554634662868489 44104236208915975997151367)
          ·
            refine ⟨66156354313373963995727051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44104236208915975997151367 66156354313373963995727051)
            ·
              refine ⟨99234531470060945993590577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66156354313373963995727051 99234531470060945993590577)
              ·
                refine ⟨74425898602545709495192933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99234531470060945993590577 74425898602545709495192933)
                ·
                  refine ⟨13954855987977320530348675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74425898602545709495192933 13954855987977320530348675)
                  ·
                    refine ⟨20932283981965980795523013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13954855987977320530348675 20932283981965980795523013)
                    ·
                      refine ⟨3924803246618621399160565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20932283981965980795523013 3924803246618621399160565)
                      ·
                        rfl

theorem cell23_7643527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_7643527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643527 prefixEnd_7643527 := by exact prefixLift 7643527
  have htrace : WordTrace (prefixWord ++ tailWord_7643527) baseStart_7643527 baseEnd_7643527 := by
    simpa [prefixWord, tailWord_7643527, baseEnd_7643527] using wordTrace_append hprefix tailTrace_7643527
  have hstable : (prefixWord ++ tailWord_7643527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643527).length < 2 ^ (prefixWord ++ tailWord_7643527).sum := by decide
  have hdescent : baseEnd_7643527 < baseStart_7643527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643544 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7643544 : Nat := 118140960795 + 7643544 * 2 ^ 59
def prefixEnd_7643544 : Nat := 4983230072969 + 3 ^ 40 * 7643544 * 2
def baseEnd_7643544 : Nat := 3924811975789747832647987

theorem tailTrace_7643544 : CollatzResearch.WordTrace tailWord_7643544 prefixEnd_7643544 3924811975789747832647987 := by
  unfold tailWord_7643544
  simp only [CollatzResearch.WordTrace]
  refine ⟨139391476310376488115520843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185855301747168650820694457 139391476310376488115520843)
  ·
    refine ⟨209087214465564732173281265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139391476310376488115520843 209087214465564732173281265)
    ·
      refine ⟨156815410849173549129960949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209087214465564732173281265 156815410849173549129960949)
      ·
        refine ⟨14701444767110020230933839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156815410849173549129960949 14701444767110020230933839)
        ·
          refine ⟨22052167150665030346400759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14701444767110020230933839 22052167150665030346400759)
          ·
            refine ⟨33078250725997545519601139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22052167150665030346400759 33078250725997545519601139)
            ·
              refine ⟨49617376088996318279401709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33078250725997545519601139 49617376088996318279401709)
              ·
                refine ⟨18606516033373619354775641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49617376088996318279401709 18606516033373619354775641)
                ·
                  refine ⟨13954887025030214516081731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18606516033373619354775641 13954887025030214516081731)
                  ·
                    refine ⟨20932330537545321774122597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13954887025030214516081731 20932330537545321774122597)
                    ·
                      refine ⟨3924811975789747832647987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20932330537545321774122597 3924811975789747832647987)
                      ·
                        rfl

theorem cell23_7643544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7643544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643544 prefixEnd_7643544 := by exact prefixLift 7643544
  have htrace : WordTrace (prefixWord ++ tailWord_7643544) baseStart_7643544 baseEnd_7643544 := by
    simpa [prefixWord, tailWord_7643544, baseEnd_7643544] using wordTrace_append hprefix tailTrace_7643544
  have hstable : (prefixWord ++ tailWord_7643544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643544).length < 2 ^ (prefixWord ++ tailWord_7643544).sum := by decide
  have hdescent : baseEnd_7643544 < baseStart_7643544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643562 : List Nat := [3, 1, 6, 1, 1, 2, 2, 2, 5]
def baseStart_7643562 : Nat := 118140960795 + 7643562 * 2 ^ 59
def prefixEnd_7643562 : Nat := 4983230072969 + 3 ^ 40 * 7643562 * 2
def baseEnd_7643562 : Nat := 436091246493503195802545

theorem tailTrace_7643562 : CollatzResearch.WordTrace tailWord_7643562 prefixEnd_7643562 436091246493503195802545 := by
  unfold tailWord_7643562
  simp only [CollatzResearch.WordTrace]
  refine ⟨69695902283671941326299235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185855739423125176870131293 69695902283671941326299235)
  ·
    refine ⟨104543853425507911989448853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69695902283671941326299235 104543853425507911989448853)
    ·
      refine ⟨4900493129320683374505415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104543853425507911989448853 4900493129320683374505415)
      ·
        refine ⟨7350739693981025061758123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900493129320683374505415 7350739693981025061758123)
        ·
          refine ⟨11026109540971537592637185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7350739693981025061758123 11026109540971537592637185)
          ·
            refine ⟨8269582155728653194477889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11026109540971537592637185 8269582155728653194477889)
            ·
              refine ⟨6202186616796489895858417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8269582155728653194477889 6202186616796489895858417)
              ·
                refine ⟨4651639962597367421893813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6202186616796489895858417 4651639962597367421893813)
                ·
                  refine ⟨436091246493503195802545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4651639962597367421893813 436091246493503195802545)
                  ·
                    rfl

theorem cell23_7643562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_7643562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643562 prefixEnd_7643562 := by exact prefixLift 7643562
  have htrace : WordTrace (prefixWord ++ tailWord_7643562) baseStart_7643562 baseEnd_7643562 := by
    simpa [prefixWord, tailWord_7643562, baseEnd_7643562] using wordTrace_append hprefix tailTrace_7643562
  have hstable : (prefixWord ++ tailWord_7643562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643562).length < 2 ^ (prefixWord ++ tailWord_7643562).sum := by decide
  have hdescent : baseEnd_7643562 < baseStart_7643562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643647 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_7643647 : Nat := 118140960795 + 7643647 * 2 ^ 59
def prefixEnd_7643647 : Nat := 4983230072969 + 3 ^ 40 * 7643647 * 2
def baseEnd_7643647 : Nat := 3924864864297160929660013

theorem tailTrace_7643647 : CollatzResearch.WordTrace tailWord_7643647 prefixEnd_7643647 3924864864297160929660013 := by
  unfold tailWord_7643647
  simp only [CollatzResearch.WordTrace]
  refine ⟨278786709339379824822041195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185857806226253216548027463 278786709339379824822041195)
  ·
    refine ⟨418180064009069737233061793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278786709339379824822041195 418180064009069737233061793)
    ·
      refine ⟨313635048006802302924796345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418180064009069737233061793 313635048006802302924796345)
      ·
        refine ⟨235226286005101727193597259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313635048006802302924796345 235226286005101727193597259)
        ·
          refine ⟨352839429007652590790395889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235226286005101727193597259 352839429007652590790395889)
          ·
            refine ⟨264629571755739443092796917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352839429007652590790395889 264629571755739443092796917)
            ·
              refine ⟨24809022352100572789949711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264629571755739443092796917 24809022352100572789949711)
              ·
                refine ⟨37213533528150859184924567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24809022352100572789949711 37213533528150859184924567)
                ·
                  refine ⟨55820300292226288777386851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37213533528150859184924567 55820300292226288777386851)
                  ·
                    refine ⟨83730450438339433166080277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55820300292226288777386851 83730450438339433166080277)
                    ·
                      refine ⟨3924864864297160929660013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83730450438339433166080277 3924864864297160929660013)
                      ·
                        rfl

theorem cell23_7643647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_7643647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643647 prefixEnd_7643647 := by exact prefixLift 7643647
  have htrace : WordTrace (prefixWord ++ tailWord_7643647) baseStart_7643647 baseEnd_7643647 := by
    simpa [prefixWord, tailWord_7643647, baseEnd_7643647] using wordTrace_append hprefix tailTrace_7643647
  have hstable : (prefixWord ++ tailWord_7643647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643647).length < 2 ^ (prefixWord ++ tailWord_7643647).sum := by decide
  have hdescent : baseEnd_7643647 < baseStart_7643647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643651 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 3, 2, 2]
def baseStart_7643651 : Nat := 118140960795 + 7643651 * 2 ^ 59
def prefixEnd_7643651 : Nat := 4983230072969 + 3 ^ 40 * 7643651 * 2
def baseEnd_7643651 : Nat := 3924866918219778914009995

theorem tailTrace_7643651 : CollatzResearch.WordTrace tailWord_7643651 prefixEnd_7643651 3924866918219778914009995 := by
  unfold tailWord_7643651
  simp only [CollatzResearch.WordTrace]
  refine ⟨278786855231365333505186807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185857903487576889003457871 278786855231365333505186807)
  ·
    refine ⟨418180282847048000257780211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278786855231365333505186807 418180282847048000257780211)
    ·
      refine ⟨627270424270572000386670317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418180282847048000257780211 627270424270572000386670317)
      ·
        refine ⟨235226409101464500145001369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627270424270572000386670317 235226409101464500145001369)
        ·
          refine ⟨176419806826098375108751027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235226409101464500145001369 176419806826098375108751027)
          ·
            refine ⟨264629710239147562663126541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176419806826098375108751027 264629710239147562663126541)
            ·
              refine ⟨99236141339680335998672453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264629710239147562663126541 99236141339680335998672453)
              ·
                refine ⟨18606776501190062999751085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99236141339680335998672453 18606776501190062999751085)
                ·
                  refine ⟨6977541187946273624906657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18606776501190062999751085 6977541187946273624906657)
                  ·
                    refine ⟨5233155890959705218679993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6977541187946273624906657 5233155890959705218679993)
                    ·
                      refine ⟨3924866918219778914009995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233155890959705218679993 3924866918219778914009995)
                      ·
                        rfl

theorem cell23_7643651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_7643651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643651 prefixEnd_7643651 := by exact prefixLift 7643651
  have htrace : WordTrace (prefixWord ++ tailWord_7643651) baseStart_7643651 baseEnd_7643651 := by
    simpa [prefixWord, tailWord_7643651, baseEnd_7643651] using wordTrace_append hprefix tailTrace_7643651
  have hstable : (prefixWord ++ tailWord_7643651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643651).length < 2 ^ (prefixWord ++ tailWord_7643651).sum := by decide
  have hdescent : baseEnd_7643651 < baseStart_7643651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643668 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7643668 : Nat := 118140960795 + 7643668 * 2 ^ 59
def prefixEnd_7643668 : Nat := 4983230072969 + 3 ^ 40 * 7643668 * 2
def baseEnd_7643668 : Nat := 3924875647390905347497417

theorem tailTrace_7643668 : CollatzResearch.WordTrace tailWord_7643668 prefixEnd_7643668 3924875647390905347497417 := by
  unfold tailWord_7643668
  simp only [CollatzResearch.WordTrace]
  refine ⟨139393737636151872704277829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185858316848202496939037105 139393737636151872704277829)
  ·
    refine ⟨26136325806778476132052093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139393737636151872704277829 26136325806778476132052093)
    ·
      refine ⟨9801122177541928549519535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26136325806778476132052093 9801122177541928549519535)
      ·
        refine ⟨14701683266312892824279303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801122177541928549519535 14701683266312892824279303)
        ·
          refine ⟨22052524899469339236418955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14701683266312892824279303 22052524899469339236418955)
          ·
            refine ⟨33078787349204008854628433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22052524899469339236418955 33078787349204008854628433)
            ·
              refine ⟨24809090511903006640971325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33078787349204008854628433 24809090511903006640971325)
              ·
                refine ⟨9303408941963627490364247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24809090511903006640971325 9303408941963627490364247)
                ·
                  refine ⟨13955113412945441235546371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9303408941963627490364247 13955113412945441235546371)
                  ·
                    refine ⟨20932670119418161853319557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13955113412945441235546371 20932670119418161853319557)
                    ·
                      refine ⟨3924875647390905347497417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20932670119418161853319557 3924875647390905347497417)
                      ·
                        rfl

theorem cell23_7643668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7643668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643668 prefixEnd_7643668 := by exact prefixLift 7643668
  have htrace : WordTrace (prefixWord ++ tailWord_7643668) baseStart_7643668 baseEnd_7643668 := by
    simpa [prefixWord, tailWord_7643668, baseEnd_7643668] using wordTrace_append hprefix tailTrace_7643668
  have hstable : (prefixWord ++ tailWord_7643668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643668).length < 2 ^ (prefixWord ++ tailWord_7643668).sum := by decide
  have hdescent : baseEnd_7643668 < baseStart_7643668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643711 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 3, 3, 2]
def baseStart_7643711 : Nat := 118140960795 + 7643711 * 2 ^ 59
def prefixEnd_7643711 : Nat := 4983230072969 + 3 ^ 40 * 7643711 * 2
def baseEnd_7643711 : Nat := 3924897727059048679259719

theorem tailTrace_7643711 : CollatzResearch.WordTrace tailWord_7643711 prefixEnd_7643711 3924897727059048679259719 := by
  unfold tailWord_7643711
  simp only [CollatzResearch.WordTrace]
  refine ⟨278789043611147963752370987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185859362407431975834913991 278789043611147963752370987)
  ·
    refine ⟨418183565416721945628556481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278789043611147963752370987 418183565416721945628556481)
    ·
      refine ⟨313637674062541459221417361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418183565416721945628556481 313637674062541459221417361)
      ·
        refine ⟨235228255546906094416063021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313637674062541459221417361 235228255546906094416063021)
        ·
          refine ⟨88210595830089785406023633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235228255546906094416063021 88210595830089785406023633)
          ·
            refine ⟨66157946872567339054517725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88210595830089785406023633 66157946872567339054517725)
            ·
              refine ⟨24809230077212752145444147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66157946872567339054517725 24809230077212752145444147)
              ·
                refine ⟨37213845115819128218166221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24809230077212752145444147 37213845115819128218166221)
                ·
                  refine ⟨13955191918432173081812333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37213845115819128218166221 13955191918432173081812333)
                  ·
                    refine ⟨5233196969412064905679625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13955191918432173081812333 5233196969412064905679625)
                    ·
                      refine ⟨3924897727059048679259719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233196969412064905679625 3924897727059048679259719)
                      ·
                        rfl

theorem cell23_7643711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_7643711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643711 prefixEnd_7643711 := by exact prefixLift 7643711
  have htrace : WordTrace (prefixWord ++ tailWord_7643711) baseStart_7643711 baseEnd_7643711 := by
    simpa [prefixWord, tailWord_7643711, baseEnd_7643711] using wordTrace_append hprefix tailTrace_7643711
  have hstable : (prefixWord ++ tailWord_7643711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643711).length < 2 ^ (prefixWord ++ tailWord_7643711).sum := by decide
  have hdescent : baseEnd_7643711 < baseStart_7643711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643718 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_7643718 : Nat := 118140960795 + 7643718 * 2 ^ 59
def prefixEnd_7643718 : Nat := 4983230072969 + 3 ^ 40 * 7643718 * 2
def baseEnd_7643718 : Nat := 3924901321423630151872187

theorem tailTrace_7643718 : CollatzResearch.WordTrace tailWord_7643718 prefixEnd_7643718 3924901321423630151872187 := by
  unfold tailWord_7643718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712165591316331373371119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185859532614748402631917205 8712165591316331373371119)
  ·
    refine ⟨13068248386974497060056679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8712165591316331373371119 13068248386974497060056679)
    ·
      refine ⟨19602372580461745590085019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13068248386974497060056679 19602372580461745590085019)
      ·
        refine ⟨29403558870692618385127529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19602372580461745590085019 29403558870692618385127529)
        ·
          refine ⟨22052669153019463788845647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29403558870692618385127529 22052669153019463788845647)
          ·
            refine ⟨33079003729529195683268471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22052669153019463788845647 33079003729529195683268471)
            ·
              refine ⟨49618505594293793524902707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33079003729529195683268471 49618505594293793524902707)
              ·
                refine ⟨74427758391440690287354061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49618505594293793524902707 74427758391440690287354061)
                ·
                  refine ⟨27910409396790258857757773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74427758391440690287354061 27910409396790258857757773)
                  ·
                    refine ⟨10466403523796347071659165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27910409396790258857757773 10466403523796347071659165)
                    ·
                      refine ⟨3924901321423630151872187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10466403523796347071659165 3924901321423630151872187)
                      ·
                        rfl

theorem cell23_7643718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_7643718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643718 prefixEnd_7643718 := by exact prefixLift 7643718
  have htrace : WordTrace (prefixWord ++ tailWord_7643718) baseStart_7643718 baseEnd_7643718 := by
    simpa [prefixWord, tailWord_7643718, baseEnd_7643718] using wordTrace_append hprefix tailTrace_7643718
  have hstable : (prefixWord ++ tailWord_7643718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643718).length < 2 ^ (prefixWord ++ tailWord_7643718).sum := by decide
  have hdescent : baseEnd_7643718 < baseStart_7643718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643737 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_7643737 : Nat := 118140960795 + 7643737 * 2 ^ 59
def prefixEnd_7643737 : Nat := 4983230072969 + 3 ^ 40 * 7643737 * 2
def baseEnd_7643737 : Nat := 3924911077556065577534599

theorem tailTrace_7643737 : CollatzResearch.WordTrace tailWord_7643737 prefixEnd_7643737 3924911077556065577534599 := by
  unfold tailWord_7643737
  simp only [CollatzResearch.WordTrace]
  refine ⟨278789991909053770192817465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185859994606035846795211643 278789991909053770192817465)
  ·
    refine ⟨209092493931790327644613099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278789991909053770192817465 209092493931790327644613099)
    ·
      refine ⟨313638740897685491466919649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209092493931790327644613099 313638740897685491466919649)
      ·
        refine ⟨235229055673264118600189737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313638740897685491466919649 235229055673264118600189737)
        ·
          refine ⟨176421791754948088950142303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235229055673264118600189737 176421791754948088950142303)
          ·
            refine ⟨264632687632422133425213455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176421791754948088950142303 264632687632422133425213455)
            ·
              refine ⟨396949031448633200137820183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264632687632422133425213455 396949031448633200137820183)
              ·
                refine ⟨595423547172949800206730275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396949031448633200137820183 595423547172949800206730275)
                ·
                  refine ⟨893135320759424700310095413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595423547172949800206730275 893135320759424700310095413)
                  ·
                    refine ⟨83731436321196065654071445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 893135320759424700310095413 83731436321196065654071445)
                    ·
                      refine ⟨3924911077556065577534599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83731436321196065654071445 3924911077556065577534599)
                      ·
                        rfl

theorem cell23_7643737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_7643737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643737 prefixEnd_7643737 := by exact prefixLift 7643737
  have htrace : WordTrace (prefixWord ++ tailWord_7643737) baseStart_7643737 baseEnd_7643737 := by
    simpa [prefixWord, tailWord_7643737, baseEnd_7643737] using wordTrace_append hprefix tailTrace_7643737
  have hstable : (prefixWord ++ tailWord_7643737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643737).length < 2 ^ (prefixWord ++ tailWord_7643737).sum := by decide
  have hdescent : baseEnd_7643737 < baseStart_7643737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643742 : List Nat := [4, 4, 1, 2, 2, 1, 1, 8]
def baseStart_7643742 : Nat := 118140960795 + 7643742 * 2 ^ 59
def prefixEnd_7643742 : Nat := 4983230072969 + 3 ^ 40 * 7643742 * 2
def baseEnd_7643742 : Nat := 145367172035531039184151

theorem tailTrace_7643742 : CollatzResearch.WordTrace tailWord_7643742 prefixEnd_7643742 145367172035531039184151 := by
  unfold tailWord_7643742
  simp only [CollatzResearch.WordTrace]
  refine ⟨34848771784254457005843685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185860116182690437364499653 34848771784254457005843685)
  ·
    refine ⟨6534144709547710688595691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34848771784254457005843685 6534144709547710688595691)
    ·
      refine ⟨9801217064321566032893537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6534144709547710688595691 9801217064321566032893537)
      ·
        refine ⟨7350912798241174524670153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9801217064321566032893537 7350912798241174524670153)
        ·
          refine ⟨5513184598680880893502615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7350912798241174524670153 5513184598680880893502615)
          ·
            refine ⟨8269776898021321340253923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5513184598680880893502615 8269776898021321340253923)
            ·
              refine ⟨12404665347031982010380885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8269776898021321340253923 12404665347031982010380885)
              ·
                refine ⟨145367172035531039184151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12404665347031982010380885 145367172035531039184151)
                ·
                  rfl

theorem cell23_7643742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_7643742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643742 prefixEnd_7643742 := by exact prefixLift 7643742
  have htrace : WordTrace (prefixWord ++ tailWord_7643742) baseStart_7643742 baseEnd_7643742 := by
    simpa [prefixWord, tailWord_7643742, baseEnd_7643742] using wordTrace_append hprefix tailTrace_7643742
  have hstable : (prefixWord ++ tailWord_7643742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643742).length < 2 ^ (prefixWord ++ tailWord_7643742).sum := by decide
  have hdescent : baseEnd_7643742 < baseStart_7643742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643744 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3]
def baseStart_7643744 : Nat := 118140960795 + 7643744 * 2 ^ 59
def prefixEnd_7643744 : Nat := 4983230072969 + 3 ^ 40 * 7643744 * 2
def baseEnd_7643744 : Nat := 3924914671920647050147067

theorem tailTrace_7643744 : CollatzResearch.WordTrace tailWord_7643744 prefixEnd_7643744 3924914671920647050147067 := by
  unfold tailWord_7643744
  simp only [CollatzResearch.WordTrace]
  refine ⟨139395123610014205194161143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185860164813352273592214857 139395123610014205194161143)
  ·
    refine ⟨209092685415021307791241715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139395123610014205194161143 209092685415021307791241715)
    ·
      refine ⟨313639028122531961686862573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209092685415021307791241715 313639028122531961686862573)
      ·
        refine ⟨117614635545949485632573465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313639028122531961686862573 117614635545949485632573465)
        ·
          refine ⟨88210976659462114224430099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117614635545949485632573465 88210976659462114224430099)
          ·
            refine ⟨132316464989193171336645149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88210976659462114224430099 132316464989193171336645149)
            ·
              refine ⟨49618674370947439251241931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132316464989193171336645149 49618674370947439251241931)
              ·
                refine ⟨74428011556421158876862897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49618674370947439251241931 74428011556421158876862897)
                ·
                  refine ⟨55821008667315869157647173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74428011556421158876862897 55821008667315869157647173)
                  ·
                    refine ⟨10466439125121725467058845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55821008667315869157647173 10466439125121725467058845)
                    ·
                      refine ⟨3924914671920647050147067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10466439125121725467058845 3924914671920647050147067)
                      ·
                        rfl

theorem cell23_7643744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_7643744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643744 prefixEnd_7643744 := by exact prefixLift 7643744
  have htrace : WordTrace (prefixWord ++ tailWord_7643744) baseStart_7643744 baseEnd_7643744 := by
    simpa [prefixWord, tailWord_7643744, baseEnd_7643744] using wordTrace_append hprefix tailTrace_7643744
  have hstable : (prefixWord ++ tailWord_7643744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643744).length < 2 ^ (prefixWord ++ tailWord_7643744).sum := by decide
  have hdescent : baseEnd_7643744 < baseStart_7643744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643758 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_7643758 : Nat := 118140960795 + 7643758 * 2 ^ 59
def prefixEnd_7643758 : Nat := 4983230072969 + 3 ^ 40 * 7643758 * 2
def baseEnd_7643758 : Nat := 3924921860649809995372003

theorem tailTrace_7643758 : CollatzResearch.WordTrace tailWord_7643758 prefixEnd_7643758 3924921860649809995372003 := by
  unfold tailWord_7643758
  simp only [CollatzResearch.WordTrace]
  refine ⟨34848844730247211347416491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185860505227985127186221285 34848844730247211347416491)
  ·
    refine ⟨52273267095370817021124737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34848844730247211347416491 52273267095370817021124737)
    ·
      refine ⟨39204950321528112765843553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52273267095370817021124737 39204950321528112765843553)
      ·
        refine ⟨29403712741146084574382665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39204950321528112765843553 29403712741146084574382665)
        ·
          refine ⟨22052784555859563430786999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29403712741146084574382665 22052784555859563430786999)
          ·
            refine ⟨33079176833789345146180499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22052784555859563430786999 33079176833789345146180499)
            ·
              refine ⟨49618765250684017719270749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33079176833789345146180499 49618765250684017719270749)
              ·
                refine ⟨18607036969006506644726531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49618765250684017719270749 18607036969006506644726531)
                ·
                  refine ⟨27910555453509759967089797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18607036969006506644726531 27910555453509759967089797)
                  ·
                    refine ⟨5233229147533079993829337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27910555453509759967089797 5233229147533079993829337)
                    ·
                      refine ⟨3924921860649809995372003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233229147533079993829337 3924921860649809995372003)
                      ·
                        rfl

theorem cell23_7643758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_7643758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643758 prefixEnd_7643758 := by exact prefixLift 7643758
  have htrace : WordTrace (prefixWord ++ tailWord_7643758) baseStart_7643758 baseEnd_7643758 := by
    simpa [prefixWord, tailWord_7643758, baseEnd_7643758] using wordTrace_append hprefix tailTrace_7643758
  have hstable : (prefixWord ++ tailWord_7643758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643758).length < 2 ^ (prefixWord ++ tailWord_7643758).sum := by decide
  have hdescent : baseEnd_7643758 < baseStart_7643758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643781 : List Nat := [1, 3, 1, 1, 4, 2, 1, 5, 5]
def baseStart_7643781 : Nat := 118140960795 + 7643781 * 2 ^ 59
def prefixEnd_7643781 : Nat := 4983230072969 + 3 ^ 40 * 7643781 * 2
def baseEnd_7643781 : Nat := 436103741189429267264933

theorem tailTrace_7643781 : CollatzResearch.WordTrace tailWord_7643781 prefixEnd_7643781 436103741189429267264933 := by
  unfold tailWord_7643781
  simp only [CollatzResearch.WordTrace]
  refine ⟨278791596720894365707419197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185861064480596243804946131 278791596720894365707419197)
  ·
    refine ⟨104546848770335387140282199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278791596720894365707419197 104546848770335387140282199)
    ·
      refine ⟨156820273155503080710423299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104546848770335387140282199 156820273155503080710423299)
      ·
        refine ⟨235230409733254621065634949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156820273155503080710423299 235230409733254621065634949)
        ·
          refine ⟨44105701824985241449806553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235230409733254621065634949 44105701824985241449806553)
          ·
            refine ⟨33079276368738931087354915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44105701824985241449806553 33079276368738931087354915)
            ·
              refine ⟨49618914553108396631032373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33079276368738931087354915 49618914553108396631032373)
              ·
                refine ⟨4651773239353912184159285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49618914553108396631032373 4651773239353912184159285)
                ·
                  refine ⟨436103741189429267264933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4651773239353912184159285 436103741189429267264933)
                  ·
                    rfl

theorem cell23_7643781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_7643781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643781 prefixEnd_7643781 := by exact prefixLift 7643781
  have htrace : WordTrace (prefixWord ++ tailWord_7643781) baseStart_7643781 baseEnd_7643781 := by
    simpa [prefixWord, tailWord_7643781, baseEnd_7643781] using wordTrace_append hprefix tailTrace_7643781
  have hstable : (prefixWord ++ tailWord_7643781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643781).length < 2 ^ (prefixWord ++ tailWord_7643781).sum := by decide
  have hdescent : baseEnd_7643781 < baseStart_7643781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643871 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 6]
def baseStart_7643871 : Nat := 118140960795 + 7643871 * 2 ^ 59
def prefixEnd_7643871 : Nat := 4983230072969 + 3 ^ 40 * 7643871 * 2
def baseEnd_7643871 : Nat := 436108875995974228139887

theorem tailTrace_7643871 : CollatzResearch.WordTrace tailWord_7643871 prefixEnd_7643871 436108875995974228139887 := by
  unfold tailWord_7643871
  simp only [CollatzResearch.WordTrace]
  refine ⟨278794879290568311078195467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185863252860378874052130311 278794879290568311078195467)
  ·
    refine ⟨418192318935852466617293201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278794879290568311078195467 418192318935852466617293201)
    ·
      refine ⟨313644239201889349962969901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418192318935852466617293201 313644239201889349962969901)
      ·
        refine ⟨117616589700708506236113713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313644239201889349962969901 117616589700708506236113713)
        ·
          refine ⟨88212442275531379677085285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117616589700708506236113713 88212442275531379677085285)
          ·
            refine ⟨16539832926662133689453491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88212442275531379677085285 16539832926662133689453491)
            ·
              refine ⟨24809749389993200534180237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16539832926662133689453491 24809749389993200534180237)
              ·
                refine ⟨9303656021247450200317589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24809749389993200534180237 9303656021247450200317589)
                ·
                  refine ⟨436108875995974228139887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9303656021247450200317589 436108875995974228139887)
                  ·
                    rfl

theorem cell23_7643871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 6].length) (baseStart_7643871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643871 prefixEnd_7643871 := by exact prefixLift 7643871
  have htrace : WordTrace (prefixWord ++ tailWord_7643871) baseStart_7643871 baseEnd_7643871 := by
    simpa [prefixWord, tailWord_7643871, baseEnd_7643871] using wordTrace_append hprefix tailTrace_7643871
  have hstable : (prefixWord ++ tailWord_7643871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643871).length < 2 ^ (prefixWord ++ tailWord_7643871).sum := by decide
  have hdescent : baseEnd_7643871 < baseStart_7643871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643921 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_7643921 : Nat := 118140960795 + 7643921 * 2 ^ 59
def prefixEnd_7643921 : Nat := 4983230072969 + 3 ^ 40 * 7643921 * 2
def baseEnd_7643921 : Nat := 3925005557996492857633753

theorem tailTrace_7643921 : CollatzResearch.WordTrace tailWord_7643921 prefixEnd_7643921 3925005557996492857633753 := by
  unfold tailWord_7643921
  simp only [CollatzResearch.WordTrace]
  refine ⟨278796702940387169617515617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185864468626924779745010411 278796702940387169617515617)
  ·
    refine ⟨209097527205290377213136713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278796702940387169617515617 209097527205290377213136713)
    ·
      refine ⟨156823145403967782909852535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209097527205290377213136713 156823145403967782909852535)
      ·
        refine ⟨235234718105951674364778803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156823145403967782909852535 235234718105951674364778803)
        ·
          refine ⟨352852077158927511547168205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235234718105951674364778803 352852077158927511547168205)
          ·
            refine ⟨132319528934597816830188077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352852077158927511547168205 132319528934597816830188077)
            ·
              refine ⟨49619823350474181311320529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132319528934597816830188077 49619823350474181311320529)
              ·
                refine ⟨37214867512855635983490397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49619823350474181311320529 37214867512855635983490397)
                ·
                  refine ⟨13955575317320863493808899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37214867512855635983490397 13955575317320863493808899)
                  ·
                    refine ⟨20933362975981295240713349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13955575317320863493808899 20933362975981295240713349)
                    ·
                      refine ⟨3925005557996492857633753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20933362975981295240713349 3925005557996492857633753)
                      ·
                        rfl

theorem cell23_7643921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_7643921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643921 prefixEnd_7643921 := by exact prefixLift 7643921
  have htrace : WordTrace (prefixWord ++ tailWord_7643921) baseStart_7643921 baseEnd_7643921 := by
    simpa [prefixWord, tailWord_7643921, baseEnd_7643921] using wordTrace_append hprefix tailTrace_7643921
  have hstable : (prefixWord ++ tailWord_7643921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643921).length < 2 ^ (prefixWord ++ tailWord_7643921).sum := by decide
  have hdescent : baseEnd_7643921 < baseStart_7643921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643938 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7643938 : Nat := 118140960795 + 7643938 * 2 ^ 59
def prefixEnd_7643938 : Nat := 4983230072969 + 3 ^ 40 * 7643938 * 2
def baseEnd_7643938 : Nat := 3925014287167619291121175

theorem tailTrace_7643938 : CollatzResearch.WordTrace tailWord_7643938 prefixEnd_7643938 3925014287167619291121175 := by
  unfold tailWord_7643938
  simp only [CollatzResearch.WordTrace]
  refine ⟨69699330745331395380221117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185864881987550387680589645 69699330745331395380221117)
  ·
    refine ⟨26137249029499273267582919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69699330745331395380221117 26137249029499273267582919)
    ·
      refine ⟨39205873544248909901374379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26137249029499273267582919 39205873544248909901374379)
      ·
        refine ⟨58808810316373364852061569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39205873544248909901374379 58808810316373364852061569)
        ·
          refine ⟨44106607737280023639046177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58808810316373364852061569 44106607737280023639046177)
          ·
            refine ⟨33079955802960017729284633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44106607737280023639046177 33079955802960017729284633)
            ·
              refine ⟨24809966852220013296963475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33079955802960017729284633 24809966852220013296963475)
              ·
                refine ⟨37214950278330019945445213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24809966852220013296963475 37214950278330019945445213)
                ·
                  refine ⟨13955606354373757479541955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37214950278330019945445213 13955606354373757479541955)
                  ·
                    refine ⟨20933409531560636219312933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13955606354373757479541955 20933409531560636219312933)
                    ·
                      refine ⟨3925014287167619291121175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20933409531560636219312933 3925014287167619291121175)
                      ·
                        rfl

theorem cell23_7643938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7643938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643938 prefixEnd_7643938 := by exact prefixLift 7643938
  have htrace : WordTrace (prefixWord ++ tailWord_7643938) baseStart_7643938 baseEnd_7643938 := by
    simpa [prefixWord, tailWord_7643938, baseEnd_7643938] using wordTrace_append hprefix tailTrace_7643938
  have hstable : (prefixWord ++ tailWord_7643938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643938).length < 2 ^ (prefixWord ++ tailWord_7643938).sum := by decide
  have hdescent : baseEnd_7643938 < baseStart_7643938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643955 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 1, 1, 4]
def baseStart_7643955 : Nat := 118140960795 + 7643955 * 2 ^ 59
def prefixEnd_7643955 : Nat := 4983230072969 + 3 ^ 40 * 7643955 * 2
def baseEnd_7643955 : Nat := 3925023016338745724608597

theorem tailTrace_7643955 : CollatzResearch.WordTrace tailWord_7643955 prefixEnd_7643955 3925023016338745724608597 := by
  unfold tailWord_7643955
  simp only [CollatzResearch.WordTrace]
  refine ⟨278797943022263993424253319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185865295348175995616168879 278797943022263993424253319)
  ·
    refine ⟨418196914533395990136379979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278797943022263993424253319 418196914533395990136379979)
    ·
      refine ⟨627295371800093985204569969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418196914533395990136379979 627295371800093985204569969)
      ·
        refine ⟨470471528850070488903427477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627295371800093985204569969 470471528850070488903427477)
        ·
          refine ⟨22053352914847054167348163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 470471528850070488903427477 22053352914847054167348163)
          ·
            refine ⟨33080029372270581251022245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22053352914847054167348163 33080029372270581251022245)
            ·
              refine ⟨6202505507300733984566671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33080029372270581251022245 6202505507300733984566671)
              ·
                refine ⟨9303758260951100976850007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6202505507300733984566671 9303758260951100976850007)
                ·
                  refine ⟨13955637391426651465275011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9303758260951100976850007 13955637391426651465275011)
                  ·
                    refine ⟨20933456087139977197912517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13955637391426651465275011 20933456087139977197912517)
                    ·
                      refine ⟨3925023016338745724608597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20933456087139977197912517 3925023016338745724608597)
                      ·
                        rfl

theorem cell23_7643955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 1, 4].length) (baseStart_7643955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643955 prefixEnd_7643955 := by exact prefixLift 7643955
  have htrace : WordTrace (prefixWord ++ tailWord_7643955) baseStart_7643955 baseEnd_7643955 := by
    simpa [prefixWord, tailWord_7643955, baseEnd_7643955] using wordTrace_append hprefix tailTrace_7643955
  have hstable : (prefixWord ++ tailWord_7643955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643955).length < 2 ^ (prefixWord ++ tailWord_7643955).sum := by decide
  have hdescent : baseEnd_7643955 < baseStart_7643955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643965 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_7643965 : Nat := 118140960795 + 7643965 * 2 ^ 59
def prefixEnd_7643965 : Nat := 4983230072969 + 3 ^ 40 * 7643965 * 2
def baseEnd_7643965 : Nat := 1308342717048430228494517

theorem tailTrace_7643965 : CollatzResearch.WordTrace tailWord_7643965 prefixEnd_7643965 1308342717048430228494517 := by
  unfold tailWord_7643965
  simp only [CollatzResearch.WordTrace]
  refine ⟨278798307752227765132117349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185865538501485176754744899 278798307752227765132117349)
  ·
    refine ⟨52274682703542705962272003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278798307752227765132117349 52274682703542705962272003)
    ·
      refine ⟨78412024055314058943408005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52274682703542705962272003 78412024055314058943408005)
      ·
        refine ⟨14702254510371386051889001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78412024055314058943408005 14702254510371386051889001)
        ·
          refine ⟨11026690882778539538916751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14702254510371386051889001 11026690882778539538916751)
          ·
            refine ⟨16540036324167809308375127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11026690882778539538916751 16540036324167809308375127)
            ·
              refine ⟨24810054486251713962562691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16540036324167809308375127 24810054486251713962562691)
              ·
                refine ⟨37215081729377570943844037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24810054486251713962562691 37215081729377570943844037)
                ·
                  refine ⟨6977827824258294551970757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37215081729377570943844037 6977827824258294551970757)
                  ·
                    refine ⟨1308342717048430228494517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977827824258294551970757 1308342717048430228494517)
                    ·
                      rfl

theorem cell23_7643965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_7643965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643965 prefixEnd_7643965 := by exact prefixLift 7643965
  have htrace : WordTrace (prefixWord ++ tailWord_7643965) baseStart_7643965 baseEnd_7643965 := by
    simpa [prefixWord, tailWord_7643965, baseEnd_7643965] using wordTrace_append hprefix tailTrace_7643965
  have hstable : (prefixWord ++ tailWord_7643965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643965).length < 2 ^ (prefixWord ++ tailWord_7643965).sum := by decide
  have hdescent : baseEnd_7643965 < baseStart_7643965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7643985 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_7643985 : Nat := 118140960795 + 7643985 * 2 ^ 59
def prefixEnd_7643985 : Nat := 4983230072969 + 3 ^ 40 * 7643985 * 2
def baseEnd_7643985 : Nat := 3925038420758380607233459

theorem tailTrace_7643985 : CollatzResearch.WordTrace tailWord_7643985 prefixEnd_7643985 3925038420758380607233459 := by
  unfold tailWord_7643985
  simp only [CollatzResearch.WordTrace]
  refine ⟨278799037212155308547845409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185866024808103539031896939 278799037212155308547845409)
  ·
    refine ⟨209099277909116481410884057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278799037212155308547845409 209099277909116481410884057)
    ·
      refine ⟨156824458431837361058163043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209099277909116481410884057 156824458431837361058163043)
      ·
        refine ⟨235236687647756041587244565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156824458431837361058163043 235236687647756041587244565)
        ·
          refine ⟨11026719733488564449402089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235236687647756041587244565 11026719733488564449402089)
          ·
            refine ⟨8270039800116423337051567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11026719733488564449402089 8270039800116423337051567)
            ·
              refine ⟨12405059700174635005577351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8270039800116423337051567 12405059700174635005577351)
              ·
                refine ⟨18607589550261952508366027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405059700174635005577351 18607589550261952508366027)
                ·
                  refine ⟨27911384325392928762549041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18607589550261952508366027 27911384325392928762549041)
                  ·
                    refine ⟨20933538244044696571911781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27911384325392928762549041 20933538244044696571911781)
                    ·
                      refine ⟨3925038420758380607233459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20933538244044696571911781 3925038420758380607233459)
                      ·
                        rfl

theorem cell23_7643985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_7643985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7643985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7643985 prefixEnd_7643985 := by exact prefixLift 7643985
  have htrace : WordTrace (prefixWord ++ tailWord_7643985) baseStart_7643985 baseEnd_7643985 := by
    simpa [prefixWord, tailWord_7643985, baseEnd_7643985] using wordTrace_append hprefix tailTrace_7643985
  have hstable : (prefixWord ++ tailWord_7643985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7643985).length < 2 ^ (prefixWord ++ tailWord_7643985).sum := by decide
  have hdescent : baseEnd_7643985 < baseStart_7643985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7643985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644022 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7644022 : Nat := 118140960795 + 7644022 * 2 ^ 59
def prefixEnd_7644022 : Nat := 4983230072969 + 3 ^ 40 * 7644022 * 2
def baseEnd_7644022 : Nat := 3925057419542596962470789

theorem tailTrace_7644022 : CollatzResearch.WordTrace tailWord_7644022 prefixEnd_7644022 3925057419542596962470789 := by
  unfold tailWord_7644022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17425024169563828991683895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 185866924475347509244628213 17425024169563828991683895)
  ·
    refine ⟨26137536254345743487525843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17425024169563828991683895 26137536254345743487525843)
    ·
      refine ⟨39206304381518615231288765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26137536254345743487525843 39206304381518615231288765)
      ·
        refine ⟨14702364143069480711733287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39206304381518615231288765 14702364143069480711733287)
        ·
          refine ⟨22053546214604221067599931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14702364143069480711733287 22053546214604221067599931)
          ·
            refine ⟨33080319321906331601399897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22053546214604221067599931 33080319321906331601399897)
            ·
              refine ⟨24810239491429748701049923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33080319321906331601399897 24810239491429748701049923)
              ·
                refine ⟨37215359237144623051574885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24810239491429748701049923 37215359237144623051574885)
                ·
                  refine ⟨6977879856964616822170291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37215359237144623051574885 6977879856964616822170291)
                  ·
                    refine ⟨10466819785446925233255437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6977879856964616822170291 10466819785446925233255437)
                    ·
                      refine ⟨3925057419542596962470789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10466819785446925233255437 3925057419542596962470789)
                      ·
                        rfl

theorem cell23_7644022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7644022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644022 prefixEnd_7644022 := by exact prefixLift 7644022
  have htrace : WordTrace (prefixWord ++ tailWord_7644022) baseStart_7644022 baseEnd_7644022 := by
    simpa [prefixWord, tailWord_7644022, baseEnd_7644022] using wordTrace_append hprefix tailTrace_7644022
  have hstable : (prefixWord ++ tailWord_7644022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644022).length < 2 ^ (prefixWord ++ tailWord_7644022).sum := by decide
  have hdescent : baseEnd_7644022 < baseStart_7644022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644039 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_7644039 : Nat := 118140960795 + 7644039 * 2 ^ 59
def prefixEnd_7644039 : Nat := 4983230072969 + 3 ^ 40 * 7644039 * 2
def baseEnd_7644039 : Nat := 3925066148713723395958211

theorem tailTrace_7644039 : CollatzResearch.WordTrace tailWord_7644039 prefixEnd_7644039 3925066148713723395958211 := by
  unfold tailWord_7644039
  simp only [CollatzResearch.WordTrace]
  refine ⟨278801006753959675770311171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185867337835973117180207447 278801006753959675770311171)
  ·
    refine ⟨418201510130939513655466757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278801006753959675770311171 418201510130939513655466757)
    ·
      refine ⟨78412783149551158810400017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418201510130939513655466757 78412783149551158810400017)
      ·
        refine ⟨58809587362163369107800013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78412783149551158810400017 58809587362163369107800013)
        ·
          refine ⟨22053595260811263415425005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58809587362163369107800013 22053595260811263415425005)
          ·
            refine ⟨8270098222804223780784377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22053595260811263415425005 8270098222804223780784377)
            ·
              refine ⟨6202573667103167835588283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8270098222804223780784377 6202573667103167835588283)
              ·
                refine ⟨9303860500654751753382425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6202573667103167835588283 9303860500654751753382425)
                ·
                  refine ⟨6977895375491063815036819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9303860500654751753382425 6977895375491063815036819)
                  ·
                    refine ⟨10466843063236595722555229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6977895375491063815036819 10466843063236595722555229)
                    ·
                      refine ⟨3925066148713723395958211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10466843063236595722555229 3925066148713723395958211)
                      ·
                        rfl

theorem cell23_7644039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_7644039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644039 prefixEnd_7644039 := by exact prefixLift 7644039
  have htrace : WordTrace (prefixWord ++ tailWord_7644039) baseStart_7644039 baseEnd_7644039 := by
    simpa [prefixWord, tailWord_7644039, baseEnd_7644039] using wordTrace_append hprefix tailTrace_7644039
  have hstable : (prefixWord ++ tailWord_7644039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644039).length < 2 ^ (prefixWord ++ tailWord_7644039).sum := by decide
  have hdescent : baseEnd_7644039 < baseStart_7644039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644085 : List Nat := [1, 3, 3, 2, 1, 1, 3, 4, 5]
def baseStart_7644085 : Nat := 118140960795 + 7644085 * 2 ^ 59
def prefixEnd_7644085 : Nat := 4983230072969 + 3 ^ 40 * 7644085 * 2
def baseEnd_7644085 : Nat := 436121085424870023998111

theorem tailTrace_7644085 : CollatzResearch.WordTrace tailWord_7644085 prefixEnd_7644085 436121085424870023998111 := by
  unfold tailWord_7644085
  simp only [CollatzResearch.WordTrace]
  refine ⟨278802684511793025626485709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185868456341195350417657139 278802684511793025626485709)
  ·
    refine ⟨104551006691922384609932141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278802684511793025626485709 104551006691922384609932141)
    ·
      refine ⟨39206627509470894228724553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104551006691922384609932141 39206627509470894228724553)
      ·
        refine ⟨29404970632103170671543415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39206627509470894228724553 29404970632103170671543415)
        ·
          refine ⟨44107455948154756007315123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29404970632103170671543415 44107455948154756007315123)
          ·
            refine ⟨66161183922232134010972685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44107455948154756007315123 66161183922232134010972685)
            ·
              refine ⟨24810443970837050254114757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66161183922232134010972685 24810443970837050254114757)
              ·
                refine ⟨4651958244531946922646517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24810443970837050254114757 4651958244531946922646517)
                ·
                  refine ⟨436121085424870023998111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4651958244531946922646517 436121085424870023998111)
                  ·
                    rfl

theorem cell23_7644085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_7644085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644085 prefixEnd_7644085 := by exact prefixLift 7644085
  have htrace : WordTrace (prefixWord ++ tailWord_7644085) baseStart_7644085 baseEnd_7644085 := by
    simpa [prefixWord, tailWord_7644085, baseEnd_7644085] using wordTrace_append hprefix tailTrace_7644085
  have hstable : (prefixWord ++ tailWord_7644085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644085).length < 2 ^ (prefixWord ++ tailWord_7644085).sum := by decide
  have hdescent : baseEnd_7644085 < baseStart_7644085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644091 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5]
def baseStart_7644091 : Nat := 118140960795 + 7644091 * 2 ^ 59
def prefixEnd_7644091 : Nat := 4983230072969 + 3 ^ 40 * 7644091 * 2
def baseEnd_7644091 : Nat := 3925092849707757192507971

theorem tailTrace_7644091 : CollatzResearch.WordTrace tailWord_7644091 prefixEnd_7644091 3925092849707757192507971 := by
  unfold tailWord_7644091
  simp only [CollatzResearch.WordTrace]
  refine ⟨278802903349771288651204127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185868602233180859100802751 278802903349771288651204127)
  ·
    refine ⟨418204355024656932976806191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278802903349771288651204127 418204355024656932976806191)
    ·
      refine ⟨627306532536985399465209287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418204355024656932976806191 627306532536985399465209287)
      ·
        refine ⟨940959798805478099197813931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627306532536985399465209287 940959798805478099197813931)
        ·
          refine ⟨1411439698208217148796720897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940959798805478099197813931 1411439698208217148796720897)
          ·
            refine ⟨1058579773656162861597540673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411439698208217148796720897 1058579773656162861597540673)
            ·
              refine ⟨793934830242122146198155505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058579773656162861597540673 793934830242122146198155505)
              ·
                refine ⟨595451122681591609648616629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793934830242122146198155505 595451122681591609648616629)
                ·
                  refine ⟨55823542751399213404557809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 595451122681591609648616629 55823542751399213404557809)
                  ·
                    refine ⟨41867657063549410053418357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55823542751399213404557809 41867657063549410053418357)
                    ·
                      refine ⟨3925092849707757192507971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41867657063549410053418357 3925092849707757192507971)
                      ·
                        rfl

theorem cell23_7644091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_7644091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644091 prefixEnd_7644091 := by exact prefixLift 7644091
  have htrace : WordTrace (prefixWord ++ tailWord_7644091) baseStart_7644091 baseEnd_7644091 := by
    simpa [prefixWord, tailWord_7644091, baseEnd_7644091] using wordTrace_append hprefix tailTrace_7644091
  have hstable : (prefixWord ++ tailWord_7644091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644091).length < 2 ^ (prefixWord ++ tailWord_7644091).sum := by decide
  have hdescent : baseEnd_7644091 < baseStart_7644091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644145 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 3, 4]
def baseStart_7644145 : Nat := 118140960795 + 7644145 * 2 ^ 59
def prefixEnd_7644145 : Nat := 4983230072969 + 3 ^ 40 * 7644145 * 2
def baseEnd_7644145 : Nat := 1308373525887699993744241

theorem tailTrace_7644145 : CollatzResearch.WordTrace tailWord_7644145 prefixEnd_7644145 1308373525887699993744241 := by
  unfold tailWord_7644145
  simp only [CollatzResearch.WordTrace]
  refine ⟨278804872891575655873669889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185869915261050437249113259 278804872891575655873669889)
  ·
    refine ⟨209103654668681741905252417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278804872891575655873669889 209103654668681741905252417)
    ·
      refine ⟨156827741001511306428939313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209103654668681741905252417 156827741001511306428939313)
      ·
        refine ⟨117620805751133479821704485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156827741001511306428939313 117620805751133479821704485)
        ·
          refine ⟨22053901078337527466569591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117620805751133479821704485 22053901078337527466569591)
          ·
            refine ⟨33080851617506291199854387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22053901078337527466569591 33080851617506291199854387)
            ·
              refine ⟨49621277426259436799781581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33080851617506291199854387 49621277426259436799781581)
              ·
                refine ⟨18607979034847288799918093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49621277426259436799781581 18607979034847288799918093)
                ·
                  refine ⟨6977992138067733299969285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18607979034847288799918093 6977992138067733299969285)
                  ·
                    refine ⟨1308373525887699993744241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977992138067733299969285 1308373525887699993744241)
                    ·
                      rfl

theorem cell23_7644145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_7644145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644145 prefixEnd_7644145 := by exact prefixLift 7644145
  have htrace : WordTrace (prefixWord ++ tailWord_7644145) baseStart_7644145 baseEnd_7644145 := by
    simpa [prefixWord, tailWord_7644145, baseEnd_7644145] using wordTrace_append hprefix tailTrace_7644145
  have hstable : (prefixWord ++ tailWord_7644145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644145).length < 2 ^ (prefixWord ++ tailWord_7644145).sum := by decide
  have hdescent : baseEnd_7644145 < baseStart_7644145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644185 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 3]
def baseStart_7644185 : Nat := 118140960795 + 7644185 * 2 ^ 59
def prefixEnd_7644185 : Nat := 4983230072969 + 3 ^ 40 * 7644185 * 2
def baseEnd_7644185 : Nat := 3925141116889279824732539

theorem tailTrace_7644185 : CollatzResearch.WordTrace tailWord_7644185 prefixEnd_7644185 3925141116889279824732539 := by
  unfold tailWord_7644185
  simp only [CollatzResearch.WordTrace]
  refine ⟨278806331811430742705126009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185870887874287161803417339 278806331811430742705126009)
  ·
    refine ⟨209104748858573057028844507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278806331811430742705126009 209104748858573057028844507)
    ·
      refine ⟨313657123287859585543266761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209104748858573057028844507 313657123287859585543266761)
      ·
        refine ⟨235242842465894689157450071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313657123287859585543266761 235242842465894689157450071)
        ·
          refine ⟨352864263698842033736175107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235242842465894689157450071 352864263698842033736175107)
          ·
            refine ⟨529296395548263050604262661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352864263698842033736175107 529296395548263050604262661)
            ·
              refine ⟨99243074165299321988299249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 529296395548263050604262661 99243074165299321988299249)
              ·
                refine ⟨74432305623974491491224437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99243074165299321988299249 74432305623974491491224437)
                ·
                  refine ⟨6978028652247608577302291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74432305623974491491224437 6978028652247608577302291)
                  ·
                    refine ⟨10467042978371412865953437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6978028652247608577302291 10467042978371412865953437)
                    ·
                      refine ⟨3925141116889279824732539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10467042978371412865953437 3925141116889279824732539)
                      ·
                        rfl

theorem cell23_7644185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_7644185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644185 prefixEnd_7644185 := by exact prefixLift 7644185
  have htrace : WordTrace (prefixWord ++ tailWord_7644185) baseStart_7644185 baseEnd_7644185 := by
    simpa [prefixWord, tailWord_7644185, baseEnd_7644185] using wordTrace_append hprefix tailTrace_7644185
  have hstable : (prefixWord ++ tailWord_7644185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644185).length < 2 ^ (prefixWord ++ tailWord_7644185).sum := by decide
  have hdescent : baseEnd_7644185 < baseStart_7644185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644196 : List Nat := [2, 3, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_7644196 : Nat := 118140960795 + 7644196 * 2 ^ 59
def prefixEnd_7644196 : Nat := 4983230072969 + 3 ^ 40 * 7644196 * 2
def baseEnd_7644196 : Nat := 1308382255058826427231663

theorem tailTrace_7644196 : CollatzResearch.WordTrace tailWord_7644196 prefixEnd_7644196 1308382255058826427231663 := by
  unfold tailWord_7644196
  simp only [CollatzResearch.WordTrace]
  refine ⟨139403366507195445791888221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185871155342927261055850961 139403366507195445791888221)
  ·
    refine ⟨52276262440198292171958083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139403366507195445791888221 52276262440198292171958083)
    ·
      refine ⟨78414393660297438257937125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52276262440198292171958083 78414393660297438257937125)
      ·
        refine ⟨14702698811305769673363211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78414393660297438257937125 14702698811305769673363211)
        ·
          refine ⟨22054048216958654510044817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14702698811305769673363211 22054048216958654510044817)
          ·
            refine ⟨16540536162718990882533613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22054048216958654510044817 16540536162718990882533613)
            ·
              refine ⟨6202701061019621580950105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16540536162718990882533613 6202701061019621580950105)
              ·
                refine ⟨4652025795764716185712579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6202701061019621580950105 4652025795764716185712579)
                ·
                  refine ⟨6978038693647074278568869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652025795764716185712579 6978038693647074278568869)
                  ·
                    refine ⟨1308382255058826427231663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978038693647074278568869 1308382255058826427231663)
                    ·
                      rfl

theorem cell23_7644196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_7644196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644196 prefixEnd_7644196 := by exact prefixLift 7644196
  have htrace : WordTrace (prefixWord ++ tailWord_7644196) baseStart_7644196 baseEnd_7644196 := by
    simpa [prefixWord, tailWord_7644196, baseEnd_7644196] using wordTrace_append hprefix tailTrace_7644196
  have hstable : (prefixWord ++ tailWord_7644196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644196).length < 2 ^ (prefixWord ++ tailWord_7644196).sum := by decide
  have hdescent : baseEnd_7644196 < baseStart_7644196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644222 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_7644222 : Nat := 118140960795 + 7644222 * 2 ^ 59
def prefixEnd_7644222 : Nat := 4983230072969 + 3 ^ 40 * 7644222 * 2
def baseEnd_7644222 : Nat := 1308386705224498726656623

theorem tailTrace_7644222 : CollatzResearch.WordTrace tailWord_7644222 prefixEnd_7644222 1308386705224498726656623 := by
  unfold tailWord_7644222
  simp only [CollatzResearch.WordTrace]
  refine ⟨34850960164037087253027865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185871787541531132016148613 34850960164037087253027865)
  ·
    refine ⟨26138220123027815439770899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34850960164037087253027865 26138220123027815439770899)
    ·
      refine ⟨39207330184541723159656349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26138220123027815439770899 39207330184541723159656349)
      ·
        refine ⟨14702748819203146184871131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39207330184541723159656349 14702748819203146184871131)
        ·
          refine ⟨22054123228804719277306697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14702748819203146184871131 22054123228804719277306697)
          ·
            refine ⟨16540592421603539457980023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22054123228804719277306697 16540592421603539457980023)
            ·
              refine ⟨24810888632405309186970035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16540592421603539457980023 24810888632405309186970035)
              ·
                refine ⟨37216332948607963780455053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24810888632405309186970035 37216332948607963780455053)
                ·
                  refine ⟨13956124855727986417670645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37216332948607963780455053 13956124855727986417670645)
                  ·
                    refine ⟨1308386705224498726656623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13956124855727986417670645 1308386705224498726656623)
                    ·
                      rfl

theorem cell23_7644222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_7644222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644222 prefixEnd_7644222 := by exact prefixLift 7644222
  have htrace : WordTrace (prefixWord ++ tailWord_7644222) baseStart_7644222 baseEnd_7644222 := by
    simpa [prefixWord, tailWord_7644222, baseEnd_7644222] using wordTrace_append hprefix tailTrace_7644222
  have hstable : (prefixWord ++ tailWord_7644222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644222).length < 2 ^ (prefixWord ++ tailWord_7644222).sum := by decide
  have hdescent : baseEnd_7644222 < baseStart_7644222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644253 : List Nat := [1, 4, 4, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7644253 : Nat := 118140960795 + 7644253 * 2 ^ 59
def prefixEnd_7644253 : Nat := 4983230072969 + 3 ^ 40 * 7644253 * 2
def baseEnd_7644253 : Nat := 3925176033573785558682227

theorem tailTrace_7644253 : CollatzResearch.WordTrace tailWord_7644253 prefixEnd_7644253 3925176033573785558682227 := by
  unfold tailWord_7644253
  simp only [CollatzResearch.WordTrace]
  refine ⟨278808811975184390318601413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185872541316789593545734275 278808811975184390318601413)
  ·
    refine ⟨52276652245347073184737765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278808811975184390318601413 52276652245347073184737765)
    ·
      refine ⟨9801872296002576222138331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52276652245347073184737765 9801872296002576222138331)
      ·
        refine ⟨14702808444003864333207497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801872296002576222138331 14702808444003864333207497)
        ·
          refine ⟨11027106333002898249905623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14702808444003864333207497 11027106333002898249905623)
          ·
            refine ⟨16540659499504347374858435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11027106333002898249905623 16540659499504347374858435)
            ·
              refine ⟨24810989249256521062287653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16540659499504347374858435 24810989249256521062287653)
              ·
                refine ⟨4652060484235597699178935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24810989249256521062287653 4652060484235597699178935)
                ·
                  refine ⟨6978090726353396548768403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652060484235597699178935 6978090726353396548768403)
                  ·
                    refine ⟨10467136089530094823152605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6978090726353396548768403 10467136089530094823152605)
                    ·
                      refine ⟨3925176033573785558682227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10467136089530094823152605 3925176033573785558682227)
                      ·
                        rfl

theorem cell23_7644253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7644253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644253 prefixEnd_7644253 := by exact prefixLift 7644253
  have htrace : WordTrace (prefixWord ++ tailWord_7644253) baseStart_7644253 baseEnd_7644253 := by
    simpa [prefixWord, tailWord_7644253, baseEnd_7644253] using wordTrace_append hprefix tailTrace_7644253
  have hstable : (prefixWord ++ tailWord_7644253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644253).length < 2 ^ (prefixWord ++ tailWord_7644253).sum := by decide
  have hdescent : baseEnd_7644253 < baseStart_7644253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644265 : List Nat := [1, 2, 1, 1, 1, 8, 1, 8]
def baseStart_7644265 : Nat := 118140960795 + 7644265 * 2 ^ 59
def prefixEnd_7644265 : Nat := 4983230072969 + 3 ^ 40 * 7644265 * 2
def baseEnd_7644265 : Nat := 145377118345986648582673

theorem tailTrace_7644265 : CollatzResearch.WordTrace tailWord_7644265 prefixEnd_7644265 145377118345986648582673 := by
  unfold tailWord_7644265
  simp only [CollatzResearch.WordTrace]
  refine ⟨278809249651140916368038249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185872833100760610912025499 278809249651140916368038249)
  ·
    refine ⟨209106937238355687276028687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278809249651140916368038249 209106937238355687276028687)
    ·
      refine ⟨313660405857533530914043031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209106937238355687276028687 313660405857533530914043031)
      ·
        refine ⟨470490608786300296371064547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313660405857533530914043031 470490608786300296371064547)
        ·
          refine ⟨705735913179450444556596821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470490608786300296371064547 705735913179450444556596821)
          ·
            refine ⟨8270342732571684897147619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 705735913179450444556596821 8270342732571684897147619)
            ·
              refine ⟨12405514098857527345721429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8270342732571684897147619 12405514098857527345721429)
              ·
                refine ⟨145377118345986648582673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12405514098857527345721429 145377118345986648582673)
                ·
                  rfl

theorem cell23_7644265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 8].length) (baseStart_7644265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644265 prefixEnd_7644265 := by exact prefixLift 7644265
  have htrace : WordTrace (prefixWord ++ tailWord_7644265) baseStart_7644265 baseEnd_7644265 := by
    simpa [prefixWord, tailWord_7644265, baseEnd_7644265] using wordTrace_append hprefix tailTrace_7644265
  have hstable : (prefixWord ++ tailWord_7644265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644265).length < 2 ^ (prefixWord ++ tailWord_7644265).sum := by decide
  have hdescent : baseEnd_7644265 < baseStart_7644265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644292 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_7644292 : Nat := 118140960795 + 7644292 * 2 ^ 59
def prefixEnd_7644292 : Nat := 4983230072969 + 3 ^ 40 * 7644292 * 2
def baseEnd_7644292 : Nat := 3925196059319310906094547

theorem tailTrace_7644292 : CollatzResearch.WordTrace tailWord_7644292 prefixEnd_7644292 3925196059319310906094547 := by
  unfold tailWord_7644292
  simp only [CollatzResearch.WordTrace]
  refine ⟨139405117211021549989635565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185873489614695399986180753 139405117211021549989635565)
  ·
    refine ⟨52276918954133081246113337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139405117211021549989635565 52276918954133081246113337)
    ·
      refine ⟨39207689215599810934585003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52276918954133081246113337 39207689215599810934585003)
      ·
        refine ⟨58811533823399716401877505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39207689215599810934585003 58811533823399716401877505)
        ·
          refine ⟨44108650367549787301408129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58811533823399716401877505 44108650367549787301408129)
          ·
            refine ⟨33081487775662340476056097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44108650367549787301408129 33081487775662340476056097)
            ·
              refine ⟨24811115831746755357042073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33081487775662340476056097 24811115831746755357042073)
              ·
                refine ⟨18608336873810066517781555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24811115831746755357042073 18608336873810066517781555)
                ·
                  refine ⟨27912505310715099776672333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18608336873810066517781555 27912505310715099776672333)
                  ·
                    refine ⟨10467189491518162416252125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27912505310715099776672333 10467189491518162416252125)
                    ·
                      refine ⟨3925196059319310906094547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10467189491518162416252125 3925196059319310906094547)
                      ·
                        rfl

theorem cell23_7644292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_7644292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644292 prefixEnd_7644292 := by exact prefixLift 7644292
  have htrace : WordTrace (prefixWord ++ tailWord_7644292) baseStart_7644292 baseEnd_7644292 := by
    simpa [prefixWord, tailWord_7644292, baseEnd_7644292] using wordTrace_append hprefix tailTrace_7644292
  have hstable : (prefixWord ++ tailWord_7644292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644292).length < 2 ^ (prefixWord ++ tailWord_7644292).sum := by decide
  have hdescent : baseEnd_7644292 < baseStart_7644292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644293 : List Nat := [1, 3, 1, 1, 6, 1, 2, 3, 1, 2, 2]
def baseStart_7644293 : Nat := 118140960795 + 7644293 * 2 ^ 59
def prefixEnd_7644293 : Nat := 4983230072969 + 3 ^ 40 * 7644293 * 2
def baseEnd_7644293 : Nat := 3925196572799965402182043

theorem tailTrace_7644293 : CollatzResearch.WordTrace tailWord_7644293 prefixEnd_7644293 3925196572799965402182043 := by
  unfold tailWord_7644293
  simp only [CollatzResearch.WordTrace]
  refine ⟨278810270895039477150057533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185873513930026318100038355 278810270895039477150057533)
  ·
    refine ⟨104553851585639803931271575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278810270895039477150057533 104553851585639803931271575)
    ·
      refine ⟨156830777378459705896907363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104553851585639803931271575 156830777378459705896907363)
      ·
        refine ⟨235246166067689558845361045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156830777378459705896907363 235246166067689558845361045)
        ·
          refine ⟨11027164034422948070876299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235246166067689558845361045 11027164034422948070876299)
          ·
            refine ⟨16540746051634422106314449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11027164034422948070876299 16540746051634422106314449)
            ·
              refine ⟨12405559538725816579735837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16540746051634422106314449 12405559538725816579735837)
              ·
                refine ⟨4652084827022181217400939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12405559538725816579735837 4652084827022181217400939)
                ·
                  refine ⟨6978127240533271826101409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652084827022181217400939 6978127240533271826101409)
                  ·
                    refine ⟨5233595430399953869576057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978127240533271826101409 5233595430399953869576057)
                    ·
                      refine ⟨3925196572799965402182043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233595430399953869576057 3925196572799965402182043)
                      ·
                        rfl

theorem cell23_7644293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_7644293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644293 prefixEnd_7644293 := by exact prefixLift 7644293
  have htrace : WordTrace (prefixWord ++ tailWord_7644293) baseStart_7644293 baseEnd_7644293 := by
    simpa [prefixWord, tailWord_7644293, baseEnd_7644293] using wordTrace_append hprefix tailTrace_7644293
  have hstable : (prefixWord ++ tailWord_7644293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644293).length < 2 ^ (prefixWord ++ tailWord_7644293).sum := by decide
  have hdescent : baseEnd_7644293 < baseStart_7644293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644325 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_7644325 : Nat := 118140960795 + 7644325 * 2 ^ 59
def prefixEnd_7644325 : Nat := 4983230072969 + 3 ^ 40 * 7644325 * 2
def baseEnd_7644325 : Nat := 1308404334726969758993965

theorem tailTrace_7644325 : CollatzResearch.WordTrace tailWord_7644325 prefixEnd_7644325 1308404334726969758993965 := by
  unfold tailWord_7644325
  simp only [CollatzResearch.WordTrace]
  refine ⟨278811438030923546615222429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185874292020615697743481619 278811438030923546615222429)
  ·
    refine ⟨104554289261596329980708411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278811438030923546615222429 104554289261596329980708411)
    ·
      refine ⟨156831433892394494971062617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104554289261596329980708411 156831433892394494971062617)
      ·
        refine ⟨117623575419295871228296963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156831433892394494971062617 117623575419295871228296963)
        ·
          refine ⟨176435363128943806842445445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117623575419295871228296963 176435363128943806842445445)
          ·
            refine ⟨33081630586676963782958521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176435363128943806842445445 33081630586676963782958521)
            ·
              refine ⟨24811222940007722837218891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33081630586676963782958521 24811222940007722837218891)
              ·
                refine ⟨37216834410011584255828337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24811222940007722837218891 37216834410011584255828337)
                ·
                  refine ⟨27912625807508688191871253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37216834410011584255828337 27912625807508688191871253)
                  ·
                    refine ⟨1308404334726969758993965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27912625807508688191871253 1308404334726969758993965)
                    ·
                      rfl

theorem cell23_7644325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_7644325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644325 prefixEnd_7644325 := by exact prefixLift 7644325
  have htrace : WordTrace (prefixWord ++ tailWord_7644325) baseStart_7644325 baseEnd_7644325 := by
    simpa [prefixWord, tailWord_7644325, baseEnd_7644325] using wordTrace_append hprefix tailTrace_7644325
  have hstable : (prefixWord ++ tailWord_7644325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644325).length < 2 ^ (prefixWord ++ tailWord_7644325).sum := by decide
  have hdescent : baseEnd_7644325 < baseStart_7644325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644332 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 1, 4, 2]
def baseStart_7644332 : Nat := 118140960795 + 7644332 * 2 ^ 59
def prefixEnd_7644332 : Nat := 4983230072969 + 3 ^ 40 * 7644332 * 2
def baseEnd_7644332 : Nat := 3925216598545490749594363

theorem tailTrace_7644332 : CollatzResearch.WordTrace tailWord_7644332 prefixEnd_7644332 3925216598545490749594363 := by
  unfold tailWord_7644332
  simp only [CollatzResearch.WordTrace]
  refine ⟨139405846670949093405363625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185874462227932124540484833 139405846670949093405363625)
  ·
    refine ⟨104554385003211820054022719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139405846670949093405363625 104554385003211820054022719)
    ·
      refine ⟨156831577504817730081034079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104554385003211820054022719 156831577504817730081034079)
      ·
        refine ⟨235247366257226595121551119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156831577504817730081034079 235247366257226595121551119)
        ·
          refine ⟨352871049385839892682326679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235247366257226595121551119 352871049385839892682326679)
          ·
            refine ⟨529306574078759839023490019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352871049385839892682326679 529306574078759839023490019)
            ·
              refine ⟨793959861118139758535235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529306574078759839023490019 793959861118139758535235029)
              ·
                refine ⟨18608434244956400590669571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 793959861118139758535235029 18608434244956400590669571)
                ·
                  refine ⟨27912651367434600886004357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18608434244956400590669571 27912651367434600886004357)
                  ·
                    refine ⟨5233622131393987666125817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27912651367434600886004357 5233622131393987666125817)
                    ·
                      refine ⟨3925216598545490749594363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233622131393987666125817 3925216598545490749594363)
                      ·
                        rfl

theorem cell23_7644332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_7644332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644332 prefixEnd_7644332 := by exact prefixLift 7644332
  have htrace : WordTrace (prefixWord ++ tailWord_7644332) baseStart_7644332 baseEnd_7644332 := by
    simpa [prefixWord, tailWord_7644332, baseEnd_7644332] using wordTrace_append hprefix tailTrace_7644332
  have hstable : (prefixWord ++ tailWord_7644332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644332).length < 2 ^ (prefixWord ++ tailWord_7644332).sum := by decide
  have hdescent : baseEnd_7644332 < baseStart_7644332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644335 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 3]
def baseStart_7644335 : Nat := 118140960795 + 7644335 * 2 ^ 59
def prefixEnd_7644335 : Nat := 4983230072969 + 3 ^ 40 * 7644335 * 2
def baseEnd_7644335 : Nat := 3925218138987454237856849

theorem tailTrace_7644335 : CollatzResearch.WordTrace tailWord_7644335 prefixEnd_7644335 3925218138987454237856849 := by
  unfold tailWord_7644335
  simp only [CollatzResearch.WordTrace]
  refine ⟨278811802760887318323086459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185874535173924878882057639 278811802760887318323086459)
  ·
    refine ⟨418217704141330977484629689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278811802760887318323086459 418217704141330977484629689)
    ·
      refine ⟨313663278105998233113472267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418217704141330977484629689 313663278105998233113472267)
      ·
        refine ⟨470494917158997349670208401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313663278105998233113472267 470494917158997349670208401)
        ·
          refine ⟨352871187869248012252656301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470494917158997349670208401 352871187869248012252656301)
          ·
            refine ⟨132326695450968004594746113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352871187869248012252656301 132326695450968004594746113)
            ·
              refine ⟨99245021588226003446059585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132326695450968004594746113 99245021588226003446059585)
              ·
                refine ⟨74433766191169502584544689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99245021588226003446059585 74433766191169502584544689)
                ·
                  refine ⟨55825324643377126938408517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74433766191169502584544689 55825324643377126938408517)
                  ·
                    refine ⟨10467248370633211300951597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55825324643377126938408517 10467248370633211300951597)
                    ·
                      refine ⟨3925218138987454237856849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10467248370633211300951597 3925218138987454237856849)
                      ·
                        rfl

theorem cell23_7644335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_7644335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644335 prefixEnd_7644335 := by exact prefixLift 7644335
  have htrace : WordTrace (prefixWord ++ tailWord_7644335) baseStart_7644335 baseEnd_7644335 := by
    simpa [prefixWord, tailWord_7644335, baseEnd_7644335] using wordTrace_append hprefix tailTrace_7644335
  have hstable : (prefixWord ++ tailWord_7644335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644335).length < 2 ^ (prefixWord ++ tailWord_7644335).sum := by decide
  have hdescent : baseEnd_7644335 < baseStart_7644335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644349 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 4, 2, 2]
def baseStart_7644349 : Nat := 118140960795 + 7644349 * 2 ^ 59
def prefixEnd_7644349 : Nat := 4983230072969 + 3 ^ 40 * 7644349 * 2
def baseEnd_7644349 : Nat := 3925225327716617183081785

theorem tailTrace_7644349 : CollatzResearch.WordTrace tailWord_7644349 prefixEnd_7644349 3925225327716617183081785 := by
  unfold tailWord_7644349
  simp only [CollatzResearch.WordTrace]
  refine ⟨278812313382836598714096101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185874875588557732476064067 278812313382836598714096101)
  ·
    refine ⟨52277308759281862258893019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278812313382836598714096101 52277308759281862258893019)
    ·
      refine ⟨78415963138922793388339529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52277308759281862258893019 78415963138922793388339529)
      ·
        refine ⟨58811972354192095041254647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78415963138922793388339529 58811972354192095041254647)
        ·
          refine ⟨88217958531288142561881971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58811972354192095041254647 88217958531288142561881971)
          ·
            refine ⟨132326937796932213842822957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88217958531288142561881971 132326937796932213842822957)
            ·
              refine ⟨49622601673849580191058609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132326937796932213842822957 49622601673849580191058609)
              ·
                refine ⟨37216951255387185143293957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49622601673849580191058609 37216951255387185143293957)
                ·
                  refine ⟨6978178360385097214367617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37216951255387185143293957 6978178360385097214367617)
                  ·
                    refine ⟨5233633770288822910775713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978178360385097214367617 5233633770288822910775713)
                    ·
                      refine ⟨3925225327716617183081785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233633770288822910775713 3925225327716617183081785)
                      ·
                        rfl

theorem cell23_7644349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_7644349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644349 prefixEnd_7644349 := by exact prefixLift 7644349
  have htrace : WordTrace (prefixWord ++ tailWord_7644349) baseStart_7644349 baseEnd_7644349 := by
    simpa [prefixWord, tailWord_7644349, baseEnd_7644349] using wordTrace_append hprefix tailTrace_7644349
  have hstable : (prefixWord ++ tailWord_7644349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644349).length < 2 ^ (prefixWord ++ tailWord_7644349).sum := by decide
  have hdescent : baseEnd_7644349 < baseStart_7644349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644352 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5]
def baseStart_7644352 : Nat := 118140960795 + 7644352 * 2 ^ 59
def prefixEnd_7644352 : Nat := 4983230072969 + 3 ^ 40 * 7644352 * 2
def baseEnd_7644352 : Nat := 3925226868158580671344271

theorem tailTrace_7644352 : CollatzResearch.WordTrace tailWord_7644352 prefixEnd_7644352 3925226868158580671344271 := by
  unfold tailWord_7644352
  simp only [CollatzResearch.WordTrace]
  refine ⟨139406211400912865113227655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185874948534550486817636873 139406211400912865113227655)
  ·
    refine ⟨209109317101369297669841483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139406211400912865113227655 209109317101369297669841483)
    ·
      refine ⟨313663975652053946504762225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209109317101369297669841483 313663975652053946504762225)
      ·
        refine ⟨235247981739040459878571669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313663975652053946504762225 235247981739040459878571669)
        ·
          refine ⟨11027249144017521556808047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235247981739040459878571669 11027249144017521556808047)
          ·
            refine ⟨16540873716026282335212071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11027249144017521556808047 16540873716026282335212071)
            ·
              refine ⟨24811310574039423502818107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16540873716026282335212071 24811310574039423502818107)
              ·
                refine ⟨37216965861059135254227161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24811310574039423502818107 37216965861059135254227161)
                ·
                  refine ⟨27912724395794351440670371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37216965861059135254227161 27912724395794351440670371)
                  ·
                    refine ⟨41869086593691527161005557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27912724395794351440670371 41869086593691527161005557)
                    ·
                      refine ⟨3925226868158580671344271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41869086593691527161005557 3925226868158580671344271)
                      ·
                        rfl

theorem cell23_7644352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_7644352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644352 prefixEnd_7644352 := by exact prefixLift 7644352
  have htrace : WordTrace (prefixWord ++ tailWord_7644352) baseStart_7644352 baseEnd_7644352 := by
    simpa [prefixWord, tailWord_7644352, baseEnd_7644352] using wordTrace_append hprefix tailTrace_7644352
  have hstable : (prefixWord ++ tailWord_7644352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644352).length < 2 ^ (prefixWord ++ tailWord_7644352).sum := by decide
  have hdescent : baseEnd_7644352 < baseStart_7644352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644425 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_7644425 : Nat := 118140960795 + 7644425 * 2 ^ 59
def prefixEnd_7644425 : Nat := 4983230072969 + 3 ^ 40 * 7644425 * 2
def baseEnd_7644425 : Nat := 3925264352246358885731435

theorem tailTrace_7644425 : CollatzResearch.WordTrace tailWord_7644425 prefixEnd_7644425 3925264352246358885731435 := by
  unfold tailWord_7644425
  simp only [CollatzResearch.WordTrace]
  refine ⟨278815085330561263693862729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185876723553707509129241819 278815085330561263693862729)
  ·
    refine ⟨209111313997920947770397047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278815085330561263693862729 209111313997920947770397047)
    ·
      refine ⟨313666970996881421655595571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209111313997920947770397047 313666970996881421655595571)
      ·
        refine ⟨470500456495322132483393357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313666970996881421655595571 470500456495322132483393357)
        ·
          refine ⟨176437671185745799681272509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470500456495322132483393357 176437671185745799681272509)
          ·
            refine ⟨66164126694654674880477191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176437671185745799681272509 66164126694654674880477191)
            ·
              refine ⟨99246190041982012320715787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66164126694654674880477191 99246190041982012320715787)
              ·
                refine ⟨148869285062973018481073681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99246190041982012320715787 148869285062973018481073681)
                ·
                  refine ⟨111651963797229763860805261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148869285062973018481073681 111651963797229763860805261)
                  ·
                    refine ⟨41869486423961161447801973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111651963797229763860805261 41869486423961161447801973)
                    ·
                      refine ⟨3925264352246358885731435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41869486423961161447801973 3925264352246358885731435)
                      ·
                        rfl

theorem cell23_7644425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_7644425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644425 prefixEnd_7644425 := by exact prefixLift 7644425
  have htrace : WordTrace (prefixWord ++ tailWord_7644425) baseStart_7644425 baseEnd_7644425 := by
    simpa [prefixWord, tailWord_7644425, baseEnd_7644425] using wordTrace_append hprefix tailTrace_7644425
  have hstable : (prefixWord ++ tailWord_7644425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644425).length < 2 ^ (prefixWord ++ tailWord_7644425).sum := by decide
  have hdescent : baseEnd_7644425 < baseStart_7644425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644435 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4]
def baseStart_7644435 : Nat := 118140960795 + 7644435 * 2 ^ 59
def prefixEnd_7644435 : Nat := 4983230072969 + 3 ^ 40 * 7644435 * 2
def baseEnd_7644435 : Nat := 3925269487052903846606389

theorem tailTrace_7644435 : CollatzResearch.WordTrace tailWord_7644435 prefixEnd_7644435 3925269487052903846606389 := by
  unfold tailWord_7644435
  simp only [CollatzResearch.WordTrace]
  refine ⟨278815450060525035401726759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185876966707016690267817839 278815450060525035401726759)
  ·
    refine ⟨418223175090787553102590139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278815450060525035401726759 418223175090787553102590139)
    ·
      refine ⟨627334762636181329653885209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418223175090787553102590139 627334762636181329653885209)
      ·
        refine ⟨470501071977135997240413907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627334762636181329653885209 470501071977135997240413907)
        ·
          refine ⟨705751607965703995860620861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470501071977135997240413907 705751607965703995860620861)
          ·
            refine ⟨264656852987138998447732823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705751607965703995860620861 264656852987138998447732823)
            ·
              refine ⟨396985279480708497671599235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264656852987138998447732823 396985279480708497671599235)
              ·
                refine ⟨595477919221062746507398853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396985279480708497671599235 595477919221062746507398853)
                ·
                  refine ⟨111652109853949264970137285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595477919221062746507398853 111652109853949264970137285)
                  ·
                    refine ⟨20934770597615487181900741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111652109853949264970137285 20934770597615487181900741)
                    ·
                      refine ⟨3925269487052903846606389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20934770597615487181900741 3925269487052903846606389)
                      ·
                        rfl

theorem cell23_7644435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_7644435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644435 prefixEnd_7644435 := by exact prefixLift 7644435
  have htrace : WordTrace (prefixWord ++ tailWord_7644435) baseStart_7644435 baseEnd_7644435 := by
    simpa [prefixWord, tailWord_7644435, baseEnd_7644435] using wordTrace_append hprefix tailTrace_7644435
  have hstable : (prefixWord ++ tailWord_7644435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644435).length < 2 ^ (prefixWord ++ tailWord_7644435).sum := by decide
  have hdescent : baseEnd_7644435 < baseStart_7644435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644439 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 2, 4, 2]
def baseStart_7644439 : Nat := 118140960795 + 7644439 * 2 ^ 59
def prefixEnd_7644439 : Nat := 4983230072969 + 3 ^ 40 * 7644439 * 2
def baseEnd_7644439 : Nat := 3925271540975521830956371

theorem tailTrace_7644439 : CollatzResearch.WordTrace tailWord_7644439 prefixEnd_7644439 3925271540975521830956371 := by
  unfold tailWord_7644439
  simp only [CollatzResearch.WordTrace]
  refine ⟨278815595952510544084872371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185877063968340362723248247 278815595952510544084872371)
  ·
    refine ⟨418223393928765816127308557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278815595952510544084872371 418223393928765816127308557)
    ·
      refine ⟨156833772723287181047740709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418223393928765816127308557 156833772723287181047740709)
      ·
        refine ⟨29406332385616346446451383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156833772723287181047740709 29406332385616346446451383)
        ·
          refine ⟨44109498578424519669677075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29406332385616346446451383 44109498578424519669677075)
          ·
            refine ⟨66164247867636779504515613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44109498578424519669677075 66164247867636779504515613)
            ·
              refine ⟨24811592950363792314193355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66164247867636779504515613 24811592950363792314193355)
              ·
                refine ⟨37217389425545688471290033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24811592950363792314193355 37217389425545688471290033)
                ·
                  refine ⟨27913042069159266353467525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37217389425545688471290033 27913042069159266353467525)
                  ·
                    refine ⟨5233695387967362441275161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27913042069159266353467525 5233695387967362441275161)
                    ·
                      refine ⟨3925271540975521830956371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233695387967362441275161 3925271540975521830956371)
                      ·
                        rfl

theorem cell23_7644439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_7644439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644439 prefixEnd_7644439 := by exact prefixLift 7644439
  have htrace : WordTrace (prefixWord ++ tailWord_7644439) baseStart_7644439 baseEnd_7644439 := by
    simpa [prefixWord, tailWord_7644439, baseEnd_7644439] using wordTrace_append hprefix tailTrace_7644439
  have hstable : (prefixWord ++ tailWord_7644439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644439).length < 2 ^ (prefixWord ++ tailWord_7644439).sum := by decide
  have hdescent : baseEnd_7644439 < baseStart_7644439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644456 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_7644456 : Nat := 118140960795 + 7644456 * 2 ^ 59
def prefixEnd_7644456 : Nat := 4983230072969 + 3 ^ 40 * 7644456 * 2
def baseEnd_7644456 : Nat := 3925280270146648264443793

theorem tailTrace_7644456 : CollatzResearch.WordTrace tailWord_7644456 prefixEnd_7644456 3925280270146648264443793 := by
  unfold tailWord_7644456
  simp only [CollatzResearch.WordTrace]
  refine ⟨139408107996724477994120611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185877477328965970658827481 139408107996724477994120611)
  ·
    refine ⟨209112161995086716991180917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139408107996724477994120611 209112161995086716991180917)
    ·
      refine ⟨19604265187039379717923211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209112161995086716991180917 19604265187039379717923211)
      ·
        refine ⟨29406397780559069576884817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19604265187039379717923211 29406397780559069576884817)
        ·
          refine ⟨22054798335419302182663613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29406397780559069576884817 22054798335419302182663613)
          ·
            refine ⟨8270549375782238318498855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22054798335419302182663613 8270549375782238318498855)
            ·
              refine ⟨12405824063673357477748283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8270549375782238318498855 12405824063673357477748283)
              ·
                refine ⟨18608736095510036216622425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405824063673357477748283 18608736095510036216622425)
                ·
                  refine ⟨13956552071632527162466819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18608736095510036216622425 13956552071632527162466819)
                  ·
                    refine ⟨20934828107448790743700229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13956552071632527162466819 20934828107448790743700229)
                    ·
                      refine ⟨3925280270146648264443793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20934828107448790743700229 3925280270146648264443793)
                      ·
                        rfl

theorem cell23_7644456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_7644456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644456 prefixEnd_7644456 := by exact prefixLift 7644456
  have htrace : WordTrace (prefixWord ++ tailWord_7644456) baseStart_7644456 baseEnd_7644456 := by
    simpa [prefixWord, tailWord_7644456, baseEnd_7644456] using wordTrace_append hprefix tailTrace_7644456
  have hstable : (prefixWord ++ tailWord_7644456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644456).length < 2 ^ (prefixWord ++ tailWord_7644456).sum := by decide
  have hdescent : baseEnd_7644456 < baseStart_7644456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644466 : List Nat := [3, 2, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_7644466 : Nat := 118140960795 + 7644466 * 2 ^ 59
def prefixEnd_7644466 : Nat := 4983230072969 + 3 ^ 40 * 7644466 * 2
def baseEnd_7644466 : Nat := 1308428468317731075106249

theorem tailTrace_7644466 : CollatzResearch.WordTrace tailWord_7644466 prefixEnd_7644466 1308428468317731075106249 := by
  unfold tailWord_7644466
  simp only [CollatzResearch.WordTrace]
  refine ⟨69704145180853181924026313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185877720482275151797403501 69704145180853181924026313)
  ·
    refine ⟨52278108885639886443019735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69704145180853181924026313 52278108885639886443019735)
    ·
      refine ⟨78417163328459829664529603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52278108885639886443019735 78417163328459829664529603)
      ·
        refine ⟨117625744992689744496794405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78417163328459829664529603 117625744992689744496794405)
        ·
          refine ⟨22054827186129327093148951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117625744992689744496794405 22054827186129327093148951)
          ·
            refine ⟨33082240779193990639723427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22054827186129327093148951 33082240779193990639723427)
            ·
              refine ⟨49623361168790985959585141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33082240779193990639723427 49623361168790985959585141)
              ·
                refine ⟨4652190109574154933711107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49623361168790985959585141 4652190109574154933711107)
                ·
                  refine ⟨6978285164361232400566661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652190109574154933711107 6978285164361232400566661)
                  ·
                    refine ⟨1308428468317731075106249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978285164361232400566661 1308428468317731075106249)
                    ·
                      rfl

theorem cell23_7644466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_7644466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644466 prefixEnd_7644466 := by exact prefixLift 7644466
  have htrace : WordTrace (prefixWord ++ tailWord_7644466) baseStart_7644466 baseEnd_7644466 := by
    simpa [prefixWord, tailWord_7644466, baseEnd_7644466] using wordTrace_append hprefix tailTrace_7644466
  have hstable : (prefixWord ++ tailWord_7644466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644466).length < 2 ^ (prefixWord ++ tailWord_7644466).sum := by decide
  have hdescent : baseEnd_7644466 < baseStart_7644466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644479 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 6]
def baseStart_7644479 : Nat := 118140960795 + 7644479 * 2 ^ 59
def prefixEnd_7644479 : Nat := 4983230072969 + 3 ^ 40 * 7644479 * 2
def baseEnd_7644479 : Nat := 436143564466855741606243

theorem tailTrace_7644479 : CollatzResearch.WordTrace tailWord_7644479 prefixEnd_7644479 436143564466855741606243 := by
  unfold tailWord_7644479
  simp only [CollatzResearch.WordTrace]
  refine ⟨278817054872365630916328491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185878036581577087277552327 278817054872365630916328491)
  ·
    refine ⟨418225582308548446374492737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278817054872365630916328491 418225582308548446374492737)
    ·
      refine ⟨313669186731411334780869553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418225582308548446374492737 313669186731411334780869553)
      ·
        refine ⟨235251890048558501085652165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313669186731411334780869553 235251890048558501085652165)
        ·
          refine ⟨44109729384104718953559781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235251890048558501085652165 44109729384104718953559781)
          ·
            refine ⟨8270574259519634803792459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44109729384104718953559781 8270574259519634803792459)
            ·
              refine ⟨12405861389279452205688689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8270574259519634803792459 12405861389279452205688689)
              ·
                refine ⟨9304396041959589154266517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12405861389279452205688689 9304396041959589154266517)
                ·
                  refine ⟨436143564466855741606243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9304396041959589154266517 436143564466855741606243)
                  ·
                    rfl

theorem cell23_7644479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 6].length) (baseStart_7644479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644479 prefixEnd_7644479 := by exact prefixLift 7644479
  have htrace : WordTrace (prefixWord ++ tailWord_7644479) baseStart_7644479 baseEnd_7644479 := by
    simpa [prefixWord, tailWord_7644479, baseEnd_7644479] using wordTrace_append hprefix tailTrace_7644479
  have hstable : (prefixWord ++ tailWord_7644479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644479).length < 2 ^ (prefixWord ++ tailWord_7644479).sum := by decide
  have hdescent : baseEnd_7644479 < baseStart_7644479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644489 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 3]
def baseStart_7644489 : Nat := 118140960795 + 7644489 * 2 ^ 59
def prefixEnd_7644489 : Nat := 4983230072969 + 3 ^ 40 * 7644489 * 2
def baseEnd_7644489 : Nat := 3925297215008246635331141

theorem tailTrace_7644489 : CollatzResearch.WordTrace tailWord_7644489 prefixEnd_7644489 3925297215008246635331141 := by
  unfold tailWord_7644489
  simp only [CollatzResearch.WordTrace]
  refine ⟨278817419602329402624192521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185878279734886268416128347 278817419602329402624192521)
  ·
    refine ⟨209113064701747051968144391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278817419602329402624192521 209113064701747051968144391)
    ·
      refine ⟨313669597052620577952216587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209113064701747051968144391 313669597052620577952216587)
      ·
        refine ⟨470504395578930866928324881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313669597052620577952216587 470504395578930866928324881)
        ·
          refine ⟨352878296684198150196243661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470504395578930866928324881 352878296684198150196243661)
          ·
            refine ⟨132329361256574306323591373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352878296684198150196243661 132329361256574306323591373)
            ·
              refine ⟨49623510471215364871346765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132329361256574306323591373 49623510471215364871346765)
              ·
                refine ⟨18608816426705761826755037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49623510471215364871346765 18608816426705761826755037)
                ·
                  refine ⟨6978306160014660685033139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18608816426705761826755037 6978306160014660685033139)
                  ·
                    refine ⟨10467459240021991027549709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6978306160014660685033139 10467459240021991027549709)
                    ·
                      refine ⟨3925297215008246635331141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10467459240021991027549709 3925297215008246635331141)
                      ·
                        rfl

theorem cell23_7644489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 3].length) (baseStart_7644489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644489 prefixEnd_7644489 := by exact prefixLift 7644489
  have htrace : WordTrace (prefixWord ++ tailWord_7644489) baseStart_7644489 baseEnd_7644489 := by
    simpa [prefixWord, tailWord_7644489, baseEnd_7644489] using wordTrace_append hprefix tailTrace_7644489
  have hstable : (prefixWord ++ tailWord_7644489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644489).length < 2 ^ (prefixWord ++ tailWord_7644489).sum := by decide
  have hdescent : baseEnd_7644489 < baseStart_7644489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644529 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_7644529 : Nat := 118140960795 + 7644529 * 2 ^ 59
def prefixEnd_7644529 : Nat := 4983230072969 + 3 ^ 40 * 7644529 * 2
def baseEnd_7644529 : Nat := 3925317754234426478830957

theorem tailTrace_7644529 : CollatzResearch.WordTrace tailWord_7644529 prefixEnd_7644529 3925317754234426478830957 := by
  unfold tailWord_7644529
  simp only [CollatzResearch.WordTrace]
  refine ⟨278818878522184489455648641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185879252348122992970432427 278818878522184489455648641)
  ·
    refine ⟨209114158891638367091736481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278818878522184489455648641 209114158891638367091736481)
    ·
      refine ⟨156835619168728775318802361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209114158891638367091736481 156835619168728775318802361)
      ·
        refine ⟨117626714376546581489101771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156835619168728775318802361 117626714376546581489101771)
        ·
          refine ⟨176440071564819872233652657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117626714376546581489101771 176440071564819872233652657)
          ·
            refine ⟨132330053673614904175239493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176440071564819872233652657 132330053673614904175239493)
            ·
              refine ⟨24811885063802794532857405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132330053673614904175239493 24811885063802794532857405)
              ·
                refine ⟨9304456898926047949821527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24811885063802794532857405 9304456898926047949821527)
                ·
                  refine ⟨13956685348389071924732291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9304456898926047949821527 13956685348389071924732291)
                  ·
                    refine ⟨20935028022583607887098437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13956685348389071924732291 20935028022583607887098437)
                    ·
                      refine ⟨3925317754234426478830957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20935028022583607887098437 3925317754234426478830957)
                      ·
                        rfl

theorem cell23_7644529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_7644529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644529 prefixEnd_7644529 := by exact prefixLift 7644529
  have htrace : WordTrace (prefixWord ++ tailWord_7644529) baseStart_7644529 baseEnd_7644529 := by
    simpa [prefixWord, tailWord_7644529, baseEnd_7644529] using wordTrace_append hprefix tailTrace_7644529
  have hstable : (prefixWord ++ tailWord_7644529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644529).length < 2 ^ (prefixWord ++ tailWord_7644529).sum := by decide
  have hdescent : baseEnd_7644529 < baseStart_7644529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644533 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7644533 : Nat := 118140960795 + 7644533 * 2 ^ 59
def prefixEnd_7644533 : Nat := 4983230072969 + 3 ^ 40 * 7644533 * 2
def baseEnd_7644533 : Nat := 3925319808157044463180939

theorem tailTrace_7644533 : CollatzResearch.WordTrace tailWord_7644533 prefixEnd_7644533 3925319808157044463180939 := by
  unfold tailWord_7644533
  simp only [CollatzResearch.WordTrace]
  refine ⟨278819024414169998138794253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185879349609446665425862835 278819024414169998138794253)
  ·
    refine ⟨104557134155313749302047845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278819024414169998138794253 104557134155313749302047845)
    ·
      refine ⟨19604462654121327994133971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104557134155313749302047845 19604462654121327994133971)
      ·
        refine ⟨29406693981181991991200957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19604462654121327994133971 29406693981181991991200957)
        ·
          refine ⟨11027510242943246996700359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29406693981181991991200957 11027510242943246996700359)
          ·
            refine ⟨16541265364414870495050539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11027510242943246996700359 16541265364414870495050539)
            ·
              refine ⟨24811898046622305742575809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16541265364414870495050539 24811898046622305742575809)
              ·
                refine ⟨18608923534966729306931857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24811898046622305742575809 18608923534966729306931857)
                ·
                  refine ⟨13956692651225046980198893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18608923534966729306931857 13956692651225046980198893)
                  ·
                    refine ⟨5233759744209392617574585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13956692651225046980198893 5233759744209392617574585)
                    ·
                      refine ⟨3925319808157044463180939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233759744209392617574585 3925319808157044463180939)
                      ·
                        rfl

theorem cell23_7644533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7644533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644533 prefixEnd_7644533 := by exact prefixLift 7644533
  have htrace : WordTrace (prefixWord ++ tailWord_7644533) baseStart_7644533 baseEnd_7644533 := by
    simpa [prefixWord, tailWord_7644533, baseEnd_7644533] using wordTrace_append hprefix tailTrace_7644533
  have hstable : (prefixWord ++ tailWord_7644533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644533).length < 2 ^ (prefixWord ++ tailWord_7644533).sum := by decide
  have hdescent : baseEnd_7644533 < baseStart_7644533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644539 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 2, 4]
def baseStart_7644539 : Nat := 118140960795 + 7644539 * 2 ^ 59
def prefixEnd_7644539 : Nat := 4983230072969 + 3 ^ 40 * 7644539 * 2
def baseEnd_7644539 : Nat := 1308440963013657146568637

theorem tailTrace_7644539 : CollatzResearch.WordTrace tailWord_7644539 prefixEnd_7644539 1308440963013657146568637 := by
  unfold tailWord_7644539
  simp only [CollatzResearch.WordTrace]
  refine ⟨278819243252148261163512671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185879495501432174109008447 278819243252148261163512671)
  ·
    refine ⟨418228864878222391745269007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278819243252148261163512671 418228864878222391745269007)
    ·
      refine ⟨627343297317333587617903511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418228864878222391745269007 627343297317333587617903511)
      ·
        refine ⟨941014945976000381426855267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627343297317333587617903511 941014945976000381426855267)
        ·
          refine ⟨1411522418964000572140282901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941014945976000381426855267 1411522418964000572140282901)
          ·
            refine ⟨66165113388937526819075761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1411522418964000572140282901 66165113388937526819075761)
            ·
              refine ⟨49623835041703145114306821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66165113388937526819075761 49623835041703145114306821)
              ·
                refine ⟨9304469070319339708932529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49623835041703145114306821 9304469070319339708932529)
                ·
                  refine ⟨6978351802739504781699397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9304469070319339708932529 6978351802739504781699397)
                  ·
                    refine ⟨1308440963013657146568637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978351802739504781699397 1308440963013657146568637)
                    ·
                      rfl

theorem cell23_7644539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 4].length) (baseStart_7644539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644539 prefixEnd_7644539 := by exact prefixLift 7644539
  have htrace : WordTrace (prefixWord ++ tailWord_7644539) baseStart_7644539 baseEnd_7644539 := by
    simpa [prefixWord, tailWord_7644539, baseEnd_7644539] using wordTrace_append hprefix tailTrace_7644539
  have hstable : (prefixWord ++ tailWord_7644539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644539).length < 2 ^ (prefixWord ++ tailWord_7644539).sum := by decide
  have hdescent : baseEnd_7644539 < baseStart_7644539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644552 : List Nat := [2, 1, 3, 3, 1, 2, 1, 10]
def baseStart_7644552 : Nat := 118140960795 + 7644552 * 2 ^ 59
def prefixEnd_7644552 : Nat := 4983230072969 + 3 ^ 40 * 7644552 * 2
def baseEnd_7644552 : Nat := 145382576455165921809013

theorem tailTrace_7644552 : CollatzResearch.WordTrace tailWord_7644552 prefixEnd_7644552 145382576455165921809013 := by
  unfold tailWord_7644552
  simp only [CollatzResearch.WordTrace]
  refine ⟨139409858700550582191867955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185879811600734109589157273 139409858700550582191867955)
  ·
    refine ⟨209114788050825873287801933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139409858700550582191867955 209114788050825873287801933)
    ·
      refine ⟨78418045519059702482925725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209114788050825873287801933 78418045519059702482925725)
      ·
        refine ⟨29406767069647388431097147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78418045519059702482925725 29406767069647388431097147)
        ·
          refine ⟨44110150604471082646645721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29406767069647388431097147 44110150604471082646645721)
          ·
            refine ⟨33082612953353311984984291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44110150604471082646645721 33082612953353311984984291)
            ·
              refine ⟨49623919430029967977476437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33082612953353311984984291 49623919430029967977476437)
              ·
                refine ⟨145382576455165921809013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49623919430029967977476437 145382576455165921809013)
                ·
                  rfl

theorem cell23_7644552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 10].length) (baseStart_7644552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644552 prefixEnd_7644552 := by exact prefixLift 7644552
  have htrace : WordTrace (prefixWord ++ tailWord_7644552) baseStart_7644552 baseEnd_7644552 := by
    simpa [prefixWord, tailWord_7644552, baseEnd_7644552] using wordTrace_append hprefix tailTrace_7644552
  have hstable : (prefixWord ++ tailWord_7644552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644552).length < 2 ^ (prefixWord ++ tailWord_7644552).sum := by decide
  have hdescent : baseEnd_7644552 < baseStart_7644552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644579 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 3]
def baseStart_7644579 : Nat := 118140960795 + 7644579 * 2 ^ 59
def prefixEnd_7644579 : Nat := 4983230072969 + 3 ^ 40 * 7644579 * 2
def baseEnd_7644579 : Nat := 3925343428267151283205727

theorem tailTrace_7644579 : CollatzResearch.WordTrace tailWord_7644579 prefixEnd_7644579 3925343428267151283205727 := by
  unfold tailWord_7644579
  simp only [CollatzResearch.WordTrace]
  refine ⟨278820702172003347994968791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185880468114668898663312527 278820702172003347994968791)
  ·
    refine ⟨418231053258005021992453187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278820702172003347994968791 418231053258005021992453187)
    ·
      refine ⟨627346579887007532988679781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418231053258005021992453187 627346579887007532988679781)
      ·
        refine ⟨117627483728813912435377459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627346579887007532988679781 117627483728813912435377459)
        ·
          refine ⟨176441225593220868653066189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117627483728813912435377459 176441225593220868653066189)
          ·
            refine ⟨66165459597457825744899821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176441225593220868653066189 66165459597457825744899821)
            ·
              refine ⟨24812047349046684654337433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66165459597457825744899821 24812047349046684654337433)
              ·
                refine ⟨18609035511785013490753075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24812047349046684654337433 18609035511785013490753075)
                ·
                  refine ⟨27913553267677520236129613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18609035511785013490753075 27913553267677520236129613)
                  ·
                    refine ⟨10467582475379070088548605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27913553267677520236129613 10467582475379070088548605)
                    ·
                      refine ⟨3925343428267151283205727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10467582475379070088548605 3925343428267151283205727)
                      ·
                        rfl

theorem cell23_7644579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_7644579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644579 prefixEnd_7644579 := by exact prefixLift 7644579
  have htrace : WordTrace (prefixWord ++ tailWord_7644579) baseStart_7644579 baseEnd_7644579 := by
    simpa [prefixWord, tailWord_7644579, baseEnd_7644579] using wordTrace_append hprefix tailTrace_7644579
  have hstable : (prefixWord ++ tailWord_7644579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644579).length < 2 ^ (prefixWord ++ tailWord_7644579).sum := by decide
  have hdescent : baseEnd_7644579 < baseStart_7644579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644583 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7644583 : Nat := 118140960795 + 7644583 * 2 ^ 59
def prefixEnd_7644583 : Nat := 4983230072969 + 3 ^ 40 * 7644583 * 2
def baseEnd_7644583 : Nat := 3925345482189769267555709

theorem tailTrace_7644583 : CollatzResearch.WordTrace tailWord_7644583 prefixEnd_7644583 3925345482189769267555709 := by
  unfold tailWord_7644583
  simp only [CollatzResearch.WordTrace]
  refine ⟨278820848063988856678114403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185880565375992571118742935 278820848063988856678114403)
  ·
    refine ⟨418231272095983285017171605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278820848063988856678114403 418231272095983285017171605)
    ·
      refine ⟨19604590879499216485179919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 418231272095983285017171605 19604590879499216485179919)
      ·
        refine ⟨29406886319248824727769879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19604590879499216485179919 29406886319248824727769879)
        ·
          refine ⟨44110329478873237091654819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29406886319248824727769879 44110329478873237091654819)
          ·
            refine ⟨66165494218309855637482229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44110329478873237091654819 66165494218309855637482229)
            ·
              refine ⟨6203015082966548966013959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66165494218309855637482229 6203015082966548966013959)
              ·
                refine ⟨9304522624449823449020939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203015082966548966013959 9304522624449823449020939)
                ·
                  refine ⟨13956783936674735173531409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9304522624449823449020939 13956783936674735173531409)
                  ·
                    refine ⟨10467587952506051380148557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13956783936674735173531409 10467587952506051380148557)
                    ·
                      refine ⟨3925345482189769267555709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10467587952506051380148557 3925345482189769267555709)
                      ·
                        rfl

theorem cell23_7644583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7644583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644583 prefixEnd_7644583 := by exact prefixLift 7644583
  have htrace : WordTrace (prefixWord ++ tailWord_7644583) baseStart_7644583 baseEnd_7644583 := by
    simpa [prefixWord, tailWord_7644583, baseEnd_7644583] using wordTrace_append hprefix tailTrace_7644583
  have hstable : (prefixWord ++ tailWord_7644583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644583).length < 2 ^ (prefixWord ++ tailWord_7644583).sum := by decide
  have hdescent : baseEnd_7644583 < baseStart_7644583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644597 : List Nat := [1, 3, 3, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_7644597 : Nat := 118140960795 + 7644597 * 2 ^ 59
def prefixEnd_7644597 : Nat := 4983230072969 + 3 ^ 40 * 7644597 * 2
def baseEnd_7644597 : Nat := 3925352670918932212780645

theorem tailTrace_7644597 : CollatzResearch.WordTrace tailWord_7644597 prefixEnd_7644597 3925352670918932212780645 := by
  unfold tailWord_7644597
  simp only [CollatzResearch.WordTrace]
  refine ⟨278821358685938137069124045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185880905790625424712749363 278821358685938137069124045)
  ·
    refine ⟨104558009507226801400921517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278821358685938137069124045 104558009507226801400921517)
    ·
      refine ⟨39209253565210050525345569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104558009507226801400921517 39209253565210050525345569)
      ·
        refine ⟨29406940173907537894009177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39209253565210050525345569 29406940173907537894009177)
        ·
          refine ⟨22055205130430653420506883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29406940173907537894009177 22055205130430653420506883)
          ·
            refine ⟨33082807695645980130760325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22055205130430653420506883 33082807695645980130760325)
            ·
              refine ⟨6203026442933621274517561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33082807695645980130760325 6203026442933621274517561)
              ·
                refine ⟨4652269832200215955888171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203026442933621274517561 4652269832200215955888171)
                ·
                  refine ⟨6978404748300323933832257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652269832200215955888171 6978404748300323933832257)
                  ·
                    refine ⟨5233803561225242950374193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978404748300323933832257 5233803561225242950374193)
                    ·
                      refine ⟨3925352670918932212780645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233803561225242950374193 3925352670918932212780645)
                      ·
                        rfl

theorem cell23_7644597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_7644597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644597 prefixEnd_7644597 := by exact prefixLift 7644597
  have htrace : WordTrace (prefixWord ++ tailWord_7644597) baseStart_7644597 baseEnd_7644597 := by
    simpa [prefixWord, tailWord_7644597, baseEnd_7644597] using wordTrace_append hprefix tailTrace_7644597
  have hstable : (prefixWord ++ tailWord_7644597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644597).length < 2 ^ (prefixWord ++ tailWord_7644597).sum := by decide
  have hdescent : baseEnd_7644597 < baseStart_7644597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644652 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_7644652 : Nat := 118140960795 + 7644652 * 2 ^ 59
def prefixEnd_7644652 : Nat := 4983230072969 + 3 ^ 40 * 7644652 * 2
def baseEnd_7644652 : Nat := 3925380912354929497592891

theorem tailTrace_7644652 : CollatzResearch.WordTrace tailWord_7644652 prefixEnd_7644652 3925380912354929497592891 := by
  unfold tailWord_7644652
  simp only [CollatzResearch.WordTrace]
  refine ⟨139411682350369440731188105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185882243133825920974917473 139411682350369440731188105)
  ·
    refine ⟨104558761762777080548391079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139411682350369440731188105 104558761762777080548391079)
    ·
      refine ⟨156838142644165620822586619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104558761762777080548391079 156838142644165620822586619)
      ·
        refine ⟨235257213966248431233879929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156838142644165620822586619 235257213966248431233879929)
        ·
          refine ⟨176442910474686323425409947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235257213966248431233879929 176442910474686323425409947)
          ·
            refine ⟨264664365712029485138114921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176442910474686323425409947 264664365712029485138114921)
            ·
              refine ⟨198498274284022113853586191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264664365712029485138114921 198498274284022113853586191)
              ·
                refine ⟨297747411426033170780379287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198498274284022113853586191 297747411426033170780379287)
                ·
                  refine ⟨446621117139049756170568931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297747411426033170780379287 446621117139049756170568931)
                  ·
                    refine ⟨669931675708574634255853397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446621117139049756170568931 669931675708574634255853397)
                    ·
                      refine ⟨3925380912354929497592891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 669931675708574634255853397 3925380912354929497592891)
                      ·
                        rfl

theorem cell23_7644652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_7644652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644652 prefixEnd_7644652 := by exact prefixLift 7644652
  have htrace : WordTrace (prefixWord ++ tailWord_7644652) baseStart_7644652 baseEnd_7644652 := by
    simpa [prefixWord, tailWord_7644652, baseEnd_7644652] using wordTrace_append hprefix tailTrace_7644652
  have hstable : (prefixWord ++ tailWord_7644652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644652).length < 2 ^ (prefixWord ++ tailWord_7644652).sum := by decide
  have hdescent : baseEnd_7644652 < baseStart_7644652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644689 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 2, 5]
def baseStart_7644689 : Nat := 118140960795 + 7644689 * 2 ^ 59
def prefixEnd_7644689 : Nat := 4983230072969 + 3 ^ 40 * 7644689 * 2
def baseEnd_7644689 : Nat := 1308466637046381950943407

theorem tailTrace_7644689 : CollatzResearch.WordTrace tailWord_7644689 prefixEnd_7644689 1308466637046381950943407 := by
  unfold tailWord_7644689
  simp only [CollatzResearch.WordTrace]
  refine ⟨278824714201604836781473121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185883142801069891187648747 278824714201604836781473121)
  ·
    refine ⟨209118535651203627586104841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278824714201604836781473121 209118535651203627586104841)
    ·
      refine ⟨156838901738402720689578631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209118535651203627586104841 156838901738402720689578631)
      ·
        refine ⟨235258352607604081034367947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156838901738402720689578631 235258352607604081034367947)
        ·
          refine ⟨352887528911406121551551921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235258352607604081034367947 352887528911406121551551921)
          ·
            refine ⟨264665646683554591163663941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352887528911406121551551921 264665646683554591163663941)
            ·
              refine ⟨49624808753166485843186989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264665646683554591163663941 49624808753166485843186989)
              ·
                refine ⟨18609303282437432191195121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49624808753166485843186989 18609303282437432191195121)
                ·
                  refine ⟨13956977461828074143396341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18609303282437432191195121 13956977461828074143396341)
                  ·
                    refine ⟨1308466637046381950943407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13956977461828074143396341 1308466637046381950943407)
                    ·
                      rfl

theorem cell23_7644689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_7644689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644689 prefixEnd_7644689 := by exact prefixLift 7644689
  have htrace : WordTrace (prefixWord ++ tailWord_7644689) baseStart_7644689 baseEnd_7644689 := by
    simpa [prefixWord, tailWord_7644689, baseEnd_7644689] using wordTrace_append hprefix tailTrace_7644689
  have hstable : (prefixWord ++ tailWord_7644689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644689).length < 2 ^ (prefixWord ++ tailWord_7644689).sum := by decide
  have hdescent : baseEnd_7644689 < baseStart_7644689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644693 : List Nat := [1, 3, 2, 1, 3, 4, 1, 3, 5]
def baseStart_7644693 : Nat := 118140960795 + 7644693 * 2 ^ 59
def prefixEnd_7644693 : Nat := 4983230072969 + 3 ^ 40 * 7644693 * 2
def baseEnd_7644693 : Nat := 436155773895751537464467

theorem tailTrace_7644693 : CollatzResearch.WordTrace tailWord_7644693 prefixEnd_7644693 436155773895751537464467 := by
  unfold tailWord_7644693
  simp only [CollatzResearch.WordTrace]
  refine ⟨278824860093590345464618733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185883240062393563643079155 278824860093590345464618733)
  ·
    refine ⟨104559322535096379549232025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278824860093590345464618733 104559322535096379549232025)
    ·
      refine ⟨78419491901322284661924019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104559322535096379549232025 78419491901322284661924019)
      ·
        refine ⟨117629237851983426992886029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78419491901322284661924019 117629237851983426992886029)
        ·
          refine ⟨44110964194493785122332261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117629237851983426992886029 44110964194493785122332261)
          ·
            refine ⟨8270805786467584710437299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44110964194493785122332261 8270805786467584710437299)
            ·
              refine ⟨12406208679701377065655949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8270805786467584710437299 12406208679701377065655949)
              ·
                refine ⟨4652328254888016399620981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12406208679701377065655949 4652328254888016399620981)
                ·
                  refine ⟨436155773895751537464467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4652328254888016399620981 436155773895751537464467)
                  ·
                    rfl

theorem cell23_7644693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_7644693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644693 prefixEnd_7644693 := by exact prefixLift 7644693
  have htrace : WordTrace (prefixWord ++ tailWord_7644693) baseStart_7644693 baseEnd_7644693 := by
    simpa [prefixWord, tailWord_7644693, baseEnd_7644693] using wordTrace_append hprefix tailTrace_7644693
  have hstable : (prefixWord ++ tailWord_7644693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644693).length < 2 ^ (prefixWord ++ tailWord_7644693).sum := by decide
  have hdescent : baseEnd_7644693 < baseStart_7644693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644743 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_7644743 : Nat := 118140960795 + 7644743 * 2 ^ 59
def prefixEnd_7644743 : Nat := 4983230072969 + 3 ^ 40 * 7644743 * 2
def baseEnd_7644743 : Nat := 3925427639094488641554973

theorem tailTrace_7644743 : CollatzResearch.WordTrace tailWord_7644743 prefixEnd_7644743 3925427639094488641554973 := by
  unfold tailWord_7644743
  simp only [CollatzResearch.WordTrace]
  refine ⟨278826683743409204003938883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185884455828939469335959255 278826683743409204003938883)
  ·
    refine ⟨418240025615113806005908325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278826683743409204003938883 418240025615113806005908325)
    ·
      refine ⟨78420004802833838626107811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418240025615113806005908325 78420004802833838626107811)
      ·
        refine ⟨117630007204250757939161717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78420004802833838626107811 117630007204250757939161717)
        ·
          refine ⟨11027813175398508556796411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117630007204250757939161717 11027813175398508556796411)
          ·
            refine ⟨16541719763097762835194617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11027813175398508556796411 16541719763097762835194617)
            ·
              refine ⟨12406289822323322126395963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16541719763097762835194617 12406289822323322126395963)
              ·
                refine ⟨18609434733484983189593945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12406289822323322126395963 18609434733484983189593945)
                ·
                  refine ⟨13957076050113737392195459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18609434733484983189593945 13957076050113737392195459)
                  ·
                    refine ⟨20935614075170606088293189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13957076050113737392195459 20935614075170606088293189)
                    ·
                      refine ⟨3925427639094488641554973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20935614075170606088293189 3925427639094488641554973)
                      ·
                        rfl

theorem cell23_7644743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_7644743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644743 prefixEnd_7644743 := by exact prefixLift 7644743
  have htrace : WordTrace (prefixWord ++ tailWord_7644743) baseStart_7644743 baseEnd_7644743 := by
    simpa [prefixWord, tailWord_7644743, baseEnd_7644743] using wordTrace_append hprefix tailTrace_7644743
  have hstable : (prefixWord ++ tailWord_7644743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644743).length < 2 ^ (prefixWord ++ tailWord_7644743).sum := by decide
  have hdescent : baseEnd_7644743 < baseStart_7644743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644753 : List Nat := [1, 2, 2, 1, 3, 2, 2, 5, 1, 4]
def baseStart_7644753 : Nat := 118140960795 + 7644753 * 2 ^ 59
def prefixEnd_7644753 : Nat := 4983230072969 + 3 ^ 40 * 7644753 * 2
def baseEnd_7644753 : Nat := 1308477591300344534143309

theorem tailTrace_7644753 : CollatzResearch.WordTrace tailWord_7644753 prefixEnd_7644753 1308477591300344534143309 := by
  unfold tailWord_7644753
  simp only [CollatzResearch.WordTrace]
  refine ⟨278827048473372975711802913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185884698982248650474535275 278827048473372975711802913)
  ·
    refine ⟨209120286355029731783852185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278827048473372975711802913 209120286355029731783852185)
    ·
      refine ⟨156840214766272298837889139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209120286355029731783852185 156840214766272298837889139)
      ·
        refine ⟨235260322149408448256833709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156840214766272298837889139 235260322149408448256833709)
        ·
          refine ⟨88222620806028168096312641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235260322149408448256833709 88222620806028168096312641)
          ·
            refine ⟨66166965604521126072234481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88222620806028168096312641 66166965604521126072234481)
            ·
              refine ⟨49625224203390844554175861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66166965604521126072234481 49625224203390844554175861)
              ·
                refine ⟨4652364769067891676953987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49625224203390844554175861 4652364769067891676953987)
                ·
                  refine ⟨6978547153601837515430981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652364769067891676953987 6978547153601837515430981)
                  ·
                    refine ⟨1308477591300344534143309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978547153601837515430981 1308477591300344534143309)
                    ·
                      rfl

theorem cell23_7644753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_7644753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644753 prefixEnd_7644753 := by exact prefixLift 7644753
  have htrace : WordTrace (prefixWord ++ tailWord_7644753) baseStart_7644753 baseEnd_7644753 := by
    simpa [prefixWord, tailWord_7644753, baseEnd_7644753] using wordTrace_append hprefix tailTrace_7644753
  have hstable : (prefixWord ++ tailWord_7644753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644753).length < 2 ^ (prefixWord ++ tailWord_7644753).sum := by decide
  have hdescent : baseEnd_7644753 < baseStart_7644753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644769 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7644769 : Nat := 118140960795 + 7644769 * 2 ^ 59
def prefixEnd_7644769 : Nat := 4983230072969 + 3 ^ 40 * 7644769 * 2
def baseEnd_7644769 : Nat := 3925440989591505539829853

theorem tailTrace_7644769 : CollatzResearch.WordTrace tailWord_7644769 prefixEnd_7644769 3925440989591505539829853 := by
  unfold tailWord_7644769
  simp only [CollatzResearch.WordTrace]
  refine ⟨278827632041315010444385361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185885088027543340296256907 278827632041315010444385361)
  ·
    refine ⟨209120724030986257833289021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278827632041315010444385361 209120724030986257833289021)
    ·
      refine ⟨78420271511619846687483383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209120724030986257833289021 78420271511619846687483383)
      ·
        refine ⟨117630407267429770031225075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78420271511619846687483383 117630407267429770031225075)
        ·
          refine ⟨176445610901144655046837613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117630407267429770031225075 176445610901144655046837613)
          ·
            refine ⟨66167104087929245642564105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176445610901144655046837613 66167104087929245642564105)
            ·
              refine ⟨49625328065946934231923079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66167104087929245642564105 49625328065946934231923079)
              ·
                refine ⟨74437992098920401347884619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49625328065946934231923079 74437992098920401347884619)
                ·
                  refine ⟨111656988148380602021826929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74437992098920401347884619 111656988148380602021826929)
                  ·
                    refine ⟨83742741111285451516370197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111656988148380602021826929 83742741111285451516370197)
                    ·
                      refine ⟨3925440989591505539829853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83742741111285451516370197 3925440989591505539829853)
                      ·
                        rfl

theorem cell23_7644769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7644769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644769 prefixEnd_7644769 := by exact prefixLift 7644769
  have htrace : WordTrace (prefixWord ++ tailWord_7644769) baseStart_7644769 baseEnd_7644769 := by
    simpa [prefixWord, tailWord_7644769, baseEnd_7644769] using wordTrace_append hprefix tailTrace_7644769
  have hstable : (prefixWord ++ tailWord_7644769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644769).length < 2 ^ (prefixWord ++ tailWord_7644769).sum := by decide
  have hdescent : baseEnd_7644769 < baseStart_7644769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644793 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 3]
def baseStart_7644793 : Nat := 118140960795 + 7644793 * 2 ^ 59
def prefixEnd_7644793 : Nat := 4983230072969 + 3 ^ 40 * 7644793 * 2
def baseEnd_7644793 : Nat := 3925453313127213445929743

theorem tailTrace_7644793 : CollatzResearch.WordTrace tailWord_7644793 prefixEnd_7644793 3925453313127213445929743 := by
  unfold tailWord_7644793
  simp only [CollatzResearch.WordTrace]
  refine ⟨278828507393228062543259033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185885671595485375028839355 278828507393228062543259033)
  ·
    refine ⟨209121380544921046907444275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278828507393228062543259033 209121380544921046907444275)
    ·
      refine ⟨313682070817381570361166413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209121380544921046907444275 313682070817381570361166413)
      ·
        refine ⟨117630776556518088885437405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313682070817381570361166413 117630776556518088885437405)
        ·
          refine ⟨44111541208694283332039027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117630776556518088885437405 44111541208694283332039027)
          ·
            refine ⟨66167311813041424998058541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44111541208694283332039027 66167311813041424998058541)
            ·
              refine ⟨24812741929890534374271953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66167311813041424998058541 24812741929890534374271953)
              ·
                refine ⟨18609556447417900780703965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24812741929890534374271953 18609556447417900780703965)
                ·
                  refine ⟨6978583667781712792763987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18609556447417900780703965 6978583667781712792763987)
                  ·
                    refine ⟨10467875501672569189145981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6978583667781712792763987 10467875501672569189145981)
                    ·
                      refine ⟨3925453313127213445929743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10467875501672569189145981 3925453313127213445929743)
                      ·
                        rfl

theorem cell23_7644793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_7644793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644793 prefixEnd_7644793 := by exact prefixLift 7644793
  have htrace : WordTrace (prefixWord ++ tailWord_7644793) baseStart_7644793 baseEnd_7644793 := by
    simpa [prefixWord, tailWord_7644793, baseEnd_7644793] using wordTrace_append hprefix tailTrace_7644793
  have hstable : (prefixWord ++ tailWord_7644793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644793).length < 2 ^ (prefixWord ++ tailWord_7644793).sum := by decide
  have hdescent : baseEnd_7644793 < baseStart_7644793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644796 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_7644796 : Nat := 118140960795 + 7644796 * 2 ^ 59
def prefixEnd_7644796 : Nat := 4983230072969 + 3 ^ 40 * 7644796 * 2
def baseEnd_7644796 : Nat := 1308484951189725644730743

theorem tailTrace_7644796 : CollatzResearch.WordTrace tailWord_7644796 prefixEnd_7644796 1308484951189725644730743 := by
  unfold tailWord_7644796
  simp only [CollatzResearch.WordTrace]
  refine ⟨139414308406108597027809121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185885744541478129370412161 139414308406108597027809121)
  ·
    refine ⟨104560731304581447770856841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139414308406108597027809121 104560731304581447770856841)
    ·
      refine ⟨78420548478436085828142631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104560731304581447770856841 78420548478436085828142631)
      ·
        refine ⟨117630822717654128742213947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78420548478436085828142631 117630822717654128742213947)
        ·
          refine ⟨176446234076481193113320921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117630822717654128742213947 176446234076481193113320921)
          ·
            refine ⟨132334675557360894834990691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176446234076481193113320921 132334675557360894834990691)
            ·
              refine ⟨198502013336041342252486037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132334675557360894834990691 198502013336041342252486037)
              ·
                refine ⟨9304781875126937918085283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198502013336041342252486037 9304781875126937918085283)
                ·
                  refine ⟨13957172812690406877127925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9304781875126937918085283 13957172812690406877127925)
                  ·
                    refine ⟨1308484951189725644730743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13957172812690406877127925 1308484951189725644730743)
                    ·
                      rfl

theorem cell23_7644796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_7644796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644796 prefixEnd_7644796 := by exact prefixLift 7644796
  have htrace : WordTrace (prefixWord ++ tailWord_7644796) baseStart_7644796 baseEnd_7644796 := by
    simpa [prefixWord, tailWord_7644796, baseEnd_7644796] using wordTrace_append hprefix tailTrace_7644796
  have hstable : (prefixWord ++ tailWord_7644796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644796).length < 2 ^ (prefixWord ++ tailWord_7644796).sum := by decide
  have hdescent : baseEnd_7644796 < baseStart_7644796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644816 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 8, 2]
def baseStart_7644816 : Nat := 118140960795 + 7644816 * 2 ^ 59
def prefixEnd_7644816 : Nat := 4983230072969 + 3 ^ 40 * 7644816 * 2
def baseEnd_7644816 : Nat := 3925465123182266855942137

theorem tailTrace_7644816 : CollatzResearch.WordTrace tailWord_7644816 prefixEnd_7644816 3925465123182266855942137 := by
  unfold tailWord_7644816
  simp only [CollatzResearch.WordTrace]
  refine ⟨139414673136072368735673151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185886230848096491647564201 139414673136072368735673151)
  ·
    refine ⟨209122009704108553103509727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139414673136072368735673151 209122009704108553103509727)
    ·
      refine ⟨313683014556162829655264591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209122009704108553103509727 313683014556162829655264591)
      ·
        refine ⟨470524521834244244482896887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313683014556162829655264591 470524521834244244482896887)
        ·
          refine ⟨705786782751366366724345331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470524521834244244482896887 705786782751366366724345331)
          ·
            refine ⟨1058680174127049550086517997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705786782751366366724345331 1058680174127049550086517997)
            ·
              refine ⟨397005065297643581282444249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1058680174127049550086517997 397005065297643581282444249)
              ·
                refine ⟨297753798973232685961833187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397005065297643581282444249 297753798973232685961833187)
                ·
                  refine ⟨446630698459849028942749781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297753798973232685961833187 446630698459849028942749781)
                  ·
                    refine ⟨5233953497576355807922849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 446630698459849028942749781 5233953497576355807922849)
                    ·
                      refine ⟨3925465123182266855942137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233953497576355807922849 3925465123182266855942137)
                      ·
                        rfl

theorem cell23_7644816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 8, 2].length) (baseStart_7644816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644816 prefixEnd_7644816 := by exact prefixLift 7644816
  have htrace : WordTrace (prefixWord ++ tailWord_7644816) baseStart_7644816 baseEnd_7644816 := by
    simpa [prefixWord, tailWord_7644816, baseEnd_7644816] using wordTrace_append hprefix tailTrace_7644816
  have hstable : (prefixWord ++ tailWord_7644816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644816).length < 2 ^ (prefixWord ++ tailWord_7644816).sum := by decide
  have hdescent : baseEnd_7644816 < baseStart_7644816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644836 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_7644836 : Nat := 118140960795 + 7644836 * 2 ^ 59
def prefixEnd_7644836 : Nat := 4983230072969 + 3 ^ 40 * 7644836 * 2
def baseEnd_7644836 : Nat := 3925475392795356777692045

theorem tailTrace_7644836 : CollatzResearch.WordTrace tailWord_7644836 prefixEnd_7644836 3925475392795356777692045 := by
  unfold tailWord_7644836
  simp only [CollatzResearch.WordTrace]
  refine ⟨139415037866036140443537181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185886717154714853924716241 139415037866036140443537181)
  ·
    refine ⟨52280639199763552666326443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139415037866036140443537181 52280639199763552666326443)
    ·
      refine ⟨78420958799645328999489665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52280639199763552666326443 78420958799645328999489665)
      ·
        refine ⟨58815719099733996749617249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78420958799645328999489665 58815719099733996749617249)
        ·
          refine ⟨44111789324800497562212937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58815719099733996749617249 44111789324800497562212937)
          ·
            refine ⟨33083841993600373171659703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44111789324800497562212937 33083841993600373171659703)
            ·
              refine ⟨49625762990400559757489555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33083841993600373171659703 49625762990400559757489555)
              ·
                refine ⟨74438644485600839636234333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49625762990400559757489555 74438644485600839636234333)
                ·
                  refine ⟨27914491682100314863587875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74438644485600839636234333 27914491682100314863587875)
                  ·
                    refine ⟨41871737523150472295381813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27914491682100314863587875 41871737523150472295381813)
                    ·
                      refine ⟨3925475392795356777692045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41871737523150472295381813 3925475392795356777692045)
                      ·
                        rfl

theorem cell23_7644836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_7644836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644836 prefixEnd_7644836 := by exact prefixLift 7644836
  have htrace : WordTrace (prefixWord ++ tailWord_7644836) baseStart_7644836 baseEnd_7644836 := by
    simpa [prefixWord, tailWord_7644836, baseEnd_7644836] using wordTrace_append hprefix tailTrace_7644836
  have hstable : (prefixWord ++ tailWord_7644836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644836).length < 2 ^ (prefixWord ++ tailWord_7644836).sum := by decide
  have hdescent : baseEnd_7644836 < baseStart_7644836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644850 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2]
def baseStart_7644850 : Nat := 118140960795 + 7644850 * 2 ^ 59
def prefixEnd_7644850 : Nat := 4983230072969 + 3 ^ 40 * 7644850 * 2
def baseEnd_7644850 : Nat := 3925482581524519722916981

theorem tailTrace_7644850 : CollatzResearch.WordTrace tailWord_7644850 prefixEnd_7644850 3925482581524519722916981 := by
  unfold tailWord_7644850
  simp only [CollatzResearch.WordTrace]
  refine ⟨69707646588505390319521001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185887057569347707518722669 69707646588505390319521001)
  ·
    refine ⟨52280734941379042739640751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69707646588505390319521001 52280734941379042739640751)
    ·
      refine ⟨78421102412068564109461127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52280734941379042739640751 78421102412068564109461127)
      ·
        refine ⟨117631653618102846164191691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78421102412068564109461127 117631653618102846164191691)
        ·
          refine ⟨176447480427154269246287537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117631653618102846164191691 176447480427154269246287537)
          ·
            refine ⟨132335610320365701934715653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176447480427154269246287537 132335610320365701934715653)
            ·
              refine ⟨24812926935068569112759185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132335610320365701934715653 24812926935068569112759185)
              ·
                refine ⟨18609695201301426834569389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24812926935068569112759185 18609695201301426834569389)
                ·
                  refine ⟨6978635700488035062963521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18609695201301426834569389 6978635700488035062963521)
                  ·
                    refine ⟨5233976775366026297222641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978635700488035062963521 5233976775366026297222641)
                    ·
                      refine ⟨3925482581524519722916981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5233976775366026297222641 3925482581524519722916981)
                      ·
                        rfl

theorem cell23_7644850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_7644850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644850 prefixEnd_7644850 := by exact prefixLift 7644850
  have htrace : WordTrace (prefixWord ++ tailWord_7644850) baseStart_7644850 baseEnd_7644850 := by
    simpa [prefixWord, tailWord_7644850, baseEnd_7644850] using wordTrace_append hprefix tailTrace_7644850
  have hstable : (prefixWord ++ tailWord_7644850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644850).length < 2 ^ (prefixWord ++ tailWord_7644850).sum := by decide
  have hdescent : baseEnd_7644850 < baseStart_7644850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644859 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6]
def baseStart_7644859 : Nat := 118140960795 + 7644859 * 2 ^ 59
def prefixEnd_7644859 : Nat := 4983230072969 + 3 ^ 40 * 7644859 * 2
def baseEnd_7644859 : Nat := 3925487202850410187704439

theorem tailTrace_7644859 : CollatzResearch.WordTrace tailWord_7644859 prefixEnd_7644859 3925487202850410187704439 := by
  unfold tailWord_7644859
  simp only [CollatzResearch.WordTrace]
  refine ⟨278830914610988955815161631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185887276407325970543441087 278830914610988955815161631)
  ·
    refine ⟨418246371916483433722742447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278830914610988955815161631 418246371916483433722742447)
    ·
      refine ⟨627369557874725150584113671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418246371916483433722742447 627369557874725150584113671)
      ·
        refine ⟨941054336812087725876170507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627369557874725150584113671 941054336812087725876170507)
        ·
          refine ⟨1411581505218131588814255761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941054336812087725876170507 1411581505218131588814255761)
          ·
            refine ⟨1058686128913598691610691821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411581505218131588814255761 1058686128913598691610691821)
            ·
              refine ⟨397007298342599509354009433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1058686128913598691610691821 397007298342599509354009433)
              ·
                refine ⟨297755473756949632015507075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397007298342599509354009433 297755473756949632015507075)
                ·
                  refine ⟨446633210635424448023260613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297755473756949632015507075 446633210635424448023260613)
                  ·
                    refine ⟨83743726994142084004361365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 446633210635424448023260613 83743726994142084004361365)
                    ·
                      refine ⟨3925487202850410187704439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83743726994142084004361365 3925487202850410187704439)
                      ·
                        rfl

theorem cell23_7644859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_7644859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644859 prefixEnd_7644859 := by exact prefixLift 7644859
  have htrace : WordTrace (prefixWord ++ tailWord_7644859) baseStart_7644859 baseEnd_7644859 := by
    simpa [prefixWord, tailWord_7644859, baseEnd_7644859] using wordTrace_append hprefix tailTrace_7644859
  have hstable : (prefixWord ++ tailWord_7644859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644859).length < 2 ^ (prefixWord ++ tailWord_7644859).sum := by decide
  have hdescent : baseEnd_7644859 < baseStart_7644859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644884 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7644884 : Nat := 118140960795 + 7644884 * 2 ^ 59
def prefixEnd_7644884 : Nat := 4983230072969 + 3 ^ 40 * 7644884 * 2
def baseEnd_7644884 : Nat := 3925500039866772589891825

theorem tailTrace_7644884 : CollatzResearch.WordTrace tailWord_7644884 prefixEnd_7644884 3925500039866772589891825 := by
  unfold tailWord_7644884
  simp only [CollatzResearch.WordTrace]
  refine ⟨139415913217949192542410853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185887884290598923389881137 139415913217949192542410853)
  ·
    refine ⟨26140483728365473601702035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139415913217949192542410853 26140483728365473601702035)
    ·
      refine ⟨39210725592548210402553053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26140483728365473601702035 39210725592548210402553053)
      ·
        refine ⟨14704022097205578900957395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39210725592548210402553053 14704022097205578900957395)
        ·
          refine ⟨22056033145808368351436093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14704022097205578900957395 22056033145808368351436093)
          ·
            refine ⟨8271012429678138131788535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22056033145808368351436093 8271012429678138131788535)
            ·
              refine ⟨12406518644517207197682803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271012429678138131788535 12406518644517207197682803)
              ·
                refine ⟨18609777966775810796524205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12406518644517207197682803 18609777966775810796524205)
                ·
                  refine ⟨6978666737540929048696577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18609777966775810796524205 6978666737540929048696577)
                  ·
                    refine ⟨5234000053155696786522433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978666737540929048696577 5234000053155696786522433)
                    ·
                      refine ⟨3925500039866772589891825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234000053155696786522433 3925500039866772589891825)
                      ·
                        rfl

theorem cell23_7644884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7644884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644884 prefixEnd_7644884 := by exact prefixLift 7644884
  have htrace : WordTrace (prefixWord ++ tailWord_7644884) baseStart_7644884 baseEnd_7644884 := by
    simpa [prefixWord, tailWord_7644884, baseEnd_7644884] using wordTrace_append hprefix tailTrace_7644884
  have hstable : (prefixWord ++ tailWord_7644884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644884).length < 2 ^ (prefixWord ++ tailWord_7644884).sum := by decide
  have hdescent : baseEnd_7644884 < baseStart_7644884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644900 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_7644900 : Nat := 118140960795 + 7644900 * 2 ^ 59
def prefixEnd_7644900 : Nat := 4983230072969 + 3 ^ 40 * 7644900 * 2
def baseEnd_7644900 : Nat := 3925508255557244527291751

theorem tailTrace_7644900 : CollatzResearch.WordTrace tailWord_7644900 prefixEnd_7644900 3925508255557244527291751 := by
  unfold tailWord_7644900
  simp only [CollatzResearch.WordTrace]
  refine ⟨139416205001920209908702077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185888273335893613211602769 139416205001920209908702077)
  ·
    refine ⟨52281076875720078715763279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139416205001920209908702077 52281076875720078715763279)
    ·
      refine ⟨78421615313580118073644919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52281076875720078715763279 78421615313580118073644919)
      ·
        refine ⟨117632422970370177110467379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78421615313580118073644919 117632422970370177110467379)
        ·
          refine ⟨176448634455555265665701069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117632422970370177110467379 176448634455555265665701069)
          ·
            refine ⟨66168237920833224624637901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176448634455555265665701069 66168237920833224624637901)
            ·
              refine ⟨24813089220312459234239213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66168237920833224624637901 24813089220312459234239213)
              ·
                refine ⟨9304908457617172212839705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24813089220312459234239213 9304908457617172212839705)
                ·
                  refine ⟨6978681343212879159629779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9304908457617172212839705 6978681343212879159629779)
                  ·
                    refine ⟨10468022014819318739444669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6978681343212879159629779 10468022014819318739444669)
                    ·
                      refine ⟨3925508255557244527291751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468022014819318739444669 3925508255557244527291751)
                      ·
                        rfl

theorem cell23_7644900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_7644900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644900 prefixEnd_7644900 := by exact prefixLift 7644900
  have htrace : WordTrace (prefixWord ++ tailWord_7644900) baseStart_7644900 baseEnd_7644900 := by
    simpa [prefixWord, tailWord_7644900, baseEnd_7644900] using wordTrace_append hprefix tailTrace_7644900
  have hstable : (prefixWord ++ tailWord_7644900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644900).length < 2 ^ (prefixWord ++ tailWord_7644900).sum := by decide
  have hdescent : baseEnd_7644900 < baseStart_7644900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644910 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_7644910 : Nat := 118140960795 + 7644910 * 2 ^ 59
def prefixEnd_7644910 : Nat := 4983230072969 + 3 ^ 40 * 7644910 * 2
def baseEnd_7644910 : Nat := 3925513390363789488166705

theorem tailTrace_7644910 : CollatzResearch.WordTrace tailWord_7644910 prefixEnd_7644910 3925513390363789488166705 := by
  unfold tailWord_7644910
  simp only [CollatzResearch.WordTrace]
  refine ⟨34854096841725523940658523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185888516489202794350178789 34854096841725523940658523)
  ·
    refine ⟨52281145262588285910987785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34854096841725523940658523 52281145262588285910987785)
    ·
      refine ⟨39210858946941214433240839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52281145262588285910987785 39210858946941214433240839)
      ·
        refine ⟨58816288420411821649861259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39210858946941214433240839 58816288420411821649861259)
        ·
          refine ⟨88224432630617732474791889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58816288420411821649861259 88224432630617732474791889)
          ·
            refine ⟨66168324472963299356093917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88224432630617732474791889 66168324472963299356093917)
            ·
              refine ⟨24813121677361237258535219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66168324472963299356093917 24813121677361237258535219)
              ·
                refine ⟨37219682516041855887802829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24813121677361237258535219 37219682516041855887802829)
                ·
                  refine ⟨13957380943515695957926061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37219682516041855887802829 13957380943515695957926061)
                  ·
                    refine ⟨5234017853818385984222273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13957380943515695957926061 5234017853818385984222273)
                    ·
                      refine ⟨3925513390363789488166705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234017853818385984222273 3925513390363789488166705)
                      ·
                        rfl

theorem cell23_7644910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_7644910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644910 prefixEnd_7644910 := by exact prefixLift 7644910
  have htrace : WordTrace (prefixWord ++ tailWord_7644910) baseStart_7644910 baseEnd_7644910 := by
    simpa [prefixWord, tailWord_7644910, baseEnd_7644910] using wordTrace_append hprefix tailTrace_7644910
  have hstable : (prefixWord ++ tailWord_7644910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644910).length < 2 ^ (prefixWord ++ tailWord_7644910).sum := by decide
  have hdescent : baseEnd_7644910 < baseStart_7644910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644940 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 4, 2, 2]
def baseStart_7644940 : Nat := 118140960795 + 7644940 * 2 ^ 59
def prefixEnd_7644940 : Nat := 4983230072969 + 3 ^ 40 * 7644940 * 2
def baseEnd_7644940 : Nat := 3925528794783424370791567

theorem tailTrace_7644940 : CollatzResearch.WordTrace tailWord_7644940 prefixEnd_7644940 3925528794783424370791567 := by
  unfold tailWord_7644940
  simp only [CollatzResearch.WordTrace]
  refine ⟨139416934461847753324430137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185889245949130337765906849 139416934461847753324430137)
  ·
    refine ⟨104562700846385814993322603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139416934461847753324430137 104562700846385814993322603)
    ·
      refine ⟨156844051269578722489983905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104562700846385814993322603 156844051269578722489983905)
      ·
        refine ⟨117633038452184041867487929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156844051269578722489983905 117633038452184041867487929)
        ·
          refine ⟨88224778839138031400615947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117633038452184041867487929 88224778839138031400615947)
          ·
            refine ⟨132337168258707047100923921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88224778839138031400615947 132337168258707047100923921)
            ·
              refine ⟨99252876194030285325692941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132337168258707047100923921 99252876194030285325692941)
              ·
                refine ⟨37219828572761356997134853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99252876194030285325692941 37219828572761356997134853)
                ·
                  refine ⟨6978717857392754436962785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37219828572761356997134853 6978717857392754436962785)
                  ·
                    refine ⟨5234038393044565827722089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978717857392754436962785 5234038393044565827722089)
                    ·
                      refine ⟨3925528794783424370791567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234038393044565827722089 3925528794783424370791567)
                      ·
                        rfl

theorem cell23_7644940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_7644940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644940 prefixEnd_7644940 := by exact prefixLift 7644940
  have htrace : WordTrace (prefixWord ++ tailWord_7644940) baseStart_7644940 baseEnd_7644940 := by
    simpa [prefixWord, tailWord_7644940, baseEnd_7644940] using wordTrace_append hprefix tailTrace_7644940
  have hstable : (prefixWord ++ tailWord_7644940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644940).length < 2 ^ (prefixWord ++ tailWord_7644940).sum := by decide
  have hdescent : baseEnd_7644940 < baseStart_7644940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644941 : List Nat := [1, 7, 2, 1, 2, 1, 1, 8]
def baseStart_7644941 : Nat := 118140960795 + 7644941 * 2 ^ 59
def prefixEnd_7644941 : Nat := 4983230072969 + 3 ^ 40 * 7644941 * 2
def baseEnd_7644941 : Nat := 145389974380151069143669

theorem tailTrace_7644941 : CollatzResearch.WordTrace tailWord_7644941 prefixEnd_7644941 145389974380151069143669 := by
  unfold tailWord_7644941
  simp only [CollatzResearch.WordTrace]
  refine ⟨278833905396691883819646677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185889270264461255879764451 278833905396691883819646677)
  ·
    refine ⟨6535169657734966027022969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 278833905396691883819646677 6535169657734966027022969)
    ·
      refine ⟨4901377243301224520267227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6535169657734966027022969 4901377243301224520267227)
      ·
        refine ⟨7352065864951836780400841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901377243301224520267227 7352065864951836780400841)
        ·
          refine ⟨5514049398713877585300631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7352065864951836780400841 5514049398713877585300631)
          ·
            refine ⟨8271074098070816377950947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514049398713877585300631 8271074098070816377950947)
            ·
              refine ⟨12406611147106224566926421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271074098070816377950947 12406611147106224566926421)
              ·
                refine ⟨145389974380151069143669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12406611147106224566926421 145389974380151069143669)
                ·
                  rfl

theorem cell23_7644941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 8].length) (baseStart_7644941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644941 prefixEnd_7644941 := by exact prefixLift 7644941
  have htrace : WordTrace (prefixWord ++ tailWord_7644941) baseStart_7644941 baseEnd_7644941 := by
    simpa [prefixWord, tailWord_7644941, baseEnd_7644941] using wordTrace_append hprefix tailTrace_7644941
  have hstable : (prefixWord ++ tailWord_7644941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644941).length < 2 ^ (prefixWord ++ tailWord_7644941).sum := by decide
  have hdescent : baseEnd_7644941 < baseStart_7644941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644983 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 7, 2]
def baseStart_7644983 : Nat := 118140960795 + 7644983 * 2 ^ 59
def prefixEnd_7644983 : Nat := 4983230072969 + 3 ^ 40 * 7644983 * 2
def baseEnd_7644983 : Nat := 3925550874451567702553869

theorem tailTrace_7644983 : CollatzResearch.WordTrace tailWord_7644983 prefixEnd_7644983 3925550874451567702553869 := by
  unfold tailWord_7644983
  simp only [CollatzResearch.WordTrace]
  refine ⟨278835437262539724992675603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185890291508359816661783735 278835437262539724992675603)
  ·
    refine ⟨418253155893809587489013405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278835437262539724992675603 418253155893809587489013405)
    ·
      refine ⟨156844933460178595308380027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 418253155893809587489013405 156844933460178595308380027)
      ·
        refine ⟨235267400190267892962570041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156844933460178595308380027 235267400190267892962570041)
        ·
          refine ⟨176450550142700919721927531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235267400190267892962570041 176450550142700919721927531)
          ·
            refine ⟨264675825214051379582891297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176450550142700919721927531 264675825214051379582891297)
            ·
              refine ⟨198506868910538534687168473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264675825214051379582891297 198506868910538534687168473)
              ·
                refine ⟨148880151682903901015376355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198506868910538534687168473 148880151682903901015376355)
                ·
                  refine ⟨223320227524355851523064533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148880151682903901015376355 223320227524355851523064533)
                  ·
                    refine ⟨5234067832602090270071825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 223320227524355851523064533 5234067832602090270071825)
                    ·
                      refine ⟨3925550874451567702553869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234067832602090270071825 3925550874451567702553869)
                      ·
                        rfl

theorem cell23_7644983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_7644983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644983 prefixEnd_7644983 := by exact prefixLift 7644983
  have htrace : WordTrace (prefixWord ++ tailWord_7644983) baseStart_7644983 baseEnd_7644983 := by
    simpa [prefixWord, tailWord_7644983, baseEnd_7644983] using wordTrace_append hprefix tailTrace_7644983
  have hstable : (prefixWord ++ tailWord_7644983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644983).length < 2 ^ (prefixWord ++ tailWord_7644983).sum := by decide
  have hdescent : baseEnd_7644983 < baseStart_7644983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644990 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_7644990 : Nat := 118140960795 + 7644990 * 2 ^ 59
def prefixEnd_7644990 : Nat := 4983230072969 + 3 ^ 40 * 7644990 * 2
def baseEnd_7644990 : Nat := 3925554468816149175166337

theorem tailTrace_7644990 : CollatzResearch.WordTrace tailWord_7644990 prefixEnd_7644990 3925554468816149175166337 := by
  unfold tailWord_7644990
  simp only [CollatzResearch.WordTrace]
  refine ⟨34854461571689295648522553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185890461715676243458786949 34854461571689295648522553)
  ·
    refine ⟨26140846178766971736391915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34854461571689295648522553 26140846178766971736391915)
    ·
      refine ⟨39211269268150457604587873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26140846178766971736391915 39211269268150457604587873)
      ·
        refine ⟨29408451951112843203440905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39211269268150457604587873 29408451951112843203440905)
        ·
          refine ⟨22056338963334632402580679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29408451951112843203440905 22056338963334632402580679)
          ·
            refine ⟨33084508445001948603871019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22056338963334632402580679 33084508445001948603871019)
            ·
              refine ⟨49626762667502922905806529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33084508445001948603871019 49626762667502922905806529)
              ·
                refine ⟨37220072000627192179354897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49626762667502922905806529 37220072000627192179354897)
                ·
                  refine ⟨27915054000470394134516173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37220072000627192179354897 27915054000470394134516173)
                  ·
                    refine ⟨10468145250176397800443565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27915054000470394134516173 10468145250176397800443565)
                    ·
                      refine ⟨3925554468816149175166337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468145250176397800443565 3925554468816149175166337)
                      ·
                        rfl

theorem cell23_7644990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_7644990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644990 prefixEnd_7644990 := by exact prefixLift 7644990
  have htrace : WordTrace (prefixWord ++ tailWord_7644990) baseStart_7644990 baseEnd_7644990 := by
    simpa [prefixWord, tailWord_7644990, baseEnd_7644990] using wordTrace_append hprefix tailTrace_7644990
  have hstable : (prefixWord ++ tailWord_7644990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644990).length < 2 ^ (prefixWord ++ tailWord_7644990).sum := by decide
  have hdescent : baseEnd_7644990 < baseStart_7644990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7644991 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 2, 2, 2]
def baseStart_7644991 : Nat := 118140960795 + 7644991 * 2 ^ 59
def prefixEnd_7644991 : Nat := 4983230072969 + 3 ^ 40 * 7644991 * 2
def baseEnd_7644991 : Nat := 3925554982296803671253833

theorem tailTrace_7644991 : CollatzResearch.WordTrace tailWord_7644991 prefixEnd_7644991 3925554982296803671253833 := by
  unfold tailWord_7644991
  simp only [CollatzResearch.WordTrace]
  refine ⟨278835729046510742358966827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185890486031007161572644551 278835729046510742358966827)
  ·
    refine ⟨418253593569766113538450241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278835729046510742358966827 418253593569766113538450241)
    ·
      refine ⟨313690195177324585153837681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418253593569766113538450241 313690195177324585153837681)
      ·
        refine ⟨235267646382993438865378261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313690195177324585153837681 235267646382993438865378261)
        ·
          refine ⟨5514085462101408723407303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 235267646382993438865378261 5514085462101408723407303)
          ·
            refine ⟨8271128193152113085110955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514085462101408723407303 8271128193152113085110955)
            ·
              refine ⟨12406692289728169627666433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271128193152113085110955 12406692289728169627666433)
              ·
                refine ⟨9305019217296127220749825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12406692289728169627666433 9305019217296127220749825)
                ·
                  refine ⟨6978764412972095415562369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305019217296127220749825 6978764412972095415562369)
                  ·
                    refine ⟨5234073309729071561671777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978764412972095415562369 5234073309729071561671777)
                    ·
                      refine ⟨3925554982296803671253833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234073309729071561671777 3925554982296803671253833)
                      ·
                        rfl

theorem cell23_7644991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_7644991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7644991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7644991 prefixEnd_7644991 := by exact prefixLift 7644991
  have htrace : WordTrace (prefixWord ++ tailWord_7644991) baseStart_7644991 baseEnd_7644991 := by
    simpa [prefixWord, tailWord_7644991, baseEnd_7644991] using wordTrace_append hprefix tailTrace_7644991
  have hstable : (prefixWord ++ tailWord_7644991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7644991).length < 2 ^ (prefixWord ++ tailWord_7644991).sum := by decide
  have hdescent : baseEnd_7644991 < baseStart_7644991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7644991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645013 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7645013 : Nat := 118140960795 + 7645013 * 2 ^ 59
def prefixEnd_7645013 : Nat := 4983230072969 + 3 ^ 40 * 7645013 * 2
def baseEnd_7645013 : Nat := 3925566278871202585178731

theorem tailTrace_7645013 : CollatzResearch.WordTrace tailWord_7645013 prefixEnd_7645013 3925566278871202585178731 := by
  unfold tailWord_7645013
  simp only [CollatzResearch.WordTrace]
  refine ⟨278836531452431040116267693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185891020968287360077511795 278836531452431040116267693)
  ·
    refine ⟨104563699294661640043600385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278836531452431040116267693 104563699294661640043600385)
    ·
      refine ⟨78422774470996230032700289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104563699294661640043600385 78422774470996230032700289)
      ·
        refine ⟨58817080853247172524525217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78422774470996230032700289 58817080853247172524525217)
        ·
          refine ⟨44112810639935379393393913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58817080853247172524525217 44112810639935379393393913)
          ·
            refine ⟨33084607979951534545045435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44112810639935379393393913 33084607979951534545045435)
            ·
              refine ⟨49626911969927301817568153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33084607979951534545045435 49626911969927301817568153)
              ·
                refine ⟨37220183977445476363176115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49626911969927301817568153 37220183977445476363176115)
                ·
                  refine ⟨55830275966168214544764173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37220183977445476363176115 55830275966168214544764173)
                  ·
                    refine ⟨20936353487313080454286565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55830275966168214544764173 20936353487313080454286565)
                    ·
                      refine ⟨3925566278871202585178731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20936353487313080454286565 3925566278871202585178731)
                      ·
                        rfl

theorem cell23_7645013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7645013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645013 prefixEnd_7645013 := by exact prefixLift 7645013
  have htrace : WordTrace (prefixWord ++ tailWord_7645013) baseStart_7645013 baseEnd_7645013 := by
    simpa [prefixWord, tailWord_7645013, baseEnd_7645013] using wordTrace_append hprefix tailTrace_7645013
  have hstable : (prefixWord ++ tailWord_7645013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645013).length < 2 ^ (prefixWord ++ tailWord_7645013).sum := by decide
  have hdescent : baseEnd_7645013 < baseStart_7645013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645033 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 3]
def baseStart_7645033 : Nat := 118140960795 + 7645033 * 2 ^ 59
def prefixEnd_7645033 : Nat := 4983230072969 + 3 ^ 40 * 7645033 * 2
def baseEnd_7645033 : Nat := 3925576548484292506928639

theorem tailTrace_7645033 : CollatzResearch.WordTrace tailWord_7645033 prefixEnd_7645033 3925576548484292506928639 := by
  unfold tailWord_7645033
  simp only [CollatzResearch.WordTrace]
  refine ⟨278837260912358583531995753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185891507274905722354663835 278837260912358583531995753)
  ·
    refine ⟨209127945684268937648996815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278837260912358583531995753 209127945684268937648996815)
    ·
      refine ⟨313691918526403406473495223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209127945684268937648996815 313691918526403406473495223)
      ·
        refine ⟨470537877789605109710242835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313691918526403406473495223 470537877789605109710242835)
        ·
          refine ⟨705806816684407664565364253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470537877789605109710242835 705806816684407664565364253)
          ·
            refine ⟨264677556256652874212011595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705806816684407664565364253 264677556256652874212011595)
            ·
              refine ⟨397016334384979311318017393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264677556256652874212011595 397016334384979311318017393)
              ·
                refine ⟨297762250788734483488513045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397016334384979311318017393 297762250788734483488513045)
                ·
                  refine ⟨13957605505721928913524049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 297762250788734483488513045 13957605505721928913524049)
                  ·
                    refine ⟨10468204129291446685143037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13957605505721928913524049 10468204129291446685143037)
                    ·
                      refine ⟨3925576548484292506928639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468204129291446685143037 3925576548484292506928639)
                      ·
                        rfl

theorem cell23_7645033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_7645033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645033 prefixEnd_7645033 := by exact prefixLift 7645033
  have htrace : WordTrace (prefixWord ++ tailWord_7645033) baseStart_7645033 baseEnd_7645033 := by
    simpa [prefixWord, tailWord_7645033, baseEnd_7645033] using wordTrace_append hprefix tailTrace_7645033
  have hstable : (prefixWord ++ tailWord_7645033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645033).length < 2 ^ (prefixWord ++ tailWord_7645033).sum := by decide
  have hdescent : baseEnd_7645033 < baseStart_7645033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645053 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 6]
def baseStart_7645053 : Nat := 118140960795 + 7645053 * 2 ^ 59
def prefixEnd_7645053 : Nat := 4983230072969 + 3 ^ 40 * 7645053 * 2
def baseEnd_7645053 : Nat := 436176313121931380964283

theorem tailTrace_7645053 : CollatzResearch.WordTrace tailWord_7645053 prefixEnd_7645053 436176313121931380964283 := by
  unfold tailWord_7645053
  simp only [CollatzResearch.WordTrace]
  refine ⟨278837990372286126947723813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185891993581524084631815875 278837990372286126947723813)
  ·
    refine ⟨52282123194803648802698215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278837990372286126947723813 52282123194803648802698215)
    ·
      refine ⟨78423184792205473204047323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52282123194803648802698215 78423184792205473204047323)
      ·
        refine ⟨117634777188308209806070985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78423184792205473204047323 117634777188308209806070985)
        ·
          refine ⟨88226082891231157354553239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117634777188308209806070985 88226082891231157354553239)
          ·
            refine ⟨132339124336846736031829859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88226082891231157354553239 132339124336846736031829859)
            ·
              refine ⟨198508686505270104047744789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132339124336846736031829859 198508686505270104047744789)
              ·
                refine ⟨9305094679934536127238037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198508686505270104047744789 9305094679934536127238037)
                ·
                  refine ⟨436176313121931380964283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9305094679934536127238037 436176313121931380964283)
                  ·
                    rfl

theorem cell23_7645053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_7645053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645053 prefixEnd_7645053 := by exact prefixLift 7645053
  have htrace : WordTrace (prefixWord ++ tailWord_7645053) baseStart_7645053 baseEnd_7645053 := by
    simpa [prefixWord, tailWord_7645053, baseEnd_7645053] using wordTrace_append hprefix tailTrace_7645053
  have hstable : (prefixWord ++ tailWord_7645053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645053).length < 2 ^ (prefixWord ++ tailWord_7645053).sum := by decide
  have hdescent : baseEnd_7645053 < baseStart_7645053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645113 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 3, 6]
def baseStart_7645113 : Nat := 118140960795 + 7645113 * 2 ^ 59
def prefixEnd_7645113 : Nat := 4983230072969 + 3 ^ 40 * 7645113 * 2
def baseEnd_7645113 : Nat := 1308539208978884064642757

theorem tailTrace_7645113 : CollatzResearch.WordTrace tailWord_7645113 prefixEnd_7645113 1308539208978884064642757 := by
  unfold tailWord_7645113
  simp only [CollatzResearch.WordTrace]
  refine ⟨278840178752068757194907993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185893452501379171463271995 278840178752068757194907993)
  ·
    refine ⟨209130134064051567896180995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278840178752068757194907993 209130134064051567896180995)
    ·
      refine ⟨313695201096077351844271493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209130134064051567896180995 313695201096077351844271493)
      ·
        refine ⟨58817850205514503470800905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313695201096077351844271493 58817850205514503470800905)
        ·
          refine ⟨44113387654135877603100679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58817850205514503470800905 44113387654135877603100679)
          ·
            refine ⟨66170081481203816404651019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44113387654135877603100679 66170081481203816404651019)
            ·
              refine ⟨99255122221805724606976529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66170081481203816404651019 99255122221805724606976529)
              ·
                refine ⟨74441341666354293455232397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99255122221805724606976529 74441341666354293455232397)
                ·
                  refine ⟨27915503124882860045712149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74441341666354293455232397 27915503124882860045712149)
                  ·
                    refine ⟨1308539208978884064642757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27915503124882860045712149 1308539208978884064642757)
                    ·
                      rfl

theorem cell23_7645113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_7645113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645113 prefixEnd_7645113 := by exact prefixLift 7645113
  have htrace : WordTrace (prefixWord ++ tailWord_7645113) baseStart_7645113 baseEnd_7645113 := by
    simpa [prefixWord, tailWord_7645113, baseEnd_7645113] using wordTrace_append hprefix tailTrace_7645113
  have hstable : (prefixWord ++ tailWord_7645113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645113).length < 2 ^ (prefixWord ++ tailWord_7645113).sum := by decide
  have hdescent : baseEnd_7645113 < baseStart_7645113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645123 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 3]
def baseStart_7645123 : Nat := 118140960795 + 7645123 * 2 ^ 59
def prefixEnd_7645123 : Nat := 4983230072969 + 3 ^ 40 * 7645123 * 2
def baseEnd_7645123 : Nat := 3925622761743197154803225

theorem tailTrace_7645123 : CollatzResearch.WordTrace tailWord_7645123 prefixEnd_7645123 3925622761743197154803225 := by
  unfold tailWord_7645123
  simp only [CollatzResearch.WordTrace]
  refine ⟨278840543482032528902772023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185893695654688352601848015 278840543482032528902772023)
  ·
    refine ⟨418260815223048793354158035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278840543482032528902772023 418260815223048793354158035)
    ·
      refine ⟨627391222834573190031237053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418260815223048793354158035 627391222834573190031237053)
      ·
        refine ⟨235271708562964946261713895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627391222834573190031237053 235271708562964946261713895)
        ·
          refine ⟨352907562844447419392570843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235271708562964946261713895 352907562844447419392570843)
          ·
            refine ⟨529361344266671129088856265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352907562844447419392570843 529361344266671129088856265)
            ·
              refine ⟨397021008200003346816642199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529361344266671129088856265 397021008200003346816642199)
              ·
                refine ⟨595531512300005020224963299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397021008200003346816642199 595531512300005020224963299)
                ·
                  refine ⟨893297268450007530337444949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595531512300005020224963299 893297268450007530337444949)
                  ·
                    refine ⟨10468327364648525746141933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 893297268450007530337444949 10468327364648525746141933)
                    ·
                      refine ⟨3925622761743197154803225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468327364648525746141933 3925622761743197154803225)
                      ·
                        rfl

theorem cell23_7645123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_7645123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645123 prefixEnd_7645123 := by exact prefixLift 7645123
  have htrace : WordTrace (prefixWord ++ tailWord_7645123) baseStart_7645123 baseEnd_7645123 := by
    simpa [prefixWord, tailWord_7645123, baseEnd_7645123] using wordTrace_append hprefix tailTrace_7645123
  have hstable : (prefixWord ++ tailWord_7645123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645123).length < 2 ^ (prefixWord ++ tailWord_7645123).sum := by decide
  have hdescent : baseEnd_7645123 < baseStart_7645123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645183 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_7645183 : Nat := 118140960795 + 7645183 * 2 ^ 59
def prefixEnd_7645183 : Nat := 4983230072969 + 3 ^ 40 * 7645183 * 2
def baseEnd_7645183 : Nat := 3925653570582466920052949

theorem tailTrace_7645183 : CollatzResearch.WordTrace tailWord_7645183 prefixEnd_7645183 3925653570582466920052949 := by
  unfold tailWord_7645183
  simp only [CollatzResearch.WordTrace]
  refine ⟨278842731861815159149956203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185895154574543439433304135 278842731861815159149956203)
  ·
    refine ⟨418264097792722738724934305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278842731861815159149956203 418264097792722738724934305)
    ·
      refine ⟨313698073344542054043700729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418264097792722738724934305 313698073344542054043700729)
      ·
        refine ⟨235273555008406540532775547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313698073344542054043700729 235273555008406540532775547)
        ·
          refine ⟨352910332512609810799163321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235273555008406540532775547 352910332512609810799163321)
          ·
            refine ⟨264682749384457358099372491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352910332512609810799163321 264682749384457358099372491)
            ·
              refine ⟨397024124076686037149058737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264682749384457358099372491 397024124076686037149058737)
              ·
                refine ⟨297768093057514527861794053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397024124076686037149058737 297768093057514527861794053)
                ·
                  refine ⟨55831517448283973974086385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 297768093057514527861794053 55831517448283973974086385)
                  ·
                    refine ⟨41873638086212980480564789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55831517448283973974086385 41873638086212980480564789)
                    ·
                      refine ⟨3925653570582466920052949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41873638086212980480564789 3925653570582466920052949)
                      ·
                        rfl

theorem cell23_7645183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_7645183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645183 prefixEnd_7645183 := by exact prefixLift 7645183
  have htrace : WordTrace (prefixWord ++ tailWord_7645183) baseStart_7645183 baseEnd_7645183 := by
    simpa [prefixWord, tailWord_7645183, baseEnd_7645183] using wordTrace_append hprefix tailTrace_7645183
  have hstable : (prefixWord ++ tailWord_7645183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645183).length < 2 ^ (prefixWord ++ tailWord_7645183).sum := by decide
  have hdescent : baseEnd_7645183 < baseStart_7645183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645187 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 3]
def baseStart_7645187 : Nat := 118140960795 + 7645187 * 2 ^ 59
def prefixEnd_7645187 : Nat := 4983230072969 + 3 ^ 40 * 7645187 * 2
def baseEnd_7645187 : Nat := 3925655624505084904402931

theorem tailTrace_7645187 : CollatzResearch.WordTrace tailWord_7645187 prefixEnd_7645187 3925655624505084904402931 := by
  unfold tailWord_7645187
  simp only [CollatzResearch.WordTrace]
  refine ⟨278842877753800667833101815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185895251835867111888734543 278842877753800667833101815)
  ·
    refine ⟨418264316630701001749652723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278842877753800667833101815 418264316630701001749652723)
    ·
      refine ⟨627396474946051502624479085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418264316630701001749652723 627396474946051502624479085)
      ·
        refine ⟨235273678104769313484179657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627396474946051502624479085 235273678104769313484179657)
        ·
          refine ⟨176455258578576985113134743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235273678104769313484179657 176455258578576985113134743)
          ·
            refine ⟨264682887867865477669702115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176455258578576985113134743 264682887867865477669702115)
            ·
              refine ⟨397024331801798216504553173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264682887867865477669702115 397024331801798216504553173)
              ·
                refine ⟨9305257776604645699325465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 397024331801798216504553173 9305257776604645699325465)
                ·
                  refine ⟨6978943332453484274494099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305257776604645699325465 6978943332453484274494099)
                  ·
                    refine ⟨10468414998680226411741149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6978943332453484274494099 10468414998680226411741149)
                    ·
                      refine ⟨3925655624505084904402931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468414998680226411741149 3925655624505084904402931)
                      ·
                        rfl

theorem cell23_7645187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_7645187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645187 prefixEnd_7645187 := by exact prefixLift 7645187
  have htrace : WordTrace (prefixWord ++ tailWord_7645187) baseStart_7645187 baseEnd_7645187 := by
    simpa [prefixWord, tailWord_7645187, baseEnd_7645187] using wordTrace_append hprefix tailTrace_7645187
  have hstable : (prefixWord ++ tailWord_7645187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645187).length < 2 ^ (prefixWord ++ tailWord_7645187).sum := by decide
  have hdescent : baseEnd_7645187 < baseStart_7645187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645194 : List Nat := [3, 1, 2, 2, 5, 1, 2, 7]
def baseStart_7645194 : Nat := 118140960795 + 7645194 * 2 ^ 59
def prefixEnd_7645194 : Nat := 4983230072969 + 3 ^ 40 * 7645194 * 2
def baseEnd_7645194 : Nat := 145394785884061717667237

theorem tailTrace_7645194 : CollatzResearch.WordTrace tailWord_7645194 prefixEnd_7645194 145394785884061717667237 := by
  unfold tailWord_7645194
  simp only [CollatzResearch.WordTrace]
  refine ⟨69710783266193827007151659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185895422043183538685737757 69710783266193827007151659)
  ·
    refine ⟨104566174899290740510727489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69710783266193827007151659 104566174899290740510727489)
    ·
      refine ⟨78424631174468055383045617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104566174899290740510727489 78424631174468055383045617)
      ·
        refine ⟨58818473380851041537284213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78424631174468055383045617 58818473380851041537284213)
        ·
          refine ⟨5514231879454785144120395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58818473380851041537284213 5514231879454785144120395)
          ·
            refine ⟨8271347819182177716180593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514231879454785144120395 8271347819182177716180593)
            ·
              refine ⟨6203510864386633287135445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271347819182177716180593 6203510864386633287135445)
              ·
                refine ⟨145394785884061717667237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6203510864386633287135445 145394785884061717667237)
                ·
                  rfl

theorem cell23_7645194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 7].length) (baseStart_7645194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645194 prefixEnd_7645194 := by exact prefixLift 7645194
  have htrace : WordTrace (prefixWord ++ tailWord_7645194) baseStart_7645194 baseEnd_7645194 := by
    simpa [prefixWord, tailWord_7645194, baseEnd_7645194] using wordTrace_append hprefix tailTrace_7645194
  have hstable : (prefixWord ++ tailWord_7645194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645194).length < 2 ^ (prefixWord ++ tailWord_7645194).sum := by decide
  have hdescent : baseEnd_7645194 < baseStart_7645194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645203 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 1, 8]
def baseStart_7645203 : Nat := 118140960795 + 7645203 * 2 ^ 59
def prefixEnd_7645203 : Nat := 4983230072969 + 3 ^ 40 * 7645203 * 2
def baseEnd_7645203 : Nat := 1308554613398518947267619

theorem tailTrace_7645203 : CollatzResearch.WordTrace tailWord_7645203 prefixEnd_7645203 1308554613398518947267619 := by
  unfold tailWord_7645203
  simp only [CollatzResearch.WordTrace]
  refine ⟨278843461321742702565684263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185895640881161801710456175 278843461321742702565684263)
  ·
    refine ⟨418265191982614053848526395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278843461321742702565684263 418265191982614053848526395)
    ·
      refine ⟨627397787973921080772789593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418265191982614053848526395 627397787973921080772789593)
      ·
        refine ⟨470548340980440810579592195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627397787973921080772789593 470548340980440810579592195)
        ·
          refine ⟨705822511470661215869388293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470548340980440810579592195 705822511470661215869388293)
          ·
            refine ⟨132341720900748977975510305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 705822511470661215869388293 132341720900748977975510305)
            ·
              refine ⟨99256290675561733481632729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132341720900748977975510305 99256290675561733481632729)
              ·
                refine ⟨74442218006671300111224547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99256290675561733481632729 74442218006671300111224547)
                ·
                  refine ⟨111663327010006950166836821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74442218006671300111224547 111663327010006950166836821)
                  ·
                    refine ⟨1308554613398518947267619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111663327010006950166836821 1308554613398518947267619)
                    ·
                      rfl

theorem cell23_7645203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 8].length) (baseStart_7645203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645203 prefixEnd_7645203 := by exact prefixLift 7645203
  have htrace : WordTrace (prefixWord ++ tailWord_7645203) baseStart_7645203 baseEnd_7645203 := by
    simpa [prefixWord, tailWord_7645203, baseEnd_7645203] using wordTrace_append hprefix tailTrace_7645203
  have hstable : (prefixWord ++ tailWord_7645203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645203).length < 2 ^ (prefixWord ++ tailWord_7645203).sum := by decide
  have hdescent : baseEnd_7645203 < baseStart_7645203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645205 : List Nat := [1, 3, 2, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_7645205 : Nat := 118140960795 + 7645205 * 2 ^ 59
def prefixEnd_7645205 : Nat := 4983230072969 + 3 ^ 40 * 7645205 * 2
def baseEnd_7645205 : Nat := 3925664867156865833977849

theorem tailTrace_7645205 : CollatzResearch.WordTrace tailWord_7645205 prefixEnd_7645205 3925664867156865833977849 := by
  unfold tailWord_7645205
  simp only [CollatzResearch.WordTrace]
  refine ⟨278843534267735456907257069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185895689511823637938171379 278843534267735456907257069)
  ·
    refine ⟨104566325350400796340221401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278843534267735456907257069 104566325350400796340221401)
    ·
      refine ⟨78424744012800597255166051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104566325350400796340221401 78424744012800597255166051)
      ·
        refine ⟨117637116019200895882749077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78424744012800597255166051 117637116019200895882749077)
        ·
          refine ⟨5514239813400041994503863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117637116019200895882749077 5514239813400041994503863)
          ·
            refine ⟨8271359720100062991755795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514239813400041994503863 8271359720100062991755795)
            ·
              refine ⟨12407039580150094487633693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271359720100062991755795 12407039580150094487633693)
              ·
                refine ⟨4652639842556285432862635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12407039580150094487633693 4652639842556285432862635)
                ·
                  refine ⟨6978959763834428149293953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652639842556285432862635 6978959763834428149293953)
                  ·
                    refine ⟨5234219822875821111970465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6978959763834428149293953 5234219822875821111970465)
                    ·
                      refine ⟨3925664867156865833977849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234219822875821111970465 3925664867156865833977849)
                      ·
                        rfl

theorem cell23_7645205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_7645205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645205 prefixEnd_7645205 := by exact prefixLift 7645205
  have htrace : WordTrace (prefixWord ++ tailWord_7645205) baseStart_7645205 baseEnd_7645205 := by
    simpa [prefixWord, tailWord_7645205, baseEnd_7645205] using wordTrace_append hprefix tailTrace_7645205
  have hstable : (prefixWord ++ tailWord_7645205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645205).length < 2 ^ (prefixWord ++ tailWord_7645205).sum := by decide
  have hdescent : baseEnd_7645205 < baseStart_7645205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645243 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9]
def baseStart_7645243 : Nat := 118140960795 + 7645243 * 2 ^ 59
def prefixEnd_7645243 : Nat := 4983230072969 + 3 ^ 40 * 7645243 * 2
def baseEnd_7645243 : Nat := 3925684379421736685302673

theorem tailTrace_7645243 : CollatzResearch.WordTrace tailWord_7645243 prefixEnd_7645243 3925684379421736685302673 := by
  unfold tailWord_7645243
  simp only [CollatzResearch.WordTrace]
  refine ⟨278844920241597789397140383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185896613494398526264760255 278844920241597789397140383)
  ·
    refine ⟨418267380362396684095710575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278844920241597789397140383 418267380362396684095710575)
    ·
      refine ⟨627401070543595026143565863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418267380362396684095710575 627401070543595026143565863)
      ·
        refine ⟨941101605815392539215348795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627401070543595026143565863 941101605815392539215348795)
        ·
          refine ⟨1411652408723088808823023193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941101605815392539215348795 1411652408723088808823023193)
          ·
            refine ⟨1058739306542316606617267395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411652408723088808823023193 1058739306542316606617267395)
            ·
              refine ⟨1588108959813474909925901093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058739306542316606617267395 1588108959813474909925901093)
              ·
                refine ⟨297770429965026545611106455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1588108959813474909925901093 297770429965026545611106455)
                ·
                  refine ⟨446655644947539818416659683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297770429965026545611106455 446655644947539818416659683)
                  ·
                    refine ⟨669983467421309727624989525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 446655644947539818416659683 669983467421309727624989525)
                    ·
                      refine ⟨3925684379421736685302673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 669983467421309727624989525 3925684379421736685302673)
                      ·
                        rfl

theorem cell23_7645243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_7645243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645243 prefixEnd_7645243 := by exact prefixLift 7645243
  have htrace : WordTrace (prefixWord ++ tailWord_7645243) baseStart_7645243 baseEnd_7645243 := by
    simpa [prefixWord, tailWord_7645243, baseEnd_7645243] using wordTrace_append hprefix tailTrace_7645243
  have hstable : (prefixWord ++ tailWord_7645243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645243).length < 2 ^ (prefixWord ++ tailWord_7645243).sum := by decide
  have hdescent : baseEnd_7645243 < baseStart_7645243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645284 : List Nat := [2, 3, 1, 1, 2, 1, 6, 2, 5]
def baseStart_7645284 : Nat := 118140960795 + 7645284 * 2 ^ 59
def prefixEnd_7645284 : Nat := 4983230072969 + 3 ^ 40 * 7645284 * 2
def baseEnd_7645284 : Nat := 436189492458730113876665

theorem tailTrace_7645284 : CollatzResearch.WordTrace tailWord_7645284 prefixEnd_7645284 436189492458730113876665 := by
  unfold tailWord_7645284
  simp only [CollatzResearch.WordTrace]
  refine ⟨139423207817224626699691453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185897610422966168932921937 139423207817224626699691453)
  ·
    refine ⟨52283702931459235012384295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139423207817224626699691453 52283702931459235012384295)
    ·
      refine ⟨78425554397188852518576443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52283702931459235012384295 78425554397188852518576443)
      ·
        refine ⟨117638331595783278777864665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78425554397188852518576443 117638331595783278777864665)
        ·
          refine ⟨88228748696837459083398499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117638331595783278777864665 88228748696837459083398499)
          ·
            refine ⟨132343123045256188625097749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88228748696837459083398499 132343123045256188625097749)
            ·
              refine ⟨6203583892746383841801457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132343123045256188625097749 6203583892746383841801457)
              ·
                refine ⟨4652687919559787881351093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203583892746383841801457 4652687919559787881351093)
                ·
                  refine ⟨436189492458730113876665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4652687919559787881351093 436189492458730113876665)
                  ·
                    rfl

theorem cell23_7645284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_7645284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645284 prefixEnd_7645284 := by exact prefixLift 7645284
  have htrace : WordTrace (prefixWord ++ tailWord_7645284) baseStart_7645284 baseEnd_7645284 := by
    simpa [prefixWord, tailWord_7645284, baseEnd_7645284] using wordTrace_append hprefix tailTrace_7645284
  have hstable : (prefixWord ++ tailWord_7645284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645284).length < 2 ^ (prefixWord ++ tailWord_7645284).sum := by decide
  have hdescent : baseEnd_7645284 < baseStart_7645284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645287 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_7645287 : Nat := 118140960795 + 7645287 * 2 ^ 59
def prefixEnd_7645287 : Nat := 4983230072969 + 3 ^ 40 * 7645287 * 2
def baseEnd_7645287 : Nat := 3925706972570534513152471

theorem tailTrace_7645287 : CollatzResearch.WordTrace tailWord_7645287 prefixEnd_7645287 3925706972570534513152471 := by
  unfold tailWord_7645287
  simp only [CollatzResearch.WordTrace]
  refine ⟨278846525053438384911742115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185897683368958923274494743 278846525053438384911742115)
  ·
    refine ⟨418269787580157577367613173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278846525053438384911742115 418269787580157577367613173)
    ·
      refine ⟨39212792585639772878213735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 418269787580157577367613173 39212792585639772878213735)
      ·
        refine ⟨58819188878459659317320603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39212792585639772878213735 58819188878459659317320603)
        ·
          refine ⟨88228783317689488975980905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58819188878459659317320603 88228783317689488975980905)
          ·
            refine ⟨66171587488267116731985679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88228783317689488975980905 66171587488267116731985679)
            ·
              refine ⟨99257381232400675097978519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66171587488267116731985679 99257381232400675097978519)
              ·
                refine ⟨148886071848601012646967779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99257381232400675097978519 148886071848601012646967779)
                ·
                  refine ⟨223329107772901518970451669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148886071848601012646967779 223329107772901518970451669)
                  ·
                    refine ⟨5234275963427379350869961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 223329107772901518970451669 5234275963427379350869961)
                    ·
                      refine ⟨3925706972570534513152471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234275963427379350869961 3925706972570534513152471)
                      ·
                        rfl

theorem cell23_7645287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_7645287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645287 prefixEnd_7645287 := by exact prefixLift 7645287
  have htrace : WordTrace (prefixWord ++ tailWord_7645287) baseStart_7645287 baseEnd_7645287 := by
    simpa [prefixWord, tailWord_7645287, baseEnd_7645287] using wordTrace_append hprefix tailTrace_7645287
  have hstable : (prefixWord ++ tailWord_7645287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645287).length < 2 ^ (prefixWord ++ tailWord_7645287).sum := by decide
  have hdescent : baseEnd_7645287 < baseStart_7645287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645317 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_7645317 : Nat := 118140960795 + 7645317 * 2 ^ 59
def prefixEnd_7645317 : Nat := 4983230072969 + 3 ^ 40 * 7645317 * 2
def baseEnd_7645317 : Nat := 3925722376990169395777333

theorem tailTrace_7645317 : CollatzResearch.WordTrace tailWord_7645317 prefixEnd_7645317 3925722376990169395777333 := by
  unfold tailWord_7645317
  simp only [CollatzResearch.WordTrace]
  refine ⟨278847619243329700035334205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185898412828886466690222803 278847619243329700035334205)
  ·
    refine ⟨104567857216248637513250327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278847619243329700035334205 104567857216248637513250327)
    ·
      refine ⟨156851785824372956269875491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104567857216248637513250327 156851785824372956269875491)
      ·
        refine ⟨235277678736559434404813237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156851785824372956269875491 235277678736559434404813237)
        ·
          refine ⟨22057282381552446975451241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 235277678736559434404813237 22057282381552446975451241)
          ·
            refine ⟨16542961786164335231588431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22057282381552446975451241 16542961786164335231588431)
            ·
              refine ⟨24814442679246502847382647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16542961786164335231588431 24814442679246502847382647)
              ·
                refine ⟨37221664018869754271073971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24814442679246502847382647 37221664018869754271073971)
                ·
                  refine ⟨55832496028304631406610957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37221664018869754271073971 55832496028304631406610957)
                  ·
                    refine ⟨20937186010614236777479109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55832496028304631406610957 20937186010614236777479109)
                    ·
                      refine ⟨3925722376990169395777333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20937186010614236777479109 3925722376990169395777333)
                      ·
                        rfl

theorem cell23_7645317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_7645317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645317 prefixEnd_7645317 := by exact prefixLift 7645317
  have htrace : WordTrace (prefixWord ++ tailWord_7645317) baseStart_7645317 baseEnd_7645317 := by
    simpa [prefixWord, tailWord_7645317, baseEnd_7645317] using wordTrace_append hprefix tailTrace_7645317
  have hstable : (prefixWord ++ tailWord_7645317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645317).length < 2 ^ (prefixWord ++ tailWord_7645317).sum := by decide
  have hdescent : baseEnd_7645317 < baseStart_7645317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645337 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 3]
def baseStart_7645337 : Nat := 118140960795 + 7645337 * 2 ^ 59
def prefixEnd_7645337 : Nat := 4983230072969 + 3 ^ 40 * 7645337 * 2
def baseEnd_7645337 : Nat := 3925732646603259317527241

theorem tailTrace_7645337 : CollatzResearch.WordTrace tailWord_7645337 prefixEnd_7645337 3925732646603259317527241 := by
  unfold tailWord_7645337
  simp only [CollatzResearch.WordTrace]
  refine ⟨278848348703257243451062265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185898899135504828967374843 278848348703257243451062265)
  ·
    refine ⟨209136261527442932588296699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278848348703257243451062265 209136261527442932588296699)
    ·
      refine ⟨313704392291164398882445049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209136261527442932588296699 313704392291164398882445049)
      ·
        refine ⟨235278294218373299161833787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313704392291164398882445049 235278294218373299161833787)
        ·
          refine ⟨352917441327559948742750681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235278294218373299161833787 352917441327559948742750681)
          ·
            refine ⟨264688080995669961557063011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352917441327559948742750681 264688080995669961557063011)
            ·
              refine ⟨397032121493504942335594517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264688080995669961557063011 397032121493504942335594517)
              ·
                refine ⟨18610880695008044171980993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 397032121493504942335594517 18610880695008044171980993)
                ·
                  refine ⟨13958160521256033128985745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18610880695008044171980993 13958160521256033128985745)
                  ·
                    refine ⟨10468620390942024846739309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13958160521256033128985745 10468620390942024846739309)
                    ·
                      refine ⟨3925732646603259317527241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468620390942024846739309 3925732646603259317527241)
                      ·
                        rfl

theorem cell23_7645337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_7645337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645337 prefixEnd_7645337 := by exact prefixLift 7645337
  have htrace : WordTrace (prefixWord ++ tailWord_7645337) baseStart_7645337 baseEnd_7645337 := by
    simpa [prefixWord, tailWord_7645337, baseEnd_7645337] using wordTrace_append hprefix tailTrace_7645337
  have hstable : (prefixWord ++ tailWord_7645337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645337).length < 2 ^ (prefixWord ++ tailWord_7645337).sum := by decide
  have hdescent : baseEnd_7645337 < baseStart_7645337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645344 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 3, 4]
def baseStart_7645344 : Nat := 118140960795 + 7645344 * 2 ^ 59
def prefixEnd_7645344 : Nat := 4983230072969 + 3 ^ 40 * 7645344 * 2
def baseEnd_7645344 : Nat := 1308578746989280263379903

theorem tailTrace_7645344 : CollatzResearch.WordTrace tailWord_7645344 prefixEnd_7645344 1308578746989280263379903 := by
  unfold tailWord_7645344
  simp only [CollatzResearch.WordTrace]
  refine ⟨139424302007115941823283543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185899069342821255764378057 139424302007115941823283543)
  ·
    refine ⟨209136453010673912734925315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139424302007115941823283543 209136453010673912734925315)
    ·
      refine ⟨313704679516010869102387973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209136453010673912734925315 313704679516010869102387973)
      ·
        refine ⟨58819627409252037956697745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313704679516010869102387973 58819627409252037956697745)
        ·
          refine ⟨44114720556939028467523309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58819627409252037956697745 44114720556939028467523309)
          ·
            refine ⟨16543020208852135675321241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44114720556939028467523309 16543020208852135675321241)
            ·
              refine ⟨12407265156639101756490931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16543020208852135675321241 12407265156639101756490931)
              ·
                refine ⟨18610897734958652634736397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12407265156639101756490931 18610897734958652634736397)
                ·
                  refine ⟨6979086650609494738026149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18610897734958652634736397 6979086650609494738026149)
                  ·
                    refine ⟨1308578746989280263379903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6979086650609494738026149 1308578746989280263379903)
                    ·
                      rfl

theorem cell23_7645344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_7645344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645344 prefixEnd_7645344 := by exact prefixLift 7645344
  have htrace : WordTrace (prefixWord ++ tailWord_7645344) baseStart_7645344 baseEnd_7645344 := by
    simpa [prefixWord, tailWord_7645344, baseEnd_7645344] using wordTrace_append hprefix tailTrace_7645344
  have hstable : (prefixWord ++ tailWord_7645344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645344).length < 2 ^ (prefixWord ++ tailWord_7645344).sum := by decide
  have hdescent : baseEnd_7645344 < baseStart_7645344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645387 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 1, 5]
def baseStart_7645387 : Nat := 118140960795 + 7645387 * 2 ^ 59
def prefixEnd_7645387 : Nat := 4983230072969 + 3 ^ 40 * 7645387 * 2
def baseEnd_7645387 : Nat := 1308586106878661373967337

theorem tailTrace_7645387 : CollatzResearch.WordTrace tailWord_7645387 prefixEnd_7645387 1308586106878661373967337 := by
  unfold tailWord_7645387
  simp only [CollatzResearch.WordTrace]
  refine ⟨278850172353076101990382415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185900114902050734660254943 278850172353076101990382415)
  ·
    refine ⟨418275258529614152985573623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278850172353076101990382415 418275258529614152985573623)
    ·
      refine ⟨627412887794421229478360435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418275258529614152985573623 627412887794421229478360435)
      ·
        refine ⟨941119331691631844217540653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627412887794421229478360435 941119331691631844217540653)
        ·
          refine ⟨352919749384361941581577745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941119331691631844217540653 352919749384361941581577745)
          ·
            refine ⟨264689812038271456186183309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352919749384361941581577745 264689812038271456186183309)
            ·
              refine ⟨99258679514351796069818741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264689812038271456186183309 99258679514351796069818741)
              ·
                refine ⟨9305501204470480881545507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99258679514351796069818741 9305501204470480881545507)
                ·
                  refine ⟨13958251806705721322318261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9305501204470480881545507 13958251806705721322318261)
                  ·
                    refine ⟨1308586106878661373967337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13958251806705721322318261 1308586106878661373967337)
                    ·
                      rfl

theorem cell23_7645387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 5].length) (baseStart_7645387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645387 prefixEnd_7645387 := by exact prefixLift 7645387
  have htrace : WordTrace (prefixWord ++ tailWord_7645387) baseStart_7645387 baseEnd_7645387 := by
    simpa [prefixWord, tailWord_7645387, baseEnd_7645387] using wordTrace_append hprefix tailTrace_7645387
  have hstable : (prefixWord ++ tailWord_7645387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645387).length < 2 ^ (prefixWord ++ tailWord_7645387).sum := by decide
  have hdescent : baseEnd_7645387 < baseStart_7645387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645401 : List Nat := [1, 2, 1, 2, 3, 1, 2, 6, 1, 1, 3]
def baseStart_7645401 : Nat := 118140960795 + 7645401 * 2 ^ 59
def prefixEnd_7645401 : Nat := 4983230072969 + 3 ^ 40 * 7645401 * 2
def baseEnd_7645401 : Nat := 3925765509365147067126947

theorem tailTrace_7645401 : CollatzResearch.WordTrace tailWord_7645401 prefixEnd_7645401 3925765509365147067126947 := by
  unfold tailWord_7645401
  simp only [CollatzResearch.WordTrace]
  refine ⟨278850682975025382381392057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185900455316683588254261371 278850682975025382381392057)
  ·
    refine ⟨209138012231269036786044043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278850682975025382381392057 209138012231269036786044043)
    ·
      refine ⟨313707018346903555179066065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209138012231269036786044043 313707018346903555179066065)
      ·
        refine ⟨235280263760177666384299549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313707018346903555179066065 235280263760177666384299549)
        ·
          refine ⟨88230098910066624894112331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235280263760177666384299549 88230098910066624894112331)
          ·
            refine ⟨132345148365099937341168497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88230098910066624894112331 132345148365099937341168497)
            ·
              refine ⟨99258861273824953005876373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132345148365099937341168497 99258861273824953005876373)
              ·
                refine ⟨4652759122210544672150455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99258861273824953005876373 4652759122210544672150455)
                ·
                  refine ⟨6979138683315817008225683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652759122210544672150455 6979138683315817008225683)
                  ·
                    refine ⟨10468708024973725512338525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979138683315817008225683 10468708024973725512338525)
                    ·
                      refine ⟨3925765509365147067126947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468708024973725512338525 3925765509365147067126947)
                      ·
                        rfl

theorem cell23_7645401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_7645401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645401 prefixEnd_7645401 := by exact prefixLift 7645401
  have htrace : WordTrace (prefixWord ++ tailWord_7645401) baseStart_7645401 baseEnd_7645401 := by
    simpa [prefixWord, tailWord_7645401, baseEnd_7645401] using wordTrace_append hprefix tailTrace_7645401
  have hstable : (prefixWord ++ tailWord_7645401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645401).length < 2 ^ (prefixWord ++ tailWord_7645401).sum := by decide
  have hdescent : baseEnd_7645401 < baseStart_7645401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645407 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_7645407 : Nat := 118140960795 + 7645407 * 2 ^ 59
def prefixEnd_7645407 : Nat := 4983230072969 + 3 ^ 40 * 7645407 * 2
def baseEnd_7645407 : Nat := 3925768590249074043651919

theorem tailTrace_7645407 : CollatzResearch.WordTrace tailWord_7645407 prefixEnd_7645407 3925768590249074043651919 := by
  unfold tailWord_7645407
  simp only [CollatzResearch.WordTrace]
  refine ⟨278850901813003645406110475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185900601208669096937406983 278850901813003645406110475)
  ·
    refine ⟨418276352719505468109165713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278850901813003645406110475 418276352719505468109165713)
    ·
      refine ⟨313707264539629101081874285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418276352719505468109165713 313707264539629101081874285)
      ·
        refine ⟨117640224202360912905702857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313707264539629101081874285 117640224202360912905702857)
        ·
          refine ⟨88230168151770684679277143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117640224202360912905702857 88230168151770684679277143)
          ·
            refine ⟨132345252227656027018915715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88230168151770684679277143 132345252227656027018915715)
            ·
              refine ⟨198517878341484040528373573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132345252227656027018915715 198517878341484040528373573)
              ·
                refine ⟨37222102189028257599070045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198517878341484040528373573 37222102189028257599070045)
                ·
                  refine ⟨13958288320885596599651267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37222102189028257599070045 13958288320885596599651267)
                  ·
                    refine ⟨20937432481328394899476901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13958288320885596599651267 20937432481328394899476901)
                    ·
                      refine ⟨3925768590249074043651919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20937432481328394899476901 3925768590249074043651919)
                      ·
                        rfl

theorem cell23_7645407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_7645407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645407 prefixEnd_7645407 := by exact prefixLift 7645407
  have htrace : WordTrace (prefixWord ++ tailWord_7645407) baseStart_7645407 baseEnd_7645407 := by
    simpa [prefixWord, tailWord_7645407, baseEnd_7645407] using wordTrace_append hprefix tailTrace_7645407
  have hstable : (prefixWord ++ tailWord_7645407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645407).length < 2 ^ (prefixWord ++ tailWord_7645407).sum := by decide
  have hdescent : baseEnd_7645407 < baseStart_7645407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645441 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_7645441 : Nat := 118140960795 + 7645441 * 2 ^ 59
def prefixEnd_7645441 : Nat := 4983230072969 + 3 ^ 40 * 7645441 * 2
def baseEnd_7645441 : Nat := 3925786048591326910626763

theorem tailTrace_7645441 : CollatzResearch.WordTrace tailWord_7645441 prefixEnd_7645441 3925786048591326910626763 := by
  unfold tailWord_7645441
  simp only [CollatzResearch.WordTrace]
  refine ⟨278852141894880469212848177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185901427929920312808565451 278852141894880469212848177)
  ·
    refine ⟨209139106421160351909636133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278852141894880469212848177 209139106421160351909636133)
    ·
      refine ⟨39213582453967565983056775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209139106421160351909636133 39213582453967565983056775)
      ·
        refine ⟨58820373680951348974585163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39213582453967565983056775 58820373680951348974585163)
        ·
          refine ⟨88230560521427023461877745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58820373680951348974585163 88230560521427023461877745)
          ·
            refine ⟨66172920391070267596408309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88230560521427023461877745 66172920391070267596408309)
            ·
              refine ⟨6203711286662837587163279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66172920391070267596408309 6203711286662837587163279)
              ·
                refine ⟨9305566929994256380744919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203711286662837587163279 9305566929994256380744919)
                ·
                  refine ⟨13958350394991384571117379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9305566929994256380744919 13958350394991384571117379)
                  ·
                    refine ⟨20937525592487076856676069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13958350394991384571117379 20937525592487076856676069)
                    ·
                      refine ⟨3925786048591326910626763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20937525592487076856676069 3925786048591326910626763)
                      ·
                        rfl

theorem cell23_7645441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_7645441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645441 prefixEnd_7645441 := by exact prefixLift 7645441
  have htrace : WordTrace (prefixWord ++ tailWord_7645441) baseStart_7645441 baseEnd_7645441 := by
    simpa [prefixWord, tailWord_7645441, baseEnd_7645441] using wordTrace_append hprefix tailTrace_7645441
  have hstable : (prefixWord ++ tailWord_7645441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645441).length < 2 ^ (prefixWord ++ tailWord_7645441).sum := by decide
  have hdescent : baseEnd_7645441 < baseStart_7645441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645447 : List Nat := [1, 1, 4, 5, 12]
def baseStart_7645447 : Nat := 118140960795 + 7645447 * 2 ^ 59
def prefixEnd_7645447 : Nat := 4983230072969 + 3 ^ 40 * 7645447 * 2
def baseEnd_7645447 : Nat := 5385170273628606155215

theorem tailTrace_7645447 : CollatzResearch.WordTrace tailWord_7645447 prefixEnd_7645447 5385170273628606155215 := by
  unfold tailWord_7645447
  simp only [CollatzResearch.WordTrace]
  refine ⟨278852360732858732237566595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185901573821905821491711063 278852360732858732237566595)
  ·
    refine ⟨418278541099288098356349893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278852360732858732237566595 418278541099288098356349893)
    ·
      refine ⟨78427226456116518441815605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418278541099288098356349893 78427226456116518441815605)
      ·
        refine ⟨7352552480260923603920213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78427226456116518441815605 7352552480260923603920213)
        ·
          refine ⟨5385170273628606155215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7352552480260923603920213 5385170273628606155215)
          ·
            rfl

theorem cell23_7645447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 12].length) (baseStart_7645447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645447 prefixEnd_7645447 := by exact prefixLift 7645447
  have htrace : WordTrace (prefixWord ++ tailWord_7645447) baseStart_7645447 baseEnd_7645447 := by
    simpa [prefixWord, tailWord_7645447, baseEnd_7645447] using wordTrace_append hprefix tailTrace_7645447
  have hstable : (prefixWord ++ tailWord_7645447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645447).length < 2 ^ (prefixWord ++ tailWord_7645447).sum := by decide
  have hdescent : baseEnd_7645447 < baseStart_7645447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645479 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7645479 : Nat := 118140960795 + 7645479 * 2 ^ 59
def prefixEnd_7645479 : Nat := 4983230072969 + 3 ^ 40 * 7645479 * 2
def baseEnd_7645479 : Nat := 3925805560856197761951589

theorem tailTrace_7645479 : CollatzResearch.WordTrace tailWord_7645479 prefixEnd_7645479 3925805560856197761951589 := by
  unfold tailWord_7645479
  simp only [CollatzResearch.WordTrace]
  refine ⟨278853527868742801702731491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185902351912495201135154327 278853527868742801702731491)
  ·
    refine ⟨418280291803114202554097237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278853527868742801702731491 418280291803114202554097237)
    ·
      refine ⟨4901722169567744561180827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 418280291803114202554097237 4901722169567744561180827)
      ·
        refine ⟨7352583254351616841771241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901722169567744561180827 7352583254351616841771241)
        ·
          refine ⟨5514437440763712631328431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7352583254351616841771241 5514437440763712631328431)
          ·
            refine ⟨8271656161145568946992647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514437440763712631328431 8271656161145568946992647)
            ·
              refine ⟨12407484241718353420488971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271656161145568946992647 12407484241718353420488971)
              ·
                refine ⟨18611226362577530130733457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12407484241718353420488971 18611226362577530130733457)
                ·
                  refine ⟨13958419771933147598050093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18611226362577530130733457 13958419771933147598050093)
                  ·
                    refine ⟨5234407414474930349268785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13958419771933147598050093 5234407414474930349268785)
                    ·
                      refine ⟨3925805560856197761951589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234407414474930349268785 3925805560856197761951589)
                      ·
                        rfl

theorem cell23_7645479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7645479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645479 prefixEnd_7645479 := by exact prefixLift 7645479
  have htrace : WordTrace (prefixWord ++ tailWord_7645479) baseStart_7645479 baseEnd_7645479 := by
    simpa [prefixWord, tailWord_7645479, baseEnd_7645479] using wordTrace_append hprefix tailTrace_7645479
  have hstable : (prefixWord ++ tailWord_7645479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645479).length < 2 ^ (prefixWord ++ tailWord_7645479).sum := by decide
  have hdescent : baseEnd_7645479 < baseStart_7645479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645492 : List Nat := [2, 5, 1, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_7645492 : Nat := 118140960795 + 7645492 * 2 ^ 59
def prefixEnd_7645492 : Nat := 4983230072969 + 3 ^ 40 * 7645492 * 2
def baseEnd_7645492 : Nat := 3925812236104706211089029

theorem tailTrace_7645492 : CollatzResearch.WordTrace tailWord_7645492 prefixEnd_7645492 3925812236104706211089029 := by
  unfold tailWord_7645492
  simp only [CollatzResearch.WordTrace]
  refine ⟨139427001008847852461477365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185902668011797136615303153 139427001008847852461477365)
  ·
    refine ⟨13071281344579486168263503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139427001008847852461477365 13071281344579486168263503)
    ·
      refine ⟨19606922016869229252395255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13071281344579486168263503 19606922016869229252395255)
      ·
        refine ⟨29410383025303843878592883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19606922016869229252395255 29410383025303843878592883)
        ·
          refine ⟨44115574537955765817889325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29410383025303843878592883 44115574537955765817889325)
          ·
            refine ⟨16543340451733412181708497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44115574537955765817889325 16543340451733412181708497)
            ·
              refine ⟨12407505338800059136281373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16543340451733412181708497 12407505338800059136281373)
              ·
                refine ⟨4652814502050022176105515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12407505338800059136281373 4652814502050022176105515)
                ·
                  refine ⟨6979221753075033264158273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652814502050022176105515 6979221753075033264158273)
                  ·
                    refine ⟨5234416314806274948118705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6979221753075033264158273 5234416314806274948118705)
                    ·
                      refine ⟨3925812236104706211089029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234416314806274948118705 3925812236104706211089029)
                      ·
                        rfl

theorem cell23_7645492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_7645492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645492 prefixEnd_7645492 := by exact prefixLift 7645492
  have htrace : WordTrace (prefixWord ++ tailWord_7645492) baseStart_7645492 baseEnd_7645492 := by
    simpa [prefixWord, tailWord_7645492, baseEnd_7645492] using wordTrace_append hprefix tailTrace_7645492
  have hstable : (prefixWord ++ tailWord_7645492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645492).length < 2 ^ (prefixWord ++ tailWord_7645492).sum := by decide
  have hdescent : baseEnd_7645492 < baseStart_7645492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645507 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 2, 6]
def baseStart_7645507 : Nat := 118140960795 + 7645507 * 2 ^ 59
def prefixEnd_7645507 : Nat := 4983230072969 + 3 ^ 40 * 7645507 * 2
def baseEnd_7645507 : Nat := 1308606646104841217467153

theorem tailTrace_7645507 : CollatzResearch.WordTrace tailWord_7645507 prefixEnd_7645507 1308606646104841217467153 := by
  unfold tailWord_7645507
  simp only [CollatzResearch.WordTrace]
  refine ⟨278854549112641362484750775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185903032741760908323167183 278854549112641362484750775)
  ·
    refine ⟨418281823668962043727126163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278854549112641362484750775 418281823668962043727126163)
    ·
      refine ⟨627422735503443065590689245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418281823668962043727126163 627422735503443065590689245)
      ·
        refine ⟨235283525813791149596508467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627422735503443065590689245 235283525813791149596508467)
        ·
          refine ⟨352925288720686724394762701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235283525813791149596508467 352925288720686724394762701)
          ·
            refine ⟨132346983270257521648036013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352925288720686724394762701 132346983270257521648036013)
            ·
              refine ⟨49630118726346570618013505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132346983270257521648036013 49630118726346570618013505)
              ·
                refine ⟨37222589044759927963510129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49630118726346570618013505 37222589044759927963510129)
                ·
                  refine ⟨27916941783569945972632597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37222589044759927963510129 27916941783569945972632597)
                  ·
                    refine ⟨1308606646104841217467153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27916941783569945972632597 1308606646104841217467153)
                    ·
                      rfl

theorem cell23_7645507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 6].length) (baseStart_7645507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645507 prefixEnd_7645507 := by exact prefixLift 7645507
  have htrace : WordTrace (prefixWord ++ tailWord_7645507) baseStart_7645507 baseEnd_7645507 := by
    simpa [prefixWord, tailWord_7645507, baseEnd_7645507] using wordTrace_append hprefix tailTrace_7645507
  have hstable : (prefixWord ++ tailWord_7645507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645507).length < 2 ^ (prefixWord ++ tailWord_7645507).sum := by decide
  have hdescent : baseEnd_7645507 < baseStart_7645507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645514 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_7645514 : Nat := 118140960795 + 7645514 * 2 ^ 59
def prefixEnd_7645514 : Nat := 4983230072969 + 3 ^ 40 * 7645514 * 2
def baseEnd_7645514 : Nat := 3925823532679105125013927

theorem tailTrace_7645514 : CollatzResearch.WordTrace tailWord_7645514 prefixEnd_7645514 3925823532679105125013927 := by
  unfold tailWord_7645514
  simp only [CollatzResearch.WordTrace]
  refine ⟨69713701105904000670063899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185903202949077335120170397 69713701105904000670063899)
  ·
    refine ⟨104570551658856001005095849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69713701105904000670063899 104570551658856001005095849)
    ·
      refine ⟨78427913744142000753821887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104570551658856001005095849 78427913744142000753821887)
      ·
        refine ⟨117641870616213001130732831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78427913744142000753821887 117641870616213001130732831)
        ·
          refine ⟨176462805924319501696099247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117641870616213001130732831 176462805924319501696099247)
          ·
            refine ⟨264694208886479252544148871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176462805924319501696099247 264694208886479252544148871)
            ·
              refine ⟨397041313329718878816223307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264694208886479252544148871 397041313329718878816223307)
              ·
                refine ⟨595561969994578318224334961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397041313329718878816223307 595561969994578318224334961)
                ·
                  refine ⟨446671477495933738668251221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595561969994578318224334961 446671477495933738668251221)
                  ·
                    refine ⟨5234431376905473500018569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 446671477495933738668251221 5234431376905473500018569)
                    ·
                      refine ⟨3925823532679105125013927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234431376905473500018569 3925823532679105125013927)
                      ·
                        rfl

theorem cell23_7645514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_7645514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645514 prefixEnd_7645514 := by exact prefixLift 7645514
  have htrace : WordTrace (prefixWord ++ tailWord_7645514) baseStart_7645514 baseEnd_7645514 := by
    simpa [prefixWord, tailWord_7645514, baseEnd_7645514] using wordTrace_append hprefix tailTrace_7645514
  have hstable : (prefixWord ++ tailWord_7645514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645514).length < 2 ^ (prefixWord ++ tailWord_7645514).sum := by decide
  have hdescent : baseEnd_7645514 < baseStart_7645514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645524 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_7645524 : Nat := 118140960795 + 7645524 * 2 ^ 59
def prefixEnd_7645524 : Nat := 4983230072969 + 3 ^ 40 * 7645524 * 2
def baseEnd_7645524 : Nat := 1308609555828550028629627

theorem tailTrace_7645524 : CollatzResearch.WordTrace tailWord_7645524 prefixEnd_7645524 1308609555828550028629627 := by
  unfold tailWord_7645524
  simp only [CollatzResearch.WordTrace]
  refine ⟨139427584576789887194059813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185903446102386516258746417 139427584576789887194059813)
  ·
    refine ⟨26142672108148103848886215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139427584576789887194059813 26142672108148103848886215)
    ·
      refine ⟨39214008162222155773329323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26142672108148103848886215 39214008162222155773329323)
      ·
        refine ⟨58821012243333233659993985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39214008162222155773329323 58821012243333233659993985)
        ·
          refine ⟨44115759182499925244995489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58821012243333233659993985 44115759182499925244995489)
          ·
            refine ⟨33086819386874943933746617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44115759182499925244995489 33086819386874943933746617)
            ·
              refine ⟨24815114540156207950309963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33086819386874943933746617 24815114540156207950309963)
              ·
                refine ⟨37222671810234311925464945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24815114540156207950309963 37222671810234311925464945)
                ·
                  refine ⟨27917003857675733944098709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37222671810234311925464945 27917003857675733944098709)
                  ·
                    refine ⟨1308609555828550028629627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27917003857675733944098709 1308609555828550028629627)
                    ·
                      rfl

theorem cell23_7645524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_7645524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645524 prefixEnd_7645524 := by exact prefixLift 7645524
  have htrace : WordTrace (prefixWord ++ tailWord_7645524) baseStart_7645524 baseEnd_7645524 := by
    simpa [prefixWord, tailWord_7645524, baseEnd_7645524] using wordTrace_append hprefix tailTrace_7645524
  have hstable : (prefixWord ++ tailWord_7645524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645524).length < 2 ^ (prefixWord ++ tailWord_7645524).sum := by decide
  have hdescent : baseEnd_7645524 < baseStart_7645524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645525 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_7645525 : Nat := 118140960795 + 7645525 * 2 ^ 59
def prefixEnd_7645525 : Nat := 4983230072969 + 3 ^ 40 * 7645525 * 2
def baseEnd_7645525 : Nat := 3925829180966304581976377

theorem tailTrace_7645525 : CollatzResearch.WordTrace tailWord_7645525 prefixEnd_7645525 3925829180966304581976377 := by
  unfold tailWord_7645525
  simp only [CollatzResearch.WordTrace]
  refine ⟨278855205626576151558906029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185903470417717434372604019 278855205626576151558906029)
  ·
    refine ⟨104570702109966056834589761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278855205626576151558906029 104570702109966056834589761)
    ·
      refine ⟨78428026582474542625942321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104570702109966056834589761 78428026582474542625942321)
      ·
        refine ⟨58821019936855906969456741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78428026582474542625942321 58821019936855906969456741)
        ·
          refine ⟨11028941238160482556773139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58821019936855906969456741 11028941238160482556773139)
          ·
            refine ⟨16543411857240723835159709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11028941238160482556773139 16543411857240723835159709)
            ·
              refine ⟨6203779446465271438184891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16543411857240723835159709 6203779446465271438184891)
              ·
                refine ⟨9305669169697907157277337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203779446465271438184891 9305669169697907157277337)
                ·
                  refine ⟨6979251877273430367958003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305669169697907157277337 6979251877273430367958003)
                  ·
                    refine ⟨10468877815910145551937005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979251877273430367958003 10468877815910145551937005)
                    ·
                      refine ⟨3925829180966304581976377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468877815910145551937005 3925829180966304581976377)
                      ·
                        rfl

theorem cell23_7645525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_7645525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645525 prefixEnd_7645525 := by exact prefixLift 7645525
  have htrace : WordTrace (prefixWord ++ tailWord_7645525) baseStart_7645525 baseEnd_7645525 := by
    simpa [prefixWord, tailWord_7645525, baseEnd_7645525] using wordTrace_append hprefix tailTrace_7645525
  have hstable : (prefixWord ++ tailWord_7645525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645525).length < 2 ^ (prefixWord ++ tailWord_7645525).sum := by decide
  have hdescent : baseEnd_7645525 < baseStart_7645525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645564 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_7645564 : Nat := 118140960795 + 7645564 * 2 ^ 59
def prefixEnd_7645564 : Nat := 4983230072969 + 3 ^ 40 * 7645564 * 2
def baseEnd_7645564 : Nat := 3925849206711829929388697

theorem tailTrace_7645564 : CollatzResearch.WordTrace tailWord_7645564 prefixEnd_7645564 3925849206711829929388697 := by
  unfold tailWord_7645564
  simp only [CollatzResearch.WordTrace]
  refine ⟨139428314036717430609787873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185904418715623240813050497 139428314036717430609787873)
  ·
    refine ⟨104571235527538072957340905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139428314036717430609787873 104571235527538072957340905)
    ·
      refine ⟨78428426645653554718005679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104571235527538072957340905 78428426645653554718005679)
      ·
        refine ⟨117642639968480332077008519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78428426645653554718005679 117642639968480332077008519)
        ·
          refine ⟨176463959952720498115512779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117642639968480332077008519 176463959952720498115512779)
          ·
            refine ⟨264695939929080747173269169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176463959952720498115512779 264695939929080747173269169)
            ·
              refine ⟨198521954946810560379951877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264695939929080747173269169 198521954946810560379951877)
              ·
                refine ⟨37222866552526980071240977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198521954946810560379951877 37222866552526980071240977)
                ·
                  refine ⟨27917149914395235053430733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37222866552526980071240977 27917149914395235053430733)
                  ·
                    refine ⟨10468931217898213145036525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27917149914395235053430733 10468931217898213145036525)
                    ·
                      refine ⟨3925849206711829929388697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10468931217898213145036525 3925849206711829929388697)
                      ·
                        rfl

theorem cell23_7645564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_7645564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645564 prefixEnd_7645564 := by exact prefixLift 7645564
  have htrace : WordTrace (prefixWord ++ tailWord_7645564) baseStart_7645564 baseEnd_7645564 := by
    simpa [prefixWord, tailWord_7645564, baseEnd_7645564] using wordTrace_append hprefix tailTrace_7645564
  have hstable : (prefixWord ++ tailWord_7645564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645564).length < 2 ^ (prefixWord ++ tailWord_7645564).sum := by decide
  have hdescent : baseEnd_7645564 < baseStart_7645564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645571 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 7]
def baseStart_7645571 : Nat := 118140960795 + 7645571 * 2 ^ 59
def prefixEnd_7645571 : Nat := 4983230072969 + 3 ^ 40 * 7645571 * 2
def baseEnd_7645571 : Nat := 436205866786267933555685

theorem tailTrace_7645571 : CollatzResearch.WordTrace tailWord_7645571 prefixEnd_7645571 436205866786267933555685 := by
  unfold tailWord_7645571
  simp only [CollatzResearch.WordTrace]
  refine ⟨278856883384409501415080567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185904588922939667610053711 278856883384409501415080567)
  ·
    refine ⟨418285325076614252122620851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278856883384409501415080567 418285325076614252122620851)
    ·
      refine ⟨627427987614921378183931277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418285325076614252122620851 627427987614921378183931277)
      ·
        refine ⟨235285495355595516818974229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627427987614921378183931277 235285495355595516818974229)
        ·
          refine ⟨11029007594793539850889417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235285495355595516818974229 11029007594793539850889417)
          ·
            refine ⟨8271755696095154888167063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11029007594793539850889417 8271755696095154888167063)
            ·
              refine ⟨12407633544142732332250595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271755696095154888167063 12407633544142732332250595)
              ·
                refine ⟨18611450316214098498375893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12407633544142732332250595 18611450316214098498375893)
                ·
                  refine ⟨436205866786267933555685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18611450316214098498375893 436205866786267933555685)
                  ·
                    rfl

theorem cell23_7645571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 7].length) (baseStart_7645571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645571 prefixEnd_7645571 := by exact prefixLift 7645571
  have htrace : WordTrace (prefixWord ++ tailWord_7645571) baseStart_7645571 baseEnd_7645571 := by
    simpa [prefixWord, tailWord_7645571, baseEnd_7645571] using wordTrace_append hprefix tailTrace_7645571
  have hstable : (prefixWord ++ tailWord_7645571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645571).length < 2 ^ (prefixWord ++ tailWord_7645571).sum := by decide
  have hdescent : baseEnd_7645571 < baseStart_7645571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645582 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7645582 : Nat := 118140960795 + 7645582 * 2 ^ 59
def prefixEnd_7645582 : Nat := 4983230072969 + 3 ^ 40 * 7645582 * 2
def baseEnd_7645582 : Nat := 3925858449363610858963615

theorem tailTrace_7645582 : CollatzResearch.WordTrace tailWord_7645582 prefixEnd_7645582 3925858449363610858963615 := by
  unfold tailWord_7645582
  simp only [CollatzResearch.WordTrace]
  refine ⟨34857160573421206286716375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185904856391579766862487333 34857160573421206286716375)
  ·
    refine ⟨52285740860131809430074563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34857160573421206286716375 52285740860131809430074563)
    ·
      refine ⟨78428611290197714145111845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52285740860131809430074563 78428611290197714145111845)
      ·
        refine ⟨14705364616912071402208471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78428611290197714145111845 14705364616912071402208471)
        ·
          refine ⟨22058046925368107103312707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14705364616912071402208471 22058046925368107103312707)
          ·
            refine ⟨33087070388052160654969061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22058046925368107103312707 33087070388052160654969061)
            ·
              refine ⟨6203825697759780122806699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33087070388052160654969061 6203825697759780122806699)
              ·
                refine ⟨9305738546639670184210049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203825697759780122806699 9305738546639670184210049)
                ·
                  refine ⟨6979303909979752638157537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305738546639670184210049 6979303909979752638157537)
                  ·
                    refine ⟨5234477932484814478618153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6979303909979752638157537 5234477932484814478618153)
                    ·
                      refine ⟨3925858449363610858963615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234477932484814478618153 3925858449363610858963615)
                      ·
                        rfl

theorem cell23_7645582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7645582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645582 prefixEnd_7645582 := by exact prefixLift 7645582
  have htrace : WordTrace (prefixWord ++ tailWord_7645582) baseStart_7645582 baseEnd_7645582 := by
    simpa [prefixWord, tailWord_7645582, baseEnd_7645582] using wordTrace_append hprefix tailTrace_7645582
  have hstable : (prefixWord ++ tailWord_7645582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645582).length < 2 ^ (prefixWord ++ tailWord_7645582).sum := by decide
  have hdescent : baseEnd_7645582 < baseStart_7645582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645604 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_7645604 : Nat := 118140960795 + 7645604 * 2 ^ 59
def prefixEnd_7645604 : Nat := 4983230072969 + 3 ^ 40 * 7645604 * 2
def baseEnd_7645604 : Nat := 3925869745938009772888513

theorem tailTrace_7645604 : CollatzResearch.WordTrace tailWord_7645604 prefixEnd_7645604 3925869745938009772888513 := by
  unfold tailWord_7645604
  simp only [CollatzResearch.WordTrace]
  refine ⟨139429043496644974025515933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185905391328859965367354577 139429043496644974025515933)
  ·
    refine ⟨52285891311241865259568475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139429043496644974025515933 52285891311241865259568475)
    ·
      refine ⟨78428836966862797889352713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52285891311241865259568475 78428836966862797889352713)
      ·
        refine ⟨58821627725147098417014535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78428836966862797889352713 58821627725147098417014535)
        ·
          refine ⟨88232441587720647625521803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58821627725147098417014535 88232441587720647625521803)
          ·
            refine ⟨132348662381580971438282705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88232441587720647625521803 132348662381580971438282705)
            ·
              refine ⟨99261496786185728578712029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132348662381580971438282705 99261496786185728578712029)
              ·
                refine ⟨37223061294819648217017011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99261496786185728578712029 37223061294819648217017011)
                ·
                  refine ⟨55834591942229472325525517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37223061294819648217017011 55834591942229472325525517)
                  ·
                    refine ⟨20937971978336052122072069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55834591942229472325525517 20937971978336052122072069)
                    ·
                      refine ⟨3925869745938009772888513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20937971978336052122072069 3925869745938009772888513)
                      ·
                        rfl

theorem cell23_7645604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_7645604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645604 prefixEnd_7645604 := by exact prefixLift 7645604
  have htrace : WordTrace (prefixWord ++ tailWord_7645604) baseStart_7645604 baseEnd_7645604 := by
    simpa [prefixWord, tailWord_7645604, baseEnd_7645604] using wordTrace_append hprefix tailTrace_7645604
  have hstable : (prefixWord ++ tailWord_7645604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645604).length < 2 ^ (prefixWord ++ tailWord_7645604).sum := by decide
  have hdescent : baseEnd_7645604 < baseStart_7645604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645624 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_7645624 : Nat := 118140960795 + 7645624 * 2 ^ 59
def prefixEnd_7645624 : Nat := 4983230072969 + 3 ^ 40 * 7645624 * 2
def baseEnd_7645624 : Nat := 3925880015551099694638421

theorem tailTrace_7645624 : CollatzResearch.WordTrace tailWord_7645624 prefixEnd_7645624 3925880015551099694638421 := by
  unfold tailWord_7645624
  simp only [CollatzResearch.WordTrace]
  refine ⟨139429408226608745733379963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185905877635478327644506617 139429408226608745733379963)
  ·
    refine ⟨209144112339913118600069945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139429408226608745733379963 209144112339913118600069945)
    ·
      refine ⟨156858084254934838950052459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209144112339913118600069945 156858084254934838950052459)
      ·
        refine ⟨235287126382402258425078689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156858084254934838950052459 235287126382402258425078689)
        ·
          refine ⟨176465344786801693818809017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235287126382402258425078689 176465344786801693818809017)
          ·
            refine ⟨132349008590101270364106763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176465344786801693818809017 132349008590101270364106763)
            ·
              refine ⟨198523512885151905546160145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132349008590101270364106763 198523512885151905546160145)
              ·
                refine ⟨148892634663863929159620109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198523512885151905546160145 148892634663863929159620109)
                ·
                  refine ⟨55834737998948973434857541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148892634663863929159620109 55834737998948973434857541)
                  ·
                    refine ⟨10469013374802932519035789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55834737998948973434857541 10469013374802932519035789)
                    ·
                      refine ⟨3925880015551099694638421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469013374802932519035789 3925880015551099694638421)
                      ·
                        rfl

theorem cell23_7645624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_7645624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645624 prefixEnd_7645624 := by exact prefixLift 7645624
  have htrace : WordTrace (prefixWord ++ tailWord_7645624) baseStart_7645624 baseEnd_7645624 := by
    simpa [prefixWord, tailWord_7645624, baseEnd_7645624] using wordTrace_append hprefix tailTrace_7645624
  have hstable : (prefixWord ++ tailWord_7645624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645624).length < 2 ^ (prefixWord ++ tailWord_7645624).sum := by decide
  have hdescent : baseEnd_7645624 < baseStart_7645624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645678 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_7645678 : Nat := 118140960795 + 7645678 * 2 ^ 59
def prefixEnd_7645678 : Nat := 4983230072969 + 3 ^ 40 * 7645678 * 2
def baseEnd_7645678 : Nat := 436211971500715831484797

theorem tailTrace_7645678 : CollatzResearch.WordTrace tailWord_7645678 prefixEnd_7645678 436211971500715831484797 := by
  unfold tailWord_7645678
  simp only [CollatzResearch.WordTrace]
  refine ⟨34857598249377732336153211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185907190663347905792817125 34857598249377732336153211)
  ·
    refine ⟨52286397374066598504229817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34857598249377732336153211 52286397374066598504229817)
    ·
      refine ⟨39214798030549948878172363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52286397374066598504229817 39214798030549948878172363)
      ·
        refine ⟨58822197045824923317258545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39214798030549948878172363 58822197045824923317258545)
        ·
          refine ⟨44116647784368692487943909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58822197045824923317258545 44116647784368692487943909)
          ·
            refine ⟨8271871459569129841489483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44116647784368692487943909 8271871459569129841489483)
            ·
              refine ⟨12407807189353694762234225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271871459569129841489483 12407807189353694762234225)
              ·
                refine ⟨9305855392015271071675669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12407807189353694762234225 9305855392015271071675669)
                ·
                  refine ⟨436211971500715831484797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9305855392015271071675669 436211971500715831484797)
                  ·
                    rfl

theorem cell23_7645678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_7645678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645678 prefixEnd_7645678 := by exact prefixLift 7645678
  have htrace : WordTrace (prefixWord ++ tailWord_7645678) baseStart_7645678 baseEnd_7645678 := by
    simpa [prefixWord, tailWord_7645678, baseEnd_7645678] using wordTrace_append hprefix tailTrace_7645678
  have hstable : (prefixWord ++ tailWord_7645678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645678).length < 2 ^ (prefixWord ++ tailWord_7645678).sum := by decide
  have hdescent : baseEnd_7645678 < baseStart_7645678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645688 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_7645688 : Nat := 118140960795 + 7645688 * 2 ^ 59
def prefixEnd_7645688 : Nat := 4983230072969 + 3 ^ 40 * 7645688 * 2
def baseEnd_7645688 : Nat := 3925912878312987444238127

theorem tailTrace_7645688 : CollatzResearch.WordTrace tailWord_7645688 prefixEnd_7645688 3925912878312987444238127 := by
  unfold tailWord_7645688
  simp only [CollatzResearch.WordTrace]
  refine ⟨139430575362492815198544859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185907433816657086931393145 139430575362492815198544859)
  ·
    refine ⟨209145863043739222797817289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139430575362492815198544859 209145863043739222797817289)
    ·
      refine ⟨156859397282804417098362967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209145863043739222797817289 156859397282804417098362967)
      ·
        refine ⟨235289095924206625647544451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156859397282804417098362967 235289095924206625647544451)
        ·
          refine ⟨352933643886309938471316677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235289095924206625647544451 352933643886309938471316677)
          ·
            refine ⟨66175058228683113463371877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352933643886309938471316677 66175058228683113463371877)
            ·
              refine ⟨12407823417878083774382227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66175058228683113463371877 12407823417878083774382227)
              ·
                refine ⟨18611735126817125661573341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12407823417878083774382227 18611735126817125661573341)
                ·
                  refine ⟨6979400672556422123090003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18611735126817125661573341 6979400672556422123090003)
                  ·
                    refine ⟨10469101008834633184635005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979400672556422123090003 10469101008834633184635005)
                    ·
                      refine ⟨3925912878312987444238127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469101008834633184635005 3925912878312987444238127)
                      ·
                        rfl

theorem cell23_7645688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_7645688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645688 prefixEnd_7645688 := by exact prefixLift 7645688
  have htrace : WordTrace (prefixWord ++ tailWord_7645688) baseStart_7645688 baseEnd_7645688 := by
    simpa [prefixWord, tailWord_7645688, baseEnd_7645688] using wordTrace_append hprefix tailTrace_7645688
  have hstable : (prefixWord ++ tailWord_7645688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645688).length < 2 ^ (prefixWord ++ tailWord_7645688).sum := by decide
  have hdescent : baseEnd_7645688 < baseStart_7645688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645708 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_7645708 : Nat := 118140960795 + 7645708 * 2 ^ 59
def prefixEnd_7645708 : Nat := 4983230072969 + 3 ^ 40 * 7645708 * 2
def baseEnd_7645708 : Nat := 1308641049308692455329345

theorem tailTrace_7645708 : CollatzResearch.WordTrace tailWord_7645708 prefixEnd_7645708 1308641049308692455329345 := by
  unfold tailWord_7645708
  simp only [CollatzResearch.WordTrace]
  refine ⟨139430940092456586906408889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185907920123275449208545185 139430940092456586906408889)
  ·
    refine ⟨104573205069342440179806667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139430940092456586906408889 104573205069342440179806667)
    ·
      refine ⟨156859807604013660269710001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104573205069342440179806667 156859807604013660269710001)
      ·
        refine ⟨117644855703010245202282501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156859807604013660269710001 117644855703010245202282501)
        ·
          refine ⟨22058410444314420975427969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117644855703010245202282501 22058410444314420975427969)
          ·
            refine ⟨16543807833235815731570977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22058410444314420975427969 16543807833235815731570977)
            ·
              refine ⟨12407855874926861798678233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16543807833235815731570977 12407855874926861798678233)
              ·
                refine ⟨9305891906195146349008675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12407855874926861798678233 9305891906195146349008675)
                ·
                  refine ⟨13958837859292719523513013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9305891906195146349008675 13958837859292719523513013)
                  ·
                    refine ⟨1308641049308692455329345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13958837859292719523513013 1308641049308692455329345)
                    ·
                      rfl

theorem cell23_7645708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_7645708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645708 prefixEnd_7645708 := by exact prefixLift 7645708
  have htrace : WordTrace (prefixWord ++ tailWord_7645708) baseStart_7645708 baseEnd_7645708 := by
    simpa [prefixWord, tailWord_7645708, baseEnd_7645708] using wordTrace_append hprefix tailTrace_7645708
  have hstable : (prefixWord ++ tailWord_7645708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645708).length < 2 ^ (prefixWord ++ tailWord_7645708).sum := by decide
  have hdescent : baseEnd_7645708 < baseStart_7645708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645711 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 4]
def baseStart_7645711 : Nat := 118140960795 + 7645711 * 2 ^ 59
def prefixEnd_7645711 : Nat := 4983230072969 + 3 ^ 40 * 7645711 * 2
def baseEnd_7645711 : Nat := 3925924688368040854250521

theorem tailTrace_7645711 : CollatzResearch.WordTrace tailWord_7645711 prefixEnd_7645711 3925924688368040854250521 := by
  unfold tailWord_7645711
  simp only [CollatzResearch.WordTrace]
  refine ⟨278861989603902305325176987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185907993069268203550117991 278861989603902305325176987)
  ·
    refine ⟨418292984405853457987765481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278861989603902305325176987 418292984405853457987765481)
    ·
      refine ⟨313719738304390093490824111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418292984405853457987765481 313719738304390093490824111)
      ·
        refine ⟨470579607456585140236236167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313719738304390093490824111 470579607456585140236236167)
        ·
          refine ⟨705869411184877710354354251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470579607456585140236236167 705869411184877710354354251)
          ·
            refine ⟨1058804116777316565531531377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705869411184877710354354251 1058804116777316565531531377)
            ·
              refine ⟨794103087582987424148648533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058804116777316565531531377 794103087582987424148648533)
              ·
                refine ⟨9305895557613133876741975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 794103087582987424148648533 9305895557613133876741975)
                ·
                  refine ⟨13958843336419700815112963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9305895557613133876741975 13958843336419700815112963)
                  ·
                    refine ⟨20938265004629551222669445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13958843336419700815112963 20938265004629551222669445)
                    ·
                      refine ⟨3925924688368040854250521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20938265004629551222669445 3925924688368040854250521)
                      ·
                        rfl

theorem cell23_7645711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_7645711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645711 prefixEnd_7645711 := by exact prefixLift 7645711
  have htrace : WordTrace (prefixWord ++ tailWord_7645711) baseStart_7645711 baseEnd_7645711 := by
    simpa [prefixWord, tailWord_7645711, baseEnd_7645711] using wordTrace_append hprefix tailTrace_7645711
  have hstable : (prefixWord ++ tailWord_7645711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645711).length < 2 ^ (prefixWord ++ tailWord_7645711).sum := by decide
  have hdescent : baseEnd_7645711 < baseStart_7645711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645731 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5]
def baseStart_7645731 : Nat := 118140960795 + 7645731 * 2 ^ 59
def prefixEnd_7645731 : Nat := 4983230072969 + 3 ^ 40 * 7645731 * 2
def baseEnd_7645731 : Nat := 3925934957981130776000429

theorem tailTrace_7645731 : CollatzResearch.WordTrace tailWord_7645731 prefixEnd_7645731 3925934957981130776000429 := by
  unfold tailWord_7645731
  simp only [CollatzResearch.WordTrace]
  refine ⟨278862719063829848740905047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185908479375886565827270031 278862719063829848740905047)
  ·
    refine ⟨418294078595744773111357571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278862719063829848740905047 418294078595744773111357571)
    ·
      refine ⟨627441117893617159667036357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418294078595744773111357571 627441117893617159667036357)
      ·
        refine ⟨117645209605053217437569317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627441117893617159667036357 117645209605053217437569317)
        ·
          refine ⟨22058476800947478269544247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117645209605053217437569317 22058476800947478269544247)
          ·
            refine ⟨33087715201421217404316371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22058476800947478269544247 33087715201421217404316371)
            ·
              refine ⟨49631572802131826106474557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33087715201421217404316371 49631572802131826106474557)
              ·
                refine ⟨18611839800799434789927959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49631572802131826106474557 18611839800799434789927959)
                ·
                  refine ⟨27917759701199152184891939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18611839800799434789927959 27917759701199152184891939)
                  ·
                    refine ⟨41876639551798728277337909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27917759701199152184891939 41876639551798728277337909)
                    ·
                      refine ⟨3925934957981130776000429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41876639551798728277337909 3925934957981130776000429)
                      ·
                        rfl

theorem cell23_7645731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_7645731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645731 prefixEnd_7645731 := by exact prefixLift 7645731
  have htrace : WordTrace (prefixWord ++ tailWord_7645731) baseStart_7645731 baseEnd_7645731 := by
    simpa [prefixWord, tailWord_7645731, baseEnd_7645731] using wordTrace_append hprefix tailTrace_7645731
  have hstable : (prefixWord ++ tailWord_7645731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645731).length < 2 ^ (prefixWord ++ tailWord_7645731).sum := by decide
  have hdescent : baseEnd_7645731 < baseStart_7645731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645732 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7645732 : Nat := 118140960795 + 7645732 * 2 ^ 59
def prefixEnd_7645732 : Nat := 4983230072969 + 3 ^ 40 * 7645732 * 2
def baseEnd_7645732 : Nat := 3925935471461785272087925

theorem tailTrace_7645732 : CollatzResearch.WordTrace tailWord_7645732 prefixEnd_7645732 3925935471461785272087925 := by
  unfold tailWord_7645732
  simp only [CollatzResearch.WordTrace]
  refine ⟨139431377768413112955845725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185908503691217483941127633 139431377768413112955845725)
  ·
    refine ⟨52286766663154917358442147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139431377768413112955845725 52286766663154917358442147)
    ·
      refine ⟨78430149994732376037663221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52286766663154917358442147 78430149994732376037663221)
      ·
        refine ⟨7352826562006160253530927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78430149994732376037663221 7352826562006160253530927)
        ·
          refine ⟨11029239843009240380296391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352826562006160253530927 11029239843009240380296391)
          ·
            refine ⟨16543859764513860570444587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029239843009240380296391 16543859764513860570444587)
            ·
              refine ⟨24815789646770790855666881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16543859764513860570444587 24815789646770790855666881)
              ·
                refine ⟨18611842235078093141750161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24815789646770790855666881 18611842235078093141750161)
                ·
                  refine ⟨13958881676308569856312621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18611842235078093141750161 13958881676308569856312621)
                  ·
                    refine ⟨5234580628615713696117233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13958881676308569856312621 5234580628615713696117233)
                    ·
                      refine ⟨3925935471461785272087925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234580628615713696117233 3925935471461785272087925)
                      ·
                        rfl

theorem cell23_7645732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7645732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645732 prefixEnd_7645732 := by exact prefixLift 7645732
  have htrace : WordTrace (prefixWord ++ tailWord_7645732) baseStart_7645732 baseEnd_7645732 := by
    simpa [prefixWord, tailWord_7645732, baseEnd_7645732] using wordTrace_append hprefix tailTrace_7645732
  have hstable : (prefixWord ++ tailWord_7645732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645732).length < 2 ^ (prefixWord ++ tailWord_7645732).sum := by decide
  have hdescent : baseEnd_7645732 < baseStart_7645732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645738 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_7645738 : Nat := 118140960795 + 7645738 * 2 ^ 59
def prefixEnd_7645738 : Nat := 4983230072969 + 3 ^ 40 * 7645738 * 2
def baseEnd_7645738 : Nat := 1308646184115237416204299

theorem tailTrace_7645738 : CollatzResearch.WordTrace tailWord_7645738 prefixEnd_7645738 1308646184115237416204299 := by
  unfold tailWord_7645738
  simp only [CollatzResearch.WordTrace]
  refine ⟨69715743593701122234102467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185908649583202992624273245 69715743593701122234102467)
  ·
    refine ⟨104573615390551683351153701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69715743593701122234102467 104573615390551683351153701)
    ·
      refine ⟨19607552885728440628341319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104573615390551683351153701 19607552885728440628341319)
      ·
        refine ⟨29411329328592660942511979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19607552885728440628341319 29411329328592660942511979)
        ·
          refine ⟨44116993992888991413767969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29411329328592660942511979 44116993992888991413767969)
          ·
            refine ⟨33087745494666743560325977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44116993992888991413767969 33087745494666743560325977)
            ·
              refine ⟨24815809121000057670244483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33087745494666743560325977 24815809121000057670244483)
              ·
                refine ⟨37223713681500086505366725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24815809121000057670244483 37223713681500086505366725)
                ·
                  refine ⟨6979446315281266219756261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37223713681500086505366725 6979446315281266219756261)
                  ·
                    refine ⟨1308646184115237416204299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6979446315281266219756261 1308646184115237416204299)
                    ·
                      rfl

theorem cell23_7645738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_7645738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645738 prefixEnd_7645738 := by exact prefixLift 7645738
  have htrace : WordTrace (prefixWord ++ tailWord_7645738) baseStart_7645738 baseEnd_7645738 := by
    simpa [prefixWord, tailWord_7645738, baseEnd_7645738] using wordTrace_append hprefix tailTrace_7645738
  have hstable : (prefixWord ++ tailWord_7645738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645738).length < 2 ^ (prefixWord ++ tailWord_7645738).sum := by decide
  have hdescent : baseEnd_7645738 < baseStart_7645738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645745 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 3, 2, 2]
def baseStart_7645745 : Nat := 118140960795 + 7645745 * 2 ^ 59
def prefixEnd_7645745 : Nat := 4983230072969 + 3 ^ 40 * 7645745 * 2
def baseEnd_7645745 : Nat := 3925942146710293721225365

theorem tailTrace_7645745 : CollatzResearch.WordTrace tailWord_7645745 prefixEnd_7645745 3925942146710293721225365 := by
  unfold tailWord_7645745
  simp only [CollatzResearch.WordTrace]
  refine ⟨278863229685779129131914689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185908819790519419421276459 278863229685779129131914689)
  ·
    refine ⟨209147422264334346848936017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278863229685779129131914689 209147422264334346848936017)
    ·
      refine ⟨156860566698250760136702013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209147422264334346848936017 156860566698250760136702013)
      ·
        refine ⟨58822712511844035051263255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156860566698250760136702013 58822712511844035051263255)
        ·
          refine ⟨88234068767766052576894883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58822712511844035051263255 88234068767766052576894883)
          ·
            refine ⟨132351103151649078865342325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88234068767766052576894883 132351103151649078865342325)
            ·
              refine ⟨12407915920467101143625843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132351103151649078865342325 12407915920467101143625843)
              ·
                refine ⟨18611873880700651715438765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12407915920467101143625843 18611873880700651715438765)
                ·
                  refine ⟨6979452705262744393289537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18611873880700651715438765 6979452705262744393289537)
                  ·
                    refine ⟨5234589528947058294967153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6979452705262744393289537 5234589528947058294967153)
                    ·
                      refine ⟨3925942146710293721225365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234589528947058294967153 3925942146710293721225365)
                      ·
                        rfl

theorem cell23_7645745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_7645745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645745 prefixEnd_7645745 := by exact prefixLift 7645745
  have htrace : WordTrace (prefixWord ++ tailWord_7645745) baseStart_7645745 baseEnd_7645745 := by
    simpa [prefixWord, tailWord_7645745, baseEnd_7645745] using wordTrace_append hprefix tailTrace_7645745
  have hstable : (prefixWord ++ tailWord_7645745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645745).length < 2 ^ (prefixWord ++ tailWord_7645745).sum := by decide
  have hdescent : baseEnd_7645745 < baseStart_7645745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645765 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_7645765 : Nat := 118140960795 + 7645765 * 2 ^ 59
def prefixEnd_7645765 : Nat := 4983230072969 + 3 ^ 40 * 7645765 * 2
def baseEnd_7645765 : Nat := 3925952416323383642975273

theorem tailTrace_7645765 : CollatzResearch.WordTrace tailWord_7645765 prefixEnd_7645765 3925952416323383642975273 := by
  unfold tailWord_7645765
  simp only [CollatzResearch.WordTrace]
  refine ⟨278863959145706672547642749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185909306097137781698428499 278863959145706672547642749)
  ·
    refine ⟨104573984679640002205366031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278863959145706672547642749 104573984679640002205366031)
    ·
      refine ⟨156860977019460003308049047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104573984679640002205366031 156860977019460003308049047)
      ·
        refine ⟨235291465529190004962073571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156860977019460003308049047 235291465529190004962073571)
        ·
          refine ⟨352937198293785007443110357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235291465529190004962073571 352937198293785007443110357)
          ·
            refine ⟨8271965585010586111947899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 352937198293785007443110357 8271965585010586111947899)
            ·
              refine ⟨12407948377515879167921849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271965585010586111947899 12407948377515879167921849)
              ·
                refine ⟨9305961283136909375941387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12407948377515879167921849 9305961283136909375941387)
                ·
                  refine ⟨13958941924705364063912081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9305961283136909375941387 13958941924705364063912081)
                  ·
                    refine ⟨10469206443529023047934061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13958941924705364063912081 10469206443529023047934061)
                    ·
                      refine ⟨3925952416323383642975273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469206443529023047934061 3925952416323383642975273)
                      ·
                        rfl

theorem cell23_7645765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_7645765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645765 prefixEnd_7645765 := by exact prefixLift 7645765
  have htrace : WordTrace (prefixWord ++ tailWord_7645765) baseStart_7645765 baseEnd_7645765 := by
    simpa [prefixWord, tailWord_7645765, baseEnd_7645765] using wordTrace_append hprefix tailTrace_7645765
  have hstable : (prefixWord ++ tailWord_7645765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645765).length < 2 ^ (prefixWord ++ tailWord_7645765).sum := by decide
  have hdescent : baseEnd_7645765 < baseStart_7645765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645778 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_7645778 : Nat := 118140960795 + 7645778 * 2 ^ 59
def prefixEnd_7645778 : Nat := 4983230072969 + 3 ^ 40 * 7645778 * 2
def baseEnd_7645778 : Nat := 3925959091571892092112713

theorem tailTrace_7645778 : CollatzResearch.WordTrace tailWord_7645778 prefixEnd_7645778 3925959091571892092112713 := by
  unfold tailWord_7645778
  simp only [CollatzResearch.WordTrace]
  refine ⟨69716108323664893941966497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185909622196439717178577325 69716108323664893941966497)
  ·
    refine ⟨52287081242748670456474873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69716108323664893941966497 52287081242748670456474873)
    ·
      refine ⟨39215310932061502842356155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52287081242748670456474873 39215310932061502842356155)
      ·
        refine ⟨58822966398092254263534233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39215310932061502842356155 58822966398092254263534233)
        ·
          refine ⟨44117224798569190697650675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58822966398092254263534233 44117224798569190697650675)
          ·
            refine ⟨66175837197853786046476013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44117224798569190697650675 66175837197853786046476013)
            ·
              refine ⟨24815938949195169767428505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66175837197853786046476013 24815938949195169767428505)
              ·
                refine ⟨18611954211896377325571379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24815938949195169767428505 18611954211896377325571379)
                ·
                  refine ⟨27917931317844565988357069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18611954211896377325571379 27917931317844565988357069)
                  ·
                    refine ⟨10469224244191712245633901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27917931317844565988357069 10469224244191712245633901)
                    ·
                      refine ⟨3925959091571892092112713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469224244191712245633901 3925959091571892092112713)
                      ·
                        rfl

theorem cell23_7645778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_7645778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645778 prefixEnd_7645778 := by exact prefixLift 7645778
  have htrace : WordTrace (prefixWord ++ tailWord_7645778) baseStart_7645778 baseEnd_7645778 := by
    simpa [prefixWord, tailWord_7645778, baseEnd_7645778] using wordTrace_append hprefix tailTrace_7645778
  have hstable : (prefixWord ++ tailWord_7645778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645778).length < 2 ^ (prefixWord ++ tailWord_7645778).sum := by decide
  have hdescent : baseEnd_7645778 < baseStart_7645778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645790 : List Nat := [4, 4, 1, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7645790 : Nat := 118140960795 + 7645790 * 2 ^ 59
def prefixEnd_7645790 : Nat := 4983230072969 + 3 ^ 40 * 7645790 * 2
def baseEnd_7645790 : Nat := 3925965253339746045162659

theorem tailTrace_7645790 : CollatzResearch.WordTrace tailWord_7645790 prefixEnd_7645790 3925965253339746045162659 := by
  unfold tailWord_7645790
  simp only [CollatzResearch.WordTrace]
  refine ⟨34858108871327012727162853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185909913980410734544868549 34858108871327012727162853)
  ·
    refine ⟨6535895413373814886343035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34858108871327012727162853 6535895413373814886343035)
    ·
      refine ⟨9803843120060722329514553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6535895413373814886343035 9803843120060722329514553)
      ·
        refine ⟨7352882340045541747135915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9803843120060722329514553 7352882340045541747135915)
        ·
          refine ⟨11029323510068312620703873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352882340045541747135915 11029323510068312620703873)
          ·
            refine ⟨8271992632551234465527905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11029323510068312620703873 8271992632551234465527905)
            ·
              refine ⟨6203994474413425849145929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271992632551234465527905 6203994474413425849145929)
              ·
                refine ⟨4652995855810069386859447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203994474413425849145929 4652995855810069386859447)
                ·
                  refine ⟨6979493783715104080289171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652995855810069386859447 6979493783715104080289171)
                  ·
                    refine ⟨10469240675572656120433757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979493783715104080289171 10469240675572656120433757)
                    ·
                      refine ⟨3925965253339746045162659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469240675572656120433757 3925965253339746045162659)
                      ·
                        rfl

theorem cell23_7645790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7645790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645790 prefixEnd_7645790 := by exact prefixLift 7645790
  have htrace : WordTrace (prefixWord ++ tailWord_7645790) baseStart_7645790 baseEnd_7645790 := by
    simpa [prefixWord, tailWord_7645790, baseEnd_7645790] using wordTrace_append hprefix tailTrace_7645790
  have hstable : (prefixWord ++ tailWord_7645790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645790).length < 2 ^ (prefixWord ++ tailWord_7645790).sum := by decide
  have hdescent : baseEnd_7645790 < baseStart_7645790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645795 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 3]
def baseStart_7645795 : Nat := 118140960795 + 7645795 * 2 ^ 59
def prefixEnd_7645795 : Nat := 4983230072969 + 3 ^ 40 * 7645795 * 2
def baseEnd_7645795 : Nat := 3925967820743018525600135

theorem tailTrace_7645795 : CollatzResearch.WordTrace tailWord_7645795 prefixEnd_7645795 3925967820743018525600135 := by
  unfold tailWord_7645795
  simp only [CollatzResearch.WordTrace]
  refine ⟨278865053335597987671234839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185910035557065325114156559 278865053335597987671234839)
  ·
    refine ⟨418297580003396981506852259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278865053335597987671234839 418297580003396981506852259)
    ·
      refine ⟨627446370005095472260278389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418297580003396981506852259 627446370005095472260278389)
      ·
        refine ⟨58823097187977700524401099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 627446370005095472260278389 58823097187977700524401099)
        ·
          refine ⟨88234645781966550786601649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58823097187977700524401099 88234645781966550786601649)
          ·
            refine ⟨66175984336474913089951237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88234645781966550786601649 66175984336474913089951237)
            ·
              refine ⟨12407997063089046204365857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66175984336474913089951237 12407997063089046204365857)
              ·
                refine ⟨9305997797316784653274393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12407997063089046204365857 9305997797316784653274393)
                ·
                  refine ⟨6979498347987588489955795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9305997797316784653274393 6979498347987588489955795)
                  ·
                    refine ⟨10469247521981382734933693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979498347987588489955795 10469247521981382734933693)
                    ·
                      refine ⟨3925967820743018525600135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469247521981382734933693 3925967820743018525600135)
                      ·
                        rfl

theorem cell23_7645795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_7645795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645795 prefixEnd_7645795 := by exact prefixLift 7645795
  have htrace : WordTrace (prefixWord ++ tailWord_7645795) baseStart_7645795 baseEnd_7645795 := by
    simpa [prefixWord, tailWord_7645795, baseEnd_7645795] using wordTrace_append hprefix tailTrace_7645795
  have hstable : (prefixWord ++ tailWord_7645795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645795).length < 2 ^ (prefixWord ++ tailWord_7645795).sum := by decide
  have hdescent : baseEnd_7645795 < baseStart_7645795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645805 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_7645805 : Nat := 118140960795 + 7645805 * 2 ^ 59
def prefixEnd_7645805 : Nat := 4983230072969 + 3 ^ 40 * 7645805 * 2
def baseEnd_7645805 : Nat := 3925972955549563486475089

theorem tailTrace_7645805 : CollatzResearch.WordTrace tailWord_7645805 prefixEnd_7645805 3925972955549563486475089 := by
  unfold tailWord_7645805
  simp only [CollatzResearch.WordTrace]
  refine ⟨278865418065561759379098869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185910278710374506252732579 278865418065561759379098869)
  ·
    refine ⟨26143632943646414941790519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278865418065561759379098869 26143632943646414941790519)
    ·
      refine ⟨39215449415469622412685779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26143632943646414941790519 39215449415469622412685779)
      ·
        refine ⟨58823174123204433619028669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39215449415469622412685779 58823174123204433619028669)
        ·
          refine ⟨22058690296201662607135751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58823174123204433619028669 22058690296201662607135751)
          ·
            refine ⟨33088035444302493910703627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22058690296201662607135751 33088035444302493910703627)
            ·
              refine ⟨49632053166453740866055441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33088035444302493910703627 49632053166453740866055441)
              ·
                refine ⟨37224039874840305649541581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49632053166453740866055441 37224039874840305649541581)
                ·
                  refine ⟨13959014953065114618578093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37224039874840305649541581 13959014953065114618578093)
                  ·
                    refine ⟨5234630607399417981966785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13959014953065114618578093 5234630607399417981966785)
                    ·
                      refine ⟨3925972955549563486475089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234630607399417981966785 3925972955549563486475089)
                      ·
                        rfl

theorem cell23_7645805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_7645805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645805 prefixEnd_7645805 := by exact prefixLift 7645805
  have htrace : WordTrace (prefixWord ++ tailWord_7645805) baseStart_7645805 baseEnd_7645805 := by
    simpa [prefixWord, tailWord_7645805, baseEnd_7645805] using wordTrace_append hprefix tailTrace_7645805
  have hstable : (prefixWord ++ tailWord_7645805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645805).length < 2 ^ (prefixWord ++ tailWord_7645805).sum := by decide
  have hdescent : baseEnd_7645805 < baseStart_7645805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645831 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_7645831 : Nat := 118140960795 + 7645831 * 2 ^ 59
def prefixEnd_7645831 : Nat := 4983230072969 + 3 ^ 40 * 7645831 * 2
def baseEnd_7645831 : Nat := 3925986306046580384749969

theorem tailTrace_7645831 : CollatzResearch.WordTrace tailWord_7645831 prefixEnd_7645831 3925986306046580384749969 := by
  unfold tailWord_7645831
  simp only [CollatzResearch.WordTrace]
  refine ⟨278866366363467565819545347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185910910908978377213030231 278866366363467565819545347)
  ·
    refine ⟨418299549545201348729318021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278866366363467565819545347 418299549545201348729318021)
    ·
      refine ⟨78431165539725252886747129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 418299549545201348729318021 78431165539725252886747129)
      ·
        refine ⟨58823374154793939665060347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78431165539725252886747129 58823374154793939665060347)
        ·
          refine ⟨88235061232190909497590521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58823374154793939665060347 88235061232190909497590521)
          ·
            refine ⟨66176295924143182123192891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88235061232190909497590521 66176295924143182123192891)
            ·
              refine ⟨99264443886214773184789337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66176295924143182123192891 99264443886214773184789337)
              ·
                refine ⟨74448332914661079888592003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99264443886214773184789337 74448332914661079888592003)
                ·
                  refine ⟨111672499371991619832888005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74448332914661079888592003 111672499371991619832888005)
                  ·
                    refine ⟨20938593632248428718666501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111672499371991619832888005 20938593632248428718666501)
                    ·
                      refine ⟨3925986306046580384749969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20938593632248428718666501 3925986306046580384749969)
                      ·
                        rfl

theorem cell23_7645831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_7645831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645831 prefixEnd_7645831 := by exact prefixLift 7645831
  have htrace : WordTrace (prefixWord ++ tailWord_7645831) baseStart_7645831 baseEnd_7645831 := by
    simpa [prefixWord, tailWord_7645831, baseEnd_7645831] using wordTrace_append hprefix tailTrace_7645831
  have hstable : (prefixWord ++ tailWord_7645831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645831).length < 2 ^ (prefixWord ++ tailWord_7645831).sum := by decide
  have hdescent : baseEnd_7645831 < baseStart_7645831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645852 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_7645852 : Nat := 118140960795 + 7645852 * 2 ^ 59
def prefixEnd_7645852 : Nat := 4983230072969 + 3 ^ 40 * 7645852 * 2
def baseEnd_7645852 : Nat := 3925997089140324802587373

theorem tailTrace_7645852 : CollatzResearch.WordTrace tailWord_7645852 prefixEnd_7645852 3925997089140324802587373 := by
  unfold tailWord_7645852
  simp only [CollatzResearch.WordTrace]
  refine ⟨139433566148195743203029905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185911421530927657604039873 139433566148195743203029905)
  ·
    refine ⟨104575174611146807402272429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139433566148195743203029905 104575174611146807402272429)
    ·
      refine ⟨39215690479180052775852161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104575174611146807402272429 39215690479180052775852161)
      ·
        refine ⟨29411767859385039581889121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39215690479180052775852161 29411767859385039581889121)
        ·
          refine ⟨22058825894538779686416841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29411767859385039581889121 22058825894538779686416841)
          ·
            refine ⟨16544119420904084764812631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22058825894538779686416841 16544119420904084764812631)
            ·
              refine ⟨24816179131356127147218947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16544119420904084764812631 24816179131356127147218947)
              ·
                refine ⟨37224268697034190720828421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24816179131356127147218947 37224268697034190720828421)
                ·
                  refine ⟨6979550380693910760155329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37224268697034190720828421 6979550380693910760155329)
                  ·
                    refine ⟨5234662785520433070116497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6979550380693910760155329 5234662785520433070116497)
                    ·
                      refine ⟨3925997089140324802587373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234662785520433070116497 3925997089140324802587373)
                      ·
                        rfl

theorem cell23_7645852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_7645852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645852 prefixEnd_7645852 := by exact prefixLift 7645852
  have htrace : WordTrace (prefixWord ++ tailWord_7645852) baseStart_7645852 baseEnd_7645852 := by
    simpa [prefixWord, tailWord_7645852, baseEnd_7645852] using wordTrace_append hprefix tailTrace_7645852
  have hstable : (prefixWord ++ tailWord_7645852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645852).length < 2 ^ (prefixWord ++ tailWord_7645852).sum := by decide
  have hdescent : baseEnd_7645852 < baseStart_7645852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645871 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 1, 7]
def baseStart_7645871 : Nat := 118140960795 + 7645871 * 2 ^ 59
def prefixEnd_7645871 : Nat := 4983230072969 + 3 ^ 40 * 7645871 * 2
def baseEnd_7645871 : Nat := 1308668948424253409416595

theorem tailTrace_7645871 : CollatzResearch.WordTrace tailWord_7645871 prefixEnd_7645871 1308668948424253409416595 := by
  unfold tailWord_7645871
  simp only [CollatzResearch.WordTrace]
  refine ⟨278867825283322652651001467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185911883522215101767334311 278867825283322652651001467)
  ·
    refine ⟨418301737924983978976502201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278867825283322652651001467 418301737924983978976502201)
    ·
      refine ⟨313726303443737984232376651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418301737924983978976502201 313726303443737984232376651)
      ·
        refine ⟨470589455165606976348564977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313726303443737984232376651 470589455165606976348564977)
        ·
          refine ⟨352942091374205232261423733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470589455165606976348564977 352942091374205232261423733)
          ·
            refine ⟨33088321066331740524508475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352942091374205232261423733 33088321066331740524508475)
            ·
              refine ⟨49632481599497610786762713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33088321066331740524508475 49632481599497610786762713)
              ·
                refine ⟨37224361199623208090072035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49632481599497610786762713 37224361199623208090072035)
                ·
                  refine ⟨55836541799434812135108053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37224361199623208090072035 55836541799434812135108053)
                  ·
                    refine ⟨1308668948424253409416595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55836541799434812135108053 1308668948424253409416595)
                    ·
                      rfl

theorem cell23_7645871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_7645871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645871 prefixEnd_7645871 := by exact prefixLift 7645871
  have htrace : WordTrace (prefixWord ++ tailWord_7645871) baseStart_7645871 baseEnd_7645871 := by
    simpa [prefixWord, tailWord_7645871, baseEnd_7645871] using wordTrace_append hprefix tailTrace_7645871
  have hstable : (prefixWord ++ tailWord_7645871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645871).length < 2 ^ (prefixWord ++ tailWord_7645871).sum := by decide
  have hdescent : baseEnd_7645871 < baseStart_7645871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645881 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7645881 : Nat := 118140960795 + 7645881 * 2 ^ 59
def prefixEnd_7645881 : Nat := 4983230072969 + 3 ^ 40 * 7645881 * 2
def baseEnd_7645881 : Nat := 3926011980079305189124739

theorem tailTrace_7645881 : CollatzResearch.WordTrace tailWord_7645881 prefixEnd_7645881 3926011980079305189124739 := by
  unfold tailWord_7645881
  simp only [CollatzResearch.WordTrace]
  refine ⟨278868190013286424358865497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185912126675524282905910331 278868190013286424358865497)
  ·
    refine ⟨209151142509964818269149123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278868190013286424358865497 209151142509964818269149123)
    ·
      refine ⟨313726713764947227403723685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209151142509964818269149123 313726713764947227403723685)
      ·
        refine ⟨58823758830927605138198191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313726713764947227403723685 58823758830927605138198191)
        ·
          refine ⟨88235638246391407707297287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58823758830927605138198191 88235638246391407707297287)
          ·
            refine ⟨132353457369587111560945931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88235638246391407707297287 132353457369587111560945931)
            ·
              refine ⟨198530186054380667341418897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132353457369587111560945931 198530186054380667341418897)
              ·
                refine ⟨148897639540785500506064173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198530186054380667341418897 148897639540785500506064173)
                ·
                  refine ⟨55836614827794562689774065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148897639540785500506064173 55836614827794562689774065)
                  ·
                    refine ⟨41877461120845922017330549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55836614827794562689774065 41877461120845922017330549)
                    ·
                      refine ⟨3926011980079305189124739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41877461120845922017330549 3926011980079305189124739)
                      ·
                        rfl

theorem cell23_7645881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7645881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645881 prefixEnd_7645881 := by exact prefixLift 7645881
  have htrace : WordTrace (prefixWord ++ tailWord_7645881) baseStart_7645881 baseEnd_7645881 := by
    simpa [prefixWord, tailWord_7645881, baseEnd_7645881] using wordTrace_append hprefix tailTrace_7645881
  have hstable : (prefixWord ++ tailWord_7645881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645881).length < 2 ^ (prefixWord ++ tailWord_7645881).sum := by decide
  have hdescent : baseEnd_7645881 < baseStart_7645881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645892 : List Nat := [2, 3, 3, 1, 1, 4, 1, 3, 5]
def baseStart_7645892 : Nat := 118140960795 + 7645892 * 2 ^ 59
def prefixEnd_7645892 : Nat := 4983230072969 + 3 ^ 40 * 7645892 * 2
def baseEnd_7645892 : Nat := 436224180929611627343021

theorem tailTrace_7645892 : CollatzResearch.WordTrace tailWord_7645892 prefixEnd_7645892 436224180929611627343021 := by
  unfold tailWord_7645892
  simp only [CollatzResearch.WordTrace]
  refine ⟨139434295608123286618757965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185912394144164382158343953 139434295608123286618757965)
  ·
    refine ⟨52287860853046232482034237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139434295608123286618757965 52287860853046232482034237)
    ·
      refine ⟨19607947819892337180762839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52287860853046232482034237 19607947819892337180762839)
      ·
        refine ⟨29411921729838505771144259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19607947819892337180762839 29411921729838505771144259)
        ·
          refine ⟨44117882594757758656716389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29411921729838505771144259 44117882594757758656716389)
          ·
            refine ⟨8272102986517079748134323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44117882594757758656716389 8272102986517079748134323)
            ·
              refine ⟨12408154479775619622201485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272102986517079748134323 12408154479775619622201485)
              ·
                refine ⟨4653057929915857358325557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12408154479775619622201485 4653057929915857358325557)
                ·
                  refine ⟨436224180929611627343021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4653057929915857358325557 436224180929611627343021)
                  ·
                    rfl

theorem cell23_7645892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_7645892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645892 prefixEnd_7645892 := by exact prefixLift 7645892
  have htrace : WordTrace (prefixWord ++ tailWord_7645892) baseStart_7645892 baseEnd_7645892 := by
    simpa [prefixWord, tailWord_7645892, baseEnd_7645892] using wordTrace_append hprefix tailTrace_7645892
  have hstable : (prefixWord ++ tailWord_7645892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645892).length < 2 ^ (prefixWord ++ tailWord_7645892).sum := by decide
  have hdescent : baseEnd_7645892 < baseStart_7645892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645909 : List Nat := [1, 3, 2, 5, 1, 1, 3, 2, 5]
def baseStart_7645909 : Nat := 118140960795 + 7645909 * 2 ^ 59
def prefixEnd_7645909 : Nat := 4983230072969 + 3 ^ 40 * 7645909 * 2
def baseEnd_7645909 : Nat := 436225150837514564397179

theorem tailTrace_7645909 : CollatzResearch.WordTrace tailWord_7645909 prefixEnd_7645909 436225150837514564397179 := by
  unfold tailWord_7645909
  simp only [CollatzResearch.WordTrace]
  refine ⟨278869211257184985140884781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185912807504789990093923187 278869211257184985140884781)
  ·
    refine ⟨104575954221444369427831793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278869211257184985140884781 104575954221444369427831793)
    ·
      refine ⟨78431965666083277070873845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104575954221444369427831793 78431965666083277070873845)
      ·
        refine ⟨7352996781195307225394423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78431965666083277070873845 7352996781195307225394423)
        ·
          refine ⟨11029495171792960838091635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352996781195307225394423 11029495171792960838091635)
          ·
            refine ⟨16544242757689441257137453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029495171792960838091635 16544242757689441257137453)
            ·
              refine ⟨6204091034133540471426545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16544242757689441257137453 6204091034133540471426545)
              ·
                refine ⟨4653068275600155353569909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204091034133540471426545 4653068275600155353569909)
                ·
                  refine ⟨436225150837514564397179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4653068275600155353569909 436225150837514564397179)
                  ·
                    rfl

theorem cell23_7645909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_7645909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645909 prefixEnd_7645909 := by exact prefixLift 7645909
  have htrace : WordTrace (prefixWord ++ tailWord_7645909) baseStart_7645909 baseEnd_7645909 := by
    simpa [prefixWord, tailWord_7645909, baseEnd_7645909] using wordTrace_append hprefix tailTrace_7645909
  have hstable : (prefixWord ++ tailWord_7645909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645909).length < 2 ^ (prefixWord ++ tailWord_7645909).sum := by decide
  have hdescent : baseEnd_7645909 < baseStart_7645909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645951 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_7645951 : Nat := 118140960795 + 7645951 * 2 ^ 59
def prefixEnd_7645951 : Nat := 4983230072969 + 3 ^ 40 * 7645951 * 2
def baseEnd_7645951 : Nat := 3926047923725119915249417

theorem tailTrace_7645951 : CollatzResearch.WordTrace tailWord_7645951 prefixEnd_7645951 3926047923725119915249417 := by
  unfold tailWord_7645951
  simp only [CollatzResearch.WordTrace]
  refine ⟨278870743123032826313913707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185913828748688550875942471 278870743123032826313913707)
  ·
    refine ⟨418306114684549239470870561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278870743123032826313913707 418306114684549239470870561)
    ·
      refine ⟨313729586013411929603152921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418306114684549239470870561 313729586013411929603152921)
      ·
        refine ⟨235297189510058947202364691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313729586013411929603152921 235297189510058947202364691)
        ·
          refine ⟨352945784265088420803547037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235297189510058947202364691 352945784265088420803547037)
          ·
            refine ⟨132354669099408157801330139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352945784265088420803547037 132354669099408157801330139)
            ·
              refine ⟨198532003649112236701995209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132354669099408157801330139 198532003649112236701995209)
              ·
                refine ⟨148899002736834177526496407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198532003649112236701995209 148899002736834177526496407)
                ·
                  refine ⟨223348504105251266289744611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148899002736834177526496407 223348504105251266289744611)
                  ·
                    refine ⟨335022756157876899434616917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 223348504105251266289744611 335022756157876899434616917)
                    ·
                      refine ⟨3926047923725119915249417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 335022756157876899434616917 3926047923725119915249417)
                      ·
                        rfl

theorem cell23_7645951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_7645951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645951 prefixEnd_7645951 := by exact prefixLift 7645951
  have htrace : WordTrace (prefixWord ++ tailWord_7645951) baseStart_7645951 baseEnd_7645951 := by
    simpa [prefixWord, tailWord_7645951, baseEnd_7645951] using wordTrace_append hprefix tailTrace_7645951
  have hstable : (prefixWord ++ tailWord_7645951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645951).length < 2 ^ (prefixWord ++ tailWord_7645951).sum := by decide
  have hdescent : baseEnd_7645951 < baseStart_7645951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645978 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_7645978 : Nat := 118140960795 + 7645978 * 2 ^ 59
def prefixEnd_7645978 : Nat := 4983230072969 + 3 ^ 40 * 7645978 * 2
def baseEnd_7645978 : Nat := 1308687262567597103203931

theorem tailTrace_7645978 : CollatzResearch.WordTrace tailWord_7645978 prefixEnd_7645978 1308687262567597103203931 := by
  unfold tailWord_7645978
  simp only [CollatzResearch.WordTrace]
  refine ⟨69717931973483752481286647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185914485262623339950097725 69717931973483752481286647)
  ·
    refine ⟨104576897960225628721929971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69717931973483752481286647 104576897960225628721929971)
    ·
      refine ⟨156865346940338443082894957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104576897960225628721929971 156865346940338443082894957)
      ·
        refine ⟨58824505102626916156085609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156865346940338443082894957 58824505102626916156085609)
        ·
          refine ⟨44118378826970187117064207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58824505102626916156085609 44118378826970187117064207)
          ·
            refine ⟨66177568240455280675596311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44118378826970187117064207 66177568240455280675596311)
            ·
              refine ⟨99266352360682921013394467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66177568240455280675596311 99266352360682921013394467)
              ·
                refine ⟨148899528541024381520091701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99266352360682921013394467 148899528541024381520091701)
                ·
                  refine ⟨13959330800721035767508597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148899528541024381520091701 13959330800721035767508597)
                  ·
                    refine ⟨1308687262567597103203931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13959330800721035767508597 1308687262567597103203931)
                    ·
                      rfl

theorem cell23_7645978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_7645978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645978 prefixEnd_7645978 := by exact prefixLift 7645978
  have htrace : WordTrace (prefixWord ++ tailWord_7645978) baseStart_7645978 baseEnd_7645978 := by
    simpa [prefixWord, tailWord_7645978, baseEnd_7645978] using wordTrace_append hprefix tailTrace_7645978
  have hstable : (prefixWord ++ tailWord_7645978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645978).length < 2 ^ (prefixWord ++ tailWord_7645978).sum := by decide
  have hdescent : baseEnd_7645978 < baseStart_7645978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645985 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_7645985 : Nat := 118140960795 + 7645985 * 2 ^ 59
def prefixEnd_7645985 : Nat := 4983230072969 + 3 ^ 40 * 7645985 * 2
def baseEnd_7645985 : Nat := 3926065382067372782224261

theorem tailTrace_7645985 : CollatzResearch.WordTrace tailWord_7645985 prefixEnd_7645985 3926065382067372782224261 := by
  unfold tailWord_7645985
  simp only [CollatzResearch.WordTrace]
  refine ⟨278871983204909650120651409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185914655469939766747100939 278871983204909650120651409)
  ·
    refine ⟨209153987403682237590488557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278871983204909650120651409 209153987403682237590488557)
    ·
      refine ⟨78432745276380839096433209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209153987403682237590488557 78432745276380839096433209)
      ·
        refine ⟨58824558957285629322324907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78432745276380839096433209 58824558957285629322324907)
        ·
          refine ⟨88236838435928443983487361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58824558957285629322324907 88236838435928443983487361)
          ·
            refine ⟨66177628826946332987615521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88236838435928443983487361 66177628826946332987615521)
            ·
              refine ⟨49633221620209749740711641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66177628826946332987615521 49633221620209749740711641)
              ·
                refine ⟨37224916215157312305533731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49633221620209749740711641 37224916215157312305533731)
                ·
                  refine ⟨55837374322735968458300597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37224916215157312305533731 55837374322735968458300597)
                  ·
                    refine ⟨5234753842756497042965681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55837374322735968458300597 5234753842756497042965681)
                    ·
                      refine ⟨3926065382067372782224261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234753842756497042965681 3926065382067372782224261)
                      ·
                        rfl

theorem cell23_7645985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_7645985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645985 prefixEnd_7645985 := by exact prefixLift 7645985
  have htrace : WordTrace (prefixWord ++ tailWord_7645985) baseStart_7645985 baseEnd_7645985 := by
    simpa [prefixWord, tailWord_7645985, baseEnd_7645985] using wordTrace_append hprefix tailTrace_7645985
  have hstable : (prefixWord ++ tailWord_7645985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645985).length < 2 ^ (prefixWord ++ tailWord_7645985).sum := by decide
  have hdescent : baseEnd_7645985 < baseStart_7645985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7645992 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_7645992 : Nat := 118140960795 + 7645992 * 2 ^ 59
def prefixEnd_7645992 : Nat := 4983230072969 + 3 ^ 40 * 7645992 * 2
def baseEnd_7645992 : Nat := 3926068976431954254836729

theorem tailTrace_7645992 : CollatzResearch.WordTrace tailWord_7645992 prefixEnd_7645992 3926068976431954254836729 := by
  unfold tailWord_7645992
  simp only [CollatzResearch.WordTrace]
  refine ⟨139436119257942145158078115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185914825677256193544104153 139436119257942145158078115)
  ·
    refine ⟨209154178886913217737117173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139436119257942145158078115 209154178886913217737117173)
    ·
      refine ⟨19608204270648114162854735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209154178886913217737117173 19608204270648114162854735)
      ·
        refine ⟨29412306405972171244282103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19608204270648114162854735 29412306405972171244282103)
        ·
          refine ⟨44118459608958256866423155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29412306405972171244282103 44118459608958256866423155)
          ·
            refine ⟨66177689413437385299634733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44118459608958256866423155 66177689413437385299634733)
            ·
              refine ⟨24816633530039019487363025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66177689413437385299634733 24816633530039019487363025)
              ·
                refine ⟨18612475147529264615522269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24816633530039019487363025 18612475147529264615522269)
                ·
                  refine ⟨6979678180323474230820851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18612475147529264615522269 6979678180323474230820851)
                  ·
                    refine ⟨10469517270485211346231277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979678180323474230820851 10469517270485211346231277)
                    ·
                      refine ⟨3926068976431954254836729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469517270485211346231277 3926068976431954254836729)
                      ·
                        rfl

theorem cell23_7645992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_7645992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7645992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7645992 prefixEnd_7645992 := by exact prefixLift 7645992
  have htrace : WordTrace (prefixWord ++ tailWord_7645992) baseStart_7645992 baseEnd_7645992 := by
    simpa [prefixWord, tailWord_7645992, baseEnd_7645992] using wordTrace_append hprefix tailTrace_7645992
  have hstable : (prefixWord ++ tailWord_7645992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7645992).length < 2 ^ (prefixWord ++ tailWord_7645992).sum := by decide
  have hdescent : baseEnd_7645992 < baseStart_7645992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7645992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646008 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 1, 6]
def baseStart_7646008 : Nat := 118140960795 + 7646008 * 2 ^ 59
def prefixEnd_7646008 : Nat := 4983230072969 + 3 ^ 40 * 7646008 * 2
def baseEnd_7646008 : Nat := 1308692397374142064078885

theorem tailTrace_7646008 : CollatzResearch.WordTrace tailWord_7646008 prefixEnd_7646008 1308692397374142064078885 := by
  unfold tailWord_7646008
  simp only [CollatzResearch.WordTrace]
  refine ⟨139436411041913162524369339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185915214722550883365825785 139436411041913162524369339)
  ·
    refine ⟨209154616562869743786554009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139436411041913162524369339 209154616562869743786554009)
    ·
      refine ⟨156865962422152307839915507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209154616562869743786554009 156865962422152307839915507)
      ·
        refine ⟨235298943633228461759873261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156865962422152307839915507 235298943633228461759873261)
        ·
          refine ⟨88237103862460673159952473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235298943633228461759873261 88237103862460673159952473)
          ·
            refine ⟨66177827896845504869964355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88237103862460673159952473 66177827896845504869964355)
            ·
              refine ⟨99266741845268257304946533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66177827896845504869964355 99266741845268257304946533)
              ·
                refine ⟨18612514095987798244677475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99266741845268257304946533 18612514095987798244677475)
                ·
                  refine ⟨27918771143981697367016213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18612514095987798244677475 27918771143981697367016213)
                  ·
                    refine ⟨1308692397374142064078885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27918771143981697367016213 1308692397374142064078885)
                    ·
                      rfl

theorem cell23_7646008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_7646008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646008 prefixEnd_7646008 := by exact prefixLift 7646008
  have htrace : WordTrace (prefixWord ++ tailWord_7646008) baseStart_7646008 baseEnd_7646008 := by
    simpa [prefixWord, tailWord_7646008, baseEnd_7646008] using wordTrace_append hprefix tailTrace_7646008
  have hstable : (prefixWord ++ tailWord_7646008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646008).length < 2 ^ (prefixWord ++ tailWord_7646008).sum := by decide
  have hdescent : baseEnd_7646008 < baseStart_7646008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646025 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 4, 4]
def baseStart_7646025 : Nat := 118140960795 + 7646025 * 2 ^ 59
def prefixEnd_7646025 : Nat := 4983230072969 + 3 ^ 40 * 7646025 * 2
def baseEnd_7646025 : Nat := 1308695307097850875241359

theorem tailTrace_7646025 : CollatzResearch.WordTrace tailWord_7646025 prefixEnd_7646025 1308695307097850875241359 := by
  unfold tailWord_7646025
  simp only [CollatzResearch.WordTrace]
  refine ⟨278873442124764736952107529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185915628083176491301405019 278873442124764736952107529)
  ·
    refine ⟨209155081593573552714080647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278873442124764736952107529 209155081593573552714080647)
    ·
      refine ⟨313732622390360329071120971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209155081593573552714080647 313732622390360329071120971)
      ·
        refine ⟨470598933585540493606681457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313732622390360329071120971 470598933585540493606681457)
        ·
          refine ⟨352949200189155370205011093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470598933585540493606681457 352949200189155370205011093)
          ·
            refine ⟨16544493758866657978359895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 352949200189155370205011093 16544493758866657978359895)
            ·
              refine ⟨24816740638299986967539843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16544493758866657978359895 24816740638299986967539843)
              ·
                refine ⟨37225110957449980451309765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24816740638299986967539843 37225110957449980451309765)
                ·
                  refine ⟨6979708304521871334620581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37225110957449980451309765 6979708304521871334620581)
                  ·
                    refine ⟨1308695307097850875241359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6979708304521871334620581 1308695307097850875241359)
                    ·
                      rfl

theorem cell23_7646025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_7646025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646025 prefixEnd_7646025 := by exact prefixLift 7646025
  have htrace : WordTrace (prefixWord ++ tailWord_7646025) baseStart_7646025 baseEnd_7646025 := by
    simpa [prefixWord, tailWord_7646025, baseEnd_7646025] using wordTrace_append hprefix tailTrace_7646025
  have hstable : (prefixWord ++ tailWord_7646025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646025).length < 2 ^ (prefixWord ++ tailWord_7646025).sum := by decide
  have hdescent : baseEnd_7646025 < baseStart_7646025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646032 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 3, 2, 2]
def baseStart_7646032 : Nat := 118140960795 + 7646032 * 2 ^ 59
def prefixEnd_7646032 : Nat := 4983230072969 + 3 ^ 40 * 7646032 * 2
def baseEnd_7646032 : Nat := 3926089515658134098336545

theorem tailTrace_7646032 : CollatzResearch.WordTrace tailWord_7646032 prefixEnd_7646032 3926089515658134098336545 := by
  unfold tailWord_7646032
  simp only [CollatzResearch.WordTrace]
  refine ⟨139436848717869688573806175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185915798290492918098408233 139436848717869688573806175)
  ·
    refine ⟨209155273076804532860709263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139436848717869688573806175 209155273076804532860709263)
    ·
      refine ⟨313732909615206799291063895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209155273076804532860709263 313732909615206799291063895)
      ·
        refine ⟨470599364422810198936595843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313732909615206799291063895 470599364422810198936595843)
        ·
          refine ⟨705899046634215298404893765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470599364422810198936595843 705899046634215298404893765)
          ·
            refine ⟨132356071243915368450917581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 705899046634215298404893765 132356071243915368450917581)
            ·
              refine ⟨49633526716468263169094093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132356071243915368450917581 49633526716468263169094093)
              ·
                refine ⟨18612572518675598688410285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49633526716468263169094093 18612572518675598688410285)
                ·
                  refine ⟨6979714694503349508153857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18612572518675598688410285 6979714694503349508153857)
                  ·
                    refine ⟨5234786020877512131115393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6979714694503349508153857 5234786020877512131115393)
                    ·
                      refine ⟨3926089515658134098336545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234786020877512131115393 3926089515658134098336545)
                      ·
                        rfl

theorem cell23_7646032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 2, 2].length) (baseStart_7646032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646032 prefixEnd_7646032 := by exact prefixLift 7646032
  have htrace : WordTrace (prefixWord ++ tailWord_7646032) baseStart_7646032 baseEnd_7646032 := by
    simpa [prefixWord, tailWord_7646032, baseEnd_7646032] using wordTrace_append hprefix tailTrace_7646032
  have hstable : (prefixWord ++ tailWord_7646032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646032).length < 2 ^ (prefixWord ++ tailWord_7646032).sum := by decide
  have hdescent : baseEnd_7646032 < baseStart_7646032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646052 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_7646052 : Nat := 118140960795 + 7646052 * 2 ^ 59
def prefixEnd_7646052 : Nat := 4983230072969 + 3 ^ 40 * 7646052 * 2
def baseEnd_7646052 : Nat := 3926099785271224020086453

theorem tailTrace_7646052 : CollatzResearch.WordTrace tailWord_7646052 prefixEnd_7646052 3926099785271224020086453 := by
  unfold tailWord_7646052
  simp only [CollatzResearch.WordTrace]
  refine ⟨139437213447833460281670205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185916284597111280375560273 139437213447833460281670205)
  ·
    refine ⟨52288955042937547605626327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139437213447833460281670205 52288955042937547605626327)
    ·
      refine ⟨78433432564406321408439491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52288955042937547605626327 78433432564406321408439491)
      ·
        refine ⟨117650148846609482112659237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78433432564406321408439491 117650148846609482112659237)
        ·
          refine ⟨22059402908739277896123607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117650148846609482112659237 22059402908739277896123607)
          ·
            refine ⟨33089104363108916844185411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22059402908739277896123607 33089104363108916844185411)
            ·
              refine ⟨49633656544663375266278117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33089104363108916844185411 49633656544663375266278117)
              ·
                refine ⟨9306310602124382862427147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49633656544663375266278117 9306310602124382862427147)
                ·
                  refine ⟨13959465903186574293640721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9306310602124382862427147 13959465903186574293640721)
                  ·
                    refine ⟨10469599427389930720230541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13959465903186574293640721 10469599427389930720230541)
                    ·
                      refine ⟨3926099785271224020086453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469599427389930720230541 3926099785271224020086453)
                      ·
                        rfl

theorem cell23_7646052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_7646052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646052 prefixEnd_7646052 := by exact prefixLift 7646052
  have htrace : WordTrace (prefixWord ++ tailWord_7646052) baseStart_7646052 baseEnd_7646052 := by
    simpa [prefixWord, tailWord_7646052, baseEnd_7646052] using wordTrace_append hprefix tailTrace_7646052
  have hstable : (prefixWord ++ tailWord_7646052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646052).length < 2 ^ (prefixWord ++ tailWord_7646052).sum := by decide
  have hdescent : baseEnd_7646052 < baseStart_7646052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646055 : List Nat := [1, 1, 5, 1, 2, 2, 4, 7]
def baseStart_7646055 : Nat := 118140960795 + 7646055 * 2 ^ 59
def prefixEnd_7646055 : Nat := 4983230072969 + 3 ^ 40 * 7646055 * 2
def baseEnd_7646055 : Nat := 145411160211599537346257

theorem tailTrace_7646055 : CollatzResearch.WordTrace tailWord_7646055 prefixEnd_7646055 145411160211599537346257 := by
  unfold tailWord_7646055
  simp only [CollatzResearch.WordTrace]
  refine ⟨278874536314656052075699619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185916357543104034717133079 278874536314656052075699619)
  ·
    refine ⟨418311804471984078113549429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278874536314656052075699619 418311804471984078113549429)
    ·
      refine ⟨39216731669248507323145259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 418311804471984078113549429 39216731669248507323145259)
      ·
        refine ⟨58825097503872760984717889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39216731669248507323145259 58825097503872760984717889)
        ·
          refine ⟨44118823127904570738538417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58825097503872760984717889 44118823127904570738538417)
          ·
            refine ⟨33089117345928428053903813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44118823127904570738538417 33089117345928428053903813)
            ·
              refine ⟨6204209502361580260106965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33089117345928428053903813 6204209502361580260106965)
              ·
                refine ⟨145411160211599537346257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6204209502361580260106965 145411160211599537346257)
                ·
                  rfl

theorem cell23_7646055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 7].length) (baseStart_7646055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646055 prefixEnd_7646055 := by exact prefixLift 7646055
  have htrace : WordTrace (prefixWord ++ tailWord_7646055) baseStart_7646055 baseEnd_7646055 := by
    simpa [prefixWord, tailWord_7646055, baseEnd_7646055] using wordTrace_append hprefix tailTrace_7646055
  have hstable : (prefixWord ++ tailWord_7646055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646055).length < 2 ^ (prefixWord ++ tailWord_7646055).sum := by decide
  have hdescent : baseEnd_7646055 < baseStart_7646055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646066 : List Nat := [3, 2, 1, 2, 1, 1, 5, 3, 1, 2, 2]
def baseStart_7646066 : Nat := 118140960795 + 7646066 * 2 ^ 59
def prefixEnd_7646066 : Nat := 4983230072969 + 3 ^ 40 * 7646066 * 2
def baseEnd_7646066 : Nat := 3926106974000386965311389

theorem tailTrace_7646066 : CollatzResearch.WordTrace tailWord_7646066 prefixEnd_7646066 3926106974000386965311389 := by
  unfold tailWord_7646066
  simp only [CollatzResearch.WordTrace]
  refine ⟨69718734379404050238587513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185916625011744133969566701 69718734379404050238587513)
  ·
    refine ⟨52289050784553037678940635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69718734379404050238587513 52289050784553037678940635)
    ·
      refine ⟨78433576176829556518410953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52289050784553037678940635 78433576176829556518410953)
      ·
        refine ⟨58825182132622167388808215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78433576176829556518410953 58825182132622167388808215)
        ·
          refine ⟨88237773198933251083212323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58825182132622167388808215 88237773198933251083212323)
          ·
            refine ⟨132356659798399876624818485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88237773198933251083212323 132356659798399876624818485)
            ·
              refine ⟨12408436856099988433576733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132356659798399876624818485 12408436856099988433576733)
              ·
                refine ⟨4653163821037495662591275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12408436856099988433576733 4653163821037495662591275)
                ·
                  refine ⟨6979745731556243493886913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653163821037495662591275 6979745731556243493886913)
                  ·
                    refine ⟨5234809298667182620415185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6979745731556243493886913 5234809298667182620415185)
                    ·
                      refine ⟨3926106974000386965311389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234809298667182620415185 3926106974000386965311389)
                      ·
                        rfl

theorem cell23_7646066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_7646066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646066 prefixEnd_7646066 := by exact prefixLift 7646066
  have htrace : WordTrace (prefixWord ++ tailWord_7646066) baseStart_7646066 baseEnd_7646066 := by
    simpa [prefixWord, tailWord_7646066, baseEnd_7646066] using wordTrace_append hprefix tailTrace_7646066
  have hstable : (prefixWord ++ tailWord_7646066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646066).length < 2 ^ (prefixWord ++ tailWord_7646066).sum := by decide
  have hdescent : baseEnd_7646066 < baseStart_7646066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646150 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7646150 : Nat := 118140960795 + 7646150 * 2 ^ 59
def prefixEnd_7646150 : Nat := 4983230072969 + 3 ^ 40 * 7646150 * 2
def baseEnd_7646150 : Nat := 3926150106375364636661003

theorem tailTrace_7646150 : CollatzResearch.WordTrace tailWord_7646150 prefixEnd_7646150 3926150106375364636661003 := by
  unfold tailWord_7646150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714937539040996353137747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 185918667499541255533605269 8714937539040996353137747)
  ·
    refine ⟨13072406308561494529706621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8714937539040996353137747 13072406308561494529706621)
    ·
      refine ⟨4902152365710560448639983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13072406308561494529706621 4902152365710560448639983)
      ·
        refine ⟨7353228548565840672959975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902152365710560448639983 7353228548565840672959975)
        ·
          refine ⟨11029842822848761009439963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353228548565840672959975 11029842822848761009439963)
          ·
            refine ⟨16544764234273141514159945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029842822848761009439963 16544764234273141514159945)
            ·
              refine ⟨12408573175704856135619959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16544764234273141514159945 12408573175704856135619959)
              ·
                refine ⟨18612859763557284203429939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12408573175704856135619959 18612859763557284203429939)
                ·
                  refine ⟨27919289645335926305144909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18612859763557284203429939 27919289645335926305144909)
                  ·
                    refine ⟨10469733617000972364429341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27919289645335926305144909 10469733617000972364429341)
                    ·
                      refine ⟨3926150106375364636661003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469733617000972364429341 3926150106375364636661003)
                      ·
                        rfl

theorem cell23_7646150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7646150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646150 prefixEnd_7646150 := by exact prefixLift 7646150
  have htrace : WordTrace (prefixWord ++ tailWord_7646150) baseStart_7646150 baseEnd_7646150 := by
    simpa [prefixWord, tailWord_7646150, baseEnd_7646150] using wordTrace_append hprefix tailTrace_7646150
  have hstable : (prefixWord ++ tailWord_7646150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646150).length < 2 ^ (prefixWord ++ tailWord_7646150).sum := by decide
  have hdescent : baseEnd_7646150 < baseStart_7646150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646152 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_7646152 : Nat := 118140960795 + 7646152 * 2 ^ 59
def prefixEnd_7646152 : Nat := 4983230072969 + 3 ^ 40 * 7646152 * 2
def baseEnd_7646152 : Nat := 3926151133336673628835993

theorem tailTrace_7646152 : CollatzResearch.WordTrace tailWord_7646152 prefixEnd_7646152 3926151133336673628835993 := by
  unfold tailWord_7646152
  simp only [CollatzResearch.WordTrace]
  refine ⟨139439037097652318820990355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185918716130203091761320473 139439037097652318820990355)
  ·
    refine ⟨209158555646478478231485533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139439037097652318820990355 209158555646478478231485533)
    ·
      refine ⟨78434458367429429336807075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209158555646478478231485533 78434458367429429336807075)
      ·
        refine ⟨117651687551144144005210613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78434458367429429336807075 117651687551144144005210613)
        ·
          refine ⟨11029845707919763500488495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117651687551144144005210613 11029845707919763500488495)
          ·
            refine ⟨16544768561879645250732743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029845707919763500488495 16544768561879645250732743)
            ·
              refine ⟨24817152842819467876099115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16544768561879645250732743 24817152842819467876099115)
              ·
                refine ⟨37225729264229201814148673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24817152842819467876099115 37225729264229201814148673)
                ·
                  refine ⟨27919296948171901360611505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37225729264229201814148673 27919296948171901360611505)
                  ·
                    refine ⟨20939472711128926020458629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27919296948171901360611505 20939472711128926020458629)
                    ·
                      refine ⟨3926151133336673628835993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20939472711128926020458629 3926151133336673628835993)
                      ·
                        rfl

theorem cell23_7646152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_7646152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646152 prefixEnd_7646152 := by exact prefixLift 7646152
  have htrace : WordTrace (prefixWord ++ tailWord_7646152) baseStart_7646152 baseEnd_7646152 := by
    simpa [prefixWord, tailWord_7646152, baseEnd_7646152] using wordTrace_append hprefix tailTrace_7646152
  have hstable : (prefixWord ++ tailWord_7646152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646152).length < 2 ^ (prefixWord ++ tailWord_7646152).sum := by decide
  have hdescent : baseEnd_7646152 < baseStart_7646152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646155 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 3]
def baseStart_7646155 : Nat := 118140960795 + 7646155 * 2 ^ 59
def prefixEnd_7646155 : Nat := 4983230072969 + 3 ^ 40 * 7646155 * 2
def baseEnd_7646155 : Nat := 3926152673778637117098479

theorem tailTrace_7646155 : CollatzResearch.WordTrace tailWord_7646155 prefixEnd_7646155 3926152673778637117098479 := by
  unfold tailWord_7646155
  simp only [CollatzResearch.WordTrace]
  refine ⟨278878183614293769154339919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185918789076195846102893279 278878183614293769154339919)
  ·
    refine ⟨418317275421440653731509879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278878183614293769154339919 418317275421440653731509879)
    ·
      refine ⟨627475913132160980597264819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418317275421440653731509879 627475913132160980597264819)
      ·
        refine ⟨941213869698241470895897229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627475913132160980597264819 941213869698241470895897229)
        ·
          refine ⟨352955201136840551585961461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941213869698241470895897229 352955201136840551585961461)
          ·
            refine ⟨33089550106578801711183887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352955201136840551585961461 33089550106578801711183887)
            ·
              refine ⟨49634325159868202566775831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33089550106578801711183887 49634325159868202566775831)
              ·
                refine ⟨74451487739802303850163747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49634325159868202566775831 74451487739802303850163747)
                ·
                  refine ⟨111677231609703455775245621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74451487739802303850163747 111677231609703455775245621)
                  ·
                    refine ⟨10469740463409698978929277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111677231609703455775245621 10469740463409698978929277)
                    ·
                      refine ⟨3926152673778637117098479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469740463409698978929277 3926152673778637117098479)
                      ·
                        rfl

theorem cell23_7646155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 3].length) (baseStart_7646155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646155 prefixEnd_7646155 := by exact prefixLift 7646155
  have htrace : WordTrace (prefixWord ++ tailWord_7646155) baseStart_7646155 baseEnd_7646155 := by
    simpa [prefixWord, tailWord_7646155, baseEnd_7646155] using wordTrace_append hprefix tailTrace_7646155
  have hstable : (prefixWord ++ tailWord_7646155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646155).length < 2 ^ (prefixWord ++ tailWord_7646155).sum := by decide
  have hdescent : baseEnd_7646155 < baseStart_7646155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646162 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 7]
def baseStart_7646162 : Nat := 118140960795 + 7646162 * 2 ^ 59
def prefixEnd_7646162 : Nat := 4983230072969 + 3 ^ 40 * 7646162 * 2
def baseEnd_7646162 : Nat := 436239585349246509967883

theorem tailTrace_7646162 : CollatzResearch.WordTrace tailWord_7646162 prefixEnd_7646162 436239585349246509967883 := by
  unfold tailWord_7646162
  simp only [CollatzResearch.WordTrace]
  refine ⟨69719609731317102337461185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185918959283512272899896493 69719609731317102337461185)
  ·
    refine ⟨52289707298487826753095889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69719609731317102337461185 52289707298487826753095889)
    ·
      refine ⟨39217280473865870064821917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52289707298487826753095889 39217280473865870064821917)
      ·
        refine ⟨14706480177699701274308219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39217280473865870064821917 14706480177699701274308219)
        ·
          refine ⟨22059720266549551911462329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14706480177699701274308219 22059720266549551911462329)
          ·
            refine ⟨16544790199912163933596747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22059720266549551911462329 16544790199912163933596747)
            ·
              refine ⟨24817185299868245900395121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16544790199912163933596747 24817185299868245900395121)
              ·
                refine ⟨18612888974901184425296341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24817185299868245900395121 18612888974901184425296341)
                ·
                  refine ⟨436239585349246509967883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18612888974901184425296341 436239585349246509967883)
                  ·
                    rfl

theorem cell23_7646162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_7646162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646162 prefixEnd_7646162 := by exact prefixLift 7646162
  have htrace : WordTrace (prefixWord ++ tailWord_7646162) baseStart_7646162 baseEnd_7646162 := by
    simpa [prefixWord, tailWord_7646162, baseEnd_7646162] using wordTrace_append hprefix tailTrace_7646162
  have hstable : (prefixWord ++ tailWord_7646162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646162).length < 2 ^ (prefixWord ++ tailWord_7646162).sum := by decide
  have hdescent : baseEnd_7646162 < baseStart_7646162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646190 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_7646190 : Nat := 118140960795 + 7646190 * 2 ^ 59
def prefixEnd_7646190 : Nat := 4983230072969 + 3 ^ 40 * 7646190 * 2
def baseEnd_7646190 : Nat := 3926170645601544480160819

theorem tailTrace_7646190 : CollatzResearch.WordTrace tailWord_7646190 prefixEnd_7646190 3926170645601544480160819 := by
  unfold tailWord_7646190
  simp only [CollatzResearch.WordTrace]
  refine ⟨34859932521145871266483003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185919640112777980087909349 34859932521145871266483003)
  ·
    refine ⟨52289898781718806899724505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34859932521145871266483003 52289898781718806899724505)
    ·
      refine ⟨39217424086289105174793379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52289898781718806899724505 39217424086289105174793379)
      ·
        refine ⟨58826136129433657762190069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39217424086289105174793379 58826136129433657762190069)
        ·
          refine ⟨5514950262134405415205319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58826136129433657762190069 5514950262134405415205319)
          ·
            refine ⟨8272425393201608122807979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514950262134405415205319 8272425393201608122807979)
            ·
              refine ⟨12408638089802412184211969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272425393201608122807979 12408638089802412184211969)
              ·
                refine ⟨9306478567351809138158977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12408638089802412184211969 9306478567351809138158977)
                ·
                  refine ⟨6979858925513856853619233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9306478567351809138158977 6979858925513856853619233)
                  ·
                    refine ⟨5234894194135392640214425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6979858925513856853619233 5234894194135392640214425)
                    ·
                      refine ⟨3926170645601544480160819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234894194135392640214425 3926170645601544480160819)
                      ·
                        rfl

theorem cell23_7646190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_7646190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646190 prefixEnd_7646190 := by exact prefixLift 7646190
  have htrace : WordTrace (prefixWord ++ tailWord_7646190) baseStart_7646190 baseEnd_7646190 := by
    simpa [prefixWord, tailWord_7646190, baseEnd_7646190] using wordTrace_append hprefix tailTrace_7646190
  have hstable : (prefixWord ++ tailWord_7646190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646190).length < 2 ^ (prefixWord ++ tailWord_7646190).sum := by decide
  have hdescent : baseEnd_7646190 < baseStart_7646190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646232 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_7646232 : Nat := 118140960795 + 7646232 * 2 ^ 59
def prefixEnd_7646232 : Nat := 4983230072969 + 3 ^ 40 * 7646232 * 2
def baseEnd_7646232 : Nat := 3926192211789033315835625

theorem tailTrace_7646232 : CollatzResearch.WordTrace tailWord_7646232 prefixEnd_7646232 3926192211789033315835625 := by
  unfold tailWord_7646232
  simp only [CollatzResearch.WordTrace]
  refine ⟨139440496017507405652446475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185920661356676540869928633 139440496017507405652446475)
  ·
    refine ⟨209160744026261108478669713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139440496017507405652446475 209160744026261108478669713)
    ·
      refine ⟨156870558019695831359002285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209160744026261108478669713 156870558019695831359002285)
      ·
        refine ⟨58826459257385936759625857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156870558019695831359002285 58826459257385936759625857)
        ·
          refine ⟨44119844443039452569719393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58826459257385936759625857 44119844443039452569719393)
          ·
            refine ⟨33089883332279589427289545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44119844443039452569719393 33089883332279589427289545)
            ·
              refine ⟨24817412499209692070467159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33089883332279589427289545 24817412499209692070467159)
              ·
                refine ⟨37226118748814538105700739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24817412499209692070467159 37226118748814538105700739)
                ·
                  refine ⟨55839178123221807158551109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37226118748814538105700739 55839178123221807158551109)
                  ·
                    refine ⟨10469845898104088842228333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55839178123221807158551109 10469845898104088842228333)
                    ·
                      refine ⟨3926192211789033315835625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469845898104088842228333 3926192211789033315835625)
                      ·
                        rfl

theorem cell23_7646232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_7646232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646232 prefixEnd_7646232 := by exact prefixLift 7646232
  have htrace : WordTrace (prefixWord ++ tailWord_7646232) baseStart_7646232 baseEnd_7646232 := by
    simpa [prefixWord, tailWord_7646232, baseEnd_7646232] using wordTrace_append hprefix tailTrace_7646232
  have hstable : (prefixWord ++ tailWord_7646232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646232).length < 2 ^ (prefixWord ++ tailWord_7646232).sum := by decide
  have hdescent : baseEnd_7646232 < baseStart_7646232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646256 : List Nat := [2, 1, 1, 1, 2, 4, 5, 2, 1, 4]
def baseStart_7646256 : Nat := 118140960795 + 7646256 * 2 ^ 59
def prefixEnd_7646256 : Nat := 4983230072969 + 3 ^ 40 * 7646256 * 2
def baseEnd_7646256 : Nat := 1308734845108247073978505

theorem tailTrace_7646256 : CollatzResearch.WordTrace tailWord_7646256 prefixEnd_7646256 1308734845108247073978505 := by
  unfold tailWord_7646256
  simp only [CollatzResearch.WordTrace]
  refine ⟨139440933693463931701883311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185921244924618575602511081 139440933693463931701883311)
  ·
    refine ⟨209161400540195897552824967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139440933693463931701883311 209161400540195897552824967)
    ·
      refine ⟨313742100810293846329237451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209161400540195897552824967 313742100810293846329237451)
      ·
        refine ⟨470613151215440769493856177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313742100810293846329237451 470613151215440769493856177)
        ·
          refine ⟨352959863411580577120392133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470613151215440769493856177 352959863411580577120392133)
          ·
            refine ⟨66179974389671358210073525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352959863411580577120392133 66179974389671358210073525)
            ·
              refine ⟨6204372599031689832194393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66179974389671358210073525 6204372599031689832194393)
              ·
                refine ⟨4653279449273767374145795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204372599031689832194393 4653279449273767374145795)
                ·
                  refine ⟨6979919173910651061218693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653279449273767374145795 6979919173910651061218693)
                  ·
                    refine ⟨1308734845108247073978505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6979919173910651061218693 1308734845108247073978505)
                    ·
                      rfl

theorem cell23_7646256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 4].length) (baseStart_7646256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646256 prefixEnd_7646256 := by exact prefixLift 7646256
  have htrace : WordTrace (prefixWord ++ tailWord_7646256) baseStart_7646256 baseEnd_7646256 := by
    simpa [prefixWord, tailWord_7646256, baseEnd_7646256] using wordTrace_append hprefix tailTrace_7646256
  have hstable : (prefixWord ++ tailWord_7646256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646256).length < 2 ^ (prefixWord ++ tailWord_7646256).sum := by decide
  have hdescent : baseEnd_7646256 < baseStart_7646256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646269 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 6]
def baseStart_7646269 : Nat := 118140960795 + 7646269 * 2 ^ 59
def prefixEnd_7646269 : Nat := 4983230072969 + 3 ^ 40 * 7646269 * 2
def baseEnd_7646269 : Nat := 436245690063694407896995

theorem tailTrace_7646269 : CollatzResearch.WordTrace tailWord_7646269 prefixEnd_7646269 436245690063694407896995 := by
  unfold tailWord_7646269
  simp only [CollatzResearch.WordTrace]
  refine ⟨278882341535880766623989861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185921561023920511082659907 278882341535880766623989861)
  ·
    refine ⟨52290439037977643741998099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 278882341535880766623989861 52290439037977643741998099)
    ·
      refine ⟨78435658556966465612997149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52290439037977643741998099 78435658556966465612997149)
      ·
        refine ⟨29413371958862424604873931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78435658556966465612997149 29413371958862424604873931)
        ·
          refine ⟨44120057938293636907310897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29413371958862424604873931 44120057938293636907310897)
          ·
            refine ⟨33090043453720227680483173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44120057938293636907310897 33090043453720227680483173)
            ·
              refine ⟨6204383147572542690090595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33090043453720227680483173 6204383147572542690090595)
              ·
                refine ⟨9306574721358814035135893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204383147572542690090595 9306574721358814035135893)
                ·
                  refine ⟨436245690063694407896995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9306574721358814035135893 436245690063694407896995)
                  ·
                    rfl

theorem cell23_7646269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_7646269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646269 prefixEnd_7646269 := by exact prefixLift 7646269
  have htrace : WordTrace (prefixWord ++ tailWord_7646269) baseStart_7646269 baseEnd_7646269 := by
    simpa [prefixWord, tailWord_7646269, baseEnd_7646269] using wordTrace_append hprefix tailTrace_7646269
  have hstable : (prefixWord ++ tailWord_7646269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646269).length < 2 ^ (prefixWord ++ tailWord_7646269).sum := by decide
  have hdescent : baseEnd_7646269 < baseStart_7646269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646289 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 2, 3, 2]
def baseStart_7646289 : Nat := 118140960795 + 7646289 * 2 ^ 59
def prefixEnd_7646289 : Nat := 4983230072969 + 3 ^ 40 * 7646289 * 2
def baseEnd_7646289 : Nat := 3926221480186339592822863

theorem tailTrace_7646289 : CollatzResearch.WordTrace tailWord_7646289 prefixEnd_7646289 3926221480186339592822863 := by
  unfold tailWord_7646289
  simp only [CollatzResearch.WordTrace]
  refine ⟨278883070995808310039717921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185922047330538873359811947 278883070995808310039717921)
  ·
    refine ⟨209162303246856232529788441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278883070995808310039717921 209162303246856232529788441)
    ·
      refine ⟨156871727435142174397341331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209162303246856232529788441 156871727435142174397341331)
      ·
        refine ⟨235307591152713261596011997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156871727435142174397341331 235307591152713261596011997)
        ·
          refine ⟨88240346682267473098504499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235307591152713261596011997 88240346682267473098504499)
          ·
            refine ⟨132360520023401209647756749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88240346682267473098504499 132360520023401209647756749)
            ·
              refine ⟨49635195008775453617908781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132360520023401209647756749 49635195008775453617908781)
              ·
                refine ⟨18613198128290795106715793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49635195008775453617908781 18613198128290795106715793)
                ·
                  refine ⟨13959898596218096330036845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18613198128290795106715793 13959898596218096330036845)
                  ·
                    refine ⟨5234961973581786123763817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13959898596218096330036845 5234961973581786123763817)
                    ·
                      refine ⟨3926221480186339592822863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5234961973581786123763817 3926221480186339592822863)
                      ·
                        rfl

theorem cell23_7646289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_7646289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646289 prefixEnd_7646289 := by exact prefixLift 7646289
  have htrace : WordTrace (prefixWord ++ tailWord_7646289) baseStart_7646289 baseEnd_7646289 := by
    simpa [prefixWord, tailWord_7646289, baseEnd_7646289] using wordTrace_append hprefix tailTrace_7646289
  have hstable : (prefixWord ++ tailWord_7646289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646289).length < 2 ^ (prefixWord ++ tailWord_7646289).sum := by decide
  have hdescent : baseEnd_7646289 < baseStart_7646289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646296 : List Nat := [2, 1, 2, 2, 1, 3, 2, 5, 1, 1, 3]
def baseStart_7646296 : Nat := 118140960795 + 7646296 * 2 ^ 59
def prefixEnd_7646296 : Nat := 4983230072969 + 3 ^ 40 * 7646296 * 2
def baseEnd_7646296 : Nat := 3926225074550921065435331

theorem tailTrace_7646296 : CollatzResearch.WordTrace tailWord_7646296 prefixEnd_7646296 3926225074550921065435331 := by
  unfold tailWord_7646296
  simp only [CollatzResearch.WordTrace]
  refine ⟨139441663153391475117611371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185922217537855300156815161 139441663153391475117611371)
  ·
    refine ⟨209162494730087212676417057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139441663153391475117611371 209162494730087212676417057)
    ·
      refine ⟨156871871047565409507312793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209162494730087212676417057 156871871047565409507312793)
      ·
        refine ⟨117653903285674057130484595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156871871047565409507312793 117653903285674057130484595)
        ·
          refine ⟨176480854928511085695726893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117653903285674057130484595 176480854928511085695726893)
          ·
            refine ⟨66180320598191657135897585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176480854928511085695726893 66180320598191657135897585)
            ·
              refine ⟨49635240448643742851923189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66180320598191657135897585 49635240448643742851923189)
              ·
                refine ⟨4653303792060350892367799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49635240448643742851923189 4653303792060350892367799)
                ·
                  refine ⟨6979955688090526338551699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653303792060350892367799 6979955688090526338551699)
                  ·
                    refine ⟨10469933532135789507827549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979955688090526338551699 10469933532135789507827549)
                    ·
                      refine ⟨3926225074550921065435331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469933532135789507827549 3926225074550921065435331)
                      ·
                        rfl

theorem cell23_7646296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_7646296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646296 prefixEnd_7646296 := by exact prefixLift 7646296
  have htrace : WordTrace (prefixWord ++ tailWord_7646296) baseStart_7646296 baseEnd_7646296 := by
    simpa [prefixWord, tailWord_7646296, baseEnd_7646296] using wordTrace_append hprefix tailTrace_7646296
  have hstable : (prefixWord ++ tailWord_7646296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646296).length < 2 ^ (prefixWord ++ tailWord_7646296).sum := by decide
  have hdescent : baseEnd_7646296 < baseStart_7646296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646313 : List Nat := [1, 2, 1, 1, 1, 6, 4, 2, 1, 1, 3]
def baseStart_7646313 : Nat := 118140960795 + 7646313 * 2 ^ 59
def prefixEnd_7646313 : Nat := 4983230072969 + 3 ^ 40 * 7646313 * 2
def baseEnd_7646313 : Nat := 3926233803722047498922753

theorem tailTrace_7646313 : CollatzResearch.WordTrace tailWord_7646313 prefixEnd_7646313 3926233803722047498922753 := by
  unfold tailWord_7646313
  simp only [CollatzResearch.WordTrace]
  refine ⟨278883946347721362138591593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185922630898480908092394395 278883946347721362138591593)
  ·
    refine ⟨209162959760791021603943695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278883946347721362138591593 209162959760791021603943695)
    ·
      refine ⟨313744439641186532405915543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209162959760791021603943695 313744439641186532405915543)
      ·
        refine ⟨470616659461779798608873315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313744439641186532405915543 470616659461779798608873315)
        ·
          refine ⟨705924989192669697913309973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470616659461779798608873315 705924989192669697913309973)
          ·
            refine ⟨33090233868406392089686405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 705924989192669697913309973 33090233868406392089686405)
            ·
              refine ⟨6204418850326198516816201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33090233868406392089686405 6204418850326198516816201)
              ·
                refine ⟨4653314137744648887612151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204418850326198516816201 4653314137744648887612151)
                ·
                  refine ⟨6979971206616973331418227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653314137744648887612151 6979971206616973331418227)
                  ·
                    refine ⟨10469956809925459997127341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6979971206616973331418227 10469956809925459997127341)
                    ·
                      refine ⟨3926233803722047498922753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469956809925459997127341 3926233803722047498922753)
                      ·
                        rfl

theorem cell23_7646313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 1, 3].length) (baseStart_7646313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646313 prefixEnd_7646313 := by exact prefixLift 7646313
  have htrace : WordTrace (prefixWord ++ tailWord_7646313) baseStart_7646313 baseEnd_7646313 := by
    simpa [prefixWord, tailWord_7646313, baseEnd_7646313] using wordTrace_append hprefix tailTrace_7646313
  have hstable : (prefixWord ++ tailWord_7646313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646313).length < 2 ^ (prefixWord ++ tailWord_7646313).sum := by decide
  have hdescent : baseEnd_7646313 < baseStart_7646313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646322 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_7646322 : Nat := 118140960795 + 7646322 * 2 ^ 59
def prefixEnd_7646322 : Nat := 4983230072969 + 3 ^ 40 * 7646322 * 2
def baseEnd_7646322 : Nat := 3926238425047937963710211

theorem tailTrace_7646322 : CollatzResearch.WordTrace tailWord_7646322 prefixEnd_7646322 3926238425047937963710211 := by
  unfold tailWord_7646322
  simp only [CollatzResearch.WordTrace]
  refine ⟨69721068651172189168917305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185922849736459171117112813 69721068651172189168917305)
  ·
    refine ⟨52290801488379141876687979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69721068651172189168917305 52290801488379141876687979)
    ·
      refine ⟨78436202232568712815031969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52290801488379141876687979 78436202232568712815031969)
      ·
        refine ⟨58827151674426534611273977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78436202232568712815031969 58827151674426534611273977)
        ·
          refine ⟨44120363755819900958455483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58827151674426534611273977 44120363755819900958455483)
          ·
            refine ⟨66180545633729851437683225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44120363755819900958455483 66180545633729851437683225)
            ·
              refine ⟨49635409225297388578262419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66180545633729851437683225 49635409225297388578262419)
              ·
                refine ⟨74453113837946082867393629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49635409225297388578262419 74453113837946082867393629)
                ·
                  refine ⟨27919917689229781075272611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74453113837946082867393629 27919917689229781075272611)
                  ·
                    refine ⟨41879876533844671612908917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27919917689229781075272611 41879876533844671612908917)
                    ·
                      refine ⟨3926238425047937963710211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41879876533844671612908917 3926238425047937963710211)
                      ·
                        rfl

theorem cell23_7646322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_7646322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646322 prefixEnd_7646322 := by exact prefixLift 7646322
  have htrace : WordTrace (prefixWord ++ tailWord_7646322) baseStart_7646322 baseEnd_7646322 := by
    simpa [prefixWord, tailWord_7646322, baseEnd_7646322] using wordTrace_append hprefix tailTrace_7646322
  have hstable : (prefixWord ++ tailWord_7646322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646322).length < 2 ^ (prefixWord ++ tailWord_7646322).sum := by decide
  have hdescent : baseEnd_7646322 < baseStart_7646322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646329 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 1, 6]
def baseStart_7646329 : Nat := 118140960795 + 7646329 * 2 ^ 59
def prefixEnd_7646329 : Nat := 4983230072969 + 3 ^ 40 * 7646329 * 2
def baseEnd_7646329 : Nat := 1308747339804173145440893

theorem tailTrace_7646329 : CollatzResearch.WordTrace tailWord_7646329 prefixEnd_7646329 1308747339804173145440893 := by
  unfold tailWord_7646329
  simp only [CollatzResearch.WordTrace]
  refine ⟨278884529915663396871174041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185923019943775597914116027 278884529915663396871174041)
  ·
    refine ⟨209163397436747547653380531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278884529915663396871174041 209163397436747547653380531)
    ·
      refine ⟨313745096155121321480070797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209163397436747547653380531 313745096155121321480070797)
      ·
        refine ⟨117654411058170495555026549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313745096155121321480070797 117654411058170495555026549)
        ·
          refine ⟨11030101036703483958283739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117654411058170495555026549 11030101036703483958283739)
          ·
            refine ⟨16545151555055225937425609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11030101036703483958283739 16545151555055225937425609)
            ·
              refine ⟨12408863666291419453069207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16545151555055225937425609 12408863666291419453069207)
              ·
                refine ⟨18613295499437129179603811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12408863666291419453069207 18613295499437129179603811)
                ·
                  refine ⟨27919943249155693769405717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18613295499437129179603811 27919943249155693769405717)
                  ·
                    refine ⟨1308747339804173145440893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27919943249155693769405717 1308747339804173145440893)
                    ·
                      rfl

theorem cell23_7646329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_7646329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646329 prefixEnd_7646329 := by exact prefixLift 7646329
  have htrace : WordTrace (prefixWord ++ tailWord_7646329) baseStart_7646329 baseEnd_7646329 := by
    simpa [prefixWord, tailWord_7646329, baseEnd_7646329] using wordTrace_append hprefix tailTrace_7646329
  have hstable : (prefixWord ++ tailWord_7646329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646329).length < 2 ^ (prefixWord ++ tailWord_7646329).sum := by decide
  have hdescent : baseEnd_7646329 < baseStart_7646329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646335 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_7646335 : Nat := 118140960795 + 7646335 * 2 ^ 59
def prefixEnd_7646335 : Nat := 4983230072969 + 3 ^ 40 * 7646335 * 2
def baseEnd_7646335 : Nat := 3926245100296446412847651

theorem tailTrace_7646335 : CollatzResearch.WordTrace tailWord_7646335 prefixEnd_7646335 3926245100296446412847651 := by
  unfold tailWord_7646335
  simp only [CollatzResearch.WordTrace]
  refine ⟨278884748753641659895892459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185923165835761106597261639 278884748753641659895892459)
  ·
    refine ⟨418327123130462489843838689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278884748753641659895892459 418327123130462489843838689)
    ·
      refine ⟨313745342347846867382879017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418327123130462489843838689 313745342347846867382879017)
      ·
        refine ⟨235309006760885150537159263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313745342347846867382879017 235309006760885150537159263)
        ·
          refine ⟨352963510141327725805738895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235309006760885150537159263 352963510141327725805738895)
          ·
            refine ⟨529445265211991588708608343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352963510141327725805738895 529445265211991588708608343)
            ·
              refine ⟨794167897817987383062912515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 529445265211991588708608343 794167897817987383062912515)
              ·
                refine ⟨1191251846726981074594368773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794167897817987383062912515 1191251846726981074594368773)
                ·
                  refine ⟨223359721261308951486444145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1191251846726981074594368773 223359721261308951486444145)
                  ·
                    refine ⟨167519790945981713614833109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 223359721261308951486444145 167519790945981713614833109)
                    ·
                      refine ⟨3926245100296446412847651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 167519790945981713614833109 3926245100296446412847651)
                      ·
                        rfl

theorem cell23_7646335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_7646335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646335 prefixEnd_7646335 := by exact prefixLift 7646335
  have htrace : WordTrace (prefixWord ++ tailWord_7646335) baseStart_7646335 baseEnd_7646335 := by
    simpa [prefixWord, tailWord_7646335, baseEnd_7646335] using wordTrace_append hprefix tailTrace_7646335
  have hstable : (prefixWord ++ tailWord_7646335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646335).length < 2 ^ (prefixWord ++ tailWord_7646335).sum := by decide
  have hdescent : baseEnd_7646335 < baseStart_7646335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646339 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 3]
def baseStart_7646339 : Nat := 118140960795 + 7646339 * 2 ^ 59
def prefixEnd_7646339 : Nat := 4983230072969 + 3 ^ 40 * 7646339 * 2
def baseEnd_7646339 : Nat := 3926247154219064397197633

theorem tailTrace_7646339 : CollatzResearch.WordTrace tailWord_7646339 prefixEnd_7646339 3926247154219064397197633 := by
  unfold tailWord_7646339
  simp only [CollatzResearch.WordTrace]
  refine ⟨278884894645627168579038071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185923263097084779052692047 278884894645627168579038071)
  ·
    refine ⟨418327341968440752868557107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278884894645627168579038071 418327341968440752868557107)
    ·
      refine ⟨627491012952661129302835661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418327341968440752868557107 627491012952661129302835661)
      ·
        refine ⟨235309129857247923488563373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627491012952661129302835661 235309129857247923488563373)
        ·
          refine ⟨88240923696467971308211265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235309129857247923488563373 88240923696467971308211265)
          ·
            refine ⟨66180692772350978481158449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88240923696467971308211265 66180692772350978481158449)
            ·
              refine ⟨49635519579263233860868837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66180692772350978481158449 49635519579263233860868837)
              ·
                refine ⟨9306659921111856348912907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49635519579263233860868837 9306659921111856348912907)
                ·
                  refine ⟨13959989881667784523369361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9306659921111856348912907 13959989881667784523369361)
                  ·
                    refine ⟨10469992411250838392527021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13959989881667784523369361 10469992411250838392527021)
                    ·
                      refine ⟨3926247154219064397197633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10469992411250838392527021 3926247154219064397197633)
                      ·
                        rfl

theorem cell23_7646339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_7646339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646339 prefixEnd_7646339 := by exact prefixLift 7646339
  have htrace : WordTrace (prefixWord ++ tailWord_7646339) baseStart_7646339 baseEnd_7646339 := by
    simpa [prefixWord, tailWord_7646339, baseEnd_7646339] using wordTrace_append hprefix tailTrace_7646339
  have hstable : (prefixWord ++ tailWord_7646339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646339).length < 2 ^ (prefixWord ++ tailWord_7646339).sum := by decide
  have hdescent : baseEnd_7646339 < baseStart_7646339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646352 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3]
def baseStart_7646352 : Nat := 118140960795 + 7646352 * 2 ^ 59
def prefixEnd_7646352 : Nat := 4983230072969 + 3 ^ 40 * 7646352 * 2
def baseEnd_7646352 : Nat := 3926253829467572846335073

theorem tailTrace_7646352 : CollatzResearch.WordTrace tailWord_7646352 prefixEnd_7646352 3926253829467572846335073 := by
  unfold tailWord_7646352
  simp only [CollatzResearch.WordTrace]
  refine ⟨139442684397290035899630655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185923579196386714532840873 139442684397290035899630655)
  ·
    refine ⟨209164026595935053849445983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139442684397290035899630655 209164026595935053849445983)
    ·
      refine ⟨313746039893902580774168975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209164026595935053849445983 313746039893902580774168975)
      ·
        refine ⟨470619059840853871161253463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313746039893902580774168975 470619059840853871161253463)
        ·
          refine ⟨705928589761280806741880195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470619059840853871161253463 705928589761280806741880195)
          ·
            refine ⟨1058892884641921210112820293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705928589761280806741880195 1058892884641921210112820293)
            ·
              refine ⟨198542415870360226896153805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1058892884641921210112820293 198542415870360226896153805)
              ·
                refine ⟨74453405951385085086057677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198542415870360226896153805 74453405951385085086057677)
                ·
                  refine ⟨27920027231769406907271629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74453405951385085086057677 27920027231769406907271629)
                  ·
                    refine ⟨10470010211913527590226861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27920027231769406907271629 10470010211913527590226861)
                    ·
                      refine ⟨3926253829467572846335073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470010211913527590226861 3926253829467572846335073)
                      ·
                        rfl

theorem cell23_7646352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_7646352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646352 prefixEnd_7646352 := by exact prefixLift 7646352
  have htrace : WordTrace (prefixWord ++ tailWord_7646352) baseStart_7646352 baseEnd_7646352 := by
    simpa [prefixWord, tailWord_7646352, baseEnd_7646352] using wordTrace_append hprefix tailTrace_7646352
  have hstable : (prefixWord ++ tailWord_7646352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646352).length < 2 ^ (prefixWord ++ tailWord_7646352).sum := by decide
  have hdescent : baseEnd_7646352 < baseStart_7646352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646370 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_7646370 : Nat := 118140960795 + 7646370 * 2 ^ 59
def prefixEnd_7646370 : Nat := 4983230072969 + 3 ^ 40 * 7646370 * 2
def baseEnd_7646370 : Nat := 3926263072119353775909991

theorem tailTrace_7646370 : CollatzResearch.WordTrace tailWord_7646370 prefixEnd_7646370 3926263072119353775909991 := by
  unfold tailWord_7646370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69721506327128715218354141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185924016872343240582277709 69721506327128715218354141)
  ·
    refine ⟨26145564872673268206882803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69721506327128715218354141 26145564872673268206882803)
    ·
      refine ⟨39218347309009902310324205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26145564872673268206882803 39218347309009902310324205)
      ·
        refine ⟨14706880240878713366371577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39218347309009902310324205 14706880240878713366371577)
        ·
          refine ⟨11030160180659035024778683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14706880240878713366371577 11030160180659035024778683)
          ·
            refine ⟨16545240270988552537168025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11030160180659035024778683 16545240270988552537168025)
            ·
              refine ⟨12408930203241414402876019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16545240270988552537168025 12408930203241414402876019)
              ·
                refine ⟨18613395304862121604314029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12408930203241414402876019 18613395304862121604314029)
                ·
                  refine ⟨6980023239323295601617761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18613395304862121604314029 6980023239323295601617761)
                  ·
                    refine ⟨5235017429492471701213321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6980023239323295601617761 5235017429492471701213321)
                    ·
                      refine ⟨3926263072119353775909991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235017429492471701213321 3926263072119353775909991)
                      ·
                        rfl

theorem cell23_7646370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_7646370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646370 prefixEnd_7646370 := by exact prefixLift 7646370
  have htrace : WordTrace (prefixWord ++ tailWord_7646370) baseStart_7646370 baseEnd_7646370 := by
    simpa [prefixWord, tailWord_7646370, baseEnd_7646370] using wordTrace_append hprefix tailTrace_7646370
  have hstable : (prefixWord ++ tailWord_7646370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646370).length < 2 ^ (prefixWord ++ tailWord_7646370).sum := by decide
  have hdescent : baseEnd_7646370 < baseStart_7646370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646386 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_7646386 : Nat := 118140960795 + 7646386 * 2 ^ 59
def prefixEnd_7646386 : Nat := 4983230072969 + 3 ^ 40 * 7646386 * 2
def baseEnd_7646386 : Nat := 3926271287809825713309917

theorem tailTrace_7646386 : CollatzResearch.WordTrace tailWord_7646386 prefixEnd_7646386 3926271287809825713309917 := by
  unfold tailWord_7646386
  simp only [CollatzResearch.WordTrace]
  refine ⟨69721652219114223901499753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185924405917637930403999341 69721652219114223901499753)
  ·
    refine ⟨52291239164335667926124815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69721652219114223901499753 52291239164335667926124815)
    ·
      refine ⟨78436858746503501889187223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52291239164335667926124815 78436858746503501889187223)
      ·
        refine ⟨117655288119755252833780835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78436858746503501889187223 117655288119755252833780835)
        ·
          refine ⟨176482932179632879250671253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117655288119755252833780835 176482932179632879250671253)
          ·
            refine ⟨8272637445920291214875215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176482932179632879250671253 8272637445920291214875215)
            ·
              refine ⟨12408956168880436822312823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272637445920291214875215 12408956168880436822312823)
              ·
                refine ⟨18613434253320655233469235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12408956168880436822312823 18613434253320655233469235)
                ·
                  refine ⟨27920151379980982850203853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18613434253320655233469235 27920151379980982850203853)
                  ·
                    refine ⟨10470056767492868568826445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27920151379980982850203853 10470056767492868568826445)
                    ·
                      refine ⟨3926271287809825713309917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470056767492868568826445 3926271287809825713309917)
                      ·
                        rfl

theorem cell23_7646386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_7646386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646386 prefixEnd_7646386 := by exact prefixLift 7646386
  have htrace : WordTrace (prefixWord ++ tailWord_7646386) baseStart_7646386 baseEnd_7646386 := by
    simpa [prefixWord, tailWord_7646386, baseEnd_7646386] using wordTrace_append hprefix tailTrace_7646386
  have hstable : (prefixWord ++ tailWord_7646386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646386).length < 2 ^ (prefixWord ++ tailWord_7646386).sum := by decide
  have hdescent : baseEnd_7646386 < baseStart_7646386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646404 : List Nat := [2, 3, 3, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_7646404 : Nat := 118140960795 + 7646404 * 2 ^ 59
def prefixEnd_7646404 : Nat := 4983230072969 + 3 ^ 40 * 7646404 * 2
def baseEnd_7646404 : Nat := 3926280530461606642884835

theorem tailTrace_7646404 : CollatzResearch.WordTrace tailWord_7646404 prefixEnd_7646404 3926280530461606642884835 := by
  unfold tailWord_7646404
  simp only [CollatzResearch.WordTrace]
  refine ⟨139443632695195842340077133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185924843593594456453436177 139443632695195842340077133)
  ·
    refine ⟨52291362260698440877528925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139443632695195842340077133 52291362260698440877528925)
    ·
      refine ⟨19609260847761915329073347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52291362260698440877528925 19609260847761915329073347)
      ·
        refine ⟨29413891271642872993610021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19609260847761915329073347 29413891271642872993610021)
        ·
          refine ⟨5515104613433038686301879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29413891271642872993610021 5515104613433038686301879)
          ·
            refine ⟨8272656920149558029452819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515104613433038686301879 8272656920149558029452819)
            ·
              refine ⟨12408985380224337044179229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272656920149558029452819 12408985380224337044179229)
              ·
                refine ⟨4653369517584126391567211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12408985380224337044179229 4653369517584126391567211)
                ·
                  refine ⟨6980054276376189587350817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653369517584126391567211 6980054276376189587350817)
                  ·
                    refine ⟨5235040707282142190513113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6980054276376189587350817 5235040707282142190513113)
                    ·
                      refine ⟨3926280530461606642884835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235040707282142190513113 3926280530461606642884835)
                      ·
                        rfl

theorem cell23_7646404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_7646404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646404 prefixEnd_7646404 := by exact prefixLift 7646404
  have htrace : WordTrace (prefixWord ++ tailWord_7646404) baseStart_7646404 baseEnd_7646404 := by
    simpa [prefixWord, tailWord_7646404, baseEnd_7646404] using wordTrace_append hprefix tailTrace_7646404
  have hstable : (prefixWord ++ tailWord_7646404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646404).length < 2 ^ (prefixWord ++ tailWord_7646404).sum := by decide
  have hdescent : baseEnd_7646404 < baseStart_7646404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646437 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 2, 1, 3]
def baseStart_7646437 : Nat := 118140960795 + 7646437 * 2 ^ 59
def prefixEnd_7646437 : Nat := 4983230072969 + 3 ^ 40 * 7646437 * 2
def baseEnd_7646437 : Nat := 3926297475323205013772183

theorem tailTrace_7646437 : CollatzResearch.WordTrace tailWord_7646437 prefixEnd_7646437 3926297475323205013772183 := by
  unfold tailWord_7646437
  simp only [CollatzResearch.WordTrace]
  refine ⟨278888468999272131316105565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185925645999514754210737043 278888468999272131316105565)
  ·
    refine ⟨104583175874727049243539587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 278888468999272131316105565 104583175874727049243539587)
    ·
      refine ⟨156874763812090573865309381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104583175874727049243539587 156874763812090573865309381)
      ·
        refine ⟨29414018214766982599745509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156874763812090573865309381 29414018214766982599745509)
        ·
          refine ⟨5515128415268809237452283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29414018214766982599745509 5515128415268809237452283)
          ·
            refine ⟨8272692622903213856178425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515128415268809237452283 8272692622903213856178425)
            ·
              refine ⟨6204519467177410392133819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8272692622903213856178425 6204519467177410392133819)
              ·
                refine ⟨9306779200766115588200729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204519467177410392133819 9306779200766115588200729)
                ·
                  refine ⟨6980084400574586691150547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9306779200766115588200729 6980084400574586691150547)
                  ·
                    refine ⟨10470126600861880036725821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6980084400574586691150547 10470126600861880036725821)
                    ·
                      refine ⟨3926297475323205013772183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470126600861880036725821 3926297475323205013772183)
                      ·
                        rfl

theorem cell23_7646437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_7646437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646437 prefixEnd_7646437 := by exact prefixLift 7646437
  have htrace : WordTrace (prefixWord ++ tailWord_7646437) baseStart_7646437 baseEnd_7646437 := by
    simpa [prefixWord, tailWord_7646437, baseEnd_7646437] using wordTrace_append hprefix tailTrace_7646437
  have hstable : (prefixWord ++ tailWord_7646437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646437).length < 2 ^ (prefixWord ++ tailWord_7646437).sum := by decide
  have hdescent : baseEnd_7646437 < baseStart_7646437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646443 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 2, 2, 2]
def baseStart_7646443 : Nat := 118140960795 + 7646443 * 2 ^ 59
def prefixEnd_7646443 : Nat := 4983230072969 + 3 ^ 40 * 7646443 * 2
def baseEnd_7646443 : Nat := 3926300556207131990297155

theorem tailTrace_7646443 : CollatzResearch.WordTrace tailWord_7646443 prefixEnd_7646443 3926300556207131990297155 := by
  unfold tailWord_7646443
  simp only [CollatzResearch.WordTrace]
  refine ⟨278888687837250394340823983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185925791891500262893882655 278888687837250394340823983)
  ·
    refine ⟨418333031755875591511235975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278888687837250394340823983 418333031755875591511235975)
    ·
      refine ⟨627499547633813387266853963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418333031755875591511235975 627499547633813387266853963)
      ·
        refine ⟨941249321450720080900280945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627499547633813387266853963 941249321450720080900280945)
        ·
          refine ⟨705936991088040060675210709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941249321450720080900280945 705936991088040060675210709)
          ·
            refine ⟨16545398228625938922075251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 705936991088040060675210709 16545398228625938922075251)
            ·
              refine ⟨24818097342938908383112877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16545398228625938922075251 24818097342938908383112877)
              ·
                refine ⟨9306786503602090643667329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24818097342938908383112877 9306786503602090643667329)
                ·
                  refine ⟨6980089877701567982750497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9306786503602090643667329 6980089877701567982750497)
                  ·
                    refine ⟨5235067408276175987062873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6980089877701567982750497 5235067408276175987062873)
                    ·
                      refine ⟨3926300556207131990297155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235067408276175987062873 3926300556207131990297155)
                      ·
                        rfl

theorem cell23_7646443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 2, 2].length) (baseStart_7646443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646443 prefixEnd_7646443 := by exact prefixLift 7646443
  have htrace : WordTrace (prefixWord ++ tailWord_7646443) baseStart_7646443 baseEnd_7646443 := by
    simpa [prefixWord, tailWord_7646443, baseEnd_7646443] using wordTrace_append hprefix tailTrace_7646443
  have hstable : (prefixWord ++ tailWord_7646443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646443).length < 2 ^ (prefixWord ++ tailWord_7646443).sum := by decide
  have hdescent : baseEnd_7646443 < baseStart_7646443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646516 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7646516 : Nat := 118140960795 + 7646516 * 2 ^ 59
def prefixEnd_7646516 : Nat := 4983230072969 + 3 ^ 40 * 7646516 * 2
def baseEnd_7646516 : Nat := 3926338040294910204684319

theorem tailTrace_7646516 : CollatzResearch.WordTrace tailWord_7646516 prefixEnd_7646516 3926338040294910204684319 := by
  unfold tailWord_7646516
  simp only [CollatzResearch.WordTrace]
  refine ⟨139445675182992963904115701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185927566910657285205487601 139445675182992963904115701)
  ·
    refine ⟨13073032048405590366010847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139445675182992963904115701 13073032048405590366010847)
    ·
      refine ⟨19609548072608385549016271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13073032048405590366010847 19609548072608385549016271)
      ·
        refine ⟨29414322108912578323524407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19609548072608385549016271 29414322108912578323524407)
        ·
          refine ⟨44121483163368867485286611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29414322108912578323524407 44121483163368867485286611)
          ·
            refine ⟨66182224745053301227929917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44121483163368867485286611 66182224745053301227929917)
            ·
              refine ⟨24818334279394987960473719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66182224745053301227929917 24818334279394987960473719)
              ·
                refine ⟨37227501419092481940710579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24818334279394987960473719 37227501419092481940710579)
                ·
                  refine ⟨55841252128638722911065869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37227501419092481940710579 55841252128638722911065869)
                  ·
                    refine ⟨20940469548239521091649701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55841252128638722911065869 20940469548239521091649701)
                    ·
                      refine ⟨3926338040294910204684319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20940469548239521091649701 3926338040294910204684319)
                      ·
                        rfl

theorem cell23_7646516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7646516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646516 prefixEnd_7646516 := by exact prefixLift 7646516
  have htrace : WordTrace (prefixWord ++ tailWord_7646516) baseStart_7646516 baseEnd_7646516 := by
    simpa [prefixWord, tailWord_7646516, baseEnd_7646516] using wordTrace_append hprefix tailTrace_7646516
  have hstable : (prefixWord ++ tailWord_7646516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646516).length < 2 ^ (prefixWord ++ tailWord_7646516).sum := by decide
  have hdescent : baseEnd_7646516 < baseStart_7646516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646526 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_7646526 : Nat := 118140960795 + 7646526 * 2 ^ 59
def prefixEnd_7646526 : Nat := 4983230072969 + 3 ^ 40 * 7646526 * 2
def baseEnd_7646526 : Nat := 1308781058367151721853091

theorem tailTrace_7646526 : CollatzResearch.WordTrace tailWord_7646526 prefixEnd_7646526 1308781058367151721853091 := by
  unfold tailWord_7646526
  simp only [CollatzResearch.WordTrace]
  refine ⟨34861464386993712439511929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 185927810063966466344063621 34861464386993712439511929)
  ·
    refine ⟨26146098290245284329633947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34861464386993712439511929 26146098290245284329633947)
    ·
      refine ⟨39219147435367926494450921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26146098290245284329633947 39219147435367926494450921)
      ·
        refine ⟨29414360576525944870838191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39219147435367926494450921 29414360576525944870838191)
        ·
          refine ⟨44121540864788917306257287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29414360576525944870838191 44121540864788917306257287)
          ·
            refine ⟨66182311297183375959385931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44121540864788917306257287 66182311297183375959385931)
            ·
              refine ⟨99273466945775063939078897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66182311297183375959385931 99273466945775063939078897)
              ·
                refine ⟨74455100209331297954309173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99273466945775063939078897 74455100209331297954309173)
                ·
                  refine ⟨6980165644624809183216485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74455100209331297954309173 6980165644624809183216485)
                  ·
                    refine ⟨1308781058367151721853091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6980165644624809183216485 1308781058367151721853091)
                    ·
                      rfl

theorem cell23_7646526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_7646526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646526 prefixEnd_7646526 := by exact prefixLift 7646526
  have htrace : WordTrace (prefixWord ++ tailWord_7646526) baseStart_7646526 baseEnd_7646526 := by
    simpa [prefixWord, tailWord_7646526, baseEnd_7646526] using wordTrace_append hprefix tailTrace_7646526
  have hstable : (prefixWord ++ tailWord_7646526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646526).length < 2 ^ (prefixWord ++ tailWord_7646526).sum := by decide
  have hdescent : baseEnd_7646526 < baseStart_7646526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646576 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 1, 5, 2]
def baseStart_7646576 : Nat := 118140960795 + 7646576 * 2 ^ 59
def prefixEnd_7646576 : Nat := 4983230072969 + 3 ^ 40 * 7646576 * 2
def baseEnd_7646576 : Nat := 3926368849134179969934043

theorem tailTrace_7646576 : CollatzResearch.WordTrace tailWord_7646576 prefixEnd_7646576 3926368849134179969934043 := by
  unfold tailWord_7646576
  simp only [CollatzResearch.WordTrace]
  refine ⟨139446769372884279027707791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185929025830512372036943721 139446769372884279027707791)
  ·
    refine ⟨209170154059326418541561687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139446769372884279027707791 209170154059326418541561687)
    ·
      refine ⟨313755231088989627812342531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209170154059326418541561687 313755231088989627812342531)
      ·
        refine ⟨470632846633484441718513797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313755231088989627812342531 470632846633484441718513797)
        ·
          refine ⟨88243658743778332822221337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 470632846633484441718513797 88243658743778332822221337)
          ·
            refine ⟨66182744057833749616666003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88243658743778332822221337 66182744057833749616666003)
            ·
              refine ⟨99274116086750624424999005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66182744057833749616666003 99274116086750624424999005)
              ·
                refine ⟨37227793532531484159374627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99274116086750624424999005 37227793532531484159374627)
                ·
                  refine ⟨55841690298797226239061941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37227793532531484159374627 55841690298797226239061941)
                  ·
                    refine ⟨5235158465512239959912057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55841690298797226239061941 5235158465512239959912057)
                    ·
                      refine ⟨3926368849134179969934043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5235158465512239959912057 3926368849134179969934043)
                      ·
                        rfl

theorem cell23_7646576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 5, 2].length) (baseStart_7646576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646576 prefixEnd_7646576 := by exact prefixLift 7646576
  have htrace : WordTrace (prefixWord ++ tailWord_7646576) baseStart_7646576 baseEnd_7646576 := by
    simpa [prefixWord, tailWord_7646576, baseEnd_7646576] using wordTrace_append hprefix tailTrace_7646576
  have hstable : (prefixWord ++ tailWord_7646576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646576).length < 2 ^ (prefixWord ++ tailWord_7646576).sum := by decide
  have hdescent : baseEnd_7646576 < baseStart_7646576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646594 : List Nat := [3, 4, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7646594 : Nat := 118140960795 + 7646594 * 2 ^ 59
def prefixEnd_7646594 : Nat := 4983230072969 + 3 ^ 40 * 7646594 * 2
def baseEnd_7646594 : Nat := 1308792697261986966502987

theorem tailTrace_7646594 : CollatzResearch.WordTrace tailWord_7646594 prefixEnd_7646594 1308792697261986966502987 := by
  unfold tailWord_7646594
  simp only [CollatzResearch.WordTrace]
  refine ⟨69723548814925836782392709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 185929463506468898086380557 69723548814925836782392709)
  ·
    refine ⟨13073165402798594396698633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69723548814925836782392709 13073165402798594396698633)
    ·
      refine ⟨9804874052098945797523975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13073165402798594396698633 9804874052098945797523975)
      ·
        refine ⟨14707311078148418696285963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9804874052098945797523975 14707311078148418696285963)
        ·
          refine ⟨22060966617222628044428945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14707311078148418696285963 22060966617222628044428945)
          ·
            refine ⟨16545724962916971033321709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22060966617222628044428945 16545724962916971033321709)
            ·
              refine ⟨6204646861093864137495641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16545724962916971033321709 6204646861093864137495641)
              ·
                refine ⟨4653485145820398103121731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204646861093864137495641 4653485145820398103121731)
                ·
                  refine ⟨6980227718730597154682597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653485145820398103121731 6980227718730597154682597)
                  ·
                    refine ⟨1308792697261986966502987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6980227718730597154682597 1308792697261986966502987)
                    ·
                      rfl

theorem cell23_7646594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7646594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646594 prefixEnd_7646594 := by exact prefixLift 7646594
  have htrace : WordTrace (prefixWord ++ tailWord_7646594) baseStart_7646594 baseEnd_7646594 := by
    simpa [prefixWord, tailWord_7646594, baseEnd_7646594] using wordTrace_append hprefix tailTrace_7646594
  have hstable : (prefixWord ++ tailWord_7646594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646594).length < 2 ^ (prefixWord ++ tailWord_7646594).sum := by decide
  have hdescent : baseEnd_7646594 < baseStart_7646594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646600 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7646600 : Nat := 118140960795 + 7646600 * 2 ^ 59
def prefixEnd_7646600 : Nat := 4983230072969 + 3 ^ 40 * 7646600 * 2
def baseEnd_7646600 : Nat := 3926381172669887876033933

theorem tailTrace_7646600 : CollatzResearch.WordTrace tailWord_7646600 prefixEnd_7646600 3926381172669887876033933 := by
  unfold tailWord_7646600
  simp only [CollatzResearch.WordTrace]
  refine ⟨139447207048840805077144627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 185929609398454406769526169 139447207048840805077144627)
  ·
    refine ⟨209170810573261207615716941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139447207048840805077144627 209170810573261207615716941)
    ·
      refine ⟨78439053964972952855893853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209170810573261207615716941 78439053964972952855893853)
      ·
        refine ⟨29414645236864857320960195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78439053964972952855893853 29414645236864857320960195)
        ·
          refine ⟨44121967855297285981440293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29414645236864857320960195 44121967855297285981440293)
          ·
            refine ⟨8272868972868241121520055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44121967855297285981440293 8272868972868241121520055)
            ·
              refine ⟨12409303459302361682280083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272868972868241121520055 12409303459302361682280083)
              ·
                refine ⟨18613955188953542523420125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12409303459302361682280083 18613955188953542523420125)
                ·
                  refine ⟨6980233195857578446282547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18613955188953542523420125 6980233195857578446282547)
                  ·
                    refine ⟨10470349793786367669423821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6980233195857578446282547 10470349793786367669423821)
                    ·
                      refine ⟨3926381172669887876033933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10470349793786367669423821 3926381172669887876033933)
                      ·
                        rfl

theorem cell23_7646600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7646600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646600 prefixEnd_7646600 := by exact prefixLift 7646600
  have htrace : WordTrace (prefixWord ++ tailWord_7646600) baseStart_7646600 baseEnd_7646600 := by
    simpa [prefixWord, tailWord_7646600, baseEnd_7646600] using wordTrace_append hprefix tailTrace_7646600
  have hstable : (prefixWord ++ tailWord_7646600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646600).length < 2 ^ (prefixWord ++ tailWord_7646600).sum := by decide
  have hdescent : baseEnd_7646600 < baseStart_7646600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7646623 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 4]
def baseStart_7646623 : Nat := 118140960795 + 7646623 * 2 ^ 59
def prefixEnd_7646623 : Nat := 4983230072969 + 3 ^ 40 * 7646623 * 2
def baseEnd_7646623 : Nat := 3926392982724941286046327

theorem tailTrace_7646623 : CollatzResearch.WordTrace tailWord_7646623 prefixEnd_7646623 3926392982724941286046327 := by
  unfold tailWord_7646623
  simp only [CollatzResearch.WordTrace]
  refine ⟨278895252976598285082376523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 185930168651065523388251015 278895252976598285082376523)
  ·
    refine ⟨418342879464897427623564785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278895252976598285082376523 418342879464897427623564785)
    ·
      refine ⟨313757159598673070717673589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418342879464897427623564785 313757159598673070717673589)
      ·
        refine ⟨29414733712375600379781899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313757159598673070717673589 29414733712375600379781899)
        ·
          refine ⟨44122100568563400569672849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29414733712375600379781899 44122100568563400569672849)
          ·
            refine ⟨33091575426422550427254637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44122100568563400569672849 33091575426422550427254637)
            ·
              refine ⟨12409340784908456410220489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33091575426422550427254637 12409340784908456410220489)
              ·
                refine ⟨9307005588681342307665367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12409340784908456410220489 9307005588681342307665367)
                ·
                  refine ⟨13960508383022013461498051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307005588681342307665367 13960508383022013461498051)
                  ·
                    refine ⟨20940762574533020192247077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13960508383022013461498051 20940762574533020192247077)
                    ·
                      refine ⟨3926392982724941286046327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20940762574533020192247077 3926392982724941286046327)
                      ·
                        rfl

theorem cell23_7646623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_7646623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7646623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7646623 prefixEnd_7646623 := by exact prefixLift 7646623
  have htrace : WordTrace (prefixWord ++ tailWord_7646623) baseStart_7646623 baseEnd_7646623 := by
    simpa [prefixWord, tailWord_7646623, baseEnd_7646623] using wordTrace_append hprefix tailTrace_7646623
  have hstable : (prefixWord ++ tailWord_7646623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7646623).length < 2 ^ (prefixWord ++ tailWord_7646623).sum := by decide
  have hdescent : baseEnd_7646623 < baseStart_7646623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7646623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
