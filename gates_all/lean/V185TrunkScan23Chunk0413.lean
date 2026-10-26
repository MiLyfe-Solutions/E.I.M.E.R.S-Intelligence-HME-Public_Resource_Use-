import V185TrunkScan23Chunk0412

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2441705 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 3, 4, 2]
def baseStart_2441705 : Nat := 118140960795 + 2441705 * 2 ^ 59
def prefixEnd_2441705 : Nat := 4983230072969 + 3 ^ 40 * 2441705 * 2
def baseEnd_2441705 : Nat := 1253768281486474551658309

theorem tailTrace_2441705 : CollatzResearch.WordTrace tailWord_2441705 prefixEnd_2441705 1253768281486474551658309 := by
  unfold tailWord_2441705
  simp only [CollatzResearch.WordTrace]
  refine ⟨89056297619127269859246569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59370865079418179906164379 89056297619127269859246569)
  ·
    refine ⟨66792223214345452394434927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89056297619127269859246569 66792223214345452394434927)
    ·
      refine ⟨100188334821518178591652391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66792223214345452394434927 100188334821518178591652391)
      ·
        refine ⟨150282502232277267887478587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100188334821518178591652391 150282502232277267887478587)
        ·
          refine ⟨225423753348415901831217881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150282502232277267887478587 225423753348415901831217881)
          ·
            refine ⟨169067815011311926373413411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225423753348415901831217881 169067815011311926373413411)
            ·
              refine ⟨253601722516967889560120117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169067815011311926373413411 253601722516967889560120117)
              ·
                refine ⟨23775161485965739646261261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253601722516967889560120117 23775161485965739646261261)
                ·
                  refine ⟨8915685557237152367347973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23775161485965739646261261 8915685557237152367347973)
                  ·
                    refine ⟨1671691041981966068877745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8915685557237152367347973 1671691041981966068877745)
                    ·
                      refine ⟨1253768281486474551658309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671691041981966068877745 1253768281486474551658309)
                      ·
                        rfl

theorem cell23_2441705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 4, 2].length) (baseStart_2441705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441705 prefixEnd_2441705 := by exact prefixLift 2441705
  have htrace : WordTrace (prefixWord ++ tailWord_2441705) baseStart_2441705 baseEnd_2441705 := by
    simpa [prefixWord, tailWord_2441705, baseEnd_2441705] using wordTrace_append hprefix tailTrace_2441705
  have hstable : (prefixWord ++ tailWord_2441705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441705).length < 2 ^ (prefixWord ++ tailWord_2441705).sum := by decide
  have hdescent : baseEnd_2441705 < baseStart_2441705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441708 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_2441708 : Nat := 118140960795 + 2441708 * 2 ^ 59
def prefixEnd_2441708 : Nat := 4983230072969 + 3 ^ 40 * 2441708 * 2
def baseEnd_2441708 : Nat := 1253769821928438039920795

theorem tailTrace_2441708 : CollatzResearch.WordTrace tailWord_2441708 prefixEnd_2441708 1253769821928438039920795 := by
  unfold tailWord_2441708
  simp only [CollatzResearch.WordTrace]
  refine ⟨44528203519058200685802889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59370938025410934247737185 44528203519058200685802889)
  ·
    refine ⟨33396152639293650514352167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44528203519058200685802889 33396152639293650514352167)
    ·
      refine ⟨50094228958940475771528251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33396152639293650514352167 50094228958940475771528251)
      ·
        refine ⟨75141343438410713657292377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50094228958940475771528251 75141343438410713657292377)
        ·
          refine ⟨56356007578808035242969283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75141343438410713657292377 56356007578808035242969283)
          ·
            refine ⟨84534011368212052864453925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56356007578808035242969283 84534011368212052864453925)
            ·
              refine ⟨15850127131539759912085111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84534011368212052864453925 15850127131539759912085111)
              ·
                refine ⟨23775190697309639868127667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15850127131539759912085111 23775190697309639868127667)
                ·
                  refine ⟨35662786045964459802191501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23775190697309639868127667 35662786045964459802191501)
                  ·
                    refine ⟨13373544767236672425821813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35662786045964459802191501 13373544767236672425821813)
                    ·
                      refine ⟨1253769821928438039920795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13373544767236672425821813 1253769821928438039920795)
                      ·
                        rfl

theorem cell23_2441708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_2441708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441708 prefixEnd_2441708 := by exact prefixLift 2441708
  have htrace : WordTrace (prefixWord ++ tailWord_2441708) baseStart_2441708 baseEnd_2441708 := by
    simpa [prefixWord, tailWord_2441708, baseEnd_2441708] using wordTrace_append hprefix tailTrace_2441708
  have hstable : (prefixWord ++ tailWord_2441708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441708).length < 2 ^ (prefixWord ++ tailWord_2441708).sum := by decide
  have hdescent : baseEnd_2441708 < baseStart_2441708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441739 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 1, 4, 2]
def baseStart_2441739 : Nat := 118140960795 + 2441739 * 2 ^ 59
def prefixEnd_2441739 : Nat := 4983230072969 + 3 ^ 40 * 2441739 * 2
def baseEnd_2441739 : Nat := 1253785739828727418633153

theorem tailTrace_2441739 : CollatzResearch.WordTrace tailWord_2441739 prefixEnd_2441739 1253785739828727418633153 := by
  unfold tailWord_2441739
  simp only [CollatzResearch.WordTrace]
  refine ⟨89057537701004093665984271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59371691800669395777322847 89057537701004093665984271)
  ·
    refine ⟨133586306551506140498976407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89057537701004093665984271 133586306551506140498976407)
    ·
      refine ⟨200379459827259210748464611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133586306551506140498976407 200379459827259210748464611)
      ·
        refine ⟨300569189740888816122696917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200379459827259210748464611 300569189740888816122696917)
        ·
          refine ⟨7044590384552081627875709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 300569189740888816122696917 7044590384552081627875709)
          ·
            refine ⟨2641721394207030610453391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7044590384552081627875709 2641721394207030610453391)
            ·
              refine ⟨3962582091310545915680087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641721394207030610453391 3962582091310545915680087)
              ·
                refine ⟨5943873136965818873520131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962582091310545915680087 5943873136965818873520131)
                ·
                  refine ⟨8915809705448728310280197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5943873136965818873520131 8915809705448728310280197)
                  ·
                    refine ⟨1671714319771636558177537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8915809705448728310280197 1671714319771636558177537)
                    ·
                      refine ⟨1253785739828727418633153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671714319771636558177537 1253785739828727418633153)
                      ·
                        rfl

theorem cell23_2441739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 4, 2].length) (baseStart_2441739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441739 prefixEnd_2441739 := by exact prefixLift 2441739
  have htrace : WordTrace (prefixWord ++ tailWord_2441739) baseStart_2441739 baseEnd_2441739 := by
    simpa [prefixWord, tailWord_2441739, baseEnd_2441739] using wordTrace_append hprefix tailTrace_2441739
  have hstable : (prefixWord ++ tailWord_2441739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441739).length < 2 ^ (prefixWord ++ tailWord_2441739).sum := by decide
  have hdescent : baseEnd_2441739 < baseStart_2441739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441785 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2441785 : Nat := 118140960795 + 2441785 * 2 ^ 59
def prefixEnd_2441785 : Nat := 4983230072969 + 3 ^ 40 * 2441785 * 2
def baseEnd_2441785 : Nat := 1253809359938834238657941

theorem tailTrace_2441785 : CollatzResearch.WordTrace tailWord_2441785 prefixEnd_2441785 1253809359938834238657941 := by
  unfold tailWord_2441785
  simp only [CollatzResearch.WordTrace]
  refine ⟨89059215458837443522158809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59372810305891629014772539 89059215458837443522158809)
  ·
    refine ⟨66794411594128082641619107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89059215458837443522158809 66794411594128082641619107)
    ·
      refine ⟨100191617391192123962428661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66794411594128082641619107 100191617391192123962428661)
      ·
        refine ⟨9392964130424261621477687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100191617391192123962428661 9392964130424261621477687)
        ·
          refine ⟨14089446195636392432216531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9392964130424261621477687 14089446195636392432216531)
          ·
            refine ⟨21134169293454588648324797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14089446195636392432216531 21134169293454588648324797)
            ·
              refine ⟨7925313485045470743121799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21134169293454588648324797 7925313485045470743121799)
              ·
                refine ⟨11887970227568206114682699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7925313485045470743121799 11887970227568206114682699)
                ·
                  refine ⟨17831955341352309172024049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11887970227568206114682699 17831955341352309172024049)
                  ·
                    refine ⟨13373966506014231879018037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17831955341352309172024049 13373966506014231879018037)
                    ·
                      refine ⟨1253809359938834238657941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13373966506014231879018037 1253809359938834238657941)
                      ·
                        rfl

theorem cell23_2441785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2441785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441785 prefixEnd_2441785 := by exact prefixLift 2441785
  have htrace : WordTrace (prefixWord ++ tailWord_2441785) baseStart_2441785 baseEnd_2441785 := by
    simpa [prefixWord, tailWord_2441785, baseEnd_2441785] using wordTrace_append hprefix tailTrace_2441785
  have hstable : (prefixWord ++ tailWord_2441785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441785).length < 2 ^ (prefixWord ++ tailWord_2441785).sum := by decide
  have hdescent : baseEnd_2441785 < baseStart_2441785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441812 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_2441812 : Nat := 118140960795 + 2441812 * 2 ^ 59
def prefixEnd_2441812 : Nat := 4983230072969 + 3 ^ 40 * 2441812 * 2
def baseEnd_2441812 : Nat := 1253823223916505633020317

theorem tailTrace_2441812 : CollatzResearch.WordTrace tailWord_2441812 prefixEnd_2441812 1253823223916505633020317 := by
  unfold tailWord_2441812
  simp only [CollatzResearch.WordTrace]
  refine ⟨44530100114869813566695845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59373466819826418088927793 44530100114869813566695845)
  ·
    refine ⟨8349393771538090043755471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44530100114869813566695845 8349393771538090043755471)
    ·
      refine ⟨12524090657307135065633207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8349393771538090043755471 12524090657307135065633207)
      ·
        refine ⟨18786135985960702598449811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12524090657307135065633207 18786135985960702598449811)
        ·
          refine ⟨28179203978941053897674717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18786135985960702598449811 28179203978941053897674717)
          ·
            refine ⟨10567201492102895211628019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28179203978941053897674717 10567201492102895211628019)
            ·
              refine ⟨15850802238154342817442029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10567201492102895211628019 15850802238154342817442029)
              ·
                refine ⟨5944050839307878556540761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15850802238154342817442029 5944050839307878556540761)
                ·
                  refine ⟨4458038129480908917405571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5944050839307878556540761 4458038129480908917405571)
                  ·
                    refine ⟨6687057194221363376108357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4458038129480908917405571 6687057194221363376108357)
                    ·
                      refine ⟨1253823223916505633020317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6687057194221363376108357 1253823223916505633020317)
                      ·
                        rfl

theorem cell23_2441812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_2441812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441812 prefixEnd_2441812 := by exact prefixLift 2441812
  have htrace : WordTrace (prefixWord ++ tailWord_2441812) baseStart_2441812 baseEnd_2441812 := by
    simpa [prefixWord, tailWord_2441812, baseEnd_2441812] using wordTrace_append hprefix tailTrace_2441812
  have hstable : (prefixWord ++ tailWord_2441812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441812).length < 2 ^ (prefixWord ++ tailWord_2441812).sum := by decide
  have hdescent : baseEnd_2441812 < baseStart_2441812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441846 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_2441846 : Nat := 118140960795 + 2441846 * 2 ^ 59
def prefixEnd_2441846 : Nat := 4983230072969 + 3 ^ 40 * 2441846 * 2
def baseEnd_2441846 : Nat := 1253840682258758499995161

theorem tailTrace_2441846 : CollatzResearch.WordTrace tailWord_2441846 prefixEnd_2441846 1253840682258758499995161 := by
  unfold tailWord_2441846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566340019476028183758087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59374293541077633960086261 5566340019476028183758087)
  ·
    refine ⟨8349510029214042275637131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5566340019476028183758087 8349510029214042275637131)
    ·
      refine ⟨12524265043821063413455697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8349510029214042275637131 12524265043821063413455697)
      ·
        refine ⟨9393198782865797560091773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12524265043821063413455697 9393198782865797560091773)
        ·
          refine ⟨3522449543574674085034415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9393198782865797560091773 3522449543574674085034415)
          ·
            refine ⟨5283674315362011127551623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522449543574674085034415 5283674315362011127551623)
            ·
              refine ⟨7925511473043016691327435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283674315362011127551623 7925511473043016691327435)
              ·
                refine ⟨11888267209564525036991153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7925511473043016691327435 11888267209564525036991153)
                ·
                  refine ⟨8916200407173393777743365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11888267209564525036991153 8916200407173393777743365)
                  ·
                    refine ⟨1671787576345011333326881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8916200407173393777743365 1671787576345011333326881)
                    ·
                      refine ⟨1253840682258758499995161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671787576345011333326881 1253840682258758499995161)
                      ·
                        rfl

theorem cell23_2441846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_2441846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441846 prefixEnd_2441846 := by exact prefixLift 2441846
  have htrace : WordTrace (prefixWord ++ tailWord_2441846) baseStart_2441846 baseEnd_2441846 := by
    simpa [prefixWord, tailWord_2441846, baseEnd_2441846] using wordTrace_append hprefix tailTrace_2441846
  have hstable : (prefixWord ++ tailWord_2441846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441846).length < 2 ^ (prefixWord ++ tailWord_2441846).sum := by decide
  have hdescent : baseEnd_2441846 < baseStart_2441846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441866 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2441866 : Nat := 118140960795 + 2441866 * 2 ^ 59
def prefixEnd_2441866 : Nat := 4983230072969 + 3 ^ 40 * 2441866 * 2
def baseEnd_2441866 : Nat := 1253850951871848421745069

theorem tailTrace_2441866 : CollatzResearch.WordTrace tailWord_2441866 prefixEnd_2441866 1253850951871848421745069 := by
  unfold tailWord_2441866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22265542442885998588964363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59374779847695996237238301 22265542442885998588964363)
  ·
    refine ⟨33398313664328997883446545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22265542442885998588964363 33398313664328997883446545)
    ·
      refine ⟨25048735248246748412584909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33398313664328997883446545 25048735248246748412584909)
      ·
        refine ⟨9393275718092530654719341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25048735248246748412584909 9393275718092530654719341)
        ·
          refine ⟨3522478394284698995519753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9393275718092530654719341 3522478394284698995519753)
          ·
            refine ⟨2641858795713524246639815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3522478394284698995519753 2641858795713524246639815)
            ·
              refine ⟨3962788193570286369959723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641858795713524246639815 3962788193570286369959723)
              ·
                refine ⟨5944182290355429554939585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962788193570286369959723 5944182290355429554939585)
                ·
                  refine ⟨4458136717766572166204689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5944182290355429554939585 4458136717766572166204689)
                  ·
                    refine ⟨3343602538324929124653517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4458136717766572166204689 3343602538324929124653517)
                    ·
                      refine ⟨1253850951871848421745069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3343602538324929124653517 1253850951871848421745069)
                      ·
                        rfl

theorem cell23_2441866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2441866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441866 prefixEnd_2441866 := by exact prefixLift 2441866
  have htrace : WordTrace (prefixWord ++ tailWord_2441866) baseStart_2441866 baseEnd_2441866 := by
    simpa [prefixWord, tailWord_2441866, baseEnd_2441866] using wordTrace_append hprefix tailTrace_2441866
  have hstable : (prefixWord ++ tailWord_2441866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441866).length < 2 ^ (prefixWord ++ tailWord_2441866).sum := by decide
  have hdescent : baseEnd_2441866 < baseStart_2441866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441919 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 4]
def baseStart_2441919 : Nat := 118140960795 + 2441919 * 2 ^ 59
def prefixEnd_2441919 : Nat := 4983230072969 + 3 ^ 40 * 2441919 * 2
def baseEnd_2441919 : Nat := 1253878166346536714382325

theorem tailTrace_2441919 : CollatzResearch.WordTrace tailWord_2441919 prefixEnd_2441919 1253878166346536714382325 := by
  unfold tailWord_2441919
  simp only [CollatzResearch.WordTrace]
  refine ⟨89064102840351984407536811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59376068560234656271691207 89064102840351984407536811)
  ·
    refine ⟨133596154260527976611305217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89064102840351984407536811 133596154260527976611305217)
    ·
      refine ⟨100197115695395982458478913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133596154260527976611305217 100197115695395982458478913)
      ·
        refine ⟨75147836771546986843859185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100197115695395982458478913 75147836771546986843859185)
        ·
          refine ⟨56360877578660240132894389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75147836771546986843859185 56360877578660240132894389)
          ·
            refine ⟨5283832272999397512458849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56360877578660240132894389 5283832272999397512458849)
            ·
              refine ⟨3962874204749548134344137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5283832272999397512458849 3962874204749548134344137)
              ·
                refine ⟨2972155653562161100758103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3962874204749548134344137 2972155653562161100758103)
                ·
                  refine ⟨4458233480343241651137155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972155653562161100758103 4458233480343241651137155)
                  ·
                    refine ⟨6687350220514862476705733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4458233480343241651137155 6687350220514862476705733)
                    ·
                      refine ⟨1253878166346536714382325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6687350220514862476705733 1253878166346536714382325)
                      ·
                        rfl

theorem cell23_2441919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_2441919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441919 prefixEnd_2441919 := by exact prefixLift 2441919
  have htrace : WordTrace (prefixWord ++ tailWord_2441919) baseStart_2441919 baseEnd_2441919 := by
    simpa [prefixWord, tailWord_2441919, baseEnd_2441919] using wordTrace_append hprefix tailTrace_2441919
  have hstable : (prefixWord ++ tailWord_2441919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441919).length < 2 ^ (prefixWord ++ tailWord_2441919).sum := by decide
  have hdescent : baseEnd_2441919 < baseStart_2441919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441953 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_2441953 : Nat := 118140960795 + 2441953 * 2 ^ 59
def prefixEnd_2441953 : Nat := 4983230072969 + 3 ^ 40 * 2441953 * 2
def baseEnd_2441953 : Nat := 1253895624688789581357169

theorem tailTrace_2441953 : CollatzResearch.WordTrace tailWord_2441953 prefixEnd_2441953 1253895624688789581357169 := by
  unfold tailWord_2441953
  simp only [CollatzResearch.WordTrace]
  refine ⟨89065342922228808214274513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59376895281485872142849675 89065342922228808214274513)
  ·
    refine ⟨66799007191671606160705885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89065342922228808214274513 66799007191671606160705885)
    ·
      refine ⟨25049627696876852310264707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66799007191671606160705885 25049627696876852310264707)
      ·
        refine ⟨37574441545315278465397061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25049627696876852310264707 37574441545315278465397061)
        ·
          refine ⟨7045207789746614712261949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37574441545315278465397061 7045207789746614712261949)
          ·
            refine ⟨2641952921154980517098231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7045207789746614712261949 2641952921154980517098231)
            ·
              refine ⟨3962929381732470775647347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641952921154980517098231 3962929381732470775647347)
              ·
                refine ⟨5944394072598706163471021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962929381732470775647347 5944394072598706163471021)
                ·
                  refine ⟨2229147777224514811301633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5944394072598706163471021 2229147777224514811301633)
                  ·
                    refine ⟨1671860832918386108476225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2229147777224514811301633 1671860832918386108476225)
                    ·
                      refine ⟨1253895624688789581357169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671860832918386108476225 1253895624688789581357169)
                      ·
                        rfl

theorem cell23_2441953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_2441953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441953 prefixEnd_2441953 := by exact prefixLift 2441953
  have htrace : WordTrace (prefixWord ++ tailWord_2441953) baseStart_2441953 baseEnd_2441953 := by
    simpa [prefixWord, tailWord_2441953, baseEnd_2441953] using wordTrace_append hprefix tailTrace_2441953
  have hstable : (prefixWord ++ tailWord_2441953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441953).length < 2 ^ (prefixWord ++ tailWord_2441953).sum := by decide
  have hdescent : baseEnd_2441953 < baseStart_2441953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441975 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_2441975 : Nat := 118140960795 + 2441975 * 2 ^ 59
def prefixEnd_2441975 : Nat := 4983230072969 + 3 ^ 40 * 2441975 * 2
def baseEnd_2441975 : Nat := 1253906921263188495282067

theorem tailTrace_2441975 : CollatzResearch.WordTrace tailWord_2441975 prefixEnd_2441975 1253906921263188495282067 := by
  unfold tailWord_2441975
  simp only [CollatzResearch.WordTrace]
  refine ⟨89066145328149105971575379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59377430218766070647716919 89066145328149105971575379)
  ·
    refine ⟨133599217992223658957363069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89066145328149105971575379 133599217992223658957363069)
    ·
      refine ⟨50099706747083872109011151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133599217992223658957363069 50099706747083872109011151)
      ·
        refine ⟨75149560120625808163516727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50099706747083872109011151 75149560120625808163516727)
        ·
          refine ⟨112724340180938712245275091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75149560120625808163516727 112724340180938712245275091)
          ·
            refine ⟨169086510271408068367912637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112724340180938712245275091 169086510271408068367912637)
            ·
              refine ⟨63407441351778025637967239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169086510271408068367912637 63407441351778025637967239)
              ·
                refine ⟨95111162027667038456950859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63407441351778025637967239 95111162027667038456950859)
                ·
                  refine ⟨142666743041500557685426289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95111162027667038456950859 142666743041500557685426289)
                  ·
                    refine ⟨107000057281125418264069717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142666743041500557685426289 107000057281125418264069717)
                    ·
                      refine ⟨1253906921263188495282067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 107000057281125418264069717 1253906921263188495282067)
                      ·
                        rfl

theorem cell23_2441975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_2441975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441975 prefixEnd_2441975 := by exact prefixLift 2441975
  have htrace : WordTrace (prefixWord ++ tailWord_2441975) baseStart_2441975 baseEnd_2441975 := by
    simpa [prefixWord, tailWord_2441975, baseEnd_2441975] using wordTrace_append hprefix tailTrace_2441975
  have hstable : (prefixWord ++ tailWord_2441975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441975).length < 2 ^ (prefixWord ++ tailWord_2441975).sum := by decide
  have hdescent : baseEnd_2441975 < baseStart_2441975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441986 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2441986 : Nat := 118140960795 + 2441986 * 2 ^ 59
def prefixEnd_2441986 : Nat := 4983230072969 + 3 ^ 40 * 2441986 * 2
def baseEnd_2441986 : Nat := 1253912569550387952244517

theorem tailTrace_2441986 : CollatzResearch.WordTrace tailWord_2441986 prefixEnd_2441986 1253912569550387952244517 := by
  unfold tailWord_2441986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22266636632777313712556453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59377697687406169900150541 22266636632777313712556453)
  ·
    refine ⟨4174994368645746321104335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22266636632777313712556453 4174994368645746321104335)
    ·
      refine ⟨6262491552968619481656503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4174994368645746321104335 6262491552968619481656503)
      ·
        refine ⟨9393737329452929222484755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6262491552968619481656503 9393737329452929222484755)
        ·
          refine ⟨14090605994179393833727133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9393737329452929222484755 14090605994179393833727133)
          ·
            refine ⟨5283977247817272687647675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14090605994179393833727133 5283977247817272687647675)
            ·
              refine ⟨7925965871725909031471513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283977247817272687647675 7925965871725909031471513)
              ·
                refine ⟨5944474403794431773603635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7925965871725909031471513 5944474403794431773603635)
                ·
                  refine ⟨8916711605691647660405453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5944474403794431773603635 8916711605691647660405453)
                  ·
                    refine ⟨3343766852134367872652045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8916711605691647660405453 3343766852134367872652045)
                    ·
                      refine ⟨1253912569550387952244517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3343766852134367872652045 1253912569550387952244517)
                      ·
                        rfl

theorem cell23_2441986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2441986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2441986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2441986 prefixEnd_2441986 := by exact prefixLift 2441986
  have htrace : WordTrace (prefixWord ++ tailWord_2441986) baseStart_2441986 baseEnd_2441986 := by
    simpa [prefixWord, tailWord_2441986, baseEnd_2441986] using wordTrace_append hprefix tailTrace_2441986
  have hstable : (prefixWord ++ tailWord_2441986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441986).length < 2 ^ (prefixWord ++ tailWord_2441986).sum := by decide
  have hdescent : baseEnd_2441986 < baseStart_2441986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442054 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2442054 : Nat := 118140960795 + 2442054 * 2 ^ 59
def prefixEnd_2442054 : Nat := 4983230072969 + 3 ^ 40 * 2442054 * 2
def baseEnd_2442054 : Nat := 1253947486234893686194205

theorem tailTrace_2442054 : CollatzResearch.WordTrace tailWord_2442054 prefixEnd_2442054 1253947486234893686194205 := by
  unfold tailWord_2442054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783407084214465701990663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59379351129908601642467477 2783407084214465701990663)
  ·
    refine ⟨4175110626321698552985995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2783407084214465701990663 4175110626321698552985995)
    ·
      refine ⟨6262665939482547829478993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4175110626321698552985995 6262665939482547829478993)
      ·
        refine ⟨4696999454611910872109245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6262665939482547829478993 4696999454611910872109245)
        ·
          refine ⟨1761374795479466577040967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4696999454611910872109245 1761374795479466577040967)
          ·
            refine ⟨2642062193219199865561451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761374795479466577040967 2642062193219199865561451)
            ·
              refine ⟨3963093289828799798342177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642062193219199865561451 3963093289828799798342177)
              ·
                refine ⟨2972319967371599848756633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3963093289828799798342177 2972319967371599848756633)
                ·
                  refine ⟨2229239975528699886567475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2972319967371599848756633 2229239975528699886567475)
                  ·
                    refine ⟨3343859963293049829851213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2229239975528699886567475 3343859963293049829851213)
                    ·
                      refine ⟨1253947486234893686194205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3343859963293049829851213 1253947486234893686194205)
                      ·
                        rfl

theorem cell23_2442054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2442054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442054 prefixEnd_2442054 := by exact prefixLift 2442054
  have htrace : WordTrace (prefixWord ++ tailWord_2442054) baseStart_2442054 baseEnd_2442054 := by
    simpa [prefixWord, tailWord_2442054, baseEnd_2442054] using wordTrace_append hprefix tailTrace_2442054
  have hstable : (prefixWord ++ tailWord_2442054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442054).length < 2 ^ (prefixWord ++ tailWord_2442054).sum := by decide
  have hdescent : baseEnd_2442054 < baseStart_2442054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442060 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 2, 2, 2]
def baseStart_2442060 : Nat := 118140960795 + 2442060 * 2 ^ 59
def prefixEnd_2442060 : Nat := 4983230072969 + 3 ^ 40 * 2442060 * 2
def baseEnd_2442060 : Nat := 1253950567118820662719177

theorem tailTrace_2442060 : CollatzResearch.WordTrace tailWord_2442060 prefixEnd_2442060 1253950567118820662719177 := by
  unfold tailWord_2442060
  simp only [CollatzResearch.WordTrace]
  refine ⟨44534622766420582744209817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59379497021894110325613089 44534622766420582744209817)
  ·
    refine ⟨33400967074815437058157363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44534622766420582744209817 33400967074815437058157363)
    ·
      refine ⟨50101450612223155587236045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33400967074815437058157363 50101450612223155587236045)
      ·
        refine ⟨18788043979583683345213517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50101450612223155587236045 18788043979583683345213517)
        ·
          refine ⟨7045516492343881254455069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18788043979583683345213517 7045516492343881254455069)
          ·
            refine ⟨2642068684628955470420651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7045516492343881254455069 2642068684628955470420651)
            ·
              refine ⟨3963103026943433205630977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642068684628955470420651 3963103026943433205630977)
              ·
                refine ⟨2972327270207574904223233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3963103026943433205630977 2972327270207574904223233)
                ·
                  refine ⟨2229245452655681178167425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2972327270207574904223233 2229245452655681178167425)
                  ·
                    refine ⟨1671934089491760883625569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2229245452655681178167425 1671934089491760883625569)
                    ·
                      refine ⟨1253950567118820662719177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671934089491760883625569 1253950567118820662719177)
                      ·
                        rfl

theorem cell23_2442060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_2442060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442060 prefixEnd_2442060 := by exact prefixLift 2442060
  have htrace : WordTrace (prefixWord ++ tailWord_2442060) baseStart_2442060 baseEnd_2442060 := by
    simpa [prefixWord, tailWord_2442060, baseEnd_2442060] using wordTrace_append hprefix tailTrace_2442060
  have hstable : (prefixWord ++ tailWord_2442060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442060).length < 2 ^ (prefixWord ++ tailWord_2442060).sum := by decide
  have hdescent : baseEnd_2442060 < baseStart_2442060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442072 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2442072 : Nat := 118140960795 + 2442072 * 2 ^ 59
def prefixEnd_2442072 : Nat := 4983230072969 + 3 ^ 40 * 2442072 * 2
def baseEnd_2442072 : Nat := 1253956728886674615769121

theorem tailTrace_2442072 : CollatzResearch.WordTrace tailWord_2442072 prefixEnd_2442072 1253956728886674615769121 := by
  unfold tailWord_2442072
  simp only [CollatzResearch.WordTrace]
  refine ⟨44534841604398845768928235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59379788805865127691904313 44534841604398845768928235)
  ·
    refine ⟨66802262406598268653392353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44534841604398845768928235 66802262406598268653392353)
    ·
      refine ⟨50101696804948701490044265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66802262406598268653392353 50101696804948701490044265)
      ·
        refine ⟨37576272603711526117533199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50101696804948701490044265 37576272603711526117533199)
        ·
          refine ⟨56364408905567289176299799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37576272603711526117533199 56364408905567289176299799)
          ·
            refine ⟨84546613358350933764449699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56364408905567289176299799 84546613358350933764449699)
            ·
              refine ⟨126819920037526400646674549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84546613358350933764449699 126819920037526400646674549)
              ·
                refine ⟨11889367503518100060625739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126819920037526400646674549 11889367503518100060625739)
                ·
                  refine ⟨17834051255277150090938609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11889367503518100060625739 17834051255277150090938609)
                  ·
                    refine ⟨13375538441457862568203957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17834051255277150090938609 13375538441457862568203957)
                    ·
                      refine ⟨1253956728886674615769121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13375538441457862568203957 1253956728886674615769121)
                      ·
                        rfl

theorem cell23_2442072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2442072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442072 prefixEnd_2442072 := by exact prefixLift 2442072
  have htrace : WordTrace (prefixWord ++ tailWord_2442072) baseStart_2442072 baseEnd_2442072 := by
    simpa [prefixWord, tailWord_2442072, baseEnd_2442072] using wordTrace_append hprefix tailTrace_2442072
  have hstable : (prefixWord ++ tailWord_2442072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442072).length < 2 ^ (prefixWord ++ tailWord_2442072).sum := by decide
  have hdescent : baseEnd_2442072 < baseStart_2442072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442076 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2442076 : Nat := 118140960795 + 2442076 * 2 ^ 59
def prefixEnd_2442076 : Nat := 4983230072969 + 3 ^ 40 * 2442076 * 2
def baseEnd_2442076 : Nat := 1253958782809292600119103

theorem tailTrace_2442076 : CollatzResearch.WordTrace tailWord_2442076 prefixEnd_2442076 1253958782809292600119103 := by
  unfold tailWord_2442076
  simp only [CollatzResearch.WordTrace]
  refine ⟨44534914550391600110501041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59379886067188800147334721 44534914550391600110501041)
  ·
    refine ⟨33401185912793700082875781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44534914550391600110501041 33401185912793700082875781)
    ·
      refine ⟨6262722358648818765539209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33401185912793700082875781 6262722358648818765539209)
      ·
        refine ⟨4697041768986614074154407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6262722358648818765539209 4697041768986614074154407)
        ·
          refine ⟨7045562653479921111231611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697041768986614074154407 7045562653479921111231611)
          ·
            refine ⟨10568343980219881666847417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045562653479921111231611 10568343980219881666847417)
            ·
              refine ⟨7926257985164911250135563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10568343980219881666847417 7926257985164911250135563)
              ·
                refine ⟨11889386977747366875203345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7926257985164911250135563 11889386977747366875203345)
                ·
                  refine ⟨8917040233310525156402509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11889386977747366875203345 8917040233310525156402509)
                  ·
                    refine ⟨3343890087491446933650941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8917040233310525156402509 3343890087491446933650941)
                    ·
                      refine ⟨1253958782809292600119103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3343890087491446933650941 1253958782809292600119103)
                      ·
                        rfl

theorem cell23_2442076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2442076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442076 prefixEnd_2442076 := by exact prefixLift 2442076
  have htrace : WordTrace (prefixWord ++ tailWord_2442076) baseStart_2442076 baseEnd_2442076 := by
    simpa [prefixWord, tailWord_2442076, baseEnd_2442076] using wordTrace_append hprefix tailTrace_2442076
  have hstable : (prefixWord ++ tailWord_2442076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442076).length < 2 ^ (prefixWord ++ tailWord_2442076).sum := by decide
  have hdescent : baseEnd_2442076 < baseStart_2442076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442092 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_2442092 : Nat := 118140960795 + 2442092 * 2 ^ 59
def prefixEnd_2442092 : Nat := 4983230072969 + 3 ^ 40 * 2442092 * 2
def baseEnd_2442092 : Nat := 417988999499921512506343

theorem tailTrace_2442092 : CollatzResearch.WordTrace tailWord_2442092 prefixEnd_2442092 417988999499921512506343 := by
  unfold tailWord_2442092
  simp only [CollatzResearch.WordTrace]
  refine ⟨44535206334362617476792265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59380275112483489969056353 44535206334362617476792265)
  ·
    refine ⟨33401404750771963107594199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44535206334362617476792265 33401404750771963107594199)
    ·
      refine ⟨50102107126157944661391299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33401404750771963107594199 50102107126157944661391299)
      ·
        refine ⟨75153160689236916992086949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50102107126157944661391299 75153160689236916992086949)
        ·
          refine ⟨14091217629231921936016303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75153160689236916992086949 14091217629231921936016303)
          ·
            refine ⟨21136826443847882904024455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14091217629231921936016303 21136826443847882904024455)
            ·
              refine ⟨31705239665771824356036683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21136826443847882904024455 31705239665771824356036683)
              ·
                refine ⟨47557859498657736534055025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31705239665771824356036683 47557859498657736534055025)
                ·
                  refine ⟨35668394623993302400541269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47557859498657736534055025 35668394623993302400541269)
                  ·
                    refine ⟨417988999499921512506343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35668394623993302400541269 417988999499921512506343)
                    ·
                      rfl

theorem cell23_2442092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_2442092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442092 prefixEnd_2442092 := by exact prefixLift 2442092
  have htrace : WordTrace (prefixWord ++ tailWord_2442092) baseStart_2442092 baseEnd_2442092 := by
    simpa [prefixWord, tailWord_2442092, baseEnd_2442092] using wordTrace_append hprefix tailTrace_2442092
  have hstable : (prefixWord ++ tailWord_2442092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442092).length < 2 ^ (prefixWord ++ tailWord_2442092).sum := by decide
  have hdescent : baseEnd_2442092 < baseStart_2442092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442099 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 1, 6, 2]
def baseStart_2442099 : Nat := 118140960795 + 2442099 * 2 ^ 59
def prefixEnd_2442099 : Nat := 4983230072969 + 3 ^ 40 * 2442099 * 2
def baseEnd_2442099 : Nat := 1253970592864346010131497

theorem tailTrace_2442099 : CollatzResearch.WordTrace tailWord_2442099 prefixEnd_2442099 1253970592864346010131497 := by
  unfold tailWord_2442099
  simp only [CollatzResearch.WordTrace]
  refine ⟨89070667979699875149089351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59380445319799916766059567 89070667979699875149089351)
  ·
    refine ⟨133606001969549812723634027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89070667979699875149089351 133606001969549812723634027)
    ·
      refine ⟨200409002954324719085451041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133606001969549812723634027 200409002954324719085451041)
      ·
        refine ⟨150306752215743539314088281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200409002954324719085451041 150306752215743539314088281)
        ·
          refine ⟨112730064161807654485566211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150306752215743539314088281 112730064161807654485566211)
          ·
            refine ⟨169095096242711481728349317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112730064161807654485566211 169095096242711481728349317)
            ·
              refine ⟨31705330545508402824065497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169095096242711481728349317 31705330545508402824065497)
              ·
                refine ⟨23778997909131302118049123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31705330545508402824065497 23778997909131302118049123)
                ·
                  refine ⟨35668496863696953177073685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23778997909131302118049123 35668496863696953177073685)
                  ·
                    refine ⟨1671960790485794680175329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35668496863696953177073685 1671960790485794680175329)
                    ·
                      refine ⟨1253970592864346010131497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1671960790485794680175329 1253970592864346010131497)
                      ·
                        rfl

theorem cell23_2442099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6, 2].length) (baseStart_2442099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442099 prefixEnd_2442099 := by exact prefixLift 2442099
  have htrace : WordTrace (prefixWord ++ tailWord_2442099) baseStart_2442099 baseEnd_2442099 := by
    simpa [prefixWord, tailWord_2442099, baseEnd_2442099] using wordTrace_append hprefix tailTrace_2442099
  have hstable : (prefixWord ++ tailWord_2442099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442099).length < 2 ^ (prefixWord ++ tailWord_2442099).sum := by decide
  have hdescent : baseEnd_2442099 < baseStart_2442099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442109 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_2442109 : Nat := 118140960795 + 2442109 * 2 ^ 59
def prefixEnd_2442109 : Nat := 4983230072969 + 3 ^ 40 * 2442109 * 2
def baseEnd_2442109 : Nat := 417991909223630323668817

theorem tailTrace_2442109 : CollatzResearch.WordTrace tailWord_2442109 prefixEnd_2442109 417991909223630323668817 := by
  unfold tailWord_2442109
  simp only [CollatzResearch.WordTrace]
  refine ⟨89071032709663646856953381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59380688473109097904635587 89071032709663646856953381)
  ·
    refine ⟨16700818633061933785678759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89071032709663646856953381 16700818633061933785678759)
    ·
      refine ⟨25051227949592900678518139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16700818633061933785678759 25051227949592900678518139)
      ·
        refine ⟨37576841924389351017777209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25051227949592900678518139 37576841924389351017777209)
        ·
          refine ⟨28182631443292013263332907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37576841924389351017777209 28182631443292013263332907)
          ·
            refine ⟨42273947164938019894999361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28182631443292013263332907 42273947164938019894999361)
            ·
              refine ⟨31705460373703514921249521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42273947164938019894999361 31705460373703514921249521)
              ·
                refine ⟨23779095280277636190937141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31705460373703514921249521 23779095280277636190937141)
                ·
                  refine ⟨2229290182526028392900357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23779095280277636190937141 2229290182526028392900357)
                  ·
                    refine ⟨417991909223630323668817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2229290182526028392900357 417991909223630323668817)
                    ·
                      rfl

theorem cell23_2442109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_2442109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442109 prefixEnd_2442109 := by exact prefixLift 2442109
  have htrace : WordTrace (prefixWord ++ tailWord_2442109) baseStart_2442109 baseEnd_2442109 := by
    simpa [prefixWord, tailWord_2442109, baseEnd_2442109] using wordTrace_append hprefix tailTrace_2442109
  have hstable : (prefixWord ++ tailWord_2442109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442109).length < 2 ^ (prefixWord ++ tailWord_2442109).sum := by decide
  have hdescent : baseEnd_2442109 < baseStart_2442109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442112 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_2442112 : Nat := 118140960795 + 2442112 * 2 ^ 59
def prefixEnd_2442112 : Nat := 4983230072969 + 3 ^ 40 * 2442112 * 2
def baseEnd_2442112 : Nat := 1253977268112854459268937

theorem tailTrace_2442112 : CollatzResearch.WordTrace tailWord_2442112 prefixEnd_2442112 1253977268112854459268937 := by
  unfold tailWord_2442112
  simp only [CollatzResearch.WordTrace]
  refine ⟨44535571064326389184656295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59380761419101852246208393 44535571064326389184656295)
  ·
    refine ⟨66803356596489583776984443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44535571064326389184656295 66803356596489583776984443)
    ·
      refine ⟨100205034894734375665476665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66803356596489583776984443 100205034894734375665476665)
      ·
        refine ⟨75153776171050781749107499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100205034894734375665476665 75153776171050781749107499)
        ·
          refine ⟨112730664256576172623661249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75153776171050781749107499 112730664256576172623661249)
          ·
            refine ⟨84547998192432129467745937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112730664256576172623661249 84547998192432129467745937)
            ·
              refine ⟨63410998644324097100809453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84547998192432129467745937 63410998644324097100809453)
              ·
                refine ⟨23779124491621536412803545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63410998644324097100809453 23779124491621536412803545)
                ·
                  refine ⟨17834343368716152309602659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23779124491621536412803545 17834343368716152309602659)
                  ·
                    refine ⟨26751515053074228464403989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17834343368716152309602659 26751515053074228464403989)
                    ·
                      refine ⟨1253977268112854459268937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26751515053074228464403989 1253977268112854459268937)
                      ·
                        rfl

theorem cell23_2442112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_2442112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442112 prefixEnd_2442112 := by exact prefixLift 2442112
  have htrace : WordTrace (prefixWord ++ tailWord_2442112) baseStart_2442112 baseEnd_2442112 := by
    simpa [prefixWord, tailWord_2442112, baseEnd_2442112] using wordTrace_append hprefix tailTrace_2442112
  have hstable : (prefixWord ++ tailWord_2442112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442112).length < 2 ^ (prefixWord ++ tailWord_2442112).sum := by decide
  have hdescent : baseEnd_2442112 < baseStart_2442112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442210 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2442210 : Nat := 118140960795 + 2442210 * 2 ^ 59
def prefixEnd_2442210 : Nat := 4983230072969 + 3 ^ 40 * 2442210 * 2
def baseEnd_2442210 : Nat := 1254027589216995075843487

theorem tailTrace_2442210 : CollatzResearch.WordTrace tailWord_2442210 prefixEnd_2442210 1254027589216995075843487 := by
  unfold tailWord_2442210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22268679120574435276595021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59383144321531827404253389 22268679120574435276595021)
  ·
    refine ⟨8350754670215413228723133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22268679120574435276595021 8350754670215413228723133)
    ·
      refine ⟨3131533001330779960771175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8350754670215413228723133 3131533001330779960771175)
      ·
        refine ⟨4697299501996169941156763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131533001330779960771175 4697299501996169941156763)
        ·
          refine ⟨7045949252994254911735145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697299501996169941156763 7045949252994254911735145)
          ·
            refine ⟨5284461939745691183801359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7045949252994254911735145 5284461939745691183801359)
            ·
              refine ⟨7926692909618536775702039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284461939745691183801359 7926692909618536775702039)
              ·
                refine ⟨11890039364427805163553059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7926692909618536775702039 11890039364427805163553059)
                ·
                  refine ⟨17835059046641707745329589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11890039364427805163553059 17835059046641707745329589)
                  ·
                    refine ⟨1672036785622660101124649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17835059046641707745329589 1672036785622660101124649)
                    ·
                      refine ⟨1254027589216995075843487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672036785622660101124649 1254027589216995075843487)
                      ·
                        rfl

theorem cell23_2442210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2442210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442210 prefixEnd_2442210 := by exact prefixLift 2442210
  have htrace : WordTrace (prefixWord ++ tailWord_2442210) baseStart_2442210 baseEnd_2442210 := by
    simpa [prefixWord, tailWord_2442210, baseEnd_2442210] using wordTrace_append hprefix tailTrace_2442210
  have hstable : (prefixWord ++ tailWord_2442210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442210).length < 2 ^ (prefixWord ++ tailWord_2442210).sum := by decide
  have hdescent : baseEnd_2442210 < baseStart_2442210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442223 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 1, 1, 4]
def baseStart_2442223 : Nat := 118140960795 + 2442223 * 2 ^ 59
def prefixEnd_2442223 : Nat := 4983230072969 + 3 ^ 40 * 2442223 * 2
def baseEnd_2442223 : Nat := 1254034264465503524980927

theorem tailTrace_2442223 : CollatzResearch.WordTrace tailWord_2442223 prefixEnd_2442223 1254034264465503524980927 := by
  unfold tailWord_2442223
  simp only [CollatzResearch.WordTrace]
  refine ⟨89075190631250644326603323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59383460420833762884402215 89075190631250644326603323)
  ·
    refine ⟨133612785946875966489904985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89075190631250644326603323 133612785946875966489904985)
    ·
      refine ⟨100209589460156974867428739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133612785946875966489904985 100209589460156974867428739)
      ·
        refine ⟨150314384190235462301143109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100209589460156974867428739 150314384190235462301143109)
        ·
          refine ⟨28183947035669149181464333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150314384190235462301143109 28183947035669149181464333)
          ·
            refine ⟨10568980138375930943049125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28183947035669149181464333 10568980138375930943049125)
            ·
              refine ⟨1981683775945487051821711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10568980138375930943049125 1981683775945487051821711)
              ·
                refine ⟨2972525663918230577732567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981683775945487051821711 2972525663918230577732567)
                ·
                  refine ⟨4458788495877345866598851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972525663918230577732567 4458788495877345866598851)
                  ·
                    refine ⟨6688182743816018799898277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4458788495877345866598851 6688182743816018799898277)
                    ·
                      refine ⟨1254034264465503524980927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6688182743816018799898277 1254034264465503524980927)
                      ·
                        rfl

theorem cell23_2442223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 1, 4].length) (baseStart_2442223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442223 prefixEnd_2442223 := by exact prefixLift 2442223
  have htrace : WordTrace (prefixWord ++ tailWord_2442223) baseStart_2442223 baseEnd_2442223 := by
    simpa [prefixWord, tailWord_2442223, baseEnd_2442223] using wordTrace_append hprefix tailTrace_2442223
  have hstable : (prefixWord ++ tailWord_2442223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442223).length < 2 ^ (prefixWord ++ tailWord_2442223).sum := by decide
  have hdescent : baseEnd_2442223 < baseStart_2442223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442239 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 3]
def baseStart_2442239 : Nat := 118140960795 + 2442239 * 2 ^ 59
def prefixEnd_2442239 : Nat := 4983230072969 + 3 ^ 40 * 2442239 * 2
def baseEnd_2442239 : Nat := 1254042480155975462380853

theorem tailTrace_2442239 : CollatzResearch.WordTrace tailWord_2442239 prefixEnd_2442239 1254042480155975462380853 := by
  unfold tailWord_2442239
  simp only [CollatzResearch.WordTrace]
  refine ⟨89075774199192679059185771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59383849466128452706123847 89075774199192679059185771)
  ·
    refine ⟨133613661298789018588778657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89075774199192679059185771 133613661298789018588778657)
    ·
      refine ⟨100210245974091763941583993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133613661298789018588778657 100210245974091763941583993)
      ·
        refine ⟨75157684480568822956187995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100210245974091763941583993 75157684480568822956187995)
        ·
          refine ⟨112736526720853234434281993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75157684480568822956187995 112736526720853234434281993)
          ·
            refine ⟨84552395040639925825711495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112736526720853234434281993 84552395040639925825711495)
            ·
              refine ⟨126828592560959888738567243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84552395040639925825711495 126828592560959888738567243)
              ·
                refine ⟨190242888841439833107850865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126828592560959888738567243 190242888841439833107850865)
                ·
                  refine ⟨142682166631079874830888149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190242888841439833107850865 142682166631079874830888149)
                  ·
                    refine ⟨3344113280415934566348941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142682166631079874830888149 3344113280415934566348941)
                    ·
                      refine ⟨1254042480155975462380853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344113280415934566348941 1254042480155975462380853)
                      ·
                        rfl

theorem cell23_2442239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_2442239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442239 prefixEnd_2442239 := by exact prefixLift 2442239
  have htrace : WordTrace (prefixWord ++ tailWord_2442239) baseStart_2442239 baseEnd_2442239 := by
    simpa [prefixWord, tailWord_2442239, baseEnd_2442239] using wordTrace_append hprefix tailTrace_2442239
  have hstable : (prefixWord ++ tailWord_2442239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442239).length < 2 ^ (prefixWord ++ tailWord_2442239).sum := by decide
  have hdescent : baseEnd_2442239 < baseStart_2442239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442250 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_2442250 : Nat := 118140960795 + 2442250 * 2 ^ 59
def prefixEnd_2442250 : Nat := 4983230072969 + 3 ^ 40 * 2442250 * 2
def baseEnd_2442250 : Nat := 418016042814391639781101

theorem tailTrace_2442250 : CollatzResearch.WordTrace tailWord_2442250 prefixEnd_2442250 418016042814391639781101 := by
  unfold tailWord_2442250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22269043850538206984459051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59384116934768551958557469 22269043850538206984459051)
  ·
    refine ⟨33403565775807310476688577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22269043850538206984459051 33403565775807310476688577)
    ·
      refine ⟨25052674331855482857516433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33403565775807310476688577 25052674331855482857516433)
      ·
        refine ⟨18789505748891612143137325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25052674331855482857516433 18789505748891612143137325)
        ·
          refine ⟨7046064655834354553676497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18789505748891612143137325 7046064655834354553676497)
          ·
            refine ⟨5284548491875765915257373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7046064655834354553676497 5284548491875765915257373)
            ·
              refine ⟨1981705684453412218221515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5284548491875765915257373 1981705684453412218221515)
              ·
                refine ⟨2972558526680118327332273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981705684453412218221515 2972558526680118327332273)
                ·
                  refine ⟨2229418895010088745499205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2972558526680118327332273 2229418895010088745499205)
                  ·
                    refine ⟨418016042814391639781101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2229418895010088745499205 418016042814391639781101)
                    ·
                      rfl

theorem cell23_2442250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_2442250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442250 prefixEnd_2442250 := by exact prefixLift 2442250
  have htrace : WordTrace (prefixWord ++ tailWord_2442250) baseStart_2442250 baseEnd_2442250 := by
    simpa [prefixWord, tailWord_2442250, baseEnd_2442250] using wordTrace_append hprefix tailTrace_2442250
  have hstable : (prefixWord ++ tailWord_2442250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442250).length < 2 ^ (prefixWord ++ tailWord_2442250).sum := by decide
  have hdescent : baseEnd_2442250 < baseStart_2442250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442256 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 8, 1, 3]
def baseStart_2442256 : Nat := 118140960795 + 2442256 * 2 ^ 59
def prefixEnd_2442256 : Nat := 4983230072969 + 3 ^ 40 * 2442256 * 2
def baseEnd_2442256 : Nat := 1254051209327101895868275

theorem tailTrace_2442256 : CollatzResearch.WordTrace tailWord_2442256 prefixEnd_2442256 1254051209327101895868275 := by
  unfold tailWord_2442256
  simp only [CollatzResearch.WordTrace]
  refine ⟨44538197120065545481277311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59384262826754060641703081 44538197120065545481277311)
  ·
    refine ⟨66807295680098318221915967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44538197120065545481277311 66807295680098318221915967)
    ·
      refine ⟨100210943520147477332873951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66807295680098318221915967 100210943520147477332873951)
      ·
        refine ⟨150316415280221215999310927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100210943520147477332873951 150316415280221215999310927)
        ·
          refine ⟨225474622920331823998966391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150316415280221215999310927 225474622920331823998966391)
          ·
            refine ⟨338211934380497735998449587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225474622920331823998966391 338211934380497735998449587)
            ·
              refine ⟨507317901570746603997674381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338211934380497735998449587 507317901570746603997674381)
              ·
                refine ⟨190244213089029976499127893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507317901570746603997674381 190244213089029976499127893)
                ·
                  refine ⟨2229424372137070037099155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 190244213089029976499127893 2229424372137070037099155)
                  ·
                    refine ⟨3344136558205605055648733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2229424372137070037099155 3344136558205605055648733)
                    ·
                      refine ⟨1254051209327101895868275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344136558205605055648733 1254051209327101895868275)
                      ·
                        rfl

theorem cell23_2442256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 8, 1, 3].length) (baseStart_2442256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442256 prefixEnd_2442256 := by exact prefixLift 2442256
  have htrace : WordTrace (prefixWord ++ tailWord_2442256) baseStart_2442256 baseEnd_2442256 := by
    simpa [prefixWord, tailWord_2442256, baseEnd_2442256] using wordTrace_append hprefix tailTrace_2442256
  have hstable : (prefixWord ++ tailWord_2442256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442256).length < 2 ^ (prefixWord ++ tailWord_2442256).sum := by decide
  have hdescent : baseEnd_2442256 < baseStart_2442256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442263 : List Nat := [1, 1, 3, 5, 1, 3, 2, 7]
def baseStart_2442263 : Nat := 118140960795 + 2442263 * 2 ^ 59
def prefixEnd_2442263 : Nat := 4983230072969 + 3 ^ 40 * 2442263 * 2
def baseEnd_2442263 : Nat := 46446474210803087721509

theorem tailTrace_2442263 : CollatzResearch.WordTrace tailWord_2442263 prefixEnd_2442263 46446474210803087721509 := by
  unfold tailWord_2442263
  simp only [CollatzResearch.WordTrace]
  refine ⟨89076649551105731158059443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59384433034070487438706295 89076649551105731158059443)
  ·
    refine ⟨133614974326658596737089165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89076649551105731158059443 133614974326658596737089165)
    ·
      refine ⟨50105615372496973776408437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133614974326658596737089165 50105615372496973776408437)
      ·
        refine ⟨4697401441171591291538291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50105615372496973776408437 4697401441171591291538291)
        ·
          refine ⟨7046102161757386937307437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697401441171591291538291 7046102161757386937307437)
          ·
            refine ⟨2642288310659020101490289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7046102161757386937307437 2642288310659020101490289)
            ·
              refine ⟨1981716232994265076117717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642288310659020101490289 1981716232994265076117717)
              ·
                refine ⟨46446474210803087721509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1981716232994265076117717 46446474210803087721509)
                ·
                  rfl

theorem cell23_2442263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 7].length) (baseStart_2442263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442263 prefixEnd_2442263 := by exact prefixLift 2442263
  have htrace : WordTrace (prefixWord ++ tailWord_2442263) baseStart_2442263 baseEnd_2442263 := by
    simpa [prefixWord, tailWord_2442263, baseEnd_2442263] using wordTrace_append hprefix tailTrace_2442263
  have hstable : (prefixWord ++ tailWord_2442263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442263).length < 2 ^ (prefixWord ++ tailWord_2442263).sum := by decide
  have hdescent : baseEnd_2442263 < baseStart_2442263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442273 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2442273 : Nat := 118140960795 + 2442273 * 2 ^ 59
def prefixEnd_2442273 : Nat := 4983230072969 + 3 ^ 40 * 2442273 * 2
def baseEnd_2442273 : Nat := 1254059938498228329355697

theorem tailTrace_2442273 : CollatzResearch.WordTrace tailWord_2442273 prefixEnd_2442273 1254059938498228329355697 := by
  unfold tailWord_2442273
  simp only [CollatzResearch.WordTrace]
  refine ⟨89077014281069502865923473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59384676187379668577282315 89077014281069502865923473)
  ·
    refine ⟨66807760710802127149442605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89077014281069502865923473 66807760710802127149442605)
    ·
      refine ⟨25052910266550797681040977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66807760710802127149442605 25052910266550797681040977)
      ·
        refine ⟨18789682699913098260780733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25052910266550797681040977 18789682699913098260780733)
        ·
          refine ⟨7046131012467411847792775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18789682699913098260780733 7046131012467411847792775)
          ·
            refine ⟨10569196518701117771689163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046131012467411847792775 10569196518701117771689163)
            ·
              refine ⟨15853794778051676657533745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10569196518701117771689163 15853794778051676657533745)
              ·
                refine ⟨11890346083538757493150309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15853794778051676657533745 11890346083538757493150309)
                ·
                  refine ⟨2229439890663517029965683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11890346083538757493150309 2229439890663517029965683)
                  ·
                    refine ⟨3344159835995275544948525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2229439890663517029965683 3344159835995275544948525)
                    ·
                      refine ⟨1254059938498228329355697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344159835995275544948525 1254059938498228329355697)
                      ·
                        rfl

theorem cell23_2442273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2442273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442273 prefixEnd_2442273 := by exact prefixLift 2442273
  have htrace : WordTrace (prefixWord ++ tailWord_2442273) baseStart_2442273 baseEnd_2442273 := by
    simpa [prefixWord, tailWord_2442273, baseEnd_2442273] using wordTrace_append hprefix tailTrace_2442273
  have hstable : (prefixWord ++ tailWord_2442273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442273).length < 2 ^ (prefixWord ++ tailWord_2442273).sum := by decide
  have hdescent : baseEnd_2442273 < baseStart_2442273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442274 : List Nat := [3, 3, 1, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_2442274 : Nat := 118140960795 + 2442274 * 2 ^ 59
def prefixEnd_2442274 : Nat := 4983230072969 + 3 ^ 40 * 2442274 * 2
def baseEnd_2442274 : Nat := 1254060451978882825443193

theorem tailTrace_2442274 : CollatzResearch.WordTrace tailWord_2442274 prefixEnd_2442274 1254060451978882825443193 := by
  unfold tailWord_2442274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22269262688516470009177469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59384700502710586691139917 22269262688516470009177469)
  ·
    refine ⟨8350973508193676253441551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22269262688516470009177469 8350973508193676253441551)
    ·
      refine ⟨12526460262290514380162327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8350973508193676253441551 12526460262290514380162327)
      ·
        refine ⟨18789690393435771570243491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12526460262290514380162327 18789690393435771570243491)
        ·
          refine ⟨28184535590153657355365237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18789690393435771570243491 28184535590153657355365237)
          ·
            refine ⟨2642300211576905377065491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28184535590153657355365237 2642300211576905377065491)
            ·
              refine ⟨3963450317365358065598237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642300211576905377065491 3963450317365358065598237)
              ·
                refine ⟨1486293869012009274599339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3963450317365358065598237 1486293869012009274599339)
                ·
                  refine ⟨2229440803518013911899009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486293869012009274599339 2229440803518013911899009)
                  ·
                    refine ⟨1672080602638510433924257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2229440803518013911899009 1672080602638510433924257)
                    ·
                      refine ⟨1254060451978882825443193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672080602638510433924257 1254060451978882825443193)
                      ·
                        rfl

theorem cell23_2442274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_2442274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442274 prefixEnd_2442274 := by exact prefixLift 2442274
  have htrace : WordTrace (prefixWord ++ tailWord_2442274) baseStart_2442274 baseEnd_2442274 := by
    simpa [prefixWord, tailWord_2442274, baseEnd_2442274] using wordTrace_append hprefix tailTrace_2442274
  have hstable : (prefixWord ++ tailWord_2442274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442274).length < 2 ^ (prefixWord ++ tailWord_2442274).sum := by decide
  have hdescent : baseEnd_2442274 < baseStart_2442274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442283 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 1, 3, 2]
def baseStart_2442283 : Nat := 118140960795 + 2442283 * 2 ^ 59
def prefixEnd_2442283 : Nat := 4983230072969 + 3 ^ 40 * 2442283 * 2
def baseEnd_2442283 : Nat := 1254065073304773290230651

theorem tailTrace_2442283 : CollatzResearch.WordTrace tailWord_2442283 prefixEnd_2442283 1254065073304773290230651 := by
  unfold tailWord_2442283
  simp only [CollatzResearch.WordTrace]
  refine ⟨89077379011033274573787503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59384919340688849715858335 89077379011033274573787503)
  ·
    refine ⟨133616068516549911860681255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89077379011033274573787503 133616068516549911860681255)
    ·
      refine ⟨200424102774824867791021883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133616068516549911860681255 200424102774824867791021883)
      ·
        refine ⟨300636154162237301686532825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200424102774824867791021883 300636154162237301686532825)
        ·
          refine ⟨225477115621677976264899619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300636154162237301686532825 225477115621677976264899619)
          ·
            refine ⟨338215673432516964397349429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225477115621677976264899619 338215673432516964397349429)
            ·
              refine ⟨31707719384298465412251509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 338215673432516964397349429 31707719384298465412251509)
              ·
                refine ⟨2972598692277981132398579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31707719384298465412251509 2972598692277981132398579)
                ·
                  refine ⟨4458898038416971698597869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972598692277981132398579 4458898038416971698597869)
                  ·
                    refine ⟨1672086764406364386974201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4458898038416971698597869 1672086764406364386974201)
                    ·
                      refine ⟨1254065073304773290230651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672086764406364386974201 1254065073304773290230651)
                      ·
                        rfl

theorem cell23_2442283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 3, 2].length) (baseStart_2442283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442283 prefixEnd_2442283 := by exact prefixLift 2442283
  have htrace : WordTrace (prefixWord ++ tailWord_2442283) baseStart_2442283 baseEnd_2442283 := by
    simpa [prefixWord, tailWord_2442283, baseEnd_2442283] using wordTrace_append hprefix tailTrace_2442283
  have hstable : (prefixWord ++ tailWord_2442283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442283).length < 2 ^ (prefixWord ++ tailWord_2442283).sum := by decide
  have hdescent : baseEnd_2442283 < baseStart_2442283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442286 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2442286 : Nat := 118140960795 + 2442286 * 2 ^ 59
def prefixEnd_2442286 : Nat := 4983230072969 + 3 ^ 40 * 2442286 * 2
def baseEnd_2442286 : Nat := 1254066613746736778493137

theorem tailTrace_2442286 : CollatzResearch.WordTrace tailWord_2442286 prefixEnd_2442286 1254066613746736778493137 := by
  unfold tailWord_2442286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134686053752800760768339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59384992286681604057431141 11134686053752800760768339)
  ·
    refine ⟨16702029080629201141152509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11134686053752800760768339 16702029080629201141152509)
    ·
      refine ⟨6263260905235950427932191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16702029080629201141152509 6263260905235950427932191)
      ·
        refine ⟨9394891357853925641898287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6263260905235950427932191 9394891357853925641898287)
        ·
          refine ⟨14092337036780888462847431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9394891357853925641898287 14092337036780888462847431)
          ·
            refine ⟨21138505555171332694271147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14092337036780888462847431 21138505555171332694271147)
            ·
              refine ⟨31707758332756999041406721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21138505555171332694271147 31707758332756999041406721)
              ·
                refine ⟨23780818749567749281055041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31707758332756999041406721 23780818749567749281055041)
                ·
                  refine ⟨17835614062175811960791281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23780818749567749281055041 17835614062175811960791281)
                  ·
                    refine ⟨13376710546631858970593461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17835614062175811960791281 13376710546631858970593461)
                    ·
                      refine ⟨1254066613746736778493137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13376710546631858970593461 1254066613746736778493137)
                      ·
                        rfl

theorem cell23_2442286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2442286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442286 prefixEnd_2442286 := by exact prefixLift 2442286
  have htrace : WordTrace (prefixWord ++ tailWord_2442286) baseStart_2442286 baseEnd_2442286 := by
    simpa [prefixWord, tailWord_2442286, baseEnd_2442286] using wordTrace_append hprefix tailTrace_2442286
  have hstable : (prefixWord ++ tailWord_2442286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442286).length < 2 ^ (prefixWord ++ tailWord_2442286).sum := by decide
  have hdescent : baseEnd_2442286 < baseStart_2442286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442299 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5]
def baseStart_2442299 : Nat := 118140960795 + 2442299 * 2 ^ 59
def prefixEnd_2442299 : Nat := 4983230072969 + 3 ^ 40 * 2442299 * 2
def baseEnd_2442299 : Nat := 1254073288995245227630577

theorem tailTrace_2442299 : CollatzResearch.WordTrace tailWord_2442299 prefixEnd_2442299 1254073288995245227630577 := by
  unfold tailWord_2442299
  simp only [CollatzResearch.WordTrace]
  refine ⟨89077962578975309306369951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59385308385983539537579967 89077962578975309306369951)
  ·
    refine ⟨133616943868462963959554927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89077962578975309306369951 133616943868462963959554927)
    ·
      refine ⟨200425415802694445939332391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133616943868462963959554927 200425415802694445939332391)
      ·
        refine ⟨300638123704041668908998587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200425415802694445939332391 300638123704041668908998587)
        ·
          refine ⟨450957185556062503363497881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300638123704041668908998587 450957185556062503363497881)
          ·
            refine ⟨338217889167046877522623411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450957185556062503363497881 338217889167046877522623411)
            ·
              refine ⟨507326833750570316283935117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338217889167046877522623411 507326833750570316283935117)
              ·
                refine ⟨190247562656463868606475669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507326833750570316283935117 190247562656463868606475669)
                ·
                  refine ⟨8917854499521743840928547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 190247562656463868606475669 8917854499521743840928547)
                  ·
                    refine ⟨13376781749282615761392821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8917854499521743840928547 13376781749282615761392821)
                    ·
                      refine ⟨1254073288995245227630577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13376781749282615761392821 1254073288995245227630577)
                      ·
                        rfl

theorem cell23_2442299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_2442299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442299 prefixEnd_2442299 := by exact prefixLift 2442299
  have htrace : WordTrace (prefixWord ++ tailWord_2442299) baseStart_2442299 baseEnd_2442299 := by
    simpa [prefixWord, tailWord_2442299, baseEnd_2442299] using wordTrace_append hprefix tailTrace_2442299
  have hstable : (prefixWord ++ tailWord_2442299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442299).length < 2 ^ (prefixWord ++ tailWord_2442299).sum := by decide
  have hdescent : baseEnd_2442299 < baseStart_2442299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442313 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 6, 2, 2]
def baseStart_2442313 : Nat := 118140960795 + 2442313 * 2 ^ 59
def prefixEnd_2442313 : Nat := 4983230072969 + 3 ^ 40 * 2442313 * 2
def baseEnd_2442313 : Nat := 1254080477724408172855513

theorem tailTrace_2442313 : CollatzResearch.WordTrace tailWord_2442313 prefixEnd_2442313 1254080477724408172855513 := by
  unfold tailWord_2442313
  simp only [CollatzResearch.WordTrace]
  refine ⟨89078473200924589697379593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59385648800616393131586395 89078473200924589697379593)
  ·
    refine ⟨66808854900693442273034695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89078473200924589697379593 66808854900693442273034695)
    ·
      refine ⟨100213282351040163409552043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66808854900693442273034695 100213282351040163409552043)
      ·
        refine ⟨150319923526560245114328065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100213282351040163409552043 150319923526560245114328065)
        ·
          refine ⟨112739942644920183835746049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150319923526560245114328065 112739942644920183835746049)
          ·
            refine ⟨84554956983690137876809537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112739942644920183835746049 84554956983690137876809537)
            ·
              refine ⟨63416217737767603407607153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84554956983690137876809537 63416217737767603407607153)
              ·
                refine ⟨47562163303325702555705365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63416217737767603407607153 47562163303325702555705365)
                ·
                  refine ⟨2229476404843392307298689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47562163303325702555705365 2229476404843392307298689)
                  ·
                    refine ⟨1672107303632544230474017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2229476404843392307298689 1672107303632544230474017)
                    ·
                      refine ⟨1254080477724408172855513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672107303632544230474017 1254080477724408172855513)
                      ·
                        rfl

theorem cell23_2442313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 2, 2].length) (baseStart_2442313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442313 prefixEnd_2442313 := by exact prefixLift 2442313
  have htrace : WordTrace (prefixWord ++ tailWord_2442313) baseStart_2442313 baseEnd_2442313 := by
    simpa [prefixWord, tailWord_2442313, baseEnd_2442313] using wordTrace_append hprefix tailTrace_2442313
  have hstable : (prefixWord ++ tailWord_2442313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442313).length < 2 ^ (prefixWord ++ tailWord_2442313).sum := by decide
  have hdescent : baseEnd_2442313 < baseStart_2442313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442317 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_2442317 : Nat := 118140960795 + 2442317 * 2 ^ 59
def prefixEnd_2442317 : Nat := 4983230072969 + 3 ^ 40 * 2442317 * 2
def baseEnd_2442317 : Nat := 1254082531647026157205495

theorem tailTrace_2442317 : CollatzResearch.WordTrace tailWord_2442317 prefixEnd_2442317 1254082531647026157205495 := by
  unfold tailWord_2442317
  simp only [CollatzResearch.WordTrace]
  refine ⟨89078619092910098380525205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59385746061940065587016803 89078619092910098380525205)
  ·
    refine ⟨4175560269980160861587119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89078619092910098380525205 4175560269980160861587119)
    ·
      refine ⟨6263340404970241292380679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4175560269980160861587119 6263340404970241292380679)
      ·
        refine ⟨9395010607455361938571019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6263340404970241292380679 9395010607455361938571019)
        ·
          refine ⟨14092515911183042907856529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9395010607455361938571019 14092515911183042907856529)
          ·
            refine ⟨10569386933387282180892397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14092515911183042907856529 10569386933387282180892397)
            ·
              refine ⟨3963520100020230817834649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10569386933387282180892397 3963520100020230817834649)
              ·
                refine ⟨2972640075015173113375987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3963520100020230817834649 2972640075015173113375987)
                ·
                  refine ⟨4458960112522759670063981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972640075015173113375987 4458960112522759670063981)
                  ·
                    refine ⟨1672110042196034876273993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4458960112522759670063981 1672110042196034876273993)
                    ·
                      refine ⟨1254082531647026157205495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672110042196034876273993 1254082531647026157205495)
                      ·
                        rfl

theorem cell23_2442317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_2442317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442317 prefixEnd_2442317 := by exact prefixLift 2442317
  have htrace : WordTrace (prefixWord ++ tailWord_2442317) baseStart_2442317 baseEnd_2442317 := by
    simpa [prefixWord, tailWord_2442317, baseEnd_2442317] using wordTrace_append hprefix tailTrace_2442317
  have hstable : (prefixWord ++ tailWord_2442317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442317).length < 2 ^ (prefixWord ++ tailWord_2442317).sum := by decide
  have hdescent : baseEnd_2442317 < baseStart_2442317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442329 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_2442329 : Nat := 118140960795 + 2442329 * 2 ^ 59
def prefixEnd_2442329 : Nat := 4983230072969 + 3 ^ 40 * 2442329 * 2
def baseEnd_2442329 : Nat := 1254088693414880110255439

theorem tailTrace_2442329 : CollatzResearch.WordTrace tailWord_2442329 prefixEnd_2442329 1254088693414880110255439 := by
  unfold tailWord_2442329
  simp only [CollatzResearch.WordTrace]
  refine ⟨89079056768866624429962041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59386037845911082953308027 89079056768866624429962041)
  ·
    refine ⟨66809292576649968322471531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89079056768866624429962041 66809292576649968322471531)
    ·
      refine ⟨100213938864974952483707297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66809292576649968322471531 100213938864974952483707297)
      ·
        refine ⟨75160454148731214362780473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100213938864974952483707297 75160454148731214362780473)
        ·
          refine ⟨56370340611548410772085355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75160454148731214362780473 56370340611548410772085355)
          ·
            refine ⟨84555510917322616158128033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56370340611548410772085355 84555510917322616158128033)
            ·
              refine ⟨63416633187991962118596025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84555510917322616158128033 63416633187991962118596025)
              ·
                refine ⟨47562474890993971588947019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63416633187991962118596025 47562474890993971588947019)
                ·
                  refine ⟨71343712336490957383420529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47562474890993971588947019 71343712336490957383420529)
                  ·
                    refine ⟨53507784252368218037565397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71343712336490957383420529 53507784252368218037565397)
                    ·
                      refine ⟨1254088693414880110255439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53507784252368218037565397 1254088693414880110255439)
                      ·
                        rfl

theorem cell23_2442329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_2442329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442329 prefixEnd_2442329 := by exact prefixLift 2442329
  have htrace : WordTrace (prefixWord ++ tailWord_2442329) baseStart_2442329 baseEnd_2442329 := by
    simpa [prefixWord, tailWord_2442329, baseEnd_2442329] using wordTrace_append hprefix tailTrace_2442329
  have hstable : (prefixWord ++ tailWord_2442329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442329).length < 2 ^ (prefixWord ++ tailWord_2442329).sum := by decide
  have hdescent : baseEnd_2442329 < baseStart_2442329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442430 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2442430 : Nat := 118140960795 + 2442430 * 2 ^ 59
def prefixEnd_2442430 : Nat := 4983230072969 + 3 ^ 40 * 2442430 * 2
def baseEnd_2442430 : Nat := 418046851653661405030825

theorem tailTrace_2442430 : CollatzResearch.WordTrace tailWord_2442430 prefixEnd_2442430 418046851653661405030825 := by
  unfold tailWord_2442430
  simp only [CollatzResearch.WordTrace]
  refine ⟨11135342567687589834923593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59388493694333812452925829 11135342567687589834923593)
  ·
    refine ⟨8351506925765692376192695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11135342567687589834923593 8351506925765692376192695)
    ·
      refine ⟨12527260388648538564289043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351506925765692376192695 12527260388648538564289043)
      ·
        refine ⟨18790890582972807846433565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12527260388648538564289043 18790890582972807846433565)
        ·
          refine ⟨7046583968614802942412587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18790890582972807846433565 7046583968614802942412587)
          ·
            refine ⟨10569875952922204413618881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046583968614802942412587 10569875952922204413618881)
            ·
              refine ⟨7927406964691653310214161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10569875952922204413618881 7927406964691653310214161)
              ·
                refine ⟨5945555223518739982660621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7927406964691653310214161 5945555223518739982660621)
                ·
                  refine ⟨2229583208819527493497733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5945555223518739982660621 2229583208819527493497733)
                  ·
                    refine ⟨418046851653661405030825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2229583208819527493497733 418046851653661405030825)
                    ·
                      rfl

theorem cell23_2442430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2442430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442430 prefixEnd_2442430 := by exact prefixLift 2442430
  have htrace : WordTrace (prefixWord ++ tailWord_2442430) baseStart_2442430 baseEnd_2442430 := by
    simpa [prefixWord, tailWord_2442430, baseEnd_2442430] using wordTrace_append hprefix tailTrace_2442430
  have hstable : (prefixWord ++ tailWord_2442430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442430).length < 2 ^ (prefixWord ++ tailWord_2442430).sum := by decide
  have hdescent : baseEnd_2442430 < baseStart_2442430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442438 : List Nat := [6, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_2442438 : Nat := 118140960795 + 2442438 * 2 ^ 59
def prefixEnd_2442438 : Nat := 4983230072969 + 3 ^ 40 * 2442438 * 2
def baseEnd_2442438 : Nat := 139349406978468909310271

theorem tailTrace_2442438 : CollatzResearch.WordTrace tailWord_2442438 prefixEnd_2442438 139349406978468909310271 := by
  unfold tailWord_2442438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783844760170991751427499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59388688216981157363786645 2783844760170991751427499)
  ·
    refine ⟨4175767140256487627141249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2783844760170991751427499 4175767140256487627141249)
    ·
      refine ⟨3131825355192365720355937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4175767140256487627141249 3131825355192365720355937)
      ·
        refine ⟨2348869016394274290266953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3131825355192365720355937 2348869016394274290266953)
        ·
          refine ⟨1761651762295705717700215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2348869016394274290266953 1761651762295705717700215)
          ·
            refine ⟨2642477643443558576550323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761651762295705717700215 2642477643443558576550323)
            ·
              refine ⟨3963716465165337864825485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642477643443558576550323 3963716465165337864825485)
              ·
                refine ⟨1486393674437001699309557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3963716465165337864825485 1486393674437001699309557)
                ·
                  refine ⟨139349406978468909310271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1486393674437001699309557 139349406978468909310271)
                  ·
                    rfl

theorem cell23_2442438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_2442438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442438 prefixEnd_2442438 := by exact prefixLift 2442438
  have htrace : WordTrace (prefixWord ++ tailWord_2442438) baseStart_2442438 baseEnd_2442438 := by
    simpa [prefixWord, tailWord_2442438, baseEnd_2442438] using wordTrace_append hprefix tailTrace_2442438
  have hstable : (prefixWord ++ tailWord_2442438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442438).length < 2 ^ (prefixWord ++ tailWord_2442438).sum := by decide
  have hdescent : baseEnd_2442438 < baseStart_2442438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442477 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 6]
def baseStart_2442477 : Nat := 118140960795 + 2442477 * 2 ^ 59
def prefixEnd_2442477 : Nat := 4983230072969 + 3 ^ 40 * 2442477 * 2
def baseEnd_2442477 : Nat := 139351632061305059022751

theorem tailTrace_2442477 : CollatzResearch.WordTrace tailWord_2442477 prefixEnd_2442477 139351632061305059022751 := by
  unfold tailWord_2442477
  simp only [CollatzResearch.WordTrace]
  refine ⟨89084454772330445706349685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59389636514886963804233123 89084454772330445706349685)
  ·
    refine ⟨8351667634905979284970283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89084454772330445706349685 8351667634905979284970283)
    ·
      refine ⟨12527501452358968927455425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351667634905979284970283 12527501452358968927455425)
      ·
        refine ⟨9395626089269226695591569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12527501452358968927455425 9395626089269226695591569)
        ·
          refine ⟨7046719566951920021693677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9395626089269226695591569 7046719566951920021693677)
          ·
            refine ⟨2642519837606970008135129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7046719566951920021693677 2642519837606970008135129)
            ·
              refine ⟨1981889878205227506101347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642519837606970008135129 1981889878205227506101347)
              ·
                refine ⟨2972834817307841259152021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981889878205227506101347 2972834817307841259152021)
                ·
                  refine ⟨139351632061305059022751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2972834817307841259152021 139351632061305059022751)
                  ·
                    rfl

theorem cell23_2442477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_2442477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442477 prefixEnd_2442477 := by exact prefixLift 2442477
  have htrace : WordTrace (prefixWord ++ tailWord_2442477) baseStart_2442477 baseEnd_2442477 := by
    simpa [prefixWord, tailWord_2442477, baseEnd_2442477] using wordTrace_append hprefix tailTrace_2442477
  have hstable : (prefixWord ++ tailWord_2442477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442477).length < 2 ^ (prefixWord ++ tailWord_2442477).sum := by decide
  have hdescent : baseEnd_2442477 < baseStart_2442477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442497 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_2442497 : Nat := 118140960795 + 2442497 * 2 ^ 59
def prefixEnd_2442497 : Nat := 4983230072969 + 3 ^ 40 * 2442497 * 2
def baseEnd_2442497 : Nat := 1254174958164835452954667

theorem tailTrace_2442497 : CollatzResearch.WordTrace tailWord_2442497 prefixEnd_2442497 1254174958164835452954667 := by
  unfold tailWord_2442497
  simp only [CollatzResearch.WordTrace]
  refine ⟨89085184232257989122077745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59390122821505326081385163 89085184232257989122077745)
  ·
    refine ⟨66813888174193491841558309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89085184232257989122077745 66813888174193491841558309)
    ·
      refine ⟨12527604032661279720292183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66813888174193491841558309 12527604032661279720292183)
      ·
        refine ⟨18791406048991919580438275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12527604032661279720292183 18791406048991919580438275)
        ·
          refine ⟨28187109073487879370657413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18791406048991919580438275 28187109073487879370657413)
          ·
            refine ⟨5285082951278977381998265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28187109073487879370657413 5285082951278977381998265)
            ·
              refine ⟨3963812213459233036498699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5285082951278977381998265 3963812213459233036498699)
              ·
                refine ⟨5945718320188849554748049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963812213459233036498699 5945718320188849554748049)
                ·
                  refine ⟨4459288740141637166061037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5945718320188849554748049 4459288740141637166061037)
                  ·
                    refine ⟨1672233277553113937272889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4459288740141637166061037 1672233277553113937272889)
                    ·
                      refine ⟨1254174958164835452954667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672233277553113937272889 1254174958164835452954667)
                      ·
                        rfl

theorem cell23_2442497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_2442497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442497 prefixEnd_2442497 := by exact prefixLift 2442497
  have htrace : WordTrace (prefixWord ++ tailWord_2442497) baseStart_2442497 baseEnd_2442497 := by
    simpa [prefixWord, tailWord_2442497, baseEnd_2442497] using wordTrace_append hprefix tailTrace_2442497
  have hstable : (prefixWord ++ tailWord_2442497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442497).length < 2 ^ (prefixWord ++ tailWord_2442497).sum := by decide
  have hdescent : baseEnd_2442497 < baseStart_2442497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442516 : List Nat := [2, 4, 17]
def baseStart_2442516 : Nat := 118140960795 + 2442516 * 2 ^ 59
def prefixEnd_2442516 : Nat := 4983230072969 + 3 ^ 40 * 2442516 * 2
def baseEnd_2442516 : Nat := 191157554381538009239

theorem tailTrace_2442516 : CollatzResearch.WordTrace tailWord_2442516 prefixEnd_2442516 191157554381538009239 := by
  unfold tailWord_2442516
  simp only [CollatzResearch.WordTrace]
  refine ⟨44542938609594577683509701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59390584812792770244679601 44542938609594577683509701)
  ·
    refine ⟨8351800989298983315658069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44542938609594577683509701 8351800989298983315658069)
    ·
      refine ⟨191157554381538009239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 8351800989298983315658069 191157554381538009239)
      ·
        rfl

theorem cell23_2442516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 17].length) (baseStart_2442516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442516 prefixEnd_2442516 := by exact prefixLift 2442516
  have htrace : WordTrace (prefixWord ++ tailWord_2442516) baseStart_2442516 baseEnd_2442516 := by
    simpa [prefixWord, tailWord_2442516, baseEnd_2442516] using wordTrace_append hprefix tailTrace_2442516
  have hstable : (prefixWord ++ tailWord_2442516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442516).length < 2 ^ (prefixWord ++ tailWord_2442516).sum := by decide
  have hdescent : baseEnd_2442516 < baseStart_2442516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442520 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 2, 4]
def baseStart_2442520 : Nat := 118140960795 + 2442520 * 2 ^ 59
def prefixEnd_2442520 : Nat := 4983230072969 + 3 ^ 40 * 2442520 * 2
def baseEnd_2442520 : Nat := 418062256073296287655687

theorem tailTrace_2442520 : CollatzResearch.WordTrace tailWord_2442520 prefixEnd_2442520 418062256073296287655687 := by
  unfold tailWord_2442520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44543011555587332025082507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59390682074116442700110009 44543011555587332025082507)
  ·
    refine ⟨66814517333380998037623761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44543011555587332025082507 66814517333380998037623761)
    ·
      refine ⟨50110888000035748528217821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66814517333380998037623761 50110888000035748528217821)
      ·
        refine ⟨18791583000013405698081683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50110888000035748528217821 18791583000013405698081683)
        ·
          refine ⟨28187374500020108547122525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18791583000013405698081683 28187374500020108547122525)
          ·
            refine ⟨10570265437507540705170947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28187374500020108547122525 10570265437507540705170947)
            ·
              refine ⟨15855398156261311057756421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10570265437507540705170947 15855398156261311057756421)
              ·
                refine ⟨2972887154298995823329329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15855398156261311057756421 2972887154298995823329329)
                ·
                  refine ⟨2229665365724246867496997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2972887154298995823329329 2229665365724246867496997)
                  ·
                    refine ⟨418062256073296287655687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2229665365724246867496997 418062256073296287655687)
                    ·
                      rfl

theorem cell23_2442520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_2442520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442520 prefixEnd_2442520 := by exact prefixLift 2442520
  have htrace : WordTrace (prefixWord ++ tailWord_2442520) baseStart_2442520 baseEnd_2442520 := by
    simpa [prefixWord, tailWord_2442520, baseEnd_2442520] using wordTrace_append hprefix tailTrace_2442520
  have hstable : (prefixWord ++ tailWord_2442520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442520).length < 2 ^ (prefixWord ++ tailWord_2442520).sum := by decide
  have hdescent : baseEnd_2442520 < baseStart_2442520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442533 : List Nat := [1, 3, 1, 2, 4, 1, 3, 8]
def baseStart_2442533 : Nat := 118140960795 + 2442533 * 2 ^ 59
def prefixEnd_2442533 : Nat := 4983230072969 + 3 ^ 40 * 2442533 * 2
def baseEnd_2442533 : Nat := 46451609017348048596463

theorem tailTrace_2442533 : CollatzResearch.WordTrace tailWord_2442533 prefixEnd_2442533 46451609017348048596463 := by
  unfold tailWord_2442533
  simp only [CollatzResearch.WordTrace]
  refine ⟨89086497260127567270388253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59390998173418378180258835 89086497260127567270388253)
  ·
    refine ⟨33407436472547837726395595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89086497260127567270388253 33407436472547837726395595)
    ·
      refine ⟨50111154708821756589593393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33407436472547837726395595 50111154708821756589593393)
      ·
        refine ⟨37583366031616317442195045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50111154708821756589593393 37583366031616317442195045)
        ·
          refine ⟨7046881130928059520411571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37583366031616317442195045 7046881130928059520411571)
          ·
            refine ⟨10570321696392089280617357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046881130928059520411571 10570321696392089280617357)
            ·
              refine ⟨3963870636147033480231509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10570321696392089280617357 3963870636147033480231509)
              ·
                refine ⟨46451609017348048596463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3963870636147033480231509 46451609017348048596463)
                ·
                  rfl

theorem cell23_2442533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 8].length) (baseStart_2442533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442533 prefixEnd_2442533 := by exact prefixLift 2442533
  have htrace : WordTrace (prefixWord ++ tailWord_2442533) baseStart_2442533 baseEnd_2442533 := by
    simpa [prefixWord, tailWord_2442533, baseEnd_2442533] using wordTrace_append hprefix tailTrace_2442533
  have hstable : (prefixWord ++ tailWord_2442533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442533).length < 2 ^ (prefixWord ++ tailWord_2442533).sum := by decide
  have hdescent : baseEnd_2442533 < baseStart_2442533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442560 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 4, 1, 3]
def baseStart_2442560 : Nat := 118140960795 + 2442560 * 2 ^ 59
def prefixEnd_2442560 : Nat := 4983230072969 + 3 ^ 40 * 2442560 * 2
def baseEnd_2442560 : Nat := 1254207307446068706466877

theorem tailTrace_2442560 : CollatzResearch.WordTrace tailWord_2442560 prefixEnd_2442560 1254207307446068706466877 := by
  unfold tailWord_2442560
  simp only [CollatzResearch.WordTrace]
  refine ⟨44543741015514875440810567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59391654687353167254414089 44543741015514875440810567)
  ·
    refine ⟨66815611523272313161215851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44543741015514875440810567 66815611523272313161215851)
    ·
      refine ⟨100223417284908469741823777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66815611523272313161215851 100223417284908469741823777)
      ·
        refine ⟨75167562963681352306367833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100223417284908469741823777 75167562963681352306367833)
        ·
          refine ⟨56375672222761014229775875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75167562963681352306367833 56375672222761014229775875)
          ·
            refine ⟨84563508334141521344663813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56375672222761014229775875 84563508334141521344663813)
            ·
              refine ⟨15855657812651535252124465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84563508334141521344663813 15855657812651535252124465)
              ·
                refine ⟨11891743359488651439093349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15855657812651535252124465 11891743359488651439093349)
                ·
                  refine ⟨2229701879904122144830003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11891743359488651439093349 2229701879904122144830003)
                  ·
                    refine ⟨3344552819856183217245005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2229701879904122144830003 3344552819856183217245005)
                    ·
                      refine ⟨1254207307446068706466877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344552819856183217245005 1254207307446068706466877)
                      ·
                        rfl

theorem cell23_2442560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_2442560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442560 prefixEnd_2442560 := by exact prefixLift 2442560
  have htrace : WordTrace (prefixWord ++ tailWord_2442560) baseStart_2442560 baseEnd_2442560 := by
    simpa [prefixWord, tailWord_2442560, baseEnd_2442560] using wordTrace_append hprefix tailTrace_2442560
  have hstable : (prefixWord ++ tailWord_2442560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442560).length < 2 ^ (prefixWord ++ tailWord_2442560).sum := by decide
  have hdescent : baseEnd_2442560 < baseStart_2442560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442561 : List Nat := [1, 2, 5, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2442561 : Nat := 118140960795 + 2442561 * 2 ^ 59
def prefixEnd_2442561 : Nat := 4983230072969 + 3 ^ 40 * 2442561 * 2
def baseEnd_2442561 : Nat := 1254207820926723202554373

theorem tailTrace_2442561 : CollatzResearch.WordTrace tailWord_2442561 prefixEnd_2442561 1254207820926723202554373 := by
  unfold tailWord_2442561
  simp only [CollatzResearch.WordTrace]
  refine ⟨89087518504026128052407537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59391679002684085368271691 89087518504026128052407537)
  ·
    refine ⟨66815638878019596039305653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89087518504026128052407537 66815638878019596039305653)
    ·
      refine ⟨6263966144814337128684905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66815638878019596039305653 6263966144814337128684905)
      ·
        refine ⟨4697974608610752846513679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6263966144814337128684905 4697974608610752846513679)
        ·
          refine ⟨7046961912916129269770519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697974608610752846513679 7046961912916129269770519)
          ·
            refine ⟨10570442869374193904655779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046961912916129269770519 10570442869374193904655779)
            ·
              refine ⟨15855664304061290856983669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10570442869374193904655779 15855664304061290856983669)
              ·
                refine ⟨1486468528505746017842219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15855664304061290856983669 1486468528505746017842219)
                ·
                  refine ⟨2229702792758619026763329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486468528505746017842219 2229702792758619026763329)
                  ·
                    refine ⟨1672277094568964270072497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2229702792758619026763329 1672277094568964270072497)
                    ·
                      refine ⟨1254207820926723202554373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672277094568964270072497 1254207820926723202554373)
                      ·
                        rfl

theorem cell23_2442561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2442561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442561 prefixEnd_2442561 := by exact prefixLift 2442561
  have htrace : WordTrace (prefixWord ++ tailWord_2442561) baseStart_2442561 baseEnd_2442561 := by
    simpa [prefixWord, tailWord_2442561, baseEnd_2442561] using wordTrace_append hprefix tailTrace_2442561
  have hstable : (prefixWord ++ tailWord_2442561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442561).length < 2 ^ (prefixWord ++ tailWord_2442561).sum := by decide
  have hdescent : baseEnd_2442561 < baseStart_2442561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442564 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2442564 : Nat := 118140960795 + 2442564 * 2 ^ 59
def prefixEnd_2442564 : Nat := 4983230072969 + 3 ^ 40 * 2442564 * 2
def baseEnd_2442564 : Nat := 1254209361368686690816859

theorem tailTrace_2442564 : CollatzResearch.WordTrace tailWord_2442564 prefixEnd_2442564 1254209361368686690816859 := by
  unfold tailWord_2442564
  simp only [CollatzResearch.WordTrace]
  refine ⟨44543813961507629782383373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59391751948676839709844497 44543813961507629782383373)
  ·
    refine ⟨16703930235565361168393765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44543813961507629782383373 16703930235565361168393765)
    ·
      refine ⟨3131986919168505219073831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16703930235565361168393765 3131986919168505219073831)
      ·
        refine ⟨4697980378752757828610747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131986919168505219073831 4697980378752757828610747)
        ·
          refine ⟨7046970568129136742916121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697980378752757828610747 7046970568129136742916121)
          ·
            refine ⟨5285227926096852557187091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7046970568129136742916121 5285227926096852557187091)
            ·
              refine ⟨7927841889145278835780637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285227926096852557187091 7927841889145278835780637)
              ·
                refine ⟨2972940708429479563417739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7927841889145278835780637 2972940708429479563417739)
                ·
                  refine ⟨4459411062644219345126609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972940708429479563417739 4459411062644219345126609)
                  ·
                    refine ⟨3344558296983164508844957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4459411062644219345126609 3344558296983164508844957)
                    ·
                      refine ⟨1254209361368686690816859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344558296983164508844957 1254209361368686690816859)
                      ·
                        rfl

theorem cell23_2442564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2442564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442564 prefixEnd_2442564 := by exact prefixLift 2442564
  have htrace : WordTrace (prefixWord ++ tailWord_2442564) baseStart_2442564 baseEnd_2442564 := by
    simpa [prefixWord, tailWord_2442564, baseEnd_2442564] using wordTrace_append hprefix tailTrace_2442564
  have hstable : (prefixWord ++ tailWord_2442564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442564).length < 2 ^ (prefixWord ++ tailWord_2442564).sum := by decide
  have hdescent : baseEnd_2442564 < baseStart_2442564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442604 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 1, 3, 2]
def baseStart_2442604 : Nat := 118140960795 + 2442604 * 2 ^ 59
def prefixEnd_2442604 : Nat := 4983230072969 + 3 ^ 40 * 2442604 * 2
def baseEnd_2442604 : Nat := 1254229900594866534316675

theorem tailTrace_2442604 : CollatzResearch.WordTrace tailWord_2442604 prefixEnd_2442604 1254229900594866534316675 := by
  unfold tailWord_2442604
  simp only [CollatzResearch.WordTrace]
  refine ⟨44544543421435173198111433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59392724561913564264148577 44544543421435173198111433)
  ·
    refine ⟨33408407566076379898583575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44544543421435173198111433 33408407566076379898583575)
    ·
      refine ⟨50112611349114569847875363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33408407566076379898583575 50112611349114569847875363)
      ·
        refine ⟨75168917023671854771813045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50112611349114569847875363 75168917023671854771813045)
        ·
          refine ⟨7047085970969236384857473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75168917023671854771813045 7047085970969236384857473)
          ·
            refine ⟨5285314478226927288643105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7047085970969236384857473 5285314478226927288643105)
            ·
              refine ⟨3963985858670195466482329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5285314478226927288643105 3963985858670195466482329)
              ·
                refine ⟨2972989394002646599861747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3963985858670195466482329 2972989394002646599861747)
                ·
                  refine ⟨4459484091003969899792621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972989394002646599861747 4459484091003969899792621)
                  ·
                    refine ⟨1672306534126488712422233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4459484091003969899792621 1672306534126488712422233)
                    ·
                      refine ⟨1254229900594866534316675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672306534126488712422233 1254229900594866534316675)
                      ·
                        rfl

theorem cell23_2442604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_2442604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442604 prefixEnd_2442604 := by exact prefixLift 2442604
  have htrace : WordTrace (prefixWord ++ tailWord_2442604) baseStart_2442604 baseEnd_2442604 := by
    simpa [prefixWord, tailWord_2442604, baseEnd_2442604] using wordTrace_append hprefix tailTrace_2442604
  have hstable : (prefixWord ++ tailWord_2442604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442604).length < 2 ^ (prefixWord ++ tailWord_2442604).sum := by decide
  have hdescent : baseEnd_2442604 < baseStart_2442604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442617 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 4, 2, 2]
def baseStart_2442617 : Nat := 118140960795 + 2442617 * 2 ^ 59
def prefixEnd_2442617 : Nat := 4983230072969 + 3 ^ 40 * 2442617 * 2
def baseEnd_2442617 : Nat := 1254236575843374983454115

theorem tailTrace_2442617 : CollatzResearch.WordTrace tailWord_2442617 prefixEnd_2442617 1254236575843374983454115 := by
  unfold tailWord_2442617
  simp only [CollatzResearch.WordTrace]
  refine ⟨89089560991823249616446105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59393040661215499744297403 89089560991823249616446105)
  ·
    refine ⟨66817170743867437212334579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89089560991823249616446105 66817170743867437212334579)
    ·
      refine ⟨100225756115801155818501869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66817170743867437212334579 100225756115801155818501869)
      ·
        refine ⟨37584658543425433431938201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100225756115801155818501869 37584658543425433431938201)
        ·
          refine ⟨28188493907569075073953651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37584658543425433431938201 28188493907569075073953651)
          ·
            refine ⟨42282740861353612610930477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28188493907569075073953651 42282740861353612610930477)
            ·
              refine ⟨15856027823007604729098929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42282740861353612610930477 15856027823007604729098929)
              ·
                refine ⟨11892020867255703546824197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15856027823007604729098929 11892020867255703546824197)
                ·
                  refine ⟨2229753912610444415029537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11892020867255703546824197 2229753912610444415029537)
                  ·
                    refine ⟨1672315434457833311272153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2229753912610444415029537 1672315434457833311272153)
                    ·
                      refine ⟨1254236575843374983454115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672315434457833311272153 1254236575843374983454115)
                      ·
                        rfl

theorem cell23_2442617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_2442617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442617 prefixEnd_2442617 := by exact prefixLift 2442617
  have htrace : WordTrace (prefixWord ++ tailWord_2442617) baseStart_2442617 baseEnd_2442617 := by
    simpa [prefixWord, tailWord_2442617, baseEnd_2442617] using wordTrace_append hprefix tailTrace_2442617
  have hstable : (prefixWord ++ tailWord_2442617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442617).length < 2 ^ (prefixWord ++ tailWord_2442617).sum := by decide
  have hdescent : baseEnd_2442617 < baseStart_2442617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442650 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2442650 : Nat := 118140960795 + 2442650 * 2 ^ 59
def prefixEnd_2442650 : Nat := 4983230072969 + 3 ^ 40 * 2442650 * 2
def baseEnd_2442650 : Nat := 1254253520704973354341463

theorem tailTrace_2442650 : CollatzResearch.WordTrace tailWord_2442650 prefixEnd_2442650 1254253520704973354341463 := by
  unfold tailWord_2442650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22272691150175924063099351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59393843067135797501598269 22272691150175924063099351)
  ·
    refine ⟨33409036725263886094649027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22272691150175924063099351 33409036725263886094649027)
    ·
      refine ⟨50113555087895829141973541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33409036725263886094649027 50113555087895829141973541)
      ·
        refine ⟨9396291578980467964120039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50113555087895829141973541 9396291578980467964120039)
        ·
          refine ⟨14094437368470701946180059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396291578980467964120039 14094437368470701946180059)
          ·
            refine ⟨21141656052706052919270089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14094437368470701946180059 21141656052706052919270089)
            ·
              refine ⟨15856242039529539689452567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21141656052706052919270089 15856242039529539689452567)
              ·
                refine ⟨23784363059294309534178851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15856242039529539689452567 23784363059294309534178851)
                ·
                  refine ⟨35676544588941464301268277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23784363059294309534178851 35676544588941464301268277)
                  ·
                    refine ⟨3344676055213262278243901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35676544588941464301268277 3344676055213262278243901)
                    ·
                      refine ⟨1254253520704973354341463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344676055213262278243901 1254253520704973354341463)
                      ·
                        rfl

theorem cell23_2442650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2442650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442650 prefixEnd_2442650 := by exact prefixLift 2442650
  have htrace : WordTrace (prefixWord ++ tailWord_2442650) baseStart_2442650 baseEnd_2442650 := by
    simpa [prefixWord, tailWord_2442650, baseEnd_2442650] using wordTrace_append hprefix tailTrace_2442650
  have hstable : (prefixWord ++ tailWord_2442650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442650).length < 2 ^ (prefixWord ++ tailWord_2442650).sum := by decide
  have hdescent : baseEnd_2442650 < baseStart_2442650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442717 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2442717 : Nat := 118140960795 + 2442717 * 2 ^ 59
def prefixEnd_2442717 : Nat := 4983230072969 + 3 ^ 40 * 2442717 * 2
def baseEnd_2442717 : Nat := 418095974636274864067885

theorem tailTrace_2442717 : CollatzResearch.WordTrace tailWord_2442717 prefixEnd_2442717 418095974636274864067885 := by
  unfold tailWord_2442717
  simp only [CollatzResearch.WordTrace]
  refine ⟨89093208291460966695086405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59395472194307311130057603 89093208291460966695086405)
  ·
    refine ⟨16704976554648931255328701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89093208291460966695086405 16704976554648931255328701)
    ·
      refine ⟨6264366207993349220748263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16704976554648931255328701 6264366207993349220748263)
      ·
        refine ⟨9396549311990023831122395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264366207993349220748263 9396549311990023831122395)
        ·
          refine ⟨14094823967985035746683593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396549311990023831122395 14094823967985035746683593)
          ·
            refine ⟨10571117975988776810012695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14094823967985035746683593 10571117975988776810012695)
            ·
              refine ⟨15856676963983165215019043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10571117975988776810012695 15856676963983165215019043)
              ·
                refine ⟨23785015445974747822528565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15856676963983165215019043 23785015445974747822528565)
                ·
                  refine ⟨2229845198060132608362053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23785015445974747822528565 2229845198060132608362053)
                  ·
                    refine ⟨418095974636274864067885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2229845198060132608362053 418095974636274864067885)
                    ·
                      rfl

theorem cell23_2442717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2442717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442717 prefixEnd_2442717 := by exact prefixLift 2442717
  have htrace : WordTrace (prefixWord ++ tailWord_2442717) baseStart_2442717 baseEnd_2442717 := by
    simpa [prefixWord, tailWord_2442717, baseEnd_2442717] using wordTrace_append hprefix tailTrace_2442717
  have hstable : (prefixWord ++ tailWord_2442717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442717).length < 2 ^ (prefixWord ++ tailWord_2442717).sum := by decide
  have hdescent : baseEnd_2442717 < baseStart_2442717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442727 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2442727 : Nat := 118140960795 + 2442727 * 2 ^ 59
def prefixEnd_2442727 : Nat := 4983230072969 + 3 ^ 40 * 2442727 * 2
def baseEnd_2442727 : Nat := 1254293058715369553078609

theorem tailTrace_2442727 : CollatzResearch.WordTrace tailWord_2442727 prefixEnd_2442727 1254293058715369553078609 := by
  unfold tailWord_2442727
  simp only [CollatzResearch.WordTrace]
  refine ⟨89093573021424738402950435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59395715347616492268633623 89093573021424738402950435)
  ·
    refine ⟨133640359532137107604425653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89093573021424738402950435 133640359532137107604425653)
    ·
      refine ⟨12528783706137853837914905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133640359532137107604425653 12528783706137853837914905)
      ·
        refine ⟨9396587779603390378436179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12528783706137853837914905 9396587779603390378436179)
        ·
          refine ⟨14094881669405085567654269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396587779603390378436179 14094881669405085567654269)
          ·
            refine ⟨5285580626026907087870351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14094881669405085567654269 5285580626026907087870351)
            ·
              refine ⟨7928370939040360631805527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285580626026907087870351 7928370939040360631805527)
              ·
                refine ⟨11892556408560540947708291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928370939040360631805527 11892556408560540947708291)
                ·
                  refine ⟨17838834612840811421562437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11892556408560540947708291 17838834612840811421562437)
                  ·
                    refine ⟨3344781489907652141542957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17838834612840811421562437 3344781489907652141542957)
                    ·
                      refine ⟨1254293058715369553078609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344781489907652141542957 1254293058715369553078609)
                      ·
                        rfl

theorem cell23_2442727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2442727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442727 prefixEnd_2442727 := by exact prefixLift 2442727
  have htrace : WordTrace (prefixWord ++ tailWord_2442727) baseStart_2442727 baseEnd_2442727 := by
    simpa [prefixWord, tailWord_2442727, baseEnd_2442727] using wordTrace_append hprefix tailTrace_2442727
  have hstable : (prefixWord ++ tailWord_2442727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442727).length < 2 ^ (prefixWord ++ tailWord_2442727).sum := by decide
  have hdescent : baseEnd_2442727 < baseStart_2442727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442760 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 5, 5]
def baseStart_2442760 : Nat := 118140960795 + 2442760 * 2 ^ 59
def prefixEnd_2442760 : Nat := 4983230072969 + 3 ^ 40 * 2442760 * 2
def baseEnd_2442760 : Nat := 418103334525655974655319

theorem tailTrace_2442760 : CollatzResearch.WordTrace tailWord_2442760 prefixEnd_2442760 418103334525655974655319 := by
  unfold tailWord_2442760
  simp only [CollatzResearch.WordTrace]
  refine ⟨44547388315152592519450867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59396517753536790025934489 44547388315152592519450867)
  ·
    refine ⟨66821082472728888779176301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44547388315152592519450867 66821082472728888779176301)
    ·
      refine ⟨25057905927273333292191113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66821082472728888779176301 25057905927273333292191113)
      ·
        refine ⟨18793429445454999969143335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25057905927273333292191113 18793429445454999969143335)
        ·
          refine ⟨28190144168182499953715003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18793429445454999969143335 28190144168182499953715003)
          ·
            refine ⟨42285216252273749930572505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28190144168182499953715003 42285216252273749930572505)
            ·
              refine ⟨31713912189205312447929379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42285216252273749930572505 31713912189205312447929379)
              ·
                refine ⟨47570868283807968671894069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31713912189205312447929379 47570868283807968671894069)
                ·
                  refine ⟨4459768901606997062990069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47570868283807968671894069 4459768901606997062990069)
                  ·
                    refine ⟨418103334525655974655319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4459768901606997062990069 418103334525655974655319)
                    ·
                      rfl

theorem cell23_2442760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_2442760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442760 prefixEnd_2442760 := by exact prefixLift 2442760
  have htrace : WordTrace (prefixWord ++ tailWord_2442760) baseStart_2442760 baseEnd_2442760 := by
    simpa [prefixWord, tailWord_2442760, baseEnd_2442760] using wordTrace_append hprefix tailTrace_2442760
  have hstable : (prefixWord ++ tailWord_2442760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442760).length < 2 ^ (prefixWord ++ tailWord_2442760).sum := by decide
  have hdescent : baseEnd_2442760 < baseStart_2442760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442764 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 6]
def baseStart_2442764 : Nat := 118140960795 + 2442764 * 2 ^ 59
def prefixEnd_2442764 : Nat := 4983230072969 + 3 ^ 40 * 2442764 * 2
def baseEnd_2442764 : Nat := 139368006388842878701771

theorem tailTrace_2442764 : CollatzResearch.WordTrace tailWord_2442764 prefixEnd_2442764 139368006388842878701771 := by
  unfold tailWord_2442764
  simp only [CollatzResearch.WordTrace]
  refine ⟨44547461261145346861023673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59396615014860462481364897 44547461261145346861023673)
  ·
    refine ⟨33410595945859010145767755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44547461261145346861023673 33410595945859010145767755)
    ·
      refine ⟨50115893918788515218651633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33410595945859010145767755 50115893918788515218651633)
      ·
        refine ⟨37586920439091386413988725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50115893918788515218651633 37586920439091386413988725)
        ·
          refine ⟨3523773791164817476311443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37586920439091386413988725 3523773791164817476311443)
          ·
            refine ⟨5285660686747226214467165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523773791164817476311443 5285660686747226214467165)
            ·
              refine ⟨1982122757530209830425187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5285660686747226214467165 1982122757530209830425187)
              ·
                refine ⟨2973184136295314745637781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982122757530209830425187 2973184136295314745637781)
                ·
                  refine ⟨139368006388842878701771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2973184136295314745637781 139368006388842878701771)
                  ·
                    rfl

theorem cell23_2442764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_2442764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442764 prefixEnd_2442764 := by exact prefixLift 2442764
  have htrace : WordTrace (prefixWord ++ tailWord_2442764) baseStart_2442764 baseEnd_2442764 := by
    simpa [prefixWord, tailWord_2442764, baseEnd_2442764] using wordTrace_append hprefix tailTrace_2442764
  have hstable : (prefixWord ++ tailWord_2442764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442764).length < 2 ^ (prefixWord ++ tailWord_2442764).sum := by decide
  have hdescent : baseEnd_2442764 < baseStart_2442764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442784 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2442784 : Nat := 118140960795 + 2442784 * 2 ^ 59
def prefixEnd_2442784 : Nat := 4983230072969 + 3 ^ 40 * 2442784 * 2
def baseEnd_2442784 : Nat := 1254322327112675830065847

theorem tailTrace_2442784 : CollatzResearch.WordTrace tailWord_2442784 prefixEnd_2442784 1254322327112675830065847 := by
  unfold tailWord_2442784
  simp only [CollatzResearch.WordTrace]
  refine ⟨44547825991109118568887703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59397101321478824758516937 44547825991109118568887703)
  ·
    refine ⟨66821738986663677853331555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44547825991109118568887703 66821738986663677853331555)
    ·
      refine ⟨100232608479995516779997333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66821738986663677853331555 100232608479995516779997333)
      ·
        refine ⟨4698403522499789849062375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100232608479995516779997333 4698403522499789849062375)
        ·
          refine ⟨7047605283749684773593563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4698403522499789849062375 7047605283749684773593563)
          ·
            refine ⟨10571407925624527160390345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047605283749684773593563 10571407925624527160390345)
            ·
              refine ⟨7928555944218395370292759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10571407925624527160390345 7928555944218395370292759)
              ·
                refine ⟨11892833916327593055439139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928555944218395370292759 11892833916327593055439139)
                ·
                  refine ⟨17839250874491389583158709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11892833916327593055439139 17839250874491389583158709)
                  ·
                    refine ⟨1672429769483567773421129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17839250874491389583158709 1672429769483567773421129)
                    ·
                      refine ⟨1254322327112675830065847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672429769483567773421129 1254322327112675830065847)
                      ·
                        rfl

theorem cell23_2442784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2442784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442784 prefixEnd_2442784 := by exact prefixLift 2442784
  have htrace : WordTrace (prefixWord ++ tailWord_2442784) baseStart_2442784 baseEnd_2442784 := by
    simpa [prefixWord, tailWord_2442784, baseEnd_2442784] using wordTrace_append hprefix tailTrace_2442784
  have hstable : (prefixWord ++ tailWord_2442784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442784).length < 2 ^ (prefixWord ++ tailWord_2442784).sum := by decide
  have hdescent : baseEnd_2442784 < baseStart_2442784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442807 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 4, 4]
def baseStart_2442807 : Nat := 118140960795 + 2442807 * 2 ^ 59
def prefixEnd_2442807 : Nat := 4983230072969 + 3 ^ 40 * 2442807 * 2
def baseEnd_2442807 : Nat := 418111379055909746692747

theorem tailTrace_2442807 : CollatzResearch.WordTrace tailWord_2442807 prefixEnd_2442807 418111379055909746692747 := by
  unfold tailWord_2442807
  simp only [CollatzResearch.WordTrace]
  refine ⟨89096490861134912065862675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59397660574089941377241783 89096490861134912065862675)
  ·
    refine ⟨133644736291702368098794013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89096490861134912065862675 133644736291702368098794013)
    ·
      refine ⟨50116776109388388037047755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133644736291702368098794013 50116776109388388037047755)
      ·
        refine ⟨75175164164082582055571633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50116776109388388037047755 75175164164082582055571633)
        ·
          refine ⟨56381373123061936541678725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75175164164082582055571633 56381373123061936541678725)
          ·
            refine ⟨10571507460574113101564761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56381373123061936541678725 10571507460574113101564761)
            ·
              refine ⟨7928630595430584826173571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10571507460574113101564761 7928630595430584826173571)
              ·
                refine ⟨11892945893145877239260357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928630595430584826173571 11892945893145877239260357)
                ·
                  refine ⟨2229927354964851982361317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11892945893145877239260357 2229927354964851982361317)
                  ·
                    refine ⟨418111379055909746692747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2229927354964851982361317 418111379055909746692747)
                    ·
                      rfl

theorem cell23_2442807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_2442807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442807 prefixEnd_2442807 := by exact prefixLift 2442807
  have htrace : WordTrace (prefixWord ++ tailWord_2442807) baseStart_2442807 baseEnd_2442807 := by
    simpa [prefixWord, tailWord_2442807, baseEnd_2442807] using wordTrace_append hprefix tailTrace_2442807
  have hstable : (prefixWord ++ tailWord_2442807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442807).length < 2 ^ (prefixWord ++ tailWord_2442807).sum := by decide
  have hdescent : baseEnd_2442807 < baseStart_2442807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442808 : List Nat := [2, 1, 2, 1, 4, 3, 3, 2, 1, 1, 3]
def baseStart_2442808 : Nat := 118140960795 + 2442808 * 2 ^ 59
def prefixEnd_2442808 : Nat := 4983230072969 + 3 ^ 40 * 2442808 * 2
def baseEnd_2442808 : Nat := 1254334650648383736165737

theorem tailTrace_2442808 : CollatzResearch.WordTrace tailWord_2442808 prefixEnd_2442808 1254334650648383736165737 := by
  unfold tailWord_2442808
  simp only [CollatzResearch.WordTrace]
  refine ⟨44548263667065644618324539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59397684889420859491099385 44548263667065644618324539)
  ·
    refine ⟨66822395500598466927486809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44548263667065644618324539 66822395500598466927486809)
    ·
      refine ⟨50116796625448850195615107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66822395500598466927486809 50116796625448850195615107)
      ·
        refine ⟨75175194938173275293422661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50116796625448850195615107 75175194938173275293422661)
        ·
          refine ⟨14095349050907489117516749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75175194938173275293422661 14095349050907489117516749)
          ·
            refine ⟨5285755894090308419068781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14095349050907489117516749 5285755894090308419068781)
            ·
              refine ⟨1982158460283865657150793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5285755894090308419068781 1982158460283865657150793)
              ·
                refine ⟨1486618845212899242863095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982158460283865657150793 1486618845212899242863095)
                ·
                  refine ⟨2229928267819348864294643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486618845212899242863095 2229928267819348864294643)
                  ·
                    refine ⟨3344892401729023296441965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2229928267819348864294643 3344892401729023296441965)
                    ·
                      refine ⟨1254334650648383736165737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344892401729023296441965 1254334650648383736165737)
                      ·
                        rfl

theorem cell23_2442808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_2442808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442808 prefixEnd_2442808 := by exact prefixLift 2442808
  have htrace : WordTrace (prefixWord ++ tailWord_2442808) baseStart_2442808 baseEnd_2442808 := by
    simpa [prefixWord, tailWord_2442808, baseEnd_2442808] using wordTrace_append hprefix tailTrace_2442808
  have hstable : (prefixWord ++ tailWord_2442808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442808).length < 2 ^ (prefixWord ++ tailWord_2442808).sum := by decide
  have hdescent : baseEnd_2442808 < baseStart_2442808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442810 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_2442810 : Nat := 118140960795 + 2442810 * 2 ^ 59
def prefixEnd_2442810 : Nat := 4983230072969 + 3 ^ 40 * 2442810 * 2
def baseEnd_2442810 : Nat := 1254335677609692728340727

theorem tailTrace_2442810 : CollatzResearch.WordTrace tailWord_2442810 prefixEnd_2442810 1254335677609692728340727 := by
  unfold tailWord_2442810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22274150070031010894555471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59397733520082695718814589 22274150070031010894555471)
  ·
    refine ⟨33411225105046516341833207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22274150070031010894555471 33411225105046516341833207)
    ·
      refine ⟨50116837657569774512749811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33411225105046516341833207 50116837657569774512749811)
      ·
        refine ⟨75175256486354661769124717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50116837657569774512749811 75175256486354661769124717)
        ·
          refine ⟨28190721182382998163421769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75175256486354661769124717 28190721182382998163421769)
          ·
            refine ⟨21143040886787248622566327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28190721182382998163421769 21143040886787248622566327)
            ·
              refine ⟨31714561330180872933849491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21143040886787248622566327 31714561330180872933849491)
              ·
                refine ⟨47571841995271309400774237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31714561330180872933849491 47571841995271309400774237)
                ·
                  refine ⟨17839440748226741025290339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47571841995271309400774237 17839440748226741025290339)
                  ·
                    refine ⟨26759161122340111537935509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17839440748226741025290339 26759161122340111537935509)
                    ·
                      refine ⟨1254335677609692728340727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26759161122340111537935509 1254335677609692728340727)
                      ·
                        rfl

theorem cell23_2442810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_2442810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442810 prefixEnd_2442810 := by exact prefixLift 2442810
  have htrace : WordTrace (prefixWord ++ tailWord_2442810) baseStart_2442810 baseEnd_2442810 := by
    simpa [prefixWord, tailWord_2442810, baseEnd_2442810] using wordTrace_append hprefix tailTrace_2442810
  have hstable : (prefixWord ++ tailWord_2442810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442810).length < 2 ^ (prefixWord ++ tailWord_2442810).sum := by decide
  have hdescent : baseEnd_2442810 < baseStart_2442810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442817 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2442817 : Nat := 118140960795 + 2442817 * 2 ^ 59
def prefixEnd_2442817 : Nat := 4983230072969 + 3 ^ 40 * 2442817 * 2
def baseEnd_2442817 : Nat := 1254339271974274200953195

theorem tailTrace_2442817 : CollatzResearch.WordTrace tailWord_2442817 prefixEnd_2442817 1254339271974274200953195 := by
  unfold tailWord_2442817
  simp only [CollatzResearch.WordTrace]
  refine ⟨89096855591098683773726705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59397903727399122515817803 89096855591098683773726705)
  ·
    refine ⟨66822641693324012830295029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89096855591098683773726705 66822641693324012830295029)
    ·
      refine ⟨6264622658749126202840159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66822641693324012830295029 6264622658749126202840159)
      ·
        refine ⟨9396933988123689304260239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264622658749126202840159 9396933988123689304260239)
        ·
          refine ⟨14095400982185533956390359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396933988123689304260239 14095400982185533956390359)
          ·
            refine ⟨21143101473278300934585539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14095400982185533956390359 21143101473278300934585539)
            ·
              refine ⟨31714652209917451401878309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21143101473278300934585539 31714652209917451401878309)
              ·
                refine ⟨5946497289359522137852183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31714652209917451401878309 5946497289359522137852183)
                ·
                  refine ⟨8919745934039283206778275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5946497289359522137852183 8919745934039283206778275)
                  ·
                    refine ⟨13379618901058924810167413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8919745934039283206778275 13379618901058924810167413)
                    ·
                      refine ⟨1254339271974274200953195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13379618901058924810167413 1254339271974274200953195)
                      ·
                        rfl

theorem cell23_2442817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2442817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442817 prefixEnd_2442817 := by exact prefixLift 2442817
  have htrace : WordTrace (prefixWord ++ tailWord_2442817) baseStart_2442817 baseEnd_2442817 := by
    simpa [prefixWord, tailWord_2442817, baseEnd_2442817] using wordTrace_append hprefix tailTrace_2442817
  have hstable : (prefixWord ++ tailWord_2442817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442817).length < 2 ^ (prefixWord ++ tailWord_2442817).sum := by decide
  have hdescent : baseEnd_2442817 < baseStart_2442817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442834 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_2442834 : Nat := 118140960795 + 2442834 * 2 ^ 59
def prefixEnd_2442834 : Nat := 4983230072969 + 3 ^ 40 * 2442834 * 2
def baseEnd_2442834 : Nat := 1254348001145400634440617

theorem tailTrace_2442834 : CollatzResearch.WordTrace tailWord_2442834 prefixEnd_2442834 1254348001145400634440617 := by
  unfold tailWord_2442834
  simp only [CollatzResearch.WordTrace]
  refine ⟨22274368908009273919273889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59398317088024730451397037 22274368908009273919273889)
  ·
    refine ⟨16705776681006955439455417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22274368908009273919273889 16705776681006955439455417)
    ·
      refine ⟨12529332510755216579591563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16705776681006955439455417 12529332510755216579591563)
      ·
        refine ⟨18793998766132824869387345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12529332510755216579591563 18793998766132824869387345)
        ·
          refine ⟨14095499074599618652040509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18793998766132824869387345 14095499074599618652040509)
          ·
            refine ⟨5285812152974856994515191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14095499074599618652040509 5285812152974856994515191)
            ·
              refine ⟨7928718229462285491772787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285812152974856994515191 7928718229462285491772787)
              ·
                refine ⟨11893077344193428237659181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7928718229462285491772787 11893077344193428237659181)
                ·
                  refine ⟨4459904004072535589122193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11893077344193428237659181 4459904004072535589122193)
                  ·
                    refine ⟨3344928003054401691841645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4459904004072535589122193 3344928003054401691841645)
                    ·
                      refine ⟨1254348001145400634440617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344928003054401691841645 1254348001145400634440617)
                      ·
                        rfl

theorem cell23_2442834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_2442834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442834 prefixEnd_2442834 := by exact prefixLift 2442834
  have htrace : WordTrace (prefixWord ++ tailWord_2442834) baseStart_2442834 baseEnd_2442834 := by
    simpa [prefixWord, tailWord_2442834, baseEnd_2442834] using wordTrace_append hprefix tailTrace_2442834
  have hstable : (prefixWord ++ tailWord_2442834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442834).length < 2 ^ (prefixWord ++ tailWord_2442834).sum := by decide
  have hdescent : baseEnd_2442834 < baseStart_2442834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442844 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2442844 : Nat := 118140960795 + 2442844 * 2 ^ 59
def prefixEnd_2442844 : Nat := 4983230072969 + 3 ^ 40 * 2442844 * 2
def baseEnd_2442844 : Nat := 1254353135951945595315571

theorem tailTrace_2442844 : CollatzResearch.WordTrace tailWord_2442844 prefixEnd_2442844 1254353135951945595315571 := by
  unfold tailWord_2442844
  simp only [CollatzResearch.WordTrace]
  refine ⟨44548920181000433692479793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59398560241333911589973057 44548920181000433692479793)
  ·
    refine ⟨33411690135750325269359845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44548920181000433692479793 33411690135750325269359845)
    ·
      refine ⟨6264691900453185988004971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33411690135750325269359845 6264691900453185988004971)
      ·
        refine ⟨9397037850679778982007457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264691900453185988004971 9397037850679778982007457)
        ·
          refine ⟨7047778388009834236505593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9397037850679778982007457 7047778388009834236505593)
          ·
            refine ⟨5285833791007375677379195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7047778388009834236505593 5285833791007375677379195)
            ·
              refine ⟨7928750686511063516068793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285833791007375677379195 7928750686511063516068793)
              ·
                refine ⟨5946563014883297637051595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7928750686511063516068793 5946563014883297637051595)
                ·
                  refine ⟨8919844522324946455577393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5946563014883297637051595 8919844522324946455577393)
                  ·
                    refine ⟨6689883391743709841683045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8919844522324946455577393 6689883391743709841683045)
                    ·
                      refine ⟨1254353135951945595315571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6689883391743709841683045 1254353135951945595315571)
                      ·
                        rfl

theorem cell23_2442844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2442844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442844 prefixEnd_2442844 := by exact prefixLift 2442844
  have htrace : WordTrace (prefixWord ++ tailWord_2442844) baseStart_2442844 baseEnd_2442844 := by
    simpa [prefixWord, tailWord_2442844, baseEnd_2442844] using wordTrace_append hprefix tailTrace_2442844
  have hstable : (prefixWord ++ tailWord_2442844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442844).length < 2 ^ (prefixWord ++ tailWord_2442844).sum := by decide
  have hdescent : baseEnd_2442844 < baseStart_2442844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442851 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 1, 2, 3]
def baseStart_2442851 : Nat := 118140960795 + 2442851 * 2 ^ 59
def prefixEnd_2442851 : Nat := 4983230072969 + 3 ^ 40 * 2442851 * 2
def baseEnd_2442851 : Nat := 1254356730316527067928039

theorem tailTrace_2442851 : CollatzResearch.WordTrace tailWord_2442851 prefixEnd_2442851 1254356730316527067928039 := by
  unfold tailWord_2442851
  simp only [CollatzResearch.WordTrace]
  refine ⟨89098095672975507580464407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59398730448650338386976271 89098095672975507580464407)
  ·
    refine ⟨133647143509463261370696611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89098095672975507580464407 133647143509463261370696611)
    ·
      refine ⟨200470715264194892056044917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133647143509463261370696611 200470715264194892056044917)
      ·
        refine ⟨18794129556018271130254211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200470715264194892056044917 18794129556018271130254211)
        ·
          refine ⟨28191194334027406695381317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18794129556018271130254211 28191194334027406695381317)
          ·
            refine ⟨5285848937630138755383997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28191194334027406695381317 5285848937630138755383997)
            ·
              refine ⟨1982193351611302033268999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5285848937630138755383997 1982193351611302033268999)
              ·
                refine ⟨2973290027416953049903499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982193351611302033268999 2973290027416953049903499)
                ·
                  refine ⟨4459935041125429574855249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2973290027416953049903499 4459935041125429574855249)
                  ·
                    refine ⟨3344951280844072181141437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4459935041125429574855249 3344951280844072181141437)
                    ·
                      refine ⟨1254356730316527067928039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344951280844072181141437 1254356730316527067928039)
                      ·
                        rfl

theorem cell23_2442851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_2442851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442851 prefixEnd_2442851 := by exact prefixLift 2442851
  have htrace : WordTrace (prefixWord ++ tailWord_2442851) baseStart_2442851 baseEnd_2442851 := by
    simpa [prefixWord, tailWord_2442851, baseEnd_2442851] using wordTrace_append hprefix tailTrace_2442851
  have hstable : (prefixWord ++ tailWord_2442851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442851).length < 2 ^ (prefixWord ++ tailWord_2442851).sum := by decide
  have hdescent : baseEnd_2442851 < baseStart_2442851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442881 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2442881 : Nat := 118140960795 + 2442881 * 2 ^ 59
def prefixEnd_2442881 : Nat := 4983230072969 + 3 ^ 40 * 2442881 * 2
def baseEnd_2442881 : Nat := 1254372134736161950552901

theorem tailTrace_2442881 : CollatzResearch.WordTrace tailWord_2442881 prefixEnd_2442881 1254372134736161950552901 := by
  unfold tailWord_2442881
  simp only [CollatzResearch.WordTrace]
  refine ⟨89099189862866822704056497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59399459908577881802704331 89099189862866822704056497)
  ·
    refine ⟨66824392397150117028042373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89099189862866822704056497 66824392397150117028042373)
    ·
      refine ⟨12529573574465646942757945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66824392397150117028042373 12529573574465646942757945)
      ·
        refine ⟨9397180180849235207068459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12529573574465646942757945 9397180180849235207068459)
        ·
          refine ⟨14095770271273852810602689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9397180180849235207068459 14095770271273852810602689)
          ·
            refine ⟨10571827703455389607952017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14095770271273852810602689 10571827703455389607952017)
            ·
              refine ⟨7928870777591542205964013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10571827703455389607952017 7928870777591542205964013)
              ·
                refine ⟨2973326541596828327236505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7928870777591542205964013 2973326541596828327236505)
                ·
                  refine ⟨2229994906197621245427379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2973326541596828327236505 2229994906197621245427379)
                  ·
                    refine ⟨3344992359296431868141069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2229994906197621245427379 3344992359296431868141069)
                    ·
                      refine ⟨1254372134736161950552901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3344992359296431868141069 1254372134736161950552901)
                      ·
                        rfl

theorem cell23_2442881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2442881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442881 prefixEnd_2442881 := by exact prefixLift 2442881
  have htrace : WordTrace (prefixWord ++ tailWord_2442881) baseStart_2442881 baseEnd_2442881 := by
    simpa [prefixWord, tailWord_2442881, baseEnd_2442881] using wordTrace_append hprefix tailTrace_2442881
  have hstable : (prefixWord ++ tailWord_2442881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442881).length < 2 ^ (prefixWord ++ tailWord_2442881).sum := by decide
  have hdescent : baseEnd_2442881 < baseStart_2442881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442908 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2442908 : Nat := 118140960795 + 2442908 * 2 ^ 59
def prefixEnd_2442908 : Nat := 4983230072969 + 3 ^ 40 * 2442908 * 2
def baseEnd_2442908 : Nat := 1254385998713833344915277

theorem tailTrace_2442908 : CollatzResearch.WordTrace tailWord_2442908 prefixEnd_2442908 1254385998713833344915277 := by
  unfold tailWord_2442908
  simp only [CollatzResearch.WordTrace]
  refine ⟨44550087316884503157644689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59400116422512670876859585 44550087316884503157644689)
  ·
    refine ⟨33412565487663377368233517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44550087316884503157644689 33412565487663377368233517)
    ·
      refine ⟨12529712057873766513087569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33412565487663377368233517 12529712057873766513087569)
      ·
        refine ⟨9397284043405324884815677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12529712057873766513087569 9397284043405324884815677)
        ·
          refine ⟨3523981516276996831805879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9397284043405324884815677 3523981516276996831805879)
          ·
            refine ⟨5285972274415495247708819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523981516276996831805879 5285972274415495247708819)
            ·
              refine ⟨7928958411623242871563229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5285972274415495247708819 7928958411623242871563229)
              ·
                refine ⟨2973359404358716076836211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7928958411623242871563229 2973359404358716076836211)
                ·
                  refine ⟨4460039106538074115254317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2973359404358716076836211 4460039106538074115254317)
                  ·
                    refine ⟨1672514664951777793220369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4460039106538074115254317 1672514664951777793220369)
                    ·
                      refine ⟨1254385998713833344915277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672514664951777793220369 1254385998713833344915277)
                      ·
                        rfl

theorem cell23_2442908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2442908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442908 prefixEnd_2442908 := by exact prefixLift 2442908
  have htrace : WordTrace (prefixWord ++ tailWord_2442908) baseStart_2442908 baseEnd_2442908 := by
    simpa [prefixWord, tailWord_2442908, baseEnd_2442908] using wordTrace_append hprefix tailTrace_2442908
  have hstable : (prefixWord ++ tailWord_2442908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442908).length < 2 ^ (prefixWord ++ tailWord_2442908).sum := by decide
  have hdescent : baseEnd_2442908 < baseStart_2442908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442917 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_2442917 : Nat := 118140960795 + 2442917 * 2 ^ 59
def prefixEnd_2442917 : Nat := 4983230072969 + 3 ^ 40 * 2442917 * 2
def baseEnd_2442917 : Nat := 1254390620039723809702735

theorem tailTrace_2442917 : CollatzResearch.WordTrace tailWord_2442917 prefixEnd_2442917 1254390620039723809702735 := by
  unfold tailWord_2442917
  simp only [CollatzResearch.WordTrace]
  refine ⟨89100502890736400852367005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59400335260490933901578003 89100502890736400852367005)
  ·
    refine ⟨33412688584026150319637627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89100502890736400852367005 33412688584026150319637627)
    ·
      refine ⟨50119032876039225479456441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33412688584026150319637627 50119032876039225479456441)
      ·
        refine ⟨37589274657029419109592331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50119032876039225479456441 37589274657029419109592331)
        ·
          refine ⟨56383911985544128664388497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37589274657029419109592331 56383911985544128664388497)
          ·
            refine ⟨42287933989158096498291373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56383911985544128664388497 42287933989158096498291373)
            ·
              refine ⟨15857975245934286186859265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42287933989158096498291373 15857975245934286186859265)
              ·
                refine ⟨11893481434450714640144449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15857975245934286186859265 11893481434450714640144449)
                ·
                  refine ⟨8920111075838035980108337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11893481434450714640144449 8920111075838035980108337)
                  ·
                    refine ⟨6690083306878526985081253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8920111075838035980108337 6690083306878526985081253)
                    ·
                      refine ⟨1254390620039723809702735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6690083306878526985081253 1254390620039723809702735)
                      ·
                        rfl

theorem cell23_2442917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_2442917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442917 prefixEnd_2442917 := by exact prefixLift 2442917
  have htrace : WordTrace (prefixWord ++ tailWord_2442917) baseStart_2442917 baseEnd_2442917 := by
    simpa [prefixWord, tailWord_2442917, baseEnd_2442917] using wordTrace_append hprefix tailTrace_2442917
  have hstable : (prefixWord ++ tailWord_2442917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442917).length < 2 ^ (prefixWord ++ tailWord_2442917).sum := by decide
  have hdescent : baseEnd_2442917 < baseStart_2442917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442927 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 7]
def baseStart_2442927 : Nat := 118140960795 + 2442927 * 2 ^ 59
def prefixEnd_2442927 : Nat := 4983230072969 + 3 ^ 40 * 2442927 * 2
def baseEnd_2442927 : Nat := 139377306094029863397521

theorem tailTrace_2442927 : CollatzResearch.WordTrace tailWord_2442927 prefixEnd_2442927 139377306094029863397521 := by
  unfold tailWord_2442927
  simp only [CollatzResearch.WordTrace]
  refine ⟨89100867620700172560231035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59400578413800115040154023 89100867620700172560231035)
  ·
    refine ⟨133651301431050258840346553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89100867620700172560231035 133651301431050258840346553)
    ·
      refine ⟨100238476073287694130259915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133651301431050258840346553 100238476073287694130259915)
      ·
        refine ⟨150357714109931541195389873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100238476073287694130259915 150357714109931541195389873)
        ·
          refine ⟨112768285582448655896542405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150357714109931541195389873 112768285582448655896542405)
          ·
            refine ⟨21144053546709122980601701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112768285582448655896542405 21144053546709122980601701)
            ·
              refine ⟨3964510040007960558862819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21144053546709122980601701 3964510040007960558862819)
              ·
                refine ⟨5946765060011940838294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964510040007960558862819 5946765060011940838294229)
                ·
                  refine ⟨139377306094029863397521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5946765060011940838294229 139377306094029863397521)
                  ·
                    rfl

theorem cell23_2442927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 7].length) (baseStart_2442927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442927 prefixEnd_2442927 := by exact prefixLift 2442927
  have htrace : WordTrace (prefixWord ++ tailWord_2442927) baseStart_2442927 baseEnd_2442927 := by
    simpa [prefixWord, tailWord_2442927, baseEnd_2442927] using wordTrace_append hprefix tailTrace_2442927
  have hstable : (prefixWord ++ tailWord_2442927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442927).length < 2 ^ (prefixWord ++ tailWord_2442927).sum := by decide
  have hdescent : baseEnd_2442927 < baseStart_2442927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442961 : List Nat := [1, 2, 2, 1, 2, 6, 1, 3, 5]
def baseStart_2442961 : Nat := 118140960795 + 2442961 * 2 ^ 59
def prefixEnd_2442961 : Nat := 4983230072969 + 3 ^ 40 * 2442961 * 2
def baseEnd_2442961 : Nat := 139379245909835737505837

theorem tailTrace_2442961 : CollatzResearch.WordTrace tailWord_2442961 prefixEnd_2442961 139379245909835737505837 := by
  unfold tailWord_2442961
  simp only [CollatzResearch.WordTrace]
  refine ⟨89102107702576996366968737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59401405135051330911312491 89102107702576996366968737)
  ·
    refine ⟨66826580776932747275226553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89102107702576996366968737 66826580776932747275226553)
    ·
      refine ⟨50119935582699560456419915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66826580776932747275226553 50119935582699560456419915)
      ·
        refine ⟨75179903374049340684629873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50119935582699560456419915 75179903374049340684629873)
        ·
          refine ⟨56384927530537005513472405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75179903374049340684629873 56384927530537005513472405)
          ·
            refine ⟨2643043477993922133444019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56384927530537005513472405 2643043477993922133444019)
            ·
              refine ⟨3964565216990883200166029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643043477993922133444019 3964565216990883200166029)
              ·
                refine ⟨1486711956371581200062261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3964565216990883200166029 1486711956371581200062261)
                ·
                  refine ⟨139379245909835737505837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1486711956371581200062261 139379245909835737505837)
                  ·
                    rfl

theorem cell23_2442961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 5].length) (baseStart_2442961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442961 prefixEnd_2442961 := by exact prefixLift 2442961
  have htrace : WordTrace (prefixWord ++ tailWord_2442961) baseStart_2442961 baseEnd_2442961 := by
    simpa [prefixWord, tailWord_2442961, baseEnd_2442961] using wordTrace_append hprefix tailTrace_2442961
  have hstable : (prefixWord ++ tailWord_2442961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442961).length < 2 ^ (prefixWord ++ tailWord_2442961).sum := by decide
  have hdescent : baseEnd_2442961 < baseStart_2442961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442967 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2442967 : Nat := 118140960795 + 2442967 * 2 ^ 59
def prefixEnd_2442967 : Nat := 4983230072969 + 3 ^ 40 * 2442967 * 2
def baseEnd_2442967 : Nat := 1254416294072448614077505

theorem tailTrace_2442967 : CollatzResearch.WordTrace tailWord_2442967 prefixEnd_2442967 1254416294072448614077505 := by
  unfold tailWord_2442967
  simp only [CollatzResearch.WordTrace]
  refine ⟨89102326540555259391687155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59401551027036839594458103 89102326540555259391687155)
  ·
    refine ⟨133653489810832889087530733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89102326540555259391687155 133653489810832889087530733)
    ·
      refine ⟨50120058679062333407824025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133653489810832889087530733 50120058679062333407824025)
      ·
        refine ⟨37590044009296750055868019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50120058679062333407824025 37590044009296750055868019)
        ·
          refine ⟨56385066013945125083802029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37590044009296750055868019 56385066013945125083802029)
          ·
            refine ⟨21144399755229421906425761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56385066013945125083802029 21144399755229421906425761)
            ·
              refine ⟨15858299816422066429819321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21144399755229421906425761 15858299816422066429819321)
              ·
                refine ⟨11893724862316549822364491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15858299816422066429819321 11893724862316549822364491)
                ·
                  refine ⟨17840587293474824733546737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11893724862316549822364491 17840587293474824733546737)
                  ·
                    refine ⟨13380440470106118550160053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17840587293474824733546737 13380440470106118550160053)
                    ·
                      refine ⟨1254416294072448614077505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13380440470106118550160053 1254416294072448614077505)
                      ·
                        rfl

theorem cell23_2442967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2442967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442967 prefixEnd_2442967 := by exact prefixLift 2442967
  have htrace : WordTrace (prefixWord ++ tailWord_2442967) baseStart_2442967 baseEnd_2442967 := by
    simpa [prefixWord, tailWord_2442967, baseEnd_2442967] using wordTrace_append hprefix tailTrace_2442967
  have hstable : (prefixWord ++ tailWord_2442967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442967).length < 2 ^ (prefixWord ++ tailWord_2442967).sum := by decide
  have hdescent : baseEnd_2442967 < baseStart_2442967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442984 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2442984 : Nat := 118140960795 + 2442984 * 2 ^ 59
def prefixEnd_2442984 : Nat := 4983230072969 + 3 ^ 40 * 2442984 * 2
def baseEnd_2442984 : Nat := 1254425023243575047564927

theorem tailTrace_2442984 : CollatzResearch.WordTrace tailWord_2442984 prefixEnd_2442984 1254425023243575047564927 := by
  unfold tailWord_2442984
  simp only [CollatzResearch.WordTrace]
  refine ⟨44551473290746835647528003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59401964387662447530037337 44551473290746835647528003)
  ·
    refine ⟨66827209936120253471292005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44551473290746835647528003 66827209936120253471292005)
    ·
      refine ⟨12530101863022547525867251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66827209936120253471292005 12530101863022547525867251)
      ·
        refine ⟨18795152794533821288800877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12530101863022547525867251 18795152794533821288800877)
        ·
          refine ⟨7048182297950182983300329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18795152794533821288800877 7048182297950182983300329)
          ·
            refine ⟨5286136723462637237475247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7048182297950182983300329 5286136723462637237475247)
            ·
              refine ⟨7929205085193955856212871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286136723462637237475247 7929205085193955856212871)
              ·
                refine ⟨11893807627790933784319307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7929205085193955856212871 11893807627790933784319307)
                ·
                  refine ⟨17840711441686400676478961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11893807627790933784319307 17840711441686400676478961)
                  ·
                    refine ⟨13380533581264800507359221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17840711441686400676478961 13380533581264800507359221)
                    ·
                      refine ⟨1254425023243575047564927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13380533581264800507359221 1254425023243575047564927)
                      ·
                        rfl

theorem cell23_2442984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2442984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442984 prefixEnd_2442984 := by exact prefixLift 2442984
  have htrace : WordTrace (prefixWord ++ tailWord_2442984) baseStart_2442984 baseEnd_2442984 := by
    simpa [prefixWord, tailWord_2442984, baseEnd_2442984] using wordTrace_append hprefix tailTrace_2442984
  have hstable : (prefixWord ++ tailWord_2442984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442984).length < 2 ^ (prefixWord ++ tailWord_2442984).sum := by decide
  have hdescent : baseEnd_2442984 < baseStart_2442984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442994 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2442994 : Nat := 118140960795 + 2442994 * 2 ^ 59
def prefixEnd_2442994 : Nat := 4983230072969 + 3 ^ 40 * 2442994 * 2
def baseEnd_2442994 : Nat := 1254430158050120008439881

theorem tailTrace_2442994 : CollatzResearch.WordTrace tailWord_2442994 prefixEnd_2442994 1254430158050120008439881 := by
  unfold tailWord_2442994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22275827827864360750730009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59402207540971628668613357 22275827827864360750730009)
  ·
    refine ⟨16706870870898270563047507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22275827827864360750730009 16706870870898270563047507)
    ·
      refine ⟨25060306306347405844571261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16706870870898270563047507 25060306306347405844571261)
      ·
        refine ⟨9397614864880277191714223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25060306306347405844571261 9397614864880277191714223)
        ·
          refine ⟨14096422297320415787571335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9397614864880277191714223 14096422297320415787571335)
          ·
            refine ⟨21144633445980623681357003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14096422297320415787571335 21144633445980623681357003)
            ·
              refine ⟨31716950168970935522035505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21144633445980623681357003 31716950168970935522035505)
              ·
                refine ⟨23787712626728201641526629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31716950168970935522035505 23787712626728201641526629)
                ·
                  refine ⟨4460196117511537807786243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23787712626728201641526629 4460196117511537807786243)
                  ·
                    refine ⟨6690294176267306711679365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4460196117511537807786243 6690294176267306711679365)
                    ·
                      refine ⟨1254430158050120008439881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6690294176267306711679365 1254430158050120008439881)
                      ·
                        rfl

theorem cell23_2442994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2442994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2442994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2442994 prefixEnd_2442994 := by exact prefixLift 2442994
  have htrace : WordTrace (prefixWord ++ tailWord_2442994) baseStart_2442994 baseEnd_2442994 := by
    simpa [prefixWord, tailWord_2442994, baseEnd_2442994] using wordTrace_append hprefix tailTrace_2442994
  have hstable : (prefixWord ++ tailWord_2442994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442994).length < 2 ^ (prefixWord ++ tailWord_2442994).sum := by decide
  have hdescent : baseEnd_2442994 < baseStart_2442994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443004 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_2443004 : Nat := 118140960795 + 2443004 * 2 ^ 59
def prefixEnd_2443004 : Nat := 4983230072969 + 3 ^ 40 * 2443004 * 2
def baseEnd_2443004 : Nat := 418145097618888323104945

theorem tailTrace_2443004 : CollatzResearch.WordTrace tailWord_2443004 prefixEnd_2443004 418145097618888323104945 := by
  unfold tailWord_2443004
  simp only [CollatzResearch.WordTrace]
  refine ⟨44551838020710607355392033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59402450694280809807189377 44551838020710607355392033)
  ·
    refine ⟨33413878515532955516544025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44551838020710607355392033 33413878515532955516544025)
    ·
      refine ⟨25060408886649716637408019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33413878515532955516544025 25060408886649716637408019)
      ·
        refine ⟨37590613329974574956112029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25060408886649716637408019 37590613329974574956112029)
        ·
          refine ⟨14096479998740465608542011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37590613329974574956112029 14096479998740465608542011)
          ·
            refine ⟨21144719998110698412813017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14096479998740465608542011 21144719998110698412813017)
            ·
              refine ⟨15858539998583023809609763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21144719998110698412813017 15858539998583023809609763)
              ·
                refine ⟨23787809997874535714414645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15858539998583023809609763 23787809997874535714414645)
                ·
                  refine ⟨2230107187300737723226373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23787809997874535714414645 2230107187300737723226373)
                  ·
                    refine ⟨418145097618888323104945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230107187300737723226373 418145097618888323104945)
                    ·
                      rfl

theorem cell23_2443004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_2443004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443004 prefixEnd_2443004 := by exact prefixLift 2443004
  have htrace : WordTrace (prefixWord ++ tailWord_2443004) baseStart_2443004 baseEnd_2443004 := by
    simpa [prefixWord, tailWord_2443004, baseEnd_2443004] using wordTrace_append hprefix tailTrace_2443004
  have hstable : (prefixWord ++ tailWord_2443004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443004).length < 2 ^ (prefixWord ++ tailWord_2443004).sum := by decide
  have hdescent : baseEnd_2443004 < baseStart_2443004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443007 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_2443007 : Nat := 118140960795 + 2443007 * 2 ^ 59
def prefixEnd_2443007 : Nat := 4983230072969 + 3 ^ 40 * 2443007 * 2
def baseEnd_2443007 : Nat := 1254436833298628457577321

theorem tailTrace_2443007 : CollatzResearch.WordTrace tailWord_2443007 prefixEnd_2443007 1254436833298628457577321 := by
  unfold tailWord_2443007
  simp only [CollatzResearch.WordTrace]
  refine ⟨89103785460410346223143275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59402523640273564148762183 89103785460410346223143275)
  ·
    refine ⟨133655678190615519334714913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89103785460410346223143275 133655678190615519334714913)
    ·
      refine ⟨100241758642961639501036185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133655678190615519334714913 100241758642961639501036185)
      ·
        refine ⟨75181318982221229625777139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100241758642961639501036185 75181318982221229625777139)
        ·
          refine ⟨112771978473331844438665709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75181318982221229625777139 112771978473331844438665709)
          ·
            refine ⟨42289491927499441664499641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112771978473331844438665709 42289491927499441664499641)
            ·
              refine ⟨31717118945624581248374731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42289491927499441664499641 31717118945624581248374731)
              ·
                refine ⟨47575678418436871872562097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31717118945624581248374731 47575678418436871872562097)
                ·
                  refine ⟨35681758813827653904421573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47575678418436871872562097 35681758813827653904421573)
                  ·
                    refine ⟨6690329777592685107079045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35681758813827653904421573 6690329777592685107079045)
                    ·
                      refine ⟨1254436833298628457577321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6690329777592685107079045 1254436833298628457577321)
                      ·
                        rfl

theorem cell23_2443007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_2443007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443007 prefixEnd_2443007 := by exact prefixLift 2443007
  have htrace : WordTrace (prefixWord ++ tailWord_2443007) baseStart_2443007 baseEnd_2443007 := by
    simpa [prefixWord, tailWord_2443007, baseEnd_2443007] using wordTrace_append hprefix tailTrace_2443007
  have hstable : (prefixWord ++ tailWord_2443007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443007).length < 2 ^ (prefixWord ++ tailWord_2443007).sum := by decide
  have hdescent : baseEnd_2443007 < baseStart_2443007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443031 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2443031 : Nat := 118140960795 + 2443031 * 2 ^ 59
def prefixEnd_2443031 : Nat := 4983230072969 + 3 ^ 40 * 2443031 * 2
def baseEnd_2443031 : Nat := 1254449156834336363677211

theorem tailTrace_2443031 : CollatzResearch.WordTrace tailWord_2443031 prefixEnd_2443031 1254449156834336363677211 := by
  unfold tailWord_2443031
  simp only [CollatzResearch.WordTrace]
  refine ⟨89104660812323398322016947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59403107208215598881344631 89104660812323398322016947)
  ·
    refine ⟨133656991218485097483025421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89104660812323398322016947 133656991218485097483025421)
    ·
      refine ⟨50121371706931911556134533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133656991218485097483025421 50121371706931911556134533)
      ·
        refine ⟨9397757195049733416775225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50121371706931911556134533 9397757195049733416775225)
        ·
          refine ⟨7048317896287300062581419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9397757195049733416775225 7048317896287300062581419)
          ·
            refine ⟨10572476844430950093872129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048317896287300062581419 10572476844430950093872129)
            ·
              refine ⟨7929357633323212570404097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10572476844430950093872129 7929357633323212570404097)
              ·
                refine ⟨5947018224992409427803073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929357633323212570404097 5947018224992409427803073)
                ·
                  refine ⟨4460263668744307070852305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947018224992409427803073 4460263668744307070852305)
                  ·
                    refine ⟨3345197751558230303139229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4460263668744307070852305 3345197751558230303139229)
                    ·
                      refine ⟨1254449156834336363677211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3345197751558230303139229 1254449156834336363677211)
                      ·
                        rfl

theorem cell23_2443031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2443031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443031 prefixEnd_2443031 := by exact prefixLift 2443031
  have htrace : WordTrace (prefixWord ++ tailWord_2443031) baseStart_2443031 baseEnd_2443031 := by
    simpa [prefixWord, tailWord_2443031, baseEnd_2443031] using wordTrace_append hprefix tailTrace_2443031
  have hstable : (prefixWord ++ tailWord_2443031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443031).length < 2 ^ (prefixWord ++ tailWord_2443031).sum := by decide
  have hdescent : baseEnd_2443031 < baseStart_2443031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443034 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 6]
def baseStart_2443034 : Nat := 118140960795 + 2443034 * 2 ^ 59
def prefixEnd_2443034 : Nat := 4983230072969 + 3 ^ 40 * 2443034 * 2
def baseEnd_2443034 : Nat := 139383410808477761326633

theorem tailTrace_2443034 : CollatzResearch.WordTrace tailWord_2443034 prefixEnd_2443034 139383410808477761326633 := by
  unfold tailWord_2443034
  simp only [CollatzResearch.WordTrace]
  refine ⟨22276192557828132458594039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59403180154208353222917437 22276192557828132458594039)
  ·
    refine ⟨33414288836742198687891059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22276192557828132458594039 33414288836742198687891059)
    ·
      refine ⟨50121433255113298031836589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33414288836742198687891059 50121433255113298031836589)
      ·
        refine ⟨18795537470667486761938721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50121433255113298031836589 18795537470667486761938721)
        ·
          refine ⟨14096653103000615071454041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18795537470667486761938721 14096653103000615071454041)
          ·
            refine ⟨10572489827250461303590531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14096653103000615071454041 10572489827250461303590531)
            ·
              refine ⟨15858734740875691955385797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10572489827250461303590531 15858734740875691955385797)
              ·
                refine ⟨2973512763914192241634837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15858734740875691955385797 2973512763914192241634837)
                ·
                  refine ⟨139383410808477761326633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2973512763914192241634837 139383410808477761326633)
                  ·
                    rfl

theorem cell23_2443034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_2443034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443034 prefixEnd_2443034 := by exact prefixLift 2443034
  have htrace : WordTrace (prefixWord ++ tailWord_2443034) baseStart_2443034 baseEnd_2443034 := by
    simpa [prefixWord, tailWord_2443034, baseEnd_2443034] using wordTrace_append hprefix tailTrace_2443034
  have hstable : (prefixWord ++ tailWord_2443034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443034).length < 2 ^ (prefixWord ++ tailWord_2443034).sum := by decide
  have hdescent : baseEnd_2443034 < baseStart_2443034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443064 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 3, 5]
def baseStart_2443064 : Nat := 118140960795 + 2443064 * 2 ^ 59
def prefixEnd_2443064 : Nat := 4983230072969 + 3 ^ 40 * 2443064 * 2
def baseEnd_2443064 : Nat := 418155367231978244854853

theorem tailTrace_2443064 : CollatzResearch.WordTrace tailWord_2443064 prefixEnd_2443064 418155367231978244854853 := by
  unfold tailWord_2443064
  simp only [CollatzResearch.WordTrace]
  refine ⟨44552932210601922478984123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59403909614135896638645497 44552932210601922478984123)
  ·
    refine ⟨66829398315902883718476185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44552932210601922478984123 66829398315902883718476185)
    ·
      refine ⟨50122048736927162788857139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66829398315902883718476185 50122048736927162788857139)
      ·
        refine ⟨75183073105390744183285709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50122048736927162788857139 75183073105390744183285709)
        ·
          refine ⟨28193652414521529068732141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75183073105390744183285709 28193652414521529068732141)
          ·
            refine ⟨10572619655445573400774553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28193652414521529068732141 10572619655445573400774553)
            ·
              refine ⟨7929464741584180050580915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10572619655445573400774553 7929464741584180050580915)
              ·
                refine ⟨11894197112376270075871373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7929464741584180050580915 11894197112376270075871373)
                ·
                  refine ⟨4460323917141101278451765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11894197112376270075871373 4460323917141101278451765)
                  ·
                    refine ⟨418155367231978244854853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4460323917141101278451765 418155367231978244854853)
                    ·
                      rfl

theorem cell23_2443064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_2443064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443064 prefixEnd_2443064 := by exact prefixLift 2443064
  have htrace : WordTrace (prefixWord ++ tailWord_2443064) baseStart_2443064 baseEnd_2443064 := by
    simpa [prefixWord, tailWord_2443064, baseEnd_2443064] using wordTrace_append hprefix tailTrace_2443064
  have hstable : (prefixWord ++ tailWord_2443064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443064).length < 2 ^ (prefixWord ++ tailWord_2443064).sum := by decide
  have hdescent : baseEnd_2443064 < baseStart_2443064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443065 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2443065 : Nat := 118140960795 + 2443065 * 2 ^ 59
def prefixEnd_2443065 : Nat := 4983230072969 + 3 ^ 40 * 2443065 * 2
def baseEnd_2443065 : Nat := 1254466615176589230652055

theorem tailTrace_2443065 : CollatzResearch.WordTrace tailWord_2443065 prefixEnd_2443065 1254466615176589230652055 := by
  unfold tailWord_2443065
  simp only [CollatzResearch.WordTrace]
  refine ⟨89105900894200222128754649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59403933929466814752503099 89105900894200222128754649)
  ·
    refine ⟨66829425670650166596565987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89105900894200222128754649 66829425670650166596565987)
    ·
      refine ⟨100244138505975249894848981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66829425670650166596565987 100244138505975249894848981)
      ·
        refine ⟨2349471996233794919410523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 100244138505975249894848981 2349471996233794919410523)
        ·
          refine ⟨3524207994350692379115785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349471996233794919410523 3524207994350692379115785)
          ·
            refine ⟨2643155995763019284336839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3524207994350692379115785 2643155995763019284336839)
            ·
              refine ⟨3964733993644528926505259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643155995763019284336839 3964733993644528926505259)
              ·
                refine ⟨5947100990466793389757889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964733993644528926505259 5947100990466793389757889)
                ·
                  refine ⟨4460325742850095042318417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947100990466793389757889 4460325742850095042318417)
                  ·
                    refine ⟨3345244307137571281738813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4460325742850095042318417 3345244307137571281738813)
                    ·
                      refine ⟨1254466615176589230652055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3345244307137571281738813 1254466615176589230652055)
                      ·
                        rfl

theorem cell23_2443065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2443065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443065 prefixEnd_2443065 := by exact prefixLift 2443065
  have htrace : WordTrace (prefixWord ++ tailWord_2443065) baseStart_2443065 baseEnd_2443065 := by
    simpa [prefixWord, tailWord_2443065, baseEnd_2443065] using wordTrace_append hprefix tailTrace_2443065
  have hstable : (prefixWord ++ tailWord_2443065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443065).length < 2 ^ (prefixWord ++ tailWord_2443065).sum := by decide
  have hdescent : baseEnd_2443065 < baseStart_2443065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443104 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2443104 : Nat := 118140960795 + 2443104 * 2 ^ 59
def prefixEnd_2443104 : Nat := 4983230072969 + 3 ^ 40 * 2443104 * 2
def baseEnd_2443104 : Nat := 1254486640922114578064375

theorem tailTrace_2443104 : CollatzResearch.WordTrace tailWord_2443104 prefixEnd_2443104 1254486640922114578064375 := by
  unfold tailWord_2443104
  simp only [CollatzResearch.WordTrace]
  refine ⟨44553661670529465894712183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59404882227372621192949577 44553661670529465894712183)
  ·
    refine ⟨66830492505794198842068275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44553661670529465894712183 66830492505794198842068275)
    ·
      refine ⟨100245738758691298263102413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66830492505794198842068275 100245738758691298263102413)
      ·
        refine ⟨37592152034509236848663405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100245738758691298263102413 37592152034509236848663405)
        ·
          refine ⟨14097057012940963818248777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37592152034509236848663405 14097057012940963818248777)
          ·
            refine ⟨10572792759705722863686583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14097057012940963818248777 10572792759705722863686583)
            ·
              refine ⟨15859189139558584295529875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10572792759705722863686583 15859189139558584295529875)
              ·
                refine ⟨23788783709337876443294813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15859189139558584295529875 23788783709337876443294813)
                ·
                  refine ⟨8920793891001703666235555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23788783709337876443294813 8920793891001703666235555)
                  ·
                    refine ⟨13381190836502555499353333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8920793891001703666235555 13381190836502555499353333)
                    ·
                      refine ⟨1254486640922114578064375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13381190836502555499353333 1254486640922114578064375)
                      ·
                        rfl

theorem cell23_2443104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2443104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443104 prefixEnd_2443104 := by exact prefixLift 2443104
  have htrace : WordTrace (prefixWord ++ tailWord_2443104) baseStart_2443104 baseEnd_2443104 := by
    simpa [prefixWord, tailWord_2443104, baseEnd_2443104] using wordTrace_append hprefix tailTrace_2443104
  have hstable : (prefixWord ++ tailWord_2443104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443104).length < 2 ^ (prefixWord ++ tailWord_2443104).sum := by decide
  have hdescent : baseEnd_2443104 < baseStart_2443104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443118 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2443118 : Nat := 118140960795 + 2443118 * 2 ^ 59
def prefixEnd_2443118 : Nat := 4983230072969 + 3 ^ 40 * 2443118 * 2
def baseEnd_2443118 : Nat := 1254493829651277523289311

theorem tailTrace_2443118 : CollatzResearch.WordTrace tailWord_2443118 prefixEnd_2443118 1254493829651277523289311 := by
  unfold tailWord_2443118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11138479245376026522554251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59405222642005474786956005 11138479245376026522554251)
  ·
    refine ⟨16707718868064039783831377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11138479245376026522554251 16707718868064039783831377)
    ·
      refine ⟨12530789151048029837873533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16707718868064039783831377 12530789151048029837873533)
      ·
        refine ⟨4699045931643011189202575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12530789151048029837873533 4699045931643011189202575)
        ·
          refine ⟨7048568897464516783803863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699045931643011189202575 7048568897464516783803863)
          ·
            refine ⟨10572853346196775175705795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048568897464516783803863 10572853346196775175705795)
            ·
              refine ⟨15859280019295162763558693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10572853346196775175705795 15859280019295162763558693)
              ·
                refine ⟨2973615003617843018167255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15859280019295162763558693 2973615003617843018167255)
                ·
                  refine ⟨4460422505426764527250883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2973615003617843018167255 4460422505426764527250883)
                  ·
                    refine ⟨6690633758140146790876325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4460422505426764527250883 6690633758140146790876325)
                    ·
                      refine ⟨1254493829651277523289311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6690633758140146790876325 1254493829651277523289311)
                      ·
                        rfl

theorem cell23_2443118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2443118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443118 prefixEnd_2443118 := by exact prefixLift 2443118
  have htrace : WordTrace (prefixWord ++ tailWord_2443118) baseStart_2443118 baseEnd_2443118 := by
    simpa [prefixWord, tailWord_2443118, baseEnd_2443118] using wordTrace_append hprefix tailTrace_2443118
  have hstable : (prefixWord ++ tailWord_2443118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443118).length < 2 ^ (prefixWord ++ tailWord_2443118).sum := by decide
  have hdescent : baseEnd_2443118 < baseStart_2443118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443182 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2443182 : Nat := 118140960795 + 2443182 * 2 ^ 59
def prefixEnd_2443182 : Nat := 4983230072969 + 3 ^ 40 * 2443182 * 2
def baseEnd_2443182 : Nat := 1254526692413165272889017

theorem tailTrace_2443182 : CollatzResearch.WordTrace tailWord_2443182 prefixEnd_2443182 1254526692413165272889017 := by
  unfold tailWord_2443182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11138771029347043888845475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59406778823184234073842533 11138771029347043888845475)
  ·
    refine ⟨16708156544020565833268213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11138771029347043888845475 16708156544020565833268213)
    ·
      refine ⟨1566389676001928046868895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16708156544020565833268213 1566389676001928046868895)
      ·
        refine ⟨2349584514002892070303343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566389676001928046868895 2349584514002892070303343)
        ·
          refine ⟨3524376771004338105455015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349584514002892070303343 3524376771004338105455015)
          ·
            refine ⟨5286565156506507158182523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524376771004338105455015 5286565156506507158182523)
            ·
              refine ⟨7929847734759760737273785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286565156506507158182523 7929847734759760737273785)
              ·
                refine ⟨5947385801069820552955339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929847734759760737273785 5947385801069820552955339)
                ·
                  refine ⟨8921078701604730829433009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5947385801069820552955339 8921078701604730829433009)
                  ·
                    refine ⟨6690809026203548122074757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8921078701604730829433009 6690809026203548122074757)
                    ·
                      refine ⟨1254526692413165272889017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6690809026203548122074757 1254526692413165272889017)
                      ·
                        rfl

theorem cell23_2443182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2443182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443182 prefixEnd_2443182 := by exact prefixLift 2443182
  have htrace : WordTrace (prefixWord ++ tailWord_2443182) baseStart_2443182 baseEnd_2443182 := by
    simpa [prefixWord, tailWord_2443182, baseEnd_2443182] using wordTrace_append hprefix tailTrace_2443182
  have hstable : (prefixWord ++ tailWord_2443182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443182).length < 2 ^ (prefixWord ++ tailWord_2443182).sum := by decide
  have hdescent : baseEnd_2443182 < baseStart_2443182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443194 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_2443194 : Nat := 118140960795 + 2443194 * 2 ^ 59
def prefixEnd_2443194 : Nat := 4983230072969 + 3 ^ 40 * 2443194 * 2
def baseEnd_2443194 : Nat := 1254532854181019225938961

theorem tailTrace_2443194 : CollatzResearch.WordTrace tailWord_2443194 prefixEnd_2443194 1254532854181019225938961 := by
  unfold tailWord_2443194
  simp only [CollatzResearch.WordTrace]
  refine ⟨22277651477683219290050159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59407070607155251440133757 22277651477683219290050159)
  ·
    refine ⟨33416477216524828935075239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22277651477683219290050159 33416477216524828935075239)
    ·
      refine ⟨50124715824787243402612859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33416477216524828935075239 50124715824787243402612859)
      ·
        refine ⟨75187073737180865103919289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50124715824787243402612859 75187073737180865103919289)
        ·
          refine ⟨56390305302885648827939467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75187073737180865103919289 56390305302885648827939467)
          ·
            refine ⟨84585457954328473241909201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56390305302885648827939467 84585457954328473241909201)
            ·
              refine ⟨63439093465746354931431901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84585457954328473241909201 63439093465746354931431901)
              ·
                refine ⟨23789660049654883099286963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63439093465746354931431901 23789660049654883099286963)
                ·
                  refine ⟨35684490074482324648930445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23789660049654883099286963 35684490074482324648930445)
                  ·
                    refine ⟨13381683777930871743348917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35684490074482324648930445 13381683777930871743348917)
                    ·
                      refine ⟨1254532854181019225938961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13381683777930871743348917 1254532854181019225938961)
                      ·
                        rfl

theorem cell23_2443194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_2443194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443194 prefixEnd_2443194 := by exact prefixLift 2443194
  have htrace : WordTrace (prefixWord ++ tailWord_2443194) baseStart_2443194 baseEnd_2443194 := by
    simpa [prefixWord, tailWord_2443194, baseEnd_2443194] using wordTrace_append hprefix tailTrace_2443194
  have hstable : (prefixWord ++ tailWord_2443194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443194).length < 2 ^ (prefixWord ++ tailWord_2443194).sum := by decide
  have hdescent : baseEnd_2443194 < baseStart_2443194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443218 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2443218 : Nat := 118140960795 + 2443218 * 2 ^ 59
def prefixEnd_2443218 : Nat := 4983230072969 + 3 ^ 40 * 2443218 * 2
def baseEnd_2443218 : Nat := 418181725905575710679617

theorem tailTrace_2443218 : CollatzResearch.WordTrace tailWord_2443218 prefixEnd_2443218 418181725905575710679617 := by
  unfold tailWord_2443218
  simp only [CollatzResearch.WordTrace]
  refine ⟨22277870315661482314768577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59407654175097286172716205 22277870315661482314768577)
  ·
    refine ⟨16708402736746111736076433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22277870315661482314768577 16708402736746111736076433)
    ·
      refine ⟨12531302052559583802057325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16708402736746111736076433 12531302052559583802057325)
      ·
        refine ⟨4699238269709843925771497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12531302052559583802057325 4699238269709843925771497)
        ·
          refine ⟨3524428702282382944328623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4699238269709843925771497 3524428702282382944328623)
          ·
            refine ⟨5286643053423574416492935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524428702282382944328623 5286643053423574416492935)
            ·
              refine ⟨7929964580135361624739403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286643053423574416492935 7929964580135361624739403)
              ·
                refine ⟨11894946870203042437109105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7929964580135361624739403 11894946870203042437109105)
                ·
                  refine ⟨8921210152652281827831829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11894946870203042437109105 8921210152652281827831829)
                  ·
                    refine ⟨418181725905575710679617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8921210152652281827831829 418181725905575710679617)
                    ·
                      rfl

theorem cell23_2443218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2443218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443218 prefixEnd_2443218 := by exact prefixLift 2443218
  have htrace : WordTrace (prefixWord ++ tailWord_2443218) baseStart_2443218 baseEnd_2443218 := by
    simpa [prefixWord, tailWord_2443218, baseEnd_2443218] using wordTrace_append hprefix tailTrace_2443218
  have hstable : (prefixWord ++ tailWord_2443218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443218).length < 2 ^ (prefixWord ++ tailWord_2443218).sum := by decide
  have hdescent : baseEnd_2443218 < baseStart_2443218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443221 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2443221 : Nat := 118140960795 + 2443221 * 2 ^ 59
def prefixEnd_2443221 : Nat := 4983230072969 + 3 ^ 40 * 2443221 * 2
def baseEnd_2443221 : Nat := 1254546718158690620301337

theorem tailTrace_2443221 : CollatzResearch.WordTrace tailWord_2443221 prefixEnd_2443221 1254546718158690620301337 := by
  unfold tailWord_2443221
  simp only [CollatzResearch.WordTrace]
  refine ⟨89111590681635060771433517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59407727121090040514289011 89111590681635060771433517)
  ·
    refine ⟨33416846505613147789287569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89111590681635060771433517 33416846505613147789287569)
    ·
      refine ⟨25062634879209860841965677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33416846505613147789287569 25062634879209860841965677)
      ·
        refine ⟨9398488079703697815737129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25062634879209860841965677 9398488079703697815737129)
        ·
          refine ⟨7048866059777773361802847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9398488079703697815737129 7048866059777773361802847)
          ·
            refine ⟨10573299089666660042704271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048866059777773361802847 10573299089666660042704271)
            ·
              refine ⟨15859948634499990064056407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10573299089666660042704271 15859948634499990064056407)
              ·
                refine ⟨23789922951749985096084611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15859948634499990064056407 23789922951749985096084611)
                ·
                  refine ⟨35684884427624977644126917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23789922951749985096084611 35684884427624977644126917)
                  ·
                    refine ⟨6690915830179683308273797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35684884427624977644126917 6690915830179683308273797)
                    ·
                      refine ⟨1254546718158690620301337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6690915830179683308273797 1254546718158690620301337)
                      ·
                        rfl

theorem cell23_2443221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2443221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443221 prefixEnd_2443221 := by exact prefixLift 2443221
  have htrace : WordTrace (prefixWord ++ tailWord_2443221) baseStart_2443221 baseEnd_2443221 := by
    simpa [prefixWord, tailWord_2443221, baseEnd_2443221] using wordTrace_append hprefix tailTrace_2443221
  have hstable : (prefixWord ++ tailWord_2443221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443221).length < 2 ^ (prefixWord ++ tailWord_2443221).sum := by decide
  have hdescent : baseEnd_2443221 < baseStart_2443221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443225 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 1, 4, 2]
def baseStart_2443225 : Nat := 118140960795 + 2443225 * 2 ^ 59
def prefixEnd_2443225 : Nat := 4983230072969 + 3 ^ 40 * 2443225 * 2
def baseEnd_2443225 : Nat := 1254548772081308604651319

theorem tailTrace_2443225 : CollatzResearch.WordTrace tailWord_2443225 prefixEnd_2443225 1254548772081308604651319 := by
  unfold tailWord_2443225
  simp only [CollatzResearch.WordTrace]
  refine ⟨89111736573620569454579129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59407824382413712969719419 89111736573620569454579129)
  ·
    refine ⟨66833802430215427090934347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89111736573620569454579129 66833802430215427090934347)
    ·
      refine ⟨100250703645323140636401521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66833802430215427090934347 100250703645323140636401521)
      ·
        refine ⟨75188027733992355477301141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100250703645323140636401521 75188027733992355477301141)
        ·
          refine ⟨3524438800030891662998491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75188027733992355477301141 3524438800030891662998491)
          ·
            refine ⟨5286658200046337494497737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524438800030891662998491 5286658200046337494497737)
            ·
              refine ⟨3964993650034753120873303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5286658200046337494497737 3964993650034753120873303)
              ·
                refine ⟨5947490475052129681309955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964993650034753120873303 5947490475052129681309955)
                ·
                  refine ⟨8921235712578194521964933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5947490475052129681309955 8921235712578194521964933)
                  ·
                    refine ⟨1672731696108411472868425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8921235712578194521964933 1672731696108411472868425)
                    ·
                      refine ⟨1254548772081308604651319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672731696108411472868425 1254548772081308604651319)
                      ·
                        rfl

theorem cell23_2443225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_2443225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443225 prefixEnd_2443225 := by exact prefixLift 2443225
  have htrace : WordTrace (prefixWord ++ tailWord_2443225) baseStart_2443225 baseEnd_2443225 := by
    simpa [prefixWord, tailWord_2443225, baseEnd_2443225] using wordTrace_append hprefix tailTrace_2443225
  have hstable : (prefixWord ++ tailWord_2443225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443225).length < 2 ^ (prefixWord ++ tailWord_2443225).sum := by decide
  have hdescent : baseEnd_2443225 < baseStart_2443225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443231 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 7]
def baseStart_2443231 : Nat := 118140960795 + 2443231 * 2 ^ 59
def prefixEnd_2443231 : Nat := 4983230072969 + 3 ^ 40 * 2443231 * 2
def baseEnd_2443231 : Nat := 139394650329470620130699

theorem tailTrace_2443231 : CollatzResearch.WordTrace tailWord_2443231 prefixEnd_2443231 139394650329470620130699 := by
  unfold tailWord_2443231
  simp only [CollatzResearch.WordTrace]
  refine ⟨89111955411598832479297547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59407970274399221652865031 89111955411598832479297547)
  ·
    refine ⟨133667933117398248718946321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89111955411598832479297547 133667933117398248718946321)
    ·
      refine ⟨100250949838048686539209741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133667933117398248718946321 100250949838048686539209741)
      ·
        refine ⟨37594106189268257452203653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100250949838048686539209741 37594106189268257452203653)
        ·
          refine ⟨7048894910487798272288185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37594106189268257452203653 7048894910487798272288185)
          ·
            refine ⟨5286671182865848704216139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7048894910487798272288185 5286671182865848704216139)
            ·
              refine ⟨7930006774298773056324209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286671182865848704216139 7930006774298773056324209)
              ·
                refine ⟨5947505080724079792243157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7930006774298773056324209 5947505080724079792243157)
                ·
                  refine ⟨139394650329470620130699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5947505080724079792243157 139394650329470620130699)
                  ·
                    rfl

theorem cell23_2443231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 7].length) (baseStart_2443231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443231 prefixEnd_2443231 := by exact prefixLift 2443231
  have htrace : WordTrace (prefixWord ++ tailWord_2443231) baseStart_2443231 baseEnd_2443231 := by
    simpa [prefixWord, tailWord_2443231, baseEnd_2443231] using wordTrace_append hprefix tailTrace_2443231
  have hstable : (prefixWord ++ tailWord_2443231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443231).length < 2 ^ (prefixWord ++ tailWord_2443231).sum := by decide
  have hdescent : baseEnd_2443231 < baseStart_2443231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443261 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_2443261 : Nat := 118140960795 + 2443261 * 2 ^ 59
def prefixEnd_2443261 : Nat := 4983230072969 + 3 ^ 40 * 2443261 * 2
def baseEnd_2443261 : Nat := 418189085794956821267051

theorem tailTrace_2443261 : CollatzResearch.WordTrace tailWord_2443261 prefixEnd_2443261 418189085794956821267051 := by
  unfold tailWord_2443261
  simp only [CollatzResearch.WordTrace]
  refine ⟨89113049601490147602889637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59408699734326765068593091 89113049601490147602889637)
  ·
    refine ⟨16708696800279402675541807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89113049601490147602889637 16708696800279402675541807)
    ·
      refine ⟨25063045200419104013312711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16708696800279402675541807 25063045200419104013312711)
      ·
        refine ⟨37594567800628656019969067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25063045200419104013312711 37594567800628656019969067)
        ·
          refine ⟨56391851700942984029953601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37594567800628656019969067 56391851700942984029953601)
          ·
            refine ⟨42293888775707238022465201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56391851700942984029953601 42293888775707238022465201)
            ·
              refine ⟨31720416581780428516848901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42293888775707238022465201 31720416581780428516848901)
              ·
                refine ⟨5947578109083830346909169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31720416581780428516848901 5947578109083830346909169)
                ·
                  refine ⟨4460683581812872760181877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947578109083830346909169 4460683581812872760181877)
                  ·
                    refine ⟨418189085794956821267051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4460683581812872760181877 418189085794956821267051)
                    ·
                      rfl

theorem cell23_2443261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_2443261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443261 prefixEnd_2443261 := by exact prefixLift 2443261
  have htrace : WordTrace (prefixWord ++ tailWord_2443261) baseStart_2443261 baseEnd_2443261 := by
    simpa [prefixWord, tailWord_2443261, baseEnd_2443261] using wordTrace_append hprefix tailTrace_2443261
  have hstable : (prefixWord ++ tailWord_2443261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443261).length < 2 ^ (prefixWord ++ tailWord_2443261).sum := by decide
  have hdescent : baseEnd_2443261 < baseStart_2443261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443291 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 5, 4]
def baseStart_2443291 : Nat := 118140960795 + 2443291 * 2 ^ 59
def prefixEnd_2443291 : Nat := 4983230072969 + 3 ^ 40 * 2443291 * 2
def baseEnd_2443291 : Nat := 418194220601501782142005

theorem tailTrace_2443291 : CollatzResearch.WordTrace tailWord_2443291 prefixEnd_2443291 418194220601501782142005 := by
  unfold tailWord_2443291
  simp only [CollatzResearch.WordTrace]
  refine ⟨89114143791381462726481727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59409429194254308484321151 89114143791381462726481727)
  ·
    refine ⟨133671215687072194089722591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89114143791381462726481727 133671215687072194089722591)
    ·
      refine ⟨200506823530608291134583887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133671215687072194089722591 200506823530608291134583887)
      ·
        refine ⟨300760235295912436701875831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200506823530608291134583887 300760235295912436701875831)
        ·
          refine ⟨451140352943868655052813747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300760235295912436701875831 451140352943868655052813747)
          ·
            refine ⟨676710529415802982579220621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451140352943868655052813747 676710529415802982579220621)
            ·
              refine ⟨253766448530926118467207733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676710529415802982579220621 253766448530926118467207733)
              ·
                refine ⟨23790604549774323606300725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253766448530926118467207733 23790604549774323606300725)
                ·
                  refine ⟨2230369176541342838090693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23790604549774323606300725 2230369176541342838090693)
                  ·
                    refine ⟨418194220601501782142005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230369176541342838090693 418194220601501782142005)
                    ·
                      rfl

theorem cell23_2443291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 4].length) (baseStart_2443291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443291 prefixEnd_2443291 := by exact prefixLift 2443291
  have htrace : WordTrace (prefixWord ++ tailWord_2443291) baseStart_2443291 baseEnd_2443291 := by
    simpa [prefixWord, tailWord_2443291, baseEnd_2443291] using wordTrace_append hprefix tailTrace_2443291
  have hstable : (prefixWord ++ tailWord_2443291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443291).length < 2 ^ (prefixWord ++ tailWord_2443291).sum := by decide
  have hdescent : baseEnd_2443291 < baseStart_2443291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443298 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2443298 : Nat := 118140960795 + 2443298 * 2 ^ 59
def prefixEnd_2443298 : Nat := 4983230072969 + 3 ^ 40 * 2443298 * 2
def baseEnd_2443298 : Nat := 1254586256169086819038483

theorem tailTrace_2443298 : CollatzResearch.WordTrace tailWord_2443298 prefixEnd_2443298 1254586256169086819038483 := by
  unfold tailWord_2443298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22278599775589025730496637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59409599401570735281324365 22278599775589025730496637)
  ·
    refine ⟨8354474915845884648936239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22278599775589025730496637 8354474915845884648936239)
    ·
      refine ⟨12531712373768826973404359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8354474915845884648936239 12531712373768826973404359)
      ·
        refine ⟨18797568560653240460106539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12531712373768826973404359 18797568560653240460106539)
        ·
          refine ⟨28196352840979860690159809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18797568560653240460106539 28196352840979860690159809)
          ·
            refine ⟨21147264630734895517619857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28196352840979860690159809 21147264630734895517619857)
            ·
              refine ⟨15860448473051171638214893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21147264630734895517619857 15860448473051171638214893)
              ·
                refine ⟨5947668177394189364330585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15860448473051171638214893 5947668177394189364330585)
                ·
                  refine ⟨4460751133045642023247939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947668177394189364330585 4460751133045642023247939)
                  ·
                    refine ⟨6691126699568463034871909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4460751133045642023247939 6691126699568463034871909)
                    ·
                      refine ⟨1254586256169086819038483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6691126699568463034871909 1254586256169086819038483)
                      ·
                        rfl

theorem cell23_2443298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2443298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443298 prefixEnd_2443298 := by exact prefixLift 2443298
  have htrace : WordTrace (prefixWord ++ tailWord_2443298) baseStart_2443298 baseEnd_2443298 := by
    simpa [prefixWord, tailWord_2443298, baseEnd_2443298] using wordTrace_append hprefix tailTrace_2443298
  have hstable : (prefixWord ++ tailWord_2443298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443298).length < 2 ^ (prefixWord ++ tailWord_2443298).sum := by decide
  have hdescent : baseEnd_2443298 < baseStart_2443298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443331 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 3]
def baseStart_2443331 : Nat := 118140960795 + 2443331 * 2 ^ 59
def prefixEnd_2443331 : Nat := 4983230072969 + 3 ^ 40 * 2443331 * 2
def baseEnd_2443331 : Nat := 1254603201030685189925831

theorem tailTrace_2443331 : CollatzResearch.WordTrace tailWord_2443331 prefixEnd_2443331 1254603201030685189925831 := by
  unfold tailWord_2443331
  simp only [CollatzResearch.WordTrace]
  refine ⟨89115602711236549557937847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59410401807491033038625231 89115602711236549557937847)
  ·
    refine ⟨133673404066854824336906771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89115602711236549557937847 133673404066854824336906771)
    ·
      refine ⟨200510106100282236505360157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133673404066854824336906771 200510106100282236505360157)
      ·
        refine ⟨75191289787605838689510059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200510106100282236505360157 75191289787605838689510059)
        ·
          refine ⟨112786934681408758034265089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75191289787605838689510059 112786934681408758034265089)
          ·
            refine ⟨84590201011056568525698817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112786934681408758034265089 84590201011056568525698817)
            ·
              refine ⟨63442650758292426394274113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84590201011056568525698817 63442650758292426394274113)
              ·
                refine ⟨47581988068719319795705585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63442650758292426394274113 47581988068719319795705585)
                ·
                  refine ⟨35686491051539489846779189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47581988068719319795705585 35686491051539489846779189)
                  ·
                    refine ⟨3345608536081827173135549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35686491051539489846779189 3345608536081827173135549)
                    ·
                      refine ⟨1254603201030685189925831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3345608536081827173135549 1254603201030685189925831)
                      ·
                        rfl

theorem cell23_2443331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_2443331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443331 prefixEnd_2443331 := by exact prefixLift 2443331
  have htrace : WordTrace (prefixWord ++ tailWord_2443331) baseStart_2443331 baseEnd_2443331 := by
    simpa [prefixWord, tailWord_2443331, baseEnd_2443331] using wordTrace_append hprefix tailTrace_2443331
  have hstable : (prefixWord ++ tailWord_2443331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443331).length < 2 ^ (prefixWord ++ tailWord_2443331).sum := by decide
  have hdescent : baseEnd_2443331 < baseStart_2443331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443375 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 2, 3, 2]
def baseStart_2443375 : Nat := 118140960795 + 2443375 * 2 ^ 59
def prefixEnd_2443375 : Nat := 4983230072969 + 3 ^ 40 * 2443375 * 2
def baseEnd_2443375 : Nat := 1254625794179483017775629

theorem tailTrace_2443375 : CollatzResearch.WordTrace tailWord_2443375 prefixEnd_2443375 1254625794179483017775629 := by
  unfold tailWord_2443375
  simp only [CollatzResearch.WordTrace]
  refine ⟨89117207523077145072539579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59411471682051430048359719 89117207523077145072539579)
  ·
    refine ⟨133675811284615717608809369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89117207523077145072539579 133675811284615717608809369)
    ·
      refine ⟨100256858463461788206607027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133675811284615717608809369 100256858463461788206607027)
      ·
        refine ⟨150385287695192682309910541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100256858463461788206607027 150385287695192682309910541)
        ·
          refine ⟨56394482885697255866216453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150385287695192682309910541 56394482885697255866216453)
          ·
            refine ⟨10573965541068235474915585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56394482885697255866216453 10573965541068235474915585)
            ·
              refine ⟨7930474155801176606186689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10573965541068235474915585 7930474155801176606186689)
              ·
                refine ⟨5947855616850882454640017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7930474155801176606186689 5947855616850882454640017)
                ·
                  refine ⟨4460891712638161840980013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5947855616850882454640017 4460891712638161840980013)
                  ·
                    refine ⟨1672834392239310690367505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4460891712638161840980013 1672834392239310690367505)
                    ·
                      refine ⟨1254625794179483017775629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672834392239310690367505 1254625794179483017775629)
                      ·
                        rfl

theorem cell23_2443375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3, 2].length) (baseStart_2443375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443375 prefixEnd_2443375 := by exact prefixLift 2443375
  have htrace : WordTrace (prefixWord ++ tailWord_2443375) baseStart_2443375 baseEnd_2443375 := by
    simpa [prefixWord, tailWord_2443375, baseEnd_2443375] using wordTrace_append hprefix tailTrace_2443375
  have hstable : (prefixWord ++ tailWord_2443375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443375).length < 2 ^ (prefixWord ++ tailWord_2443375).sum := by decide
  have hdescent : baseEnd_2443375 < baseStart_2443375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443388 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_2443388 : Nat := 118140960795 + 2443388 * 2 ^ 59
def prefixEnd_2443388 : Nat := 4983230072969 + 3 ^ 40 * 2443388 * 2
def baseEnd_2443388 : Nat := 1254632469427991466913069

theorem tailTrace_2443388 : CollatzResearch.WordTrace tailWord_2443388 prefixEnd_2443388 1254632469427991466913069 := by
  unfold tailWord_2443388
  simp only [CollatzResearch.WordTrace]
  refine ⟨44558840836015024146381409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59411787781353365528508545 44558840836015024146381409)
  ·
    refine ⟨33419130627011268109786057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44558840836015024146381409 33419130627011268109786057)
    ·
      refine ⟨25064347970258451082339543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33419130627011268109786057 25064347970258451082339543)
      ·
        refine ⟨37596521955387676623509315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25064347970258451082339543 37596521955387676623509315)
        ·
          refine ⟨56394782933081514935263973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37596521955387676623509315 56394782933081514935263973)
          ·
            refine ⟨10574021799952784050361995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56394782933081514935263973 10574021799952784050361995)
            ·
              refine ⟨15861032699929176075542993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10574021799952784050361995 15861032699929176075542993)
              ·
                refine ⟨11895774524946882056657245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15861032699929176075542993 11895774524946882056657245)
                ·
                  refine ⟨4460915446855080771246467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11895774524946882056657245 4460915446855080771246467)
                  ·
                    refine ⟨6691373170282621156869701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4460915446855080771246467 6691373170282621156869701)
                    ·
                      refine ⟨1254632469427991466913069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6691373170282621156869701 1254632469427991466913069)
                      ·
                        rfl

theorem cell23_2443388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_2443388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443388 prefixEnd_2443388 := by exact prefixLift 2443388
  have htrace : WordTrace (prefixWord ++ tailWord_2443388) baseStart_2443388 baseEnd_2443388 := by
    simpa [prefixWord, tailWord_2443388, baseEnd_2443388] using wordTrace_append hprefix tailTrace_2443388
  have hstable : (prefixWord ++ tailWord_2443388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443388).length < 2 ^ (prefixWord ++ tailWord_2443388).sum := by decide
  have hdescent : baseEnd_2443388 < baseStart_2443388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443408 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3]
def baseStart_2443408 : Nat := 118140960795 + 2443408 * 2 ^ 59
def prefixEnd_2443408 : Nat := 4983230072969 + 3 ^ 40 * 2443408 * 2
def baseEnd_2443408 : Nat := 1254642739041081388662977

theorem tailTrace_2443408 : CollatzResearch.WordTrace tailWord_2443408 prefixEnd_2443408 1254642739041081388662977 := by
  unfold tailWord_2443408
  simp only [CollatzResearch.WordTrace]
  refine ⟨44559205565978795854245439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59412274087971727805660585 44559205565978795854245439)
  ·
    refine ⟨66838808348968193781368159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44559205565978795854245439 66838808348968193781368159)
    ·
      refine ⟨100258212523452290672052239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66838808348968193781368159 100258212523452290672052239)
      ·
        refine ⟨150387318785178436008078359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100258212523452290672052239 150387318785178436008078359)
        ·
          refine ⟨225580978177767654012117539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150387318785178436008078359 225580978177767654012117539)
          ·
            refine ⟨338371467266651481018176309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225580978177767654012117539 338371467266651481018176309)
            ·
              refine ⟨31722325056248576345454029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 338371467266651481018176309 31722325056248576345454029)
              ·
                refine ⟨11895871896093216129545261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31722325056248576345454029 11895871896093216129545261)
                ·
                  refine ⟨4460951961034956048579473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11895871896093216129545261 4460951961034956048579473)
                  ·
                    refine ⟨3345713970776217036434605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4460951961034956048579473 3345713970776217036434605)
                    ·
                      refine ⟨1254642739041081388662977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3345713970776217036434605 1254642739041081388662977)
                      ·
                        rfl

theorem cell23_2443408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_2443408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443408 prefixEnd_2443408 := by exact prefixLift 2443408
  have htrace : WordTrace (prefixWord ++ tailWord_2443408) baseStart_2443408 baseEnd_2443408 := by
    simpa [prefixWord, tailWord_2443408, baseEnd_2443408] using wordTrace_append hprefix tailTrace_2443408
  have hstable : (prefixWord ++ tailWord_2443408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443408).length < 2 ^ (prefixWord ++ tailWord_2443408).sum := by decide
  have hdescent : baseEnd_2443408 < baseStart_2443408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443428 : List Nat := [2, 3, 1, 2, 4, 1, 10]
def baseStart_2443428 : Nat := 118140960795 + 2443428 * 2 ^ 59
def prefixEnd_2443428 : Nat := 4983230072969 + 3 ^ 40 * 2443428 * 2
def baseEnd_2443428 : Nat := 15489543316718164326085

theorem tailTrace_2443428 : CollatzResearch.WordTrace tailWord_2443428 prefixEnd_2443428 15489543316718164326085 := by
  unfold tailWord_2443428
  simp only [CollatzResearch.WordTrace]
  refine ⟨44559570295942567562109469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59412760394590090082812625 44559570295942567562109469)
  ·
    refine ⟨16709838860978462835791051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44559570295942567562109469 16709838860978462835791051)
    ·
      refine ⟨25064758291467694253686577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16709838860978462835791051 25064758291467694253686577)
      ·
        refine ⟨18798568718600770690264933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25064758291467694253686577 18798568718600770690264933)
        ·
          refine ⟨3524731634737644504424675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18798568718600770690264933 3524731634737644504424675)
          ·
            refine ⟨5287097452106466756637013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524731634737644504424675 5287097452106466756637013)
            ·
              refine ⟨15489543316718164326085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5287097452106466756637013 15489543316718164326085)
              ·
                rfl

theorem cell23_2443428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 10].length) (baseStart_2443428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443428 prefixEnd_2443428 := by exact prefixLift 2443428
  have htrace : WordTrace (prefixWord ++ tailWord_2443428) baseStart_2443428 baseEnd_2443428 := by
    simpa [prefixWord, tailWord_2443428, baseEnd_2443428] using wordTrace_append hprefix tailTrace_2443428
  have hstable : (prefixWord ++ tailWord_2443428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443428).length < 2 ^ (prefixWord ++ tailWord_2443428).sum := by decide
  have hdescent : baseEnd_2443428 < baseStart_2443428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443452 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_2443452 : Nat := 118140960795 + 2443452 * 2 ^ 59
def prefixEnd_2443452 : Nat := 4983230072969 + 3 ^ 40 * 2443452 * 2
def baseEnd_2443452 : Nat := 1254665332189879216512775

theorem tailTrace_2443452 : CollatzResearch.WordTrace tailWord_2443452 prefixEnd_2443452 1254665332189879216512775 := by
  unfold tailWord_2443452
  simp only [CollatzResearch.WordTrace]
  refine ⟨44560007971899093611546305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59413343962532124815395073 44560007971899093611546305)
  ·
    refine ⟨33420005978924320208659729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44560007971899093611546305 33420005978924320208659729)
    ·
      refine ⟨25065004484193240156494797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33420005978924320208659729 25065004484193240156494797)
      ·
        refine ⟨9399376681572465058685549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25065004484193240156494797 9399376681572465058685549)
        ·
          refine ⟨3524766255589674397007081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9399376681572465058685549 3524766255589674397007081)
          ·
            refine ⟨2643574691692255797755311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3524766255589674397007081 2643574691692255797755311)
            ·
              refine ⟨3965362037538383696632967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643574691692255797755311 3965362037538383696632967)
              ·
                refine ⟨5948043056307575544949451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3965362037538383696632967 5948043056307575544949451)
                ·
                  refine ⟨8922064584461363317424177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5948043056307575544949451 8922064584461363317424177)
                  ·
                    refine ⟨6691548438346022488068133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8922064584461363317424177 6691548438346022488068133)
                    ·
                      refine ⟨1254665332189879216512775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6691548438346022488068133 1254665332189879216512775)
                      ·
                        rfl

theorem cell23_2443452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_2443452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443452 prefixEnd_2443452 := by exact prefixLift 2443452
  have htrace : WordTrace (prefixWord ++ tailWord_2443452) baseStart_2443452 baseEnd_2443452 := by
    simpa [prefixWord, tailWord_2443452, baseEnd_2443452] using wordTrace_append hprefix tailTrace_2443452
  have hstable : (prefixWord ++ tailWord_2443452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443452).length < 2 ^ (prefixWord ++ tailWord_2443452).sum := by decide
  have hdescent : baseEnd_2443452 < baseStart_2443452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443482 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2]
def baseStart_2443482 : Nat := 118140960795 + 2443482 * 2 ^ 59
def prefixEnd_2443482 : Nat := 4983230072969 + 3 ^ 40 * 2443482 * 2
def baseEnd_2443482 : Nat := 1254680736609514099137637

theorem tailTrace_2443482 : CollatzResearch.WordTrace tailWord_2443482 prefixEnd_2443482 1254680736609514099137637 := by
  unfold tailWord_2443482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280277533422375586671175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59414073422459668231123133 22280277533422375586671175)
  ·
    refine ⟨33420416300133563380006763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22280277533422375586671175 33420416300133563380006763)
    ·
      refine ⟨50130624450200345070010145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33420416300133563380006763 50130624450200345070010145)
      ·
        refine ⟨37597968337650258802507609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50130624450200345070010145 37597968337650258802507609)
        ·
          refine ⟨28198476253237694101880707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37597968337650258802507609 28198476253237694101880707)
          ·
            refine ⟨42297714379856541152821061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28198476253237694101880707 42297714379856541152821061)
            ·
              refine ⟨7930821446223101466153949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42297714379856541152821061 7930821446223101466153949)
              ·
                refine ⟨2974058042333663049807731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7930821446223101466153949 2974058042333663049807731)
                ·
                  refine ⟨4461087063500494574711597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974058042333663049807731 4461087063500494574711597)
                  ·
                    refine ⟨1672907648812685465516849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4461087063500494574711597 1672907648812685465516849)
                    ·
                      refine ⟨1254680736609514099137637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672907648812685465516849 1254680736609514099137637)
                      ·
                        rfl

theorem cell23_2443482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_2443482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443482 prefixEnd_2443482 := by exact prefixLift 2443482
  have htrace : WordTrace (prefixWord ++ tailWord_2443482) baseStart_2443482 baseEnd_2443482 := by
    simpa [prefixWord, tailWord_2443482, baseEnd_2443482] using wordTrace_append hprefix tailTrace_2443482
  have hstable : (prefixWord ++ tailWord_2443482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443482).length < 2 ^ (prefixWord ++ tailWord_2443482).sum := by decide
  have hdescent : baseEnd_2443482 < baseStart_2443482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443490 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2443490 : Nat := 118140960795 + 2443490 * 2 ^ 59
def prefixEnd_2443490 : Nat := 4983230072969 + 3 ^ 40 * 2443490 * 2
def baseEnd_2443490 : Nat := 1254684844454750067837601

theorem tailTrace_2443490 : CollatzResearch.WordTrace tailWord_2443490 prefixEnd_2443490 1254684844454750067837601 := by
  unfold tailWord_2443490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280350479415129928243981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59414267945107013141983949 22280350479415129928243981)
  ·
    refine ⟨8355131429780673723091493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22280350479415129928243981 8355131429780673723091493)
    ·
      refine ⟨1566587143083876323079655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8355131429780673723091493 1566587143083876323079655)
      ·
        refine ⟨2349880714625814484619483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566587143083876323079655 2349880714625814484619483)
        ·
          refine ⟨3524821071938721726929225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349880714625814484619483 3524821071938721726929225)
          ·
            refine ⟨2643615803954041295196919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3524821071938721726929225 2643615803954041295196919)
            ·
              refine ⟨3965423705931061942795379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643615803954041295196919 3965423705931061942795379)
              ·
                refine ⟨5948135558896592914193069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3965423705931061942795379 5948135558896592914193069)
                ·
                  refine ⟨2230550834586222342822401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5948135558896592914193069 2230550834586222342822401)
                  ·
                    refine ⟨1672913125939666757116801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2230550834586222342822401 1672913125939666757116801)
                    ·
                      refine ⟨1254684844454750067837601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672913125939666757116801 1254684844454750067837601)
                      ·
                        rfl

theorem cell23_2443490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2443490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443490 prefixEnd_2443490 := by exact prefixLift 2443490
  have htrace : WordTrace (prefixWord ++ tailWord_2443490) baseStart_2443490 baseEnd_2443490 := by
    simpa [prefixWord, tailWord_2443490, baseEnd_2443490] using wordTrace_append hprefix tailTrace_2443490
  have hstable : (prefixWord ++ tailWord_2443490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443490).length < 2 ^ (prefixWord ++ tailWord_2443490).sum := by decide
  have hdescent : baseEnd_2443490 < baseStart_2443490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443498 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2443498 : Nat := 118140960795 + 2443498 * 2 ^ 59
def prefixEnd_2443498 : Nat := 4983230072969 + 3 ^ 40 * 2443498 * 2
def baseEnd_2443498 : Nat := 1254688952299986036537563

theorem tailTrace_2443498 : CollatzResearch.WordTrace tailWord_2443498 prefixEnd_2443498 1254688952299986036537563 := by
  unfold tailWord_2443498
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280423425407884269816787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59414462467754358052844765 22280423425407884269816787)
  ·
    refine ⟨33420635138111826404725181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22280423425407884269816787 33420635138111826404725181)
    ·
      refine ⟨12532738176791934901771943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33420635138111826404725181 12532738176791934901771943)
      ·
        refine ⟨18799107265187902352657915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12532738176791934901771943 18799107265187902352657915)
        ·
          refine ⟨28198660897781853528986873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18799107265187902352657915 28198660897781853528986873)
          ·
            refine ⟨21148995673336390146740155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28198660897781853528986873 21148995673336390146740155)
            ·
              refine ⟨31723493510004585220110233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21148995673336390146740155 31723493510004585220110233)
              ·
                refine ⟨23792620132503438915082675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31723493510004585220110233 23792620132503438915082675)
                ·
                  refine ⟨35688930198755158372624013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23792620132503438915082675 35688930198755158372624013)
                  ·
                    refine ⟨13383348824533184389734005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35688930198755158372624013 13383348824533184389734005)
                    ·
                      refine ⟨1254688952299986036537563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13383348824533184389734005 1254688952299986036537563)
                      ·
                        rfl

theorem cell23_2443498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2443498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443498 prefixEnd_2443498 := by exact prefixLift 2443498
  have htrace : WordTrace (prefixWord ++ tailWord_2443498) baseStart_2443498 baseEnd_2443498 := by
    simpa [prefixWord, tailWord_2443498, baseEnd_2443498] using wordTrace_append hprefix tailTrace_2443498
  have hstable : (prefixWord ++ tailWord_2443498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443498).length < 2 ^ (prefixWord ++ tailWord_2443498).sum := by decide
  have hdescent : baseEnd_2443498 < baseStart_2443498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443506 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_2443506 : Nat := 118140960795 + 2443506 * 2 ^ 59
def prefixEnd_2443506 : Nat := 4983230072969 + 3 ^ 40 * 2443506 * 2
def baseEnd_2443506 : Nat := 1254693060145222005237527

theorem tailTrace_2443506 : CollatzResearch.WordTrace tailWord_2443506 prefixEnd_2443506 1254693060145222005237527 := by
  unfold tailWord_2443506
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280496371400638611389593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59414656990401702963705581 22280496371400638611389593)
  ·
    refine ⟨16710372278550478958542195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22280496371400638611389593 16710372278550478958542195)
    ·
      refine ⟨25065558417825718437813293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16710372278550478958542195 25065558417825718437813293)
      ·
        refine ⟨9399584406684644414179985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25065558417825718437813293 9399584406684644414179985)
        ·
          refine ⟨7049688305013483310634989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9399584406684644414179985 7049688305013483310634989)
          ·
            refine ⟨2643633114380056241488121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7049688305013483310634989 2643633114380056241488121)
            ·
              refine ⟨1982724835785042181116091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2643633114380056241488121 1982724835785042181116091)
              ·
                refine ⟨2974087253677563271674137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982724835785042181116091 2974087253677563271674137)
                ·
                  refine ⟨2230565440258172453755603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974087253677563271674137 2230565440258172453755603)
                  ·
                    refine ⟨3345848160387258680633405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2230565440258172453755603 3345848160387258680633405)
                    ·
                      refine ⟨1254693060145222005237527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3345848160387258680633405 1254693060145222005237527)
                      ·
                        rfl

theorem cell23_2443506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_2443506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443506 prefixEnd_2443506 := by exact prefixLift 2443506
  have htrace : WordTrace (prefixWord ++ tailWord_2443506) baseStart_2443506 baseEnd_2443506 := by
    simpa [prefixWord, tailWord_2443506, baseEnd_2443506] using wordTrace_append hprefix tailTrace_2443506
  have hstable : (prefixWord ++ tailWord_2443506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443506).length < 2 ^ (prefixWord ++ tailWord_2443506).sum := by decide
  have hdescent : baseEnd_2443506 < baseStart_2443506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443546 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2]
def baseStart_2443546 : Nat := 118140960795 + 2443546 * 2 ^ 59
def prefixEnd_2443546 : Nat := 4983230072969 + 3 ^ 40 * 2443546 * 2
def baseEnd_2443546 : Nat := 1254713599371401848737343

theorem tailTrace_2443546 : CollatzResearch.WordTrace tailWord_2443546 prefixEnd_2443546 1254713599371401848737343 := by
  unfold tailWord_2443546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280861101364410319253623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59415629603638427518009661 22280861101364410319253623)
  ·
    refine ⟨33421291652046615478880435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22280861101364410319253623 33421291652046615478880435)
    ·
      refine ⟨50131937478069923218320653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33421291652046615478880435 50131937478069923218320653)
      ·
        refine ⟨18799476554276221206870245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50131937478069923218320653 18799476554276221206870245)
        ·
          refine ⟨3524901853926791476288171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18799476554276221206870245 3524901853926791476288171)
          ·
            refine ⟨5287352780890187214432257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524901853926791476288171 5287352780890187214432257)
            ·
              refine ⟨3965514585667640410824193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5287352780890187214432257 3965514585667640410824193)
              ·
                refine ⟨2974135939250730308118145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3965514585667640410824193 2974135939250730308118145)
                ·
                  refine ⟨2230601954438047731088609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974135939250730308118145 2230601954438047731088609)
                  ·
                    refine ⟨1672951465828535798316457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2230601954438047731088609 1672951465828535798316457)
                    ·
                      refine ⟨1254713599371401848737343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672951465828535798316457 1254713599371401848737343)
                      ·
                        rfl

theorem cell23_2443546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_2443546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443546 prefixEnd_2443546 := by exact prefixLift 2443546
  have htrace : WordTrace (prefixWord ++ tailWord_2443546) baseStart_2443546 baseEnd_2443546 := by
    simpa [prefixWord, tailWord_2443546, baseEnd_2443546] using wordTrace_append hprefix tailTrace_2443546
  have hstable : (prefixWord ++ tailWord_2443546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443546).length < 2 ^ (prefixWord ++ tailWord_2443546).sum := by decide
  have hdescent : baseEnd_2443546 < baseStart_2443546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443548 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2443548 : Nat := 118140960795 + 2443548 * 2 ^ 59
def prefixEnd_2443548 : Nat := 4983230072969 + 3 ^ 40 * 2443548 * 2
def baseEnd_2443548 : Nat := 418238208777570280304111

theorem tailTrace_2443548 : CollatzResearch.WordTrace tailWord_2443548 prefixEnd_2443548 418238208777570280304111 := by
  unfold tailWord_2443548
  simp only [CollatzResearch.WordTrace]
  refine ⟨44561758675725197809293649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59415678234300263745724865 44561758675725197809293649)
  ·
    refine ⟨33421319006793898356970237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44561758675725197809293649 33421319006793898356970237)
    ·
      refine ⟨12532994627547711883863839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33421319006793898356970237 12532994627547711883863839)
      ·
        refine ⟨18799491941321567825795759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12532994627547711883863839 18799491941321567825795759)
        ·
          refine ⟨28199237911982351738693639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18799491941321567825795759 28199237911982351738693639)
          ·
            refine ⟨42298856867973527608040459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28199237911982351738693639 42298856867973527608040459)
            ·
              refine ⟨63448285301960291412060689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42298856867973527608040459 63448285301960291412060689)
              ·
                refine ⟨47586213976470218559045517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63448285301960291412060689 47586213976470218559045517)
                ·
                  refine ⟨17844830241176331959642069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47586213976470218559045517 17844830241176331959642069)
                  ·
                    refine ⟨418238208777570280304111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17844830241176331959642069 418238208777570280304111)
                    ·
                      rfl

theorem cell23_2443548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2443548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443548 prefixEnd_2443548 := by exact prefixLift 2443548
  have htrace : WordTrace (prefixWord ++ tailWord_2443548) baseStart_2443548 baseEnd_2443548 := by
    simpa [prefixWord, tailWord_2443548, baseEnd_2443548] using wordTrace_append hprefix tailTrace_2443548
  have hstable : (prefixWord ++ tailWord_2443548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443548).length < 2 ^ (prefixWord ++ tailWord_2443548).sum := by decide
  have hdescent : baseEnd_2443548 < baseStart_2443548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443552 : List Nat := [2, 1, 1, 5, 2, 2, 1, 4, 5]
def baseStart_2443552 : Nat := 118140960795 + 2443552 * 2 ^ 59
def prefixEnd_2443552 : Nat := 4983230072969 + 3 ^ 40 * 2443552 * 2
def baseEnd_2443552 : Nat := 139412964472814313918035

theorem tailTrace_2443552 : CollatzResearch.WordTrace tailWord_2443552 prefixEnd_2443552 139412964472814313918035 := by
  unfold tailWord_2443552
  simp only [CollatzResearch.WordTrace]
  refine ⟨44561831621717952150866455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59415775495623936201155273 44561831621717952150866455)
  ·
    refine ⟨66842747432576928226299683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44561831621717952150866455 66842747432576928226299683)
    ·
      refine ⟨100264121148865392339449525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66842747432576928226299683 100264121148865392339449525)
      ·
        refine ⟨9399761357706130531823393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100264121148865392339449525 9399761357706130531823393)
        ·
          refine ⟨7049821018279597898867545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9399761357706130531823393 7049821018279597898867545)
          ·
            refine ⟨5287365763709698424150659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7049821018279597898867545 5287365763709698424150659)
            ·
              refine ⟨7931048645564547636225989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5287365763709698424150659 7931048645564547636225989)
              ·
                refine ⟨1487071621043352681792373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7931048645564547636225989 1487071621043352681792373)
                ·
                  refine ⟨139412964472814313918035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487071621043352681792373 139412964472814313918035)
                  ·
                    rfl

theorem cell23_2443552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 5].length) (baseStart_2443552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443552 prefixEnd_2443552 := by exact prefixLift 2443552
  have htrace : WordTrace (prefixWord ++ tailWord_2443552) baseStart_2443552 baseEnd_2443552 := by
    simpa [prefixWord, tailWord_2443552, baseEnd_2443552] using wordTrace_append hprefix tailTrace_2443552
  have hstable : (prefixWord ++ tailWord_2443552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443552).length < 2 ^ (prefixWord ++ tailWord_2443552).sum := by decide
  have hdescent : baseEnd_2443552 < baseStart_2443552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443555 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 7, 2]
def baseStart_2443555 : Nat := 118140960795 + 2443555 * 2 ^ 59
def prefixEnd_2443555 : Nat := 4983230072969 + 3 ^ 40 * 2443555 * 2
def baseEnd_2443555 : Nat := 1254718220697292313524801

theorem tailTrace_2443555 : CollatzResearch.WordTrace tailWord_2443555 prefixEnd_2443555 1254718220697292313524801 := by
  unfold tailWord_2443555
  simp only [CollatzResearch.WordTrace]
  refine ⟨89123772662425035814092119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59415848441616690542728079 89123772662425035814092119)
  ·
    refine ⟨133685658993637553721138179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89123772662425035814092119 133685658993637553721138179)
    ·
      refine ⟨200528488490456330581707269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133685658993637553721138179 200528488490456330581707269)
      ·
        refine ⟨37599091591960561984070113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200528488490456330581707269 37599091591960561984070113)
        ·
          refine ⟨28199318693970421488052585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37599091591960561984070113 28199318693970421488052585)
          ·
            refine ⟨21149489020477816116039439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28199318693970421488052585 21149489020477816116039439)
            ·
              refine ⟨31724233530716724174059159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21149489020477816116039439 31724233530716724174059159)
              ·
                refine ⟨47586350296075086261088739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31724233530716724174059159 47586350296075086261088739)
                ·
                  refine ⟨71379525444112629391633109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47586350296075086261088739 71379525444112629391633109)
                  ·
                    refine ⟨1672957627596389751366401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 71379525444112629391633109 1672957627596389751366401)
                    ·
                      refine ⟨1254718220697292313524801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672957627596389751366401 1254718220697292313524801)
                      ·
                        rfl

theorem cell23_2443555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_2443555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443555 prefixEnd_2443555 := by exact prefixLift 2443555
  have htrace : WordTrace (prefixWord ++ tailWord_2443555) baseStart_2443555 baseEnd_2443555 := by
    simpa [prefixWord, tailWord_2443555, baseEnd_2443555] using wordTrace_append hprefix tailTrace_2443555
  have hstable : (prefixWord ++ tailWord_2443555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443555).length < 2 ^ (prefixWord ++ tailWord_2443555).sum := by decide
  have hdescent : baseEnd_2443555 < baseStart_2443555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443582 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2443582 : Nat := 118140960795 + 2443582 * 2 ^ 59
def prefixEnd_2443582 : Nat := 4983230072969 + 3 ^ 40 * 2443582 * 2
def baseEnd_2443582 : Nat := 418244028224987902629059

theorem tailTrace_2443582 : CollatzResearch.WordTrace tailWord_2443582 prefixEnd_2443582 418244028224987902629059 := by
  unfold tailWord_2443582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140594679165902428165625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59416504955551479616883333 11140594679165902428165625)
  ·
    refine ⟨8355446009374426821124219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11140594679165902428165625 8355446009374426821124219)
    ·
      refine ⟨12533169014061640231686329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8355446009374426821124219 12533169014061640231686329)
      ·
        refine ⟨9399876760546230173764747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12533169014061640231686329 9399876760546230173764747)
        ·
          refine ⟨14099815140819345260647121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9399876760546230173764747 14099815140819345260647121)
          ·
            refine ⟨10574861355614508945485341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14099815140819345260647121 10574861355614508945485341)
            ·
              refine ⟨3965573008355440854557003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10574861355614508945485341 3965573008355440854557003)
              ·
                refine ⟨5948359512533161281835505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3965573008355440854557003 5948359512533161281835505)
                ·
                  refine ⟨4461269634399870961376629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5948359512533161281835505 4461269634399870961376629)
                  ·
                    refine ⟨418244028224987902629059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4461269634399870961376629 418244028224987902629059)
                    ·
                      rfl

theorem cell23_2443582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2443582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443582 prefixEnd_2443582 := by exact prefixLift 2443582
  have htrace : WordTrace (prefixWord ++ tailWord_2443582) baseStart_2443582 baseEnd_2443582 := by
    simpa [prefixWord, tailWord_2443582, baseEnd_2443582] using wordTrace_append hprefix tailTrace_2443582
  have hstable : (prefixWord ++ tailWord_2443582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443582).length < 2 ^ (prefixWord ++ tailWord_2443582).sum := by decide
  have hdescent : baseEnd_2443582 < baseStart_2443582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443602 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_2443602 : Nat := 118140960795 + 2443602 * 2 ^ 59
def prefixEnd_2443602 : Nat := 4983230072969 + 3 ^ 40 * 2443602 * 2
def baseEnd_2443602 : Nat := 1254742354288053629637085

theorem tailTrace_2443602 : CollatzResearch.WordTrace tailWord_2443602 prefixEnd_2443602 1254742354288053629637085 := by
  unfold tailWord_2443602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22281371723313690710263265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59416991262169841894035373 22281371723313690710263265)
  ·
    refine ⟨16711028792485268032697449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22281371723313690710263265 16711028792485268032697449)
    ·
      refine ⟨12533271594363951024523087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16711028792485268032697449 12533271594363951024523087)
      ·
        refine ⟨18799907391545926536784631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12533271594363951024523087 18799907391545926536784631)
        ·
          refine ⟨28199861087318889805176947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18799907391545926536784631 28199861087318889805176947)
          ·
            refine ⟨42299791630978334707765421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28199861087318889805176947 42299791630978334707765421)
            ·
              refine ⟨15862421861616875515412033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42299791630978334707765421 15862421861616875515412033)
              ·
                refine ⟨11896816396212656636559025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15862421861616875515412033 11896816396212656636559025)
                ·
                  refine ⟨8922612297159492477419269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11896816396212656636559025 8922612297159492477419269)
                  ·
                    refine ⟨1672989805717404839516113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8922612297159492477419269 1672989805717404839516113)
                    ·
                      refine ⟨1254742354288053629637085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672989805717404839516113 1254742354288053629637085)
                      ·
                        rfl

theorem cell23_2443602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_2443602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443602 prefixEnd_2443602 := by exact prefixLift 2443602
  have htrace : WordTrace (prefixWord ++ tailWord_2443602) baseStart_2443602 baseEnd_2443602 := by
    simpa [prefixWord, tailWord_2443602, baseEnd_2443602] using wordTrace_append hprefix tailTrace_2443602
  have hstable : (prefixWord ++ tailWord_2443602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443602).length < 2 ^ (prefixWord ++ tailWord_2443602).sum := by decide
  have hdescent : baseEnd_2443602 < baseStart_2443602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443614 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_2443614 : Nat := 118140960795 + 2443614 * 2 ^ 59
def prefixEnd_2443614 : Nat := 4983230072969 + 3 ^ 40 * 2443614 * 2
def baseEnd_2443614 : Nat := 1254748516055907582687031

theorem tailTrace_2443614 : CollatzResearch.WordTrace tailWord_2443614 prefixEnd_2443614 1254748516055907582687031 := by
  unfold tailWord_2443614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140740571151411111311237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59417283046140859260326597 11140740571151411111311237)
  ·
    refine ⟨2088888857090889583370857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11140740571151411111311237 2088888857090889583370857)
    ·
      refine ⟨1566666642818167187528143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2088888857090889583370857 1566666642818167187528143)
      ·
        refine ⟨2349999964227250781292215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566666642818167187528143 2349999964227250781292215)
        ·
          refine ⟨3524999946340876171938323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349999964227250781292215 3524999946340876171938323)
          ·
            refine ⟨5287499919511314257907485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524999946340876171938323 5287499919511314257907485)
            ·
              refine ⟨1982812469816742846715307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5287499919511314257907485 1982812469816742846715307)
              ·
                refine ⟨2974218704725114270072961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982812469816742846715307 2974218704725114270072961)
                ·
                  refine ⟨2230664028543835702554721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974218704725114270072961 2230664028543835702554721)
                  ·
                    refine ⟨1672998021407876776916041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2230664028543835702554721 1672998021407876776916041)
                    ·
                      refine ⟨1254748516055907582687031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1672998021407876776916041 1254748516055907582687031)
                      ·
                        rfl

theorem cell23_2443614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_2443614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443614 prefixEnd_2443614 := by exact prefixLift 2443614
  have htrace : WordTrace (prefixWord ++ tailWord_2443614) baseStart_2443614 baseEnd_2443614 := by
    simpa [prefixWord, tailWord_2443614, baseEnd_2443614] using wordTrace_append hprefix tailTrace_2443614
  have hstable : (prefixWord ++ tailWord_2443614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443614).length < 2 ^ (prefixWord ++ tailWord_2443614).sum := by decide
  have hdescent : baseEnd_2443614 < baseStart_2443614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443685 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_2443685 : Nat := 118140960795 + 2443685 * 2 ^ 59
def prefixEnd_2443685 : Nat := 4983230072969 + 3 ^ 40 * 2443685 * 2
def baseEnd_2443685 : Nat := 418261657727458934966401

theorem tailTrace_2443685 : CollatzResearch.WordTrace tailWord_2443685 prefixEnd_2443685 418261657727458934966401 := by
  unfold tailWord_2443685
  simp only [CollatzResearch.WordTrace]
  refine ⟨89128514151954068016324509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59419009434636045344216339 89128514151954068016324509)
  ·
    refine ⟨33423192806982775506121691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89128514151954068016324509 33423192806982775506121691)
    ·
      refine ⟨50134789210474163259182537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33423192806982775506121691 50134789210474163259182537)
      ·
        refine ⟨37601091907855622444386903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50134789210474163259182537 37601091907855622444386903)
        ·
          refine ⟨56401637861783433666580355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37601091907855622444386903 56401637861783433666580355)
          ·
            refine ⟨84602456792675150499870533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56401637861783433666580355 84602456792675150499870533)
            ·
              refine ⟨15862960648626590718725725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84602456792675150499870533 15862960648626590718725725)
              ·
                refine ⟨5948610243234971519522147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15862960648626590718725725 5948610243234971519522147)
                ·
                  refine ⟨8922915364852457279283221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5948610243234971519522147 8922915364852457279283221)
                  ·
                    refine ⟨418261657727458934966401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8922915364852457279283221 418261657727458934966401)
                    ·
                      rfl

theorem cell23_2443685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_2443685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443685 prefixEnd_2443685 := by exact prefixLift 2443685
  have htrace : WordTrace (prefixWord ++ tailWord_2443685) baseStart_2443685 baseEnd_2443685 := by
    simpa [prefixWord, tailWord_2443685, baseEnd_2443685] using wordTrace_append hprefix tailTrace_2443685
  have hstable : (prefixWord ++ tailWord_2443685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443685).length < 2 ^ (prefixWord ++ tailWord_2443685).sum := by decide
  have hdescent : baseEnd_2443685 < baseStart_2443685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443719 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 2, 4]
def baseStart_2443719 : Nat := 118140960795 + 2443719 * 2 ^ 59
def prefixEnd_2443719 : Nat := 4983230072969 + 3 ^ 40 * 2443719 * 2
def baseEnd_2443719 : Nat := 418267477174876557291349

theorem tailTrace_2443719 : CollatzResearch.WordTrace tailWord_2443719 prefixEnd_2443719 418267477174876557291349 := by
  unfold tailWord_2443719
  simp only [CollatzResearch.WordTrace]
  refine ⟨89129754233830891823062211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59419836155887261215374807 89129754233830891823062211)
  ·
    refine ⟨133694631350746337734593317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89129754233830891823062211 133694631350746337734593317)
    ·
      refine ⟨25067743378264938325236247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133694631350746337734593317 25067743378264938325236247)
      ·
        refine ⟨37601615067397407487854371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25067743378264938325236247 37601615067397407487854371)
        ·
          refine ⟨56402422601096111231781557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37601615067397407487854371 56402422601096111231781557)
          ·
            refine ⟨5287727118852760427979521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56402422601096111231781557 5287727118852760427979521)
            ·
              refine ⟨3965795339139570320984641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5287727118852760427979521 3965795339139570320984641)
              ·
                refine ⟨2974346504354677740738481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3965795339139570320984641 2974346504354677740738481)
                ·
                  refine ⟨2230759878266008305553861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974346504354677740738481 2230759878266008305553861)
                  ·
                    refine ⟨418267477174876557291349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230759878266008305553861 418267477174876557291349)
                    ·
                      rfl

theorem cell23_2443719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_2443719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443719 prefixEnd_2443719 := by exact prefixLift 2443719
  have htrace : WordTrace (prefixWord ++ tailWord_2443719) baseStart_2443719 baseEnd_2443719 := by
    simpa [prefixWord, tailWord_2443719, baseEnd_2443719] using wordTrace_append hprefix tailTrace_2443719
  have hstable : (prefixWord ++ tailWord_2443719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443719).length < 2 ^ (prefixWord ++ tailWord_2443719).sum := by decide
  have hdescent : baseEnd_2443719 < baseStart_2443719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443732 : List Nat := [2, 4, 1, 2, 2, 1, 3, 8]
def baseStart_2443732 : Nat := 118140960795 + 2443732 * 2 ^ 59
def prefixEnd_2443732 : Nat := 4983230072969 + 3 ^ 40 * 2443732 * 2
def baseEnd_2443732 : Nat := 46474411361968078555981

theorem tailTrace_2443732 : CollatzResearch.WordTrace tailWord_2443732 prefixEnd_2443732 46474411361968078555981 := by
  unfold tailWord_2443732
  simp only [CollatzResearch.WordTrace]
  refine ⟨44565114191391897521642725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59420152255189196695523633 44565114191391897521642725)
  ·
    refine ⟨8355958910885980785308011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44565114191391897521642725 8355958910885980785308011)
    ·
      refine ⟨12533938366328971177962017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8355958910885980785308011 12533938366328971177962017)
      ·
        refine ⟨9400453774746728383471513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12533938366328971177962017 9400453774746728383471513)
        ·
          refine ⟨7050340331060046287603635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9400453774746728383471513 7050340331060046287603635)
          ·
            refine ⟨10575510496590069431405453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7050340331060046287603635 10575510496590069431405453)
            ·
              refine ⟨3965816436221276036777045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10575510496590069431405453 3965816436221276036777045)
              ·
                refine ⟨46474411361968078555981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3965816436221276036777045 46474411361968078555981)
                ·
                  rfl

theorem cell23_2443732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 8].length) (baseStart_2443732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443732 prefixEnd_2443732 := by exact prefixLift 2443732
  have htrace : WordTrace (prefixWord ++ tailWord_2443732) baseStart_2443732 baseEnd_2443732 := by
    simpa [prefixWord, tailWord_2443732, baseEnd_2443732] using wordTrace_append hprefix tailTrace_2443732
  have hstable : (prefixWord ++ tailWord_2443732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443732).length < 2 ^ (prefixWord ++ tailWord_2443732).sum := by decide
  have hdescent : baseEnd_2443732 < baseStart_2443732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443745 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2443745 : Nat := 118140960795 + 2443745 * 2 ^ 59
def prefixEnd_2443745 : Nat := 4983230072969 + 3 ^ 40 * 2443745 * 2
def baseEnd_2443745 : Nat := 418271927340548856716309

theorem tailTrace_2443745 : CollatzResearch.WordTrace tailWord_2443745 prefixEnd_2443745 418271927340548856716309 := by
  unfold tailWord_2443745
  simp only [CollatzResearch.WordTrace]
  refine ⟨89130702531736698263508689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59420468354491132175672459 89130702531736698263508689)
  ·
    refine ⟨66848026898802523697631517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89130702531736698263508689 66848026898802523697631517)
    ·
      refine ⟨25068010087050946386611819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66848026898802523697631517 25068010087050946386611819)
      ·
        refine ⟨37602015130576419579917729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25068010087050946386611819 37602015130576419579917729)
        ·
          refine ⟨28201511347932314684938297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37602015130576419579917729 28201511347932314684938297)
          ·
            refine ⟨21151133510949236013703723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28201511347932314684938297 21151133510949236013703723)
            ·
              refine ⟨31726700266423854020555585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21151133510949236013703723 31726700266423854020555585)
              ·
                refine ⟨23795025199817890515416689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31726700266423854020555585 23795025199817890515416689)
                ·
                  refine ⟨17846268899863417886562517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23795025199817890515416689 17846268899863417886562517)
                  ·
                    refine ⟨418271927340548856716309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17846268899863417886562517 418271927340548856716309)
                    ·
                      rfl

theorem cell23_2443745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2443745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443745 prefixEnd_2443745 := by exact prefixLift 2443745
  have htrace : WordTrace (prefixWord ++ tailWord_2443745) baseStart_2443745 baseEnd_2443745 := by
    simpa [prefixWord, tailWord_2443745, baseEnd_2443745] using wordTrace_append hprefix tailTrace_2443745
  have hstable : (prefixWord ++ tailWord_2443745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443745).length < 2 ^ (prefixWord ++ tailWord_2443745).sum := by decide
  have hdescent : baseEnd_2443745 < baseStart_2443745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443749 : List Nat := [1, 3, 1, 5, 2, 1, 3, 7]
def baseStart_2443749 : Nat := 118140960795 + 2443749 * 2 ^ 59
def prefixEnd_2443749 : Nat := 4983230072969 + 3 ^ 40 * 2443749 * 2
def baseEnd_2443749 : Nat := 46474734664602390907367

theorem tailTrace_2443749 : CollatzResearch.WordTrace tailWord_2443749 prefixEnd_2443749 46474734664602390907367 := by
  unfold tailWord_2443749
  simp only [CollatzResearch.WordTrace]
  refine ⟨89130848423722206946654301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59420565615814804631102867 89130848423722206946654301)
  ·
    refine ⟨33424068158895827604995363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89130848423722206946654301 33424068158895827604995363)
    ·
      refine ⟨50136102238343741407493045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33424068158895827604995363 50136102238343741407493045)
      ·
        refine ⟨4700259584844725756952473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50136102238343741407493045 4700259584844725756952473)
        ·
          refine ⟨3525194688633544317714355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4700259584844725756952473 3525194688633544317714355)
          ·
            refine ⟨5287792032950316476571533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3525194688633544317714355 5287792032950316476571533)
            ·
              refine ⟨1982922012356368678714325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5287792032950316476571533 1982922012356368678714325)
              ·
                refine ⟨46474734664602390907367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1982922012356368678714325 46474734664602390907367)
                ·
                  rfl

theorem cell23_2443749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 7].length) (baseStart_2443749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443749 prefixEnd_2443749 := by exact prefixLift 2443749
  have htrace : WordTrace (prefixWord ++ tailWord_2443749) baseStart_2443749 baseEnd_2443749 := by
    simpa [prefixWord, tailWord_2443749, baseEnd_2443749] using wordTrace_append hprefix tailTrace_2443749
  have hstable : (prefixWord ++ tailWord_2443749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443749).length < 2 ^ (prefixWord ++ tailWord_2443749).sum := by decide
  have hdescent : baseEnd_2443749 < baseStart_2443749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443755 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5]
def baseStart_2443755 : Nat := 118140960795 + 2443755 * 2 ^ 59
def prefixEnd_2443755 : Nat := 4983230072969 + 3 ^ 40 * 2443755 * 2
def baseEnd_2443755 : Nat := 1254820916828191531023881

theorem tailTrace_2443755 : CollatzResearch.WordTrace tailWord_2443755 prefixEnd_2443755 1254820916828191531023881 := by
  unfold tailWord_2443755
  simp only [CollatzResearch.WordTrace]
  refine ⟨89131067261700469971372719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59420711507800313314248479 89131067261700469971372719)
  ·
    refine ⟨133696600892550704957059079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89131067261700469971372719 133696600892550704957059079)
    ·
      refine ⟨200544901338826057435588619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133696600892550704957059079 200544901338826057435588619)
      ·
        refine ⟨300817352008239086153382929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200544901338826057435588619 300817352008239086153382929)
        ·
          refine ⟨225613014006179314615037197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300817352008239086153382929 225613014006179314615037197)
          ·
            refine ⟨84604880252317242980638949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225613014006179314615037197 84604880252317242980638949)
            ·
              refine ⟨15863415047309483058869803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84604880252317242980638949 15863415047309483058869803)
              ·
                refine ⟨23795122570964224588304705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15863415047309483058869803 23795122570964224588304705)
                ·
                  refine ⟨17846341928223168441228529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23795122570964224588304705 17846341928223168441228529)
                  ·
                    refine ⟨13384756446167376330921397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17846341928223168441228529 13384756446167376330921397)
                    ·
                      refine ⟨1254820916828191531023881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13384756446167376330921397 1254820916828191531023881)
                      ·
                        rfl

theorem cell23_2443755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_2443755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443755 prefixEnd_2443755 := by exact prefixLift 2443755
  have htrace : WordTrace (prefixWord ++ tailWord_2443755) baseStart_2443755 baseEnd_2443755 := by
    simpa [prefixWord, tailWord_2443755, baseEnd_2443755] using wordTrace_append hprefix tailTrace_2443755
  have hstable : (prefixWord ++ tailWord_2443755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443755).length < 2 ^ (prefixWord ++ tailWord_2443755).sum := by decide
  have hdescent : baseEnd_2443755 < baseStart_2443755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443775 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 4, 6]
def baseStart_2443775 : Nat := 118140960795 + 2443775 * 2 ^ 59
def prefixEnd_2443775 : Nat := 4983230072969 + 3 ^ 40 * 2443775 * 2
def baseEnd_2443775 : Nat := 418277062147093817591263

theorem tailTrace_2443775 : CollatzResearch.WordTrace tailWord_2443775 prefixEnd_2443775 418277062147093817591263 := by
  unfold tailWord_2443775
  simp only [CollatzResearch.WordTrace]
  refine ⟨89131796721628013387100779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59421197814418675591400519 89131796721628013387100779)
  ·
    refine ⟨133697695082442020080651169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89131796721628013387100779 133697695082442020080651169)
    ·
      refine ⟨100273271311831515060488377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133697695082442020080651169 100273271311831515060488377)
      ·
        refine ⟨75204953483873636295366283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100273271311831515060488377 75204953483873636295366283)
        ·
          refine ⟨112807430225810454443049425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75204953483873636295366283 112807430225810454443049425)
          ·
            refine ⟨84605572669357840832287069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112807430225810454443049425 84605572669357840832287069)
            ·
              refine ⟨31727089751009190312107651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84605572669357840832287069 31727089751009190312107651)
              ·
                refine ⟨47590634626513785468161477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31727089751009190312107651 47590634626513785468161477)
                ·
                  refine ⟨8923243992471334775280277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47590634626513785468161477 8923243992471334775280277)
                  ·
                    refine ⟨418277062147093817591263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8923243992471334775280277 418277062147093817591263)
                    ·
                      rfl

theorem cell23_2443775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_2443775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443775 prefixEnd_2443775 := by exact prefixLift 2443775
  have htrace : WordTrace (prefixWord ++ tailWord_2443775) baseStart_2443775 baseEnd_2443775 := by
    simpa [prefixWord, tailWord_2443775, baseEnd_2443775] using wordTrace_append hprefix tailTrace_2443775
  have hstable : (prefixWord ++ tailWord_2443775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443775).length < 2 ^ (prefixWord ++ tailWord_2443775).sum := by decide
  have hdescent : baseEnd_2443775 < baseStart_2443775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443785 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_2443785 : Nat := 118140960795 + 2443785 * 2 ^ 59
def prefixEnd_2443785 : Nat := 4983230072969 + 3 ^ 40 * 2443785 * 2
def baseEnd_2443785 : Nat := 1254836321247826413648743

theorem tailTrace_2443785 : CollatzResearch.WordTrace tailWord_2443785 prefixEnd_2443785 1254836321247826413648743 := by
  unfold tailWord_2443785
  simp only [CollatzResearch.WordTrace]
  refine ⟨89132161451591785094964809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59421440967727856729976539 89132161451591785094964809)
  ·
    refine ⟨66849121088693838821223607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89132161451591785094964809 66849121088693838821223607)
    ·
      refine ⟨100273681633040758231835411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66849121088693838821223607 100273681633040758231835411)
      ·
        refine ⟨150410522449561137347753117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100273681633040758231835411 150410522449561137347753117)
        ·
          refine ⟨56403945918585426505407419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150410522449561137347753117 56403945918585426505407419)
          ·
            refine ⟨84605918877878139758111129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56403945918585426505407419 84605918877878139758111129)
            ·
              refine ⟨63454439158408604818583347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84605918877878139758111129 63454439158408604818583347)
              ·
                refine ⟨95181658737612907227875021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63454439158408604818583347 95181658737612907227875021)
                ·
                  refine ⟨35693122026604840210453133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95181658737612907227875021 35693122026604840210453133)
                  ·
                    refine ⟨13384920759976815078919925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35693122026604840210453133 13384920759976815078919925)
                    ·
                      refine ⟨1254836321247826413648743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13384920759976815078919925 1254836321247826413648743)
                      ·
                        rfl

theorem cell23_2443785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_2443785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443785 prefixEnd_2443785 := by exact prefixLift 2443785
  have htrace : WordTrace (prefixWord ++ tailWord_2443785) baseStart_2443785 baseEnd_2443785 := by
    simpa [prefixWord, tailWord_2443785, baseEnd_2443785] using wordTrace_append hprefix tailTrace_2443785
  have hstable : (prefixWord ++ tailWord_2443785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443785).length < 2 ^ (prefixWord ++ tailWord_2443785).sum := by decide
  have hdescent : baseEnd_2443785 < baseStart_2443785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443802 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_2443802 : Nat := 118140960795 + 2443802 * 2 ^ 59
def prefixEnd_2443802 : Nat := 4983230072969 + 3 ^ 40 * 2443802 * 2
def baseEnd_2443802 : Nat := 1254845050418952847136165

theorem tailTrace_2443802 : CollatzResearch.WordTrace tailWord_2443802 prefixEnd_2443802 1254845050418952847136165 := by
  unfold tailWord_2443802
  simp only [CollatzResearch.WordTrace]
  refine ⟨22283195373132549249583415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59421854328353464665555773 22283195373132549249583415)
  ·
    refine ⟨33424793059698823874375123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22283195373132549249583415 33424793059698823874375123)
    ·
      refine ⟨50137189589548235811562685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33424793059698823874375123 50137189589548235811562685)
      ·
        refine ⟨18801446096080588429336007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50137189589548235811562685 18801446096080588429336007)
        ·
          refine ⟨28202169144120882644004011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18801446096080588429336007 28202169144120882644004011)
          ·
            refine ⟨42303253716181323966006017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28202169144120882644004011 42303253716181323966006017)
            ·
              refine ⟨31727440287135992974504513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42303253716181323966006017 31727440287135992974504513)
              ·
                refine ⟨23795580215351994730878385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31727440287135992974504513 23795580215351994730878385)
                ·
                  refine ⟨17846685161513996048158789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23795580215351994730878385 17846685161513996048158789)
                  ·
                    refine ⟨3346253467783874259029773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17846685161513996048158789 3346253467783874259029773)
                    ·
                      refine ⟨1254845050418952847136165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3346253467783874259029773 1254845050418952847136165)
                      ·
                        rfl

theorem cell23_2443802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_2443802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443802 prefixEnd_2443802 := by exact prefixLift 2443802
  have htrace : WordTrace (prefixWord ++ tailWord_2443802) baseStart_2443802 baseEnd_2443802 := by
    simpa [prefixWord, tailWord_2443802, baseEnd_2443802] using wordTrace_append hprefix tailTrace_2443802
  have hstable : (prefixWord ++ tailWord_2443802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443802).length < 2 ^ (prefixWord ++ tailWord_2443802).sum := by decide
  have hdescent : baseEnd_2443802 < baseStart_2443802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443844 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2443844 : Nat := 118140960795 + 2443844 * 2 ^ 59
def prefixEnd_2443844 : Nat := 4983230072969 + 3 ^ 40 * 2443844 * 2
def baseEnd_2443844 : Nat := 1254866616606441682810973

theorem tailTrace_2443844 : CollatzResearch.WordTrace tailWord_2443844 prefixEnd_2443844 1254866616606441682810973 := by
  unfold tailWord_2443844
  simp only [CollatzResearch.WordTrace]
  refine ⟨44567156679189019085681293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59422875572252025447575057 44567156679189019085681293)
  ·
    refine ⟨16712683754695882157130485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44567156679189019085681293 16712683754695882157130485)
    ·
      refine ⟨1566814102002738952230983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16712683754695882157130485 1566814102002738952230983)
      ·
        refine ⟨2350221153004108428346475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566814102002738952230983 2350221153004108428346475)
        ·
          refine ⟨3525331729506162642519713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350221153004108428346475 3525331729506162642519713)
          ·
            refine ⟨2643998797129621981889785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525331729506162642519713 2643998797129621981889785)
            ·
              refine ⟨1982999097847216486417339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2643998797129621981889785 1982999097847216486417339)
              ·
                refine ⟨2974498646770824729626009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982999097847216486417339 2974498646770824729626009)
                ·
                  refine ⟨2230873985078118547219507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974498646770824729626009 2230873985078118547219507)
                  ·
                    refine ⟨3346310977617177820829261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2230873985078118547219507 3346310977617177820829261)
                    ·
                      refine ⟨1254866616606441682810973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3346310977617177820829261 1254866616606441682810973)
                      ·
                        rfl

theorem cell23_2443844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2443844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443844 prefixEnd_2443844 := by exact prefixLift 2443844
  have htrace : WordTrace (prefixWord ++ tailWord_2443844) baseStart_2443844 baseEnd_2443844 := by
    simpa [prefixWord, tailWord_2443844, baseEnd_2443844] using wordTrace_append hprefix tailTrace_2443844
  have hstable : (prefixWord ++ tailWord_2443844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443844).length < 2 ^ (prefixWord ++ tailWord_2443844).sum := by decide
  have hdescent : baseEnd_2443844 < baseStart_2443844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443850 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_2443850 : Nat := 118140960795 + 2443850 * 2 ^ 59
def prefixEnd_2443850 : Nat := 4983230072969 + 3 ^ 40 * 2443850 * 2
def baseEnd_2443850 : Nat := 1254869697490368659335945

theorem tailTrace_2443850 : CollatzResearch.WordTrace tailWord_2443850 prefixEnd_2443850 1254869697490368659335945 := by
  unfold tailWord_2443850
  simp only [CollatzResearch.WordTrace]
  refine ⟨22283633049089075299020251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59423021464237534130720669 22283633049089075299020251)
  ·
    refine ⟨33425449573633612948530377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22283633049089075299020251 33425449573633612948530377)
    ·
      refine ⟨25069087180225209711397783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33425449573633612948530377 25069087180225209711397783)
      ·
        refine ⟨37603630770337814567096675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25069087180225209711397783 37603630770337814567096675)
        ·
          refine ⟨56405446155506721850645013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37603630770337814567096675 56405446155506721850645013)
          ·
            refine ⟨2644005288539377586748985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56405446155506721850645013 2644005288539377586748985)
            ·
              refine ⟨1983003966404533190061739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644005288539377586748985 1983003966404533190061739)
              ·
                refine ⟨2974505949606799785092609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983003966404533190061739 2974505949606799785092609)
                ·
                  refine ⟨2230879462205099838819457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974505949606799785092609 2230879462205099838819457)
                  ·
                    refine ⟨1673159596653824879114593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2230879462205099838819457 1673159596653824879114593)
                    ·
                      refine ⟨1254869697490368659335945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673159596653824879114593 1254869697490368659335945)
                      ·
                        rfl

theorem cell23_2443850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_2443850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443850 prefixEnd_2443850 := by exact prefixLift 2443850
  have htrace : WordTrace (prefixWord ++ tailWord_2443850) baseStart_2443850 baseEnd_2443850 := by
    simpa [prefixWord, tailWord_2443850, baseEnd_2443850] using wordTrace_append hprefix tailTrace_2443850
  have hstable : (prefixWord ++ tailWord_2443850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443850).length < 2 ^ (prefixWord ++ tailWord_2443850).sum := by decide
  have hdescent : baseEnd_2443850 < baseStart_2443850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443852 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_2443852 : Nat := 118140960795 + 2443852 * 2 ^ 59
def prefixEnd_2443852 : Nat := 4983230072969 + 3 ^ 40 * 2443852 * 2
def baseEnd_2443852 : Nat := 418290241483892550503645

theorem tailTrace_2443852 : CollatzResearch.WordTrace tailWord_2443852 prefixEnd_2443852 418290241483892550503645 := by
  unfold tailWord_2443852
  simp only [CollatzResearch.WordTrace]
  refine ⟨44567302571174527768826905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59423070094899370358435873 44567302571174527768826905)
  ·
    refine ⟨33425476928380895826620179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44567302571174527768826905 33425476928380895826620179)
    ·
      refine ⟨50138215392571343739930269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33425476928380895826620179 50138215392571343739930269)
      ·
        refine ⟨18801830772214253902473851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50138215392571343739930269 18801830772214253902473851)
        ·
          refine ⟨28202746158321380853710777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18801830772214253902473851 28202746158321380853710777)
          ·
            refine ⟨21152059618741035640283083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28202746158321380853710777 21152059618741035640283083)
            ·
              refine ⟨31728089428111553460424625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21152059618741035640283083 31728089428111553460424625)
              ·
                refine ⟨23796067071083665095318469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31728089428111553460424625 23796067071083665095318469)
                ·
                  refine ⟨4461762575828187205372213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23796067071083665095318469 4461762575828187205372213)
                  ·
                    refine ⟨418290241483892550503645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4461762575828187205372213 418290241483892550503645)
                    ·
                      rfl

theorem cell23_2443852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_2443852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443852 prefixEnd_2443852 := by exact prefixLift 2443852
  have htrace : WordTrace (prefixWord ++ tailWord_2443852) baseStart_2443852 baseEnd_2443852 := by
    simpa [prefixWord, tailWord_2443852, baseEnd_2443852] using wordTrace_append hprefix tailTrace_2443852
  have hstable : (prefixWord ++ tailWord_2443852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443852).length < 2 ^ (prefixWord ++ tailWord_2443852).sum := by decide
  have hdescent : baseEnd_2443852 < baseStart_2443852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443872 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2443872 : Nat := 118140960795 + 2443872 * 2 ^ 59
def prefixEnd_2443872 : Nat := 4983230072969 + 3 ^ 40 * 2443872 * 2
def baseEnd_2443872 : Nat := 1254880994064767573260843

theorem tailTrace_2443872 : CollatzResearch.WordTrace tailWord_2443872 prefixEnd_2443872 1254880994064767573260843 := by
  unfold tailWord_2443872
  simp only [CollatzResearch.WordTrace]
  refine ⟨44567667301138299476690935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59423556401517732635587913 44567667301138299476690935)
  ·
    refine ⟨66851500951707449215036403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44567667301138299476690935 66851500951707449215036403)
    ·
      refine ⟨100277251427561173822554605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66851500951707449215036403 100277251427561173822554605)
      ·
        refine ⟨37603969285335440183457977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100277251427561173822554605 37603969285335440183457977)
        ·
          refine ⟨28202976964001580137593483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37603969285335440183457977 28202976964001580137593483)
          ·
            refine ⟨42304465446002370206390225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28202976964001580137593483 42304465446002370206390225)
            ·
              refine ⟨31728349084501777654792669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42304465446002370206390225 31728349084501777654792669)
              ·
                refine ⟨11898130906688166620547251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31728349084501777654792669 11898130906688166620547251)
                ·
                  refine ⟨17847196360032249930820877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11898130906688166620547251 17847196360032249930820877)
                  ·
                    refine ⟨6692698635012093724057829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17847196360032249930820877 6692698635012093724057829)
                    ·
                      refine ⟨1254880994064767573260843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6692698635012093724057829 1254880994064767573260843)
                      ·
                        rfl

theorem cell23_2443872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2443872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443872 prefixEnd_2443872 := by exact prefixLift 2443872
  have htrace : WordTrace (prefixWord ++ tailWord_2443872) baseStart_2443872 baseEnd_2443872 := by
    simpa [prefixWord, tailWord_2443872, baseEnd_2443872] using wordTrace_append hprefix tailTrace_2443872
  have hstable : (prefixWord ++ tailWord_2443872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443872).length < 2 ^ (prefixWord ++ tailWord_2443872).sum := by decide
  have hdescent : baseEnd_2443872 < baseStart_2443872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443890 : List Nat := [3, 2, 1, 2, 5, 1, 2, 2, 5]
def baseStart_2443890 : Nat := 118140960795 + 2443890 * 2 ^ 59
def prefixEnd_2443890 : Nat := 4983230072969 + 3 ^ 40 * 2443890 * 2
def baseEnd_2443890 : Nat := 139432248524060944759529

theorem tailTrace_2443890 : CollatzResearch.WordTrace tailWord_2443890 prefixEnd_2443890 139432248524060944759529 := by
  unfold tailWord_2443890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22283997779052847006884281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59423994077474258685024749 22283997779052847006884281)
  ·
    refine ⟨16712998334289635255163211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22283997779052847006884281 16712998334289635255163211)
    ·
      refine ⟨25069497501434452882744817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16712998334289635255163211 25069497501434452882744817)
      ·
        refine ⟨18802123126075839662058613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25069497501434452882744817 18802123126075839662058613)
        ·
          refine ⟨1762699043069609968317995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18802123126075839662058613 1762699043069609968317995)
          ·
            refine ⟨2644048564604414952476993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762699043069609968317995 2644048564604414952476993)
            ·
              refine ⟨1983036423453311214357745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644048564604414952476993 1983036423453311214357745)
              ·
                refine ⟨1487277317589983410768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983036423453311214357745 1487277317589983410768309)
                ·
                  refine ⟨139432248524060944759529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487277317589983410768309 139432248524060944759529)
                  ·
                    rfl

theorem cell23_2443890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_2443890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443890 prefixEnd_2443890 := by exact prefixLift 2443890
  have htrace : WordTrace (prefixWord ++ tailWord_2443890) baseStart_2443890 baseEnd_2443890 := by
    simpa [prefixWord, tailWord_2443890, baseEnd_2443890] using wordTrace_append hprefix tailTrace_2443890
  have hstable : (prefixWord ++ tailWord_2443890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443890).length < 2 ^ (prefixWord ++ tailWord_2443890).sum := by decide
  have hdescent : baseEnd_2443890 < baseStart_2443890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443949 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_2443949 : Nat := 118140960795 + 2443949 * 2 ^ 59
def prefixEnd_2443949 : Nat := 4983230072969 + 3 ^ 40 * 2443949 * 2
def baseEnd_2443949 : Nat := 1254920532075163771997989

theorem tailTrace_2443949 : CollatzResearch.WordTrace tailWord_2443949 prefixEnd_2443949 1254920532075163771997989 := by
  unfold tailWord_2443949
  simp only [CollatzResearch.WordTrace]
  refine ⟨89138143022997641103934901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59425428681998427402623267 89138143022997641103934901)
  ·
    refine ⟨8356700908406028853493897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89138143022997641103934901 8356700908406028853493897)
    ·
      refine ⟨6267525681304521640120423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8356700908406028853493897 6267525681304521640120423)
      ·
        refine ⟨9401288521956782460180635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6267525681304521640120423 9401288521956782460180635)
        ·
          refine ⟨14101932782935173690270953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9401288521956782460180635 14101932782935173690270953)
          ·
            refine ⟨10576449587201380267703215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14101932782935173690270953 10576449587201380267703215)
            ·
              refine ⟨15864674380802070401554823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10576449587201380267703215 15864674380802070401554823)
              ·
                refine ⟨23797011571203105602332235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15864674380802070401554823 23797011571203105602332235)
                ·
                  refine ⟨35695517356804658403498353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23797011571203105602332235 35695517356804658403498353)
                  ·
                    refine ⟨26771638017603493802623765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35695517356804658403498353 26771638017603493802623765)
                    ·
                      refine ⟨1254920532075163771997989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26771638017603493802623765 1254920532075163771997989)
                      ·
                        rfl

theorem cell23_2443949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_2443949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443949 prefixEnd_2443949 := by exact prefixLift 2443949
  have htrace : WordTrace (prefixWord ++ tailWord_2443949) baseStart_2443949 baseEnd_2443949 := by
    simpa [prefixWord, tailWord_2443949, baseEnd_2443949] using wordTrace_append hprefix tailTrace_2443949
  have hstable : (prefixWord ++ tailWord_2443949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443949).length < 2 ^ (prefixWord ++ tailWord_2443949).sum := by decide
  have hdescent : baseEnd_2443949 < baseStart_2443949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443950 : List Nat := [4, 1, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2443950 : Nat := 118140960795 + 2443950 * 2 ^ 59
def prefixEnd_2443950 : Nat := 4983230072969 + 3 ^ 40 * 2443950 * 2
def baseEnd_2443950 : Nat := 418307015185272756028495

theorem tailTrace_2443950 : CollatzResearch.WordTrace tailWord_2443950 prefixEnd_2443950 418307015185272756028495 := by
  unfold tailWord_2443950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142272436999252284340163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59425452997329345516480869 11142272436999252284340163)
  ·
    refine ⟨16713408655498878426510245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11142272436999252284340163 16713408655498878426510245)
    ·
      refine ⟨3133764122906039704970671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16713408655498878426510245 3133764122906039704970671)
      ·
        refine ⟨4700646184359059557456007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133764122906039704970671 4700646184359059557456007)
        ·
          refine ⟨7050969276538589336184011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4700646184359059557456007 7050969276538589336184011)
          ·
            refine ⟨10576453914807884004276017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7050969276538589336184011 10576453914807884004276017)
            ·
              refine ⟨7932340436105913003207013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10576453914807884004276017 7932340436105913003207013)
              ·
                refine ⟨1487313831769858688101315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7932340436105913003207013 1487313831769858688101315)
                ·
                  refine ⟨2230970747654788032151973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487313831769858688101315 2230970747654788032151973)
                  ·
                    refine ⟨418307015185272756028495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230970747654788032151973 418307015185272756028495)
                    ·
                      rfl

theorem cell23_2443950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2443950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443950 prefixEnd_2443950 := by exact prefixLift 2443950
  have htrace : WordTrace (prefixWord ++ tailWord_2443950) baseStart_2443950 baseEnd_2443950 := by
    simpa [prefixWord, tailWord_2443950, baseEnd_2443950] using wordTrace_append hprefix tailTrace_2443950
  have hstable : (prefixWord ++ tailWord_2443950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443950).length < 2 ^ (prefixWord ++ tailWord_2443950).sum := by decide
  have hdescent : baseEnd_2443950 < baseStart_2443950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443966 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_2443966 : Nat := 118140960795 + 2443966 * 2 ^ 59
def prefixEnd_2443966 : Nat := 4983230072969 + 3 ^ 40 * 2443966 * 2
def baseEnd_2443966 : Nat := 1254929261246290205485411

theorem tailTrace_2443966 : CollatzResearch.WordTrace tailWord_2443966 prefixEnd_2443966 1254929261246290205485411 := by
  unfold tailWord_2443966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142345382992006625912969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59425842042624035338202501 11142345382992006625912969)
  ·
    refine ⟨8356759037244004969434727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11142345382992006625912969 8356759037244004969434727)
    ·
      refine ⟨12535138555866007454152091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8356759037244004969434727 12535138555866007454152091)
      ·
        refine ⟨18802707833799011181228137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12535138555866007454152091 18802707833799011181228137)
        ·
          refine ⟨14102030875349258385921103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18802707833799011181228137 14102030875349258385921103)
          ·
            refine ⟨21153046313023887578881655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14102030875349258385921103 21153046313023887578881655)
            ·
              refine ⟨31729569469535831368322483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21153046313023887578881655 31729569469535831368322483)
              ·
                refine ⟨47594354204303747052483725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31729569469535831368322483 47594354204303747052483725)
                ·
                  refine ⟨17847882826613905144681397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47594354204303747052483725 17847882826613905144681397)
                  ·
                    refine ⟨1673239014995053607313881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17847882826613905144681397 1673239014995053607313881)
                    ·
                      refine ⟨1254929261246290205485411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673239014995053607313881 1254929261246290205485411)
                      ·
                        rfl

theorem cell23_2443966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_2443966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443966 prefixEnd_2443966 := by exact prefixLift 2443966
  have htrace : WordTrace (prefixWord ++ tailWord_2443966) baseStart_2443966 baseEnd_2443966 := by
    simpa [prefixWord, tailWord_2443966, baseEnd_2443966] using wordTrace_append hprefix tailTrace_2443966
  have hstable : (prefixWord ++ tailWord_2443966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443966).length < 2 ^ (prefixWord ++ tailWord_2443966).sum := by decide
  have hdescent : baseEnd_2443966 < baseStart_2443966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443976 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 1, 5]
def baseStart_2443976 : Nat := 118140960795 + 2443976 * 2 ^ 59
def prefixEnd_2443976 : Nat := 4983230072969 + 3 ^ 40 * 2443976 * 2
def baseEnd_2443976 : Nat := 418311465350945055453455

theorem tailTrace_2443976 : CollatzResearch.WordTrace tailWord_2443976 prefixEnd_2443976 418311465350945055453455 := by
  unfold tailWord_2443976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44569563896949912357583891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59426085195933216476778521 44569563896949912357583891)
  ·
    refine ⟨66854345845424868536375837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44569563896949912357583891 66854345845424868536375837)
    ·
      refine ⟨25070379692034325701140939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66854345845424868536375837 25070379692034325701140939)
      ·
        refine ⟨37605569538051488551711409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25070379692034325701140939 37605569538051488551711409)
        ·
          refine ⟨28204177153538616413783557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37605569538051488551711409 28204177153538616413783557)
          ·
            refine ⟨5288283216288490577584417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28204177153538616413783557 5288283216288490577584417)
            ·
              refine ⟨3966212412216367933188313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288283216288490577584417 3966212412216367933188313)
              ·
                refine ⟨2974659309162275949891235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966212412216367933188313 2974659309162275949891235)
                ·
                  refine ⟨4461988963743413924836853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974659309162275949891235 4461988963743413924836853)
                  ·
                    refine ⟨418311465350945055453455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4461988963743413924836853 418311465350945055453455)
                    ·
                      rfl

theorem cell23_2443976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_2443976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443976 prefixEnd_2443976 := by exact prefixLift 2443976
  have htrace : WordTrace (prefixWord ++ tailWord_2443976) baseStart_2443976 baseEnd_2443976 := by
    simpa [prefixWord, tailWord_2443976, baseEnd_2443976] using wordTrace_append hprefix tailTrace_2443976
  have hstable : (prefixWord ++ tailWord_2443976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443976).length < 2 ^ (prefixWord ++ tailWord_2443976).sum := by decide
  have hdescent : baseEnd_2443976 < baseStart_2443976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2443999 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_2443999 : Nat := 118140960795 + 2443999 * 2 ^ 59
def prefixEnd_2443999 : Nat := 4983230072969 + 3 ^ 40 * 2443999 * 2
def baseEnd_2443999 : Nat := 1254946206107888576372759

theorem tailTrace_2443999 : CollatzResearch.WordTrace tailWord_2443999 prefixEnd_2443999 1254946206107888576372759 := by
  unfold tailWord_2443999
  simp only [CollatzResearch.WordTrace]
  refine ⟨89139966672816499643255051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59426644448544333095503367 89139966672816499643255051)
  ·
    refine ⟨133709950009224749464882577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89139966672816499643255051 133709950009224749464882577)
    ·
      refine ⟨100282462506918562098661933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133709950009224749464882577 100282462506918562098661933)
      ·
        refine ⟨37605923440094460786998225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100282462506918562098661933 37605923440094460786998225)
        ·
          refine ⟨28204442580070845590248669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37605923440094460786998225 28204442580070845590248669)
          ·
            refine ⟨10576665967526567096343251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28204442580070845590248669 10576665967526567096343251)
            ·
              refine ⟨15864998951289850644514877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10576665967526567096343251 15864998951289850644514877)
              ·
                refine ⟨5949374606733693991693079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15864998951289850644514877 5949374606733693991693079)
                ·
                  refine ⟨8924061910100540987539619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5949374606733693991693079 8924061910100540987539619)
                  ·
                    refine ⟨13386092865150811481309429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8924061910100540987539619 13386092865150811481309429)
                    ·
                      refine ⟨1254946206107888576372759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13386092865150811481309429 1254946206107888576372759)
                      ·
                        rfl

theorem cell23_2443999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_2443999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2443999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2443999 prefixEnd_2443999 := by exact prefixLift 2443999
  have htrace : WordTrace (prefixWord ++ tailWord_2443999) baseStart_2443999 baseEnd_2443999 := by
    simpa [prefixWord, tailWord_2443999, baseEnd_2443999] using wordTrace_append hprefix tailTrace_2443999
  have hstable : (prefixWord ++ tailWord_2443999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2443999).length < 2 ^ (prefixWord ++ tailWord_2443999).sum := by decide
  have hdescent : baseEnd_2443999 < baseStart_2443999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2443999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444030 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2444030 : Nat := 118140960795 + 2444030 * 2 ^ 59
def prefixEnd_2444030 : Nat := 4983230072969 + 3 ^ 40 * 2444030 * 2
def baseEnd_2444030 : Nat := 1254962124008177955085117

theorem tailTrace_2444030 : CollatzResearch.WordTrace tailWord_2444030 prefixEnd_2444030 1254962124008177955085117 := by
  unfold tailWord_2444030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142637166963023992204193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59427398223802794625089029 11142637166963023992204193)
  ·
    refine ⟨8356977875222267994153145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11142637166963023992204193 8356977875222267994153145)
    ·
      refine ⟨6267733406416700995614859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8356977875222267994153145 6267733406416700995614859)
      ·
        refine ⟨9401600109625051493422289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6267733406416700995614859 9401600109625051493422289)
        ·
          refine ⟨7051200082218788620066717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9401600109625051493422289 7051200082218788620066717)
          ·
            refine ⟨2644200030832045732525019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7051200082218788620066717 2644200030832045732525019)
            ·
              refine ⟨3966300046248068598787529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644200030832045732525019 3966300046248068598787529)
              ·
                refine ⟨2974725034686051449090647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966300046248068598787529 2974725034686051449090647)
                ·
                  refine ⟨4462087552029077173635971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974725034686051449090647 4462087552029077173635971)
                  ·
                    refine ⟨6693131328043615760453957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4462087552029077173635971 6693131328043615760453957)
                    ·
                      refine ⟨1254962124008177955085117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6693131328043615760453957 1254962124008177955085117)
                      ·
                        rfl

theorem cell23_2444030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2444030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444030 prefixEnd_2444030 := by exact prefixLift 2444030
  have htrace : WordTrace (prefixWord ++ tailWord_2444030) baseStart_2444030 baseEnd_2444030 := by
    simpa [prefixWord, tailWord_2444030, baseEnd_2444030] using wordTrace_append hprefix tailTrace_2444030
  have hstable : (prefixWord ++ tailWord_2444030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444030).length < 2 ^ (prefixWord ++ tailWord_2444030).sum := by decide
  have hdescent : baseEnd_2444030 < baseStart_2444030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444050 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2444050 : Nat := 118140960795 + 2444050 * 2 ^ 59
def prefixEnd_2444050 : Nat := 4983230072969 + 3 ^ 40 * 2444050 * 2
def baseEnd_2444050 : Nat := 1254972393621267876835025

theorem tailTrace_2444050 : CollatzResearch.WordTrace tailWord_2444050 prefixEnd_2444050 1254972393621267876835025 := by
  unfold tailWord_2444050
  simp only [CollatzResearch.WordTrace]
  refine ⟨22285456698907933838340401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59427884530421156902241069 22285456698907933838340401)
  ·
    refine ⟨16714092524180950378755301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22285456698907933838340401 16714092524180950378755301)
    ·
      refine ⟨3133892348283928196016619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16714092524180950378755301 3133892348283928196016619)
      ·
        refine ⟨4700838522425892294024929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133892348283928196016619 4700838522425892294024929)
        ·
          refine ⟨3525628891819419220518697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4700838522425892294024929 3525628891819419220518697)
          ·
            refine ⟨2644221668864564415389023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525628891819419220518697 2644221668864564415389023)
            ·
              refine ⟨3966332503296846623083535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644221668864564415389023 3966332503296846623083535)
              ·
                refine ⟨5949498754945269934625303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966332503296846623083535 5949498754945269934625303)
                ·
                  refine ⟨8924248132417904901937955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5949498754945269934625303 8924248132417904901937955)
                  ·
                    refine ⟨13386372198626857352906933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8924248132417904901937955 13386372198626857352906933)
                    ·
                      refine ⟨1254972393621267876835025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13386372198626857352906933 1254972393621267876835025)
                      ·
                        rfl

theorem cell23_2444050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2444050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444050 prefixEnd_2444050 := by exact prefixLift 2444050
  have htrace : WordTrace (prefixWord ++ tailWord_2444050) baseStart_2444050 baseEnd_2444050 := by
    simpa [prefixWord, tailWord_2444050, baseEnd_2444050] using wordTrace_append hprefix tailTrace_2444050
  have hstable : (prefixWord ++ tailWord_2444050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444050).length < 2 ^ (prefixWord ++ tailWord_2444050).sum := by decide
  have hdescent : baseEnd_2444050 < baseStart_2444050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444063 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 3]
def baseStart_2444063 : Nat := 118140960795 + 2444063 * 2 ^ 59
def prefixEnd_2444063 : Nat := 4983230072969 + 3 ^ 40 * 2444063 * 2
def baseEnd_2444063 : Nat := 1254979068869776325972465

theorem tailTrace_2444063 : CollatzResearch.WordTrace tailWord_2444063 prefixEnd_2444063 1254979068869776325972465 := by
  unfold tailWord_2444063
  simp only [CollatzResearch.WordTrace]
  refine ⟨89142300944584638573584843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59428200629723092382389895 89142300944584638573584843)
  ·
    refine ⟨133713451416876957860377265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89142300944584638573584843 133713451416876957860377265)
    ·
      refine ⟨100285088562657718395282949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133713451416876957860377265 100285088562657718395282949)
      ·
        refine ⟨18803454105498322199115553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100285088562657718395282949 18803454105498322199115553)
        ·
          refine ⟨14102590579123741649336665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18803454105498322199115553 14102590579123741649336665)
          ·
            refine ⟨10576942934342806237002499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14102590579123741649336665 10576942934342806237002499)
            ·
              refine ⟨15865414401514209355503749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10576942934342806237002499 15865414401514209355503749)
              ·
                refine ⟨2974765200283914254156953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15865414401514209355503749 2974765200283914254156953)
                ·
                  refine ⟨2231073900212935690617715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2974765200283914254156953 2231073900212935690617715)
                  ·
                    refine ⟨3346610850319403535926573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2231073900212935690617715 3346610850319403535926573)
                    ·
                      refine ⟨1254979068869776325972465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3346610850319403535926573 1254979068869776325972465)
                      ·
                        rfl

theorem cell23_2444063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_2444063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444063 prefixEnd_2444063 := by exact prefixLift 2444063
  have htrace : WordTrace (prefixWord ++ tailWord_2444063) baseStart_2444063 baseEnd_2444063 := by
    simpa [prefixWord, tailWord_2444063, baseEnd_2444063] using wordTrace_append hprefix tailTrace_2444063
  have hstable : (prefixWord ++ tailWord_2444063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444063).length < 2 ^ (prefixWord ++ tailWord_2444063).sum := by decide
  have hdescent : baseEnd_2444063 < baseStart_2444063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444064 : List Nat := [2, 1, 1, 5, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2444064 : Nat := 118140960795 + 2444064 * 2 ^ 59
def prefixEnd_2444064 : Nat := 4983230072969 + 3 ^ 40 * 2444064 * 2
def baseEnd_2444064 : Nat := 1254979582350430822059961

theorem tailTrace_2444064 : CollatzResearch.WordTrace tailWord_2444064 prefixEnd_2444064 1254979582350430822059961 := by
  unfold tailWord_2444064
  simp only [CollatzResearch.WordTrace]
  refine ⟨44571168708790507872185623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59428224945054010496247497 44571168708790507872185623)
  ·
    refine ⟨66856753063185761808278435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44571168708790507872185623 66856753063185761808278435)
    ·
      refine ⟨100285129594778642712417653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66856753063185761808278435 100285129594778642712417653)
      ·
        refine ⟨9401730899510497754289155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100285129594778642712417653 9401730899510497754289155)
        ·
          refine ⟨14102596349265746631433733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9401730899510497754289155 14102596349265746631433733)
          ·
            refine ⟨2644236815487327493393825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14102596349265746631433733 2644236815487327493393825)
            ·
              refine ⟨1983177611615495620045369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644236815487327493393825 1983177611615495620045369)
              ·
                refine ⟨1487383208711621715034027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983177611615495620045369 1487383208711621715034027)
                ·
                  refine ⟨2231074813067432572551041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487383208711621715034027 2231074813067432572551041)
                  ·
                    refine ⟨1673306109800574429413281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2231074813067432572551041 1673306109800574429413281)
                    ·
                      refine ⟨1254979582350430822059961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673306109800574429413281 1254979582350430822059961)
                      ·
                        rfl

theorem cell23_2444064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2444064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444064 prefixEnd_2444064 := by exact prefixLift 2444064
  have htrace : WordTrace (prefixWord ++ tailWord_2444064) baseStart_2444064 baseEnd_2444064 := by
    simpa [prefixWord, tailWord_2444064, baseEnd_2444064] using wordTrace_append hprefix tailTrace_2444064
  have hstable : (prefixWord ++ tailWord_2444064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444064).length < 2 ^ (prefixWord ++ tailWord_2444064).sum := by decide
  have hdescent : baseEnd_2444064 < baseStart_2444064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444069 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_2444069 : Nat := 118140960795 + 2444069 * 2 ^ 59
def prefixEnd_2444069 : Nat := 4983230072969 + 3 ^ 40 * 2444069 * 2
def baseEnd_2444069 : Nat := 1254982149753703302497437

theorem tailTrace_2444069 : CollatzResearch.WordTrace tailWord_2444069 prefixEnd_2444069 1254982149753703302497437 := by
  unfold tailWord_2444069
  simp only [CollatzResearch.WordTrace]
  refine ⟨89142519782562901598303261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59428346521708601065535507 89142519782562901598303261)
  ·
    refine ⟨33428444918461088099363723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89142519782562901598303261 33428444918461088099363723)
    ·
      refine ⟨50142667377691632149045585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33428444918461088099363723 50142667377691632149045585)
      ·
        refine ⟨37607000533268724111784189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50142667377691632149045585 37607000533268724111784189)
        ·
          refine ⟨14102625199975771541919071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37607000533268724111784189 14102625199975771541919071)
          ·
            refine ⟨21153937799963657312878607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14102625199975771541919071 21153937799963657312878607)
            ·
              refine ⟨31730906699945485969317911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21153937799963657312878607 31730906699945485969317911)
              ·
                refine ⟨47596360049918228953976867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31730906699945485969317911 47596360049918228953976867)
                ·
                  refine ⟨71394540074877343430965301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47596360049918228953976867 71394540074877343430965301)
                  ·
                    refine ⟨6693238132019750946652997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71394540074877343430965301 6693238132019750946652997)
                    ·
                      refine ⟨1254982149753703302497437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6693238132019750946652997 1254982149753703302497437)
                      ·
                        rfl

theorem cell23_2444069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_2444069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444069 prefixEnd_2444069 := by exact prefixLift 2444069
  have htrace : WordTrace (prefixWord ++ tailWord_2444069) baseStart_2444069 baseEnd_2444069 := by
    simpa [prefixWord, tailWord_2444069, baseEnd_2444069] using wordTrace_append hprefix tailTrace_2444069
  have hstable : (prefixWord ++ tailWord_2444069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444069).length < 2 ^ (prefixWord ++ tailWord_2444069).sum := by decide
  have hdescent : baseEnd_2444069 < baseStart_2444069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444099 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4]
def baseStart_2444099 : Nat := 118140960795 + 2444099 * 2 ^ 59
def prefixEnd_2444099 : Nat := 4983230072969 + 3 ^ 40 * 2444099 * 2
def baseEnd_2444099 : Nat := 1254997554173338185122299

theorem tailTrace_2444099 : CollatzResearch.WordTrace tailWord_2444099 prefixEnd_2444099 1254997554173338185122299 := by
  unfold tailWord_2444099
  simp only [CollatzResearch.WordTrace]
  refine ⟨89143613972454216721895351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59429075981636144481263567 89143613972454216721895351)
  ·
    refine ⟨133715420958681325082843027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89143613972454216721895351 133715420958681325082843027)
    ·
      refine ⟨200573131438021987624264541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133715420958681325082843027 200573131438021987624264541)
      ·
        refine ⟨75214924289258245359099203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200573131438021987624264541 75214924289258245359099203)
        ·
          refine ⟨112822386433887368038648805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75214924289258245359099203 112822386433887368038648805)
          ·
            refine ⟨21154197456353881507246651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112822386433887368038648805 21154197456353881507246651)
            ·
              refine ⟨31731296184530822260869977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21154197456353881507246651 31731296184530822260869977)
              ·
                refine ⟨23798472138398116695652483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31731296184530822260869977 23798472138398116695652483)
                ·
                  refine ⟨35697708207597175043478725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23798472138398116695652483 35697708207597175043478725)
                  ·
                    refine ⟨6693320288924470320652261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35697708207597175043478725 6693320288924470320652261)
                    ·
                      refine ⟨1254997554173338185122299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6693320288924470320652261 1254997554173338185122299)
                      ·
                        rfl

theorem cell23_2444099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_2444099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444099 prefixEnd_2444099 := by exact prefixLift 2444099
  have htrace : WordTrace (prefixWord ++ tailWord_2444099) baseStart_2444099 baseEnd_2444099 := by
    simpa [prefixWord, tailWord_2444099, baseEnd_2444099] using wordTrace_append hprefix tailTrace_2444099
  have hstable : (prefixWord ++ tailWord_2444099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444099).length < 2 ^ (prefixWord ++ tailWord_2444099).sum := by decide
  have hdescent : baseEnd_2444099 < baseStart_2444099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444103 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_2444103 : Nat := 118140960795 + 2444103 * 2 ^ 59
def prefixEnd_2444103 : Nat := 4983230072969 + 3 ^ 40 * 2444103 * 2
def baseEnd_2444103 : Nat := 1254999608095956169472281

theorem tailTrace_2444103 : CollatzResearch.WordTrace tailWord_2444103 prefixEnd_2444103 1254999608095956169472281 := by
  unfold tailWord_2444103
  simp only [CollatzResearch.WordTrace]
  refine ⟨89143759864439725405040963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59429173242959816936693975 89143759864439725405040963)
  ·
    refine ⟨133715639796659588107561445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89143759864439725405040963 133715639796659588107561445)
    ·
      refine ⟨25071682461873672770167771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133715639796659588107561445 25071682461873672770167771)
      ·
        refine ⟨37607523692810509155251657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25071682461873672770167771 37607523692810509155251657)
        ·
          refine ⟨28205642769607881866438743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37607523692810509155251657 28205642769607881866438743)
          ·
            refine ⟨42308464154411822799658115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28205642769607881866438743 42308464154411822799658115)
            ·
              refine ⟨63462696231617734199487173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42308464154411822799658115 63462696231617734199487173)
              ·
                refine ⟨11899255543428325162403845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63462696231617734199487173 11899255543428325162403845)
                ·
                  refine ⟨2231110414392810967950721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11899255543428325162403845 2231110414392810967950721)
                  ·
                    refine ⟨1673332810794608225963041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2231110414392810967950721 1673332810794608225963041)
                    ·
                      refine ⟨1254999608095956169472281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673332810794608225963041 1254999608095956169472281)
                      ·
                        rfl

theorem cell23_2444103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_2444103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444103 prefixEnd_2444103 := by exact prefixLift 2444103
  have htrace : WordTrace (prefixWord ++ tailWord_2444103) baseStart_2444103 baseEnd_2444103 := by
    simpa [prefixWord, tailWord_2444103, baseEnd_2444103] using wordTrace_append hprefix tailTrace_2444103
  have hstable : (prefixWord ++ tailWord_2444103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444103).length < 2 ^ (prefixWord ++ tailWord_2444103).sum := by decide
  have hdescent : baseEnd_2444103 < baseStart_2444103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444139 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 1, 7]
def baseStart_2444139 : Nat := 118140960795 + 2444139 * 2 ^ 59
def prefixEnd_2444139 : Nat := 4983230072969 + 3 ^ 40 * 2444139 * 2
def baseEnd_2444139 : Nat := 418339364466506009540705

theorem tailTrace_2444139 : CollatzResearch.WordTrace tailWord_2444139 prefixEnd_2444139 418339364466506009540705 := by
  unfold tailWord_2444139
  simp only [CollatzResearch.WordTrace]
  refine ⟨89145072892309303553351471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59430048594872869035567647 89145072892309303553351471)
  ·
    refine ⟨133717609338463955330027207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89145072892309303553351471 133717609338463955330027207)
    ·
      refine ⟨200576414007695932995040811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133717609338463955330027207 200576414007695932995040811)
      ·
        refine ⟨300864621011543899492561217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200576414007695932995040811 300864621011543899492561217)
        ·
          refine ⟨225648465758657924619420913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300864621011543899492561217 225648465758657924619420913)
          ·
            refine ⟨169236349318993443464565685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225648465758657924619420913 169236349318993443464565685)
            ·
              refine ⟨15865907748655635324803033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169236349318993443464565685 15865907748655635324803033)
              ·
                refine ⟨11899430811491726493602275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15865907748655635324803033 11899430811491726493602275)
                ·
                  refine ⟨17849146217237589740403413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11899430811491726493602275 17849146217237589740403413)
                  ·
                    refine ⟨418339364466506009540705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17849146217237589740403413 418339364466506009540705)
                    ·
                      rfl

theorem cell23_2444139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 7].length) (baseStart_2444139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444139 prefixEnd_2444139 := by exact prefixLift 2444139
  have htrace : WordTrace (prefixWord ++ tailWord_2444139) baseStart_2444139 baseEnd_2444139 := by
    simpa [prefixWord, tailWord_2444139, baseEnd_2444139] using wordTrace_append hprefix tailTrace_2444139
  have hstable : (prefixWord ++ tailWord_2444139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444139).length < 2 ^ (prefixWord ++ tailWord_2444139).sum := by decide
  have hdescent : baseEnd_2444139 < baseStart_2444139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444179 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5]
def baseStart_2444179 : Nat := 118140960795 + 2444179 * 2 ^ 59
def prefixEnd_2444179 : Nat := 4983230072969 + 3 ^ 40 * 2444179 * 2
def baseEnd_2444179 : Nat := 1255038632625697872121931

theorem tailTrace_2444179 : CollatzResearch.WordTrace tailWord_2444179 prefixEnd_2444179 1255038632625697872121931 := by
  unfold tailWord_2444179
  simp only [CollatzResearch.WordTrace]
  refine ⟨89146531812164390384807591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59431021208109593589871727 89146531812164390384807591)
  ·
    refine ⟨133719797718246585577211387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89146531812164390384807591 133719797718246585577211387)
    ·
      refine ⟨200579696577369878365817081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133719797718246585577211387 200579696577369878365817081)
      ·
        refine ⟨150434772433027408774362811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200579696577369878365817081 150434772433027408774362811)
        ·
          refine ⟨225652158649541113161544217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150434772433027408774362811 225652158649541113161544217)
          ·
            refine ⟨169239118987155834871158163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225652158649541113161544217 169239118987155834871158163)
            ·
              refine ⟨253858678480733752306737245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169239118987155834871158163 253858678480733752306737245)
              ·
                refine ⟨95197004430275157115026467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253858678480733752306737245 95197004430275157115026467)
                ·
                  refine ⟨142795506645412735672539701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95197004430275157115026467 142795506645412735672539701)
                  ·
                    refine ⟨13387078748007443969300597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142795506645412735672539701 13387078748007443969300597)
                    ·
                      refine ⟨1255038632625697872121931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13387078748007443969300597 1255038632625697872121931)
                      ·
                        rfl

theorem cell23_2444179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_2444179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444179 prefixEnd_2444179 := by exact prefixLift 2444179
  have htrace : WordTrace (prefixWord ++ tailWord_2444179) baseStart_2444179 baseEnd_2444179 := by
    simpa [prefixWord, tailWord_2444179, baseEnd_2444179] using wordTrace_append hprefix tailTrace_2444179
  have hstable : (prefixWord ++ tailWord_2444179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444179).length < 2 ^ (prefixWord ++ tailWord_2444179).sum := by decide
  have hdescent : baseEnd_2444179 < baseStart_2444179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444236 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2444236 : Nat := 118140960795 + 2444236 * 2 ^ 59
def prefixEnd_2444236 : Nat := 4983230072969 + 3 ^ 40 * 2444236 * 2
def baseEnd_2444236 : Nat := 1255067901023004149109169

theorem tailTrace_2444236 : CollatzResearch.WordTrace tailWord_2444236 prefixEnd_2444236 1255067901023004149109169 := by
  unfold tailWord_2444236
  simp only [CollatzResearch.WordTrace]
  refine ⟨44574305386478944559816281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59432407181971926079755041 44574305386478944559816281)
  ·
    refine ⟨33430729039859208419862211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44574305386478944559816281 33430729039859208419862211)
    ·
      refine ⟨50146093559788812629793317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33430729039859208419862211 50146093559788812629793317)
      ·
        refine ⟨9402392542460402368086247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50146093559788812629793317 9402392542460402368086247)
        ·
          refine ⟨14103588813690603552129371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9402392542460402368086247 14103588813690603552129371)
          ·
            refine ⟨21155383220535905328194057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14103588813690603552129371 21155383220535905328194057)
            ·
              refine ⟨15866537415401928996145543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21155383220535905328194057 15866537415401928996145543)
              ·
                refine ⟨23799806123102893494218315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15866537415401928996145543 23799806123102893494218315)
                ·
                  refine ⟨35699709184654340241327473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23799806123102893494218315 35699709184654340241327473)
                  ·
                    refine ⟨26774781888490755180995605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35699709184654340241327473 26774781888490755180995605)
                    ·
                      refine ⟨1255067901023004149109169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26774781888490755180995605 1255067901023004149109169)
                      ·
                        rfl

theorem cell23_2444236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2444236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444236 prefixEnd_2444236 := by exact prefixLift 2444236
  have htrace : WordTrace (prefixWord ++ tailWord_2444236) baseStart_2444236 baseEnd_2444236 := by
    simpa [prefixWord, tailWord_2444236, baseEnd_2444236] using wordTrace_append hprefix tailTrace_2444236
  have hstable : (prefixWord ++ tailWord_2444236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444236).length < 2 ^ (prefixWord ++ tailWord_2444236).sum := by decide
  have hdescent : baseEnd_2444236 < baseStart_2444236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444263 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2444263 : Nat := 118140960795 + 2444263 * 2 ^ 59
def prefixEnd_2444263 : Nat := 4983230072969 + 3 ^ 40 * 2444263 * 2
def baseEnd_2444263 : Nat := 418360588333558514490515

theorem tailTrace_2444263 : CollatzResearch.WordTrace tailWord_2444263 prefixEnd_2444263 418360588333558514490515 := by
  unfold tailWord_2444263
  simp only [CollatzResearch.WordTrace]
  refine ⟨89149595543860072730865443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59433063695906715153910295 89149595543860072730865443)
  ·
    refine ⟨133724393315790109096298165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89149595543860072730865443 133724393315790109096298165)
    ·
      refine ⟨12536661873355322727777953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133724393315790109096298165 12536661873355322727777953)
      ·
        refine ⟨9402496405016492045833465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12536661873355322727777953 9402496405016492045833465)
        ·
          refine ⟨7051872303762369034375099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9402496405016492045833465 7051872303762369034375099)
          ·
            refine ⟨10577808455643553551562649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7051872303762369034375099 10577808455643553551562649)
            ·
              refine ⟨7933356341732665163671987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10577808455643553551562649 7933356341732665163671987)
              ·
                refine ⟨11900034512598997745507981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7933356341732665163671987 11900034512598997745507981)
                ·
                  refine ⟨4462512942224624154565493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11900034512598997745507981 4462512942224624154565493)
                  ·
                    refine ⟨418360588333558514490515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4462512942224624154565493 418360588333558514490515)
                    ·
                      rfl

theorem cell23_2444263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2444263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444263 prefixEnd_2444263 := by exact prefixLift 2444263
  have htrace : WordTrace (prefixWord ++ tailWord_2444263) baseStart_2444263 baseEnd_2444263 := by
    simpa [prefixWord, tailWord_2444263, baseEnd_2444263] using wordTrace_append hprefix tailTrace_2444263
  have hstable : (prefixWord ++ tailWord_2444263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444263).length < 2 ^ (prefixWord ++ tailWord_2444263).sum := by decide
  have hdescent : baseEnd_2444263 < baseStart_2444263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444293 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_2444293 : Nat := 118140960795 + 2444293 * 2 ^ 59
def prefixEnd_2444293 : Nat := 4983230072969 + 3 ^ 40 * 2444293 * 2
def baseEnd_2444293 : Nat := 418365723140103475365469

theorem tailTrace_2444293 : CollatzResearch.WordTrace tailWord_2444293 prefixEnd_2444293 418365723140103475365469 := by
  unfold tailWord_2444293
  simp only [CollatzResearch.WordTrace]
  refine ⟨89150689733751387854457533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59433793155834258569638355 89150689733751387854457533)
  ·
    refine ⟨33431508650156770445421575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89150689733751387854457533 33431508650156770445421575)
    ·
      refine ⟨50147262975235155668132363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33431508650156770445421575 50147262975235155668132363)
      ·
        refine ⟨75220894462852733502198545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50147262975235155668132363 75220894462852733502198545)
        ·
          refine ⟨56415670847139550126648909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75220894462852733502198545 56415670847139550126648909)
          ·
            refine ⟨21155876567677331297493341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56415670847139550126648909 21155876567677331297493341)
            ·
              refine ⟨7933453712878999236560003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21155876567677331297493341 7933453712878999236560003)
              ·
                refine ⟨11900180569318498854840005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7933453712878999236560003 11900180569318498854840005)
                ·
                  refine ⟨2231283856747218535282501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11900180569318498854840005 2231283856747218535282501)
                  ·
                    refine ⟨418365723140103475365469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2231283856747218535282501 418365723140103475365469)
                    ·
                      rfl

theorem cell23_2444293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_2444293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444293 prefixEnd_2444293 := by exact prefixLift 2444293
  have htrace : WordTrace (prefixWord ++ tailWord_2444293) baseStart_2444293 baseEnd_2444293 := by
    simpa [prefixWord, tailWord_2444293, baseEnd_2444293] using wordTrace_append hprefix tailTrace_2444293
  have hstable : (prefixWord ++ tailWord_2444293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444293).length < 2 ^ (prefixWord ++ tailWord_2444293).sum := by decide
  have hdescent : baseEnd_2444293 < baseStart_2444293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444313 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 4]
def baseStart_2444313 : Nat := 118140960795 + 2444313 * 2 ^ 59
def prefixEnd_2444313 : Nat := 4983230072969 + 3 ^ 40 * 2444313 * 2
def baseEnd_2444313 : Nat := 1255107439033400347846315

theorem tailTrace_2444313 : CollatzResearch.WordTrace tailWord_2444313 prefixEnd_2444313 1255107439033400347846315 := by
  unfold tailWord_2444313
  simp only [CollatzResearch.WordTrace]
  refine ⟨89151419193678931270185593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59434279462452620846790395 89151419193678931270185593)
  ·
    refine ⟨66863564395259198452639195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89151419193678931270185593 66863564395259198452639195)
    ·
      refine ⟨100295346592888797678958793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66863564395259198452639195 100295346592888797678958793)
      ·
        refine ⟨75221509944666598259219095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100295346592888797678958793 75221509944666598259219095)
        ·
          refine ⟨112832264916999897388828643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75221509944666598259219095 112832264916999897388828643)
          ·
            refine ⟨169248397375499846083242965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112832264916999897388828643 169248397375499846083242965)
            ·
              refine ⟨3966759313488277642576007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169248397375499846083242965 3966759313488277642576007)
              ·
                refine ⟨5950138970232416463864011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966759313488277642576007 5950138970232416463864011)
                ·
                  refine ⟨8925208455348624695796017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5950138970232416463864011 8925208455348624695796017)
                  ·
                    refine ⟨6693906341511468521847013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8925208455348624695796017 6693906341511468521847013)
                    ·
                      refine ⟨1255107439033400347846315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6693906341511468521847013 1255107439033400347846315)
                      ·
                        rfl

theorem cell23_2444313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_2444313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444313 prefixEnd_2444313 := by exact prefixLift 2444313
  have htrace : WordTrace (prefixWord ++ tailWord_2444313) baseStart_2444313 baseEnd_2444313 := by
    simpa [prefixWord, tailWord_2444313, baseEnd_2444313] using wordTrace_append hprefix tailTrace_2444313
  have hstable : (prefixWord ++ tailWord_2444313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444313).length < 2 ^ (prefixWord ++ tailWord_2444313).sum := by decide
  have hdescent : baseEnd_2444313 < baseStart_2444313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444317 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_2444317 : Nat := 118140960795 + 2444317 * 2 ^ 59
def prefixEnd_2444317 : Nat := 4983230072969 + 3 ^ 40 * 2444317 * 2
def baseEnd_2444317 : Nat := 1255109492956018332196297

theorem tailTrace_2444317 : CollatzResearch.WordTrace tailWord_2444317 prefixEnd_2444317 1255109492956018332196297 := by
  unfold tailWord_2444317
  simp only [CollatzResearch.WordTrace]
  refine ⟨89151565085664439953331205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59434376723776293302220803 89151565085664439953331205)
  ·
    refine ⟨16715918453562082491249601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89151565085664439953331205 16715918453562082491249601)
    ·
      refine ⟨12536938840171561868437201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16715918453562082491249601 12536938840171561868437201)
      ·
        refine ⟨9402704130128671401327901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12536938840171561868437201 9402704130128671401327901)
        ·
          refine ⟨3526014048798251775497963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9402704130128671401327901 3526014048798251775497963)
          ·
            refine ⟨5289021073197377663246945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526014048798251775497963 5289021073197377663246945)
            ·
              refine ⟨3966765804898033247435209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5289021073197377663246945 3966765804898033247435209)
              ·
                refine ⟨2975074353673524935576407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966765804898033247435209 2975074353673524935576407)
                ·
                  refine ⟨4462611530510287403364611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975074353673524935576407 4462611530510287403364611)
                  ·
                    refine ⟨6693917295765431105046917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4462611530510287403364611 6693917295765431105046917)
                    ·
                      refine ⟨1255109492956018332196297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6693917295765431105046917 1255109492956018332196297)
                      ·
                        rfl

theorem cell23_2444317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_2444317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444317 prefixEnd_2444317 := by exact prefixLift 2444317
  have htrace : WordTrace (prefixWord ++ tailWord_2444317) baseStart_2444317 baseEnd_2444317 := by
    simpa [prefixWord, tailWord_2444317, baseEnd_2444317] using wordTrace_append hprefix tailTrace_2444317
  have hstable : (prefixWord ++ tailWord_2444317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444317).length < 2 ^ (prefixWord ++ tailWord_2444317).sum := by decide
  have hdescent : baseEnd_2444317 < baseStart_2444317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444323 : List Nat := [1, 1, 1, 4, 3, 2, 4, 7]
def baseStart_2444323 : Nat := 118140960795 + 2444323 * 2 ^ 59
def prefixEnd_2444323 : Nat := 4983230072969 + 3 ^ 40 * 2444323 * 2
def baseEnd_2444323 : Nat := 46485650882960937360047

theorem tailTrace_2444323 : CollatzResearch.WordTrace tailWord_2444323 prefixEnd_2444323 46485650882960937360047 := by
  unfold tailWord_2444323
  simp only [CollatzResearch.WordTrace]
  refine ⟨89151783923642702978049623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59434522615761801985366415 89151783923642702978049623)
  ·
    refine ⟨133727675885464054467074435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89151783923642702978049623 133727675885464054467074435)
    ·
      refine ⟨200591513828196081700611653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133727675885464054467074435 200591513828196081700611653)
      ·
        refine ⟨37610908842786765318864685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200591513828196081700611653 37610908842786765318864685)
        ·
          refine ⟨14104090816045036994574257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37610908842786765318864685 14104090816045036994574257)
          ·
            refine ⟨10578068112033777745930693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14104090816045036994574257 10578068112033777745930693)
            ·
              refine ⟨1983387771006333327362005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10578068112033777745930693 1983387771006333327362005)
              ·
                refine ⟨46485650882960937360047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1983387771006333327362005 46485650882960937360047)
                ·
                  rfl

theorem cell23_2444323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 7].length) (baseStart_2444323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444323 prefixEnd_2444323 := by exact prefixLift 2444323
  have htrace : WordTrace (prefixWord ++ tailWord_2444323) baseStart_2444323 baseEnd_2444323 := by
    simpa [prefixWord, tailWord_2444323, baseEnd_2444323] using wordTrace_append hprefix tailTrace_2444323
  have hstable : (prefixWord ++ tailWord_2444323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444323).length < 2 ^ (prefixWord ++ tailWord_2444323).sum := by decide
  have hdescent : baseEnd_2444323 < baseStart_2444323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444340 : List Nat := [2, 5, 1, 2, 1, 3, 9]
def baseStart_2444340 : Nat := 118140960795 + 2444340 * 2 ^ 59
def prefixEnd_2444340 : Nat := 4983230072969 + 3 ^ 40 * 2444340 * 2
def baseEnd_2444340 : Nat := 15495324728531749903811

theorem tailTrace_2444340 : CollatzResearch.WordTrace tailWord_2444340 prefixEnd_2444340 15495324728531749903811 := by
  unfold tailWord_2444340
  simp only [CollatzResearch.WordTrace]
  refine ⟨44576201982290557440709237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59434935976387409920945649 44576201982290557440709237)
  ·
    refine ⟨4179018935839739760066491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44576201982290557440709237 4179018935839739760066491)
    ·
      refine ⟨6268528403759609640099737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4179018935839739760066491 6268528403759609640099737)
      ·
        refine ⟨4701396302819707230074803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6268528403759609640099737 4701396302819707230074803)
        ·
          refine ⟨7052094454229560845112205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701396302819707230074803 7052094454229560845112205)
          ·
            refine ⟨2644535420336085316917077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7052094454229560845112205 2644535420336085316917077)
            ·
              refine ⟨15495324728531749903811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2644535420336085316917077 15495324728531749903811)
              ·
                rfl

theorem cell23_2444340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 9].length) (baseStart_2444340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444340 prefixEnd_2444340 := by exact prefixLift 2444340
  have htrace : WordTrace (prefixWord ++ tailWord_2444340) baseStart_2444340 baseEnd_2444340 := by
    simpa [prefixWord, tailWord_2444340, baseEnd_2444340] using wordTrace_append hprefix tailTrace_2444340
  have hstable : (prefixWord ++ tailWord_2444340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444340).length < 2 ^ (prefixWord ++ tailWord_2444340).sum := by decide
  have hdescent : baseEnd_2444340 < baseStart_2444340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444360 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_2444360 : Nat := 118140960795 + 2444360 * 2 ^ 59
def prefixEnd_2444360 : Nat := 4983230072969 + 3 ^ 40 * 2444360 * 2
def baseEnd_2444360 : Nat := 1255131572624161663958599

theorem tailTrace_2444360 : CollatzResearch.WordTrace tailWord_2444360 prefixEnd_2444360 1255131572624161663958599 := by
  unfold tailWord_2444360
  simp only [CollatzResearch.WordTrace]
  refine ⟨44576566712254329148573267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59435422283005772198097689 44576566712254329148573267)
  ·
    refine ⟨66864850068381493722859901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44576566712254329148573267 66864850068381493722859901)
    ·
      refine ⟨25074318775643060146072463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66864850068381493722859901 25074318775643060146072463)
      ·
        refine ⟨37611478163464590219108695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25074318775643060146072463 37611478163464590219108695)
        ·
          refine ⟨56417217245196885328663043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37611478163464590219108695 56417217245196885328663043)
          ·
            refine ⟨84625825867795327992994565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56417217245196885328663043 84625825867795327992994565)
            ·
              refine ⟨15867342350211623998686481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84625825867795327992994565 15867342350211623998686481)
              ·
                refine ⟨11900506762658717999014861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15867342350211623998686481 11900506762658717999014861)
                ·
                  refine ⟨4462690035997019249630573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11900506762658717999014861 4462690035997019249630573)
                  ·
                    refine ⟨1673508763498882218611465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4462690035997019249630573 1673508763498882218611465)
                    ·
                      refine ⟨1255131572624161663958599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673508763498882218611465 1255131572624161663958599)
                      ·
                        rfl

theorem cell23_2444360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_2444360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444360 prefixEnd_2444360 := by exact prefixLift 2444360
  have htrace : WordTrace (prefixWord ++ tailWord_2444360) baseStart_2444360 baseEnd_2444360 := by
    simpa [prefixWord, tailWord_2444360, baseEnd_2444360] using wordTrace_append hprefix tailTrace_2444360
  have hstable : (prefixWord ++ tailWord_2444360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444360).length < 2 ^ (prefixWord ++ tailWord_2444360).sum := by decide
  have hdescent : baseEnd_2444360 < baseStart_2444360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444393 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_2444393 : Nat := 118140960795 + 2444393 * 2 ^ 59
def prefixEnd_2444393 : Nat := 4983230072969 + 3 ^ 40 * 2444393 * 2
def baseEnd_2444393 : Nat := 1255148517485760034845947

theorem tailTrace_2444393 : CollatzResearch.WordTrace tailWord_2444393 prefixEnd_2444393 1255148517485760034845947 := by
  unfold tailWord_2444393
  simp only [CollatzResearch.WordTrace]
  refine ⟨89154337033389104933097833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59436224688926069955398555 89154337033389104933097833)
  ·
    refine ⟨66865752775041828699823375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89154337033389104933097833 66865752775041828699823375)
    ·
      refine ⟨100298629162562743049735063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66865752775041828699823375 100298629162562743049735063)
      ·
        refine ⟨150447943743844114574602595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100298629162562743049735063 150447943743844114574602595)
        ·
          refine ⟨225671915615766171861903893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150447943743844114574602595 225671915615766171861903893)
          ·
            refine ⟨10578371044489039306026745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 225671915615766171861903893 10578371044489039306026745)
            ·
              refine ⟨7933778283366779479520059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10578371044489039306026745 7933778283366779479520059)
              ·
                refine ⟨11900667425050169219280089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7933778283366779479520059 11900667425050169219280089)
                ·
                  refine ⟨8925500568787626914460067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11900667425050169219280089 8925500568787626914460067)
                  ·
                    refine ⟨13388250853181440371690101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8925500568787626914460067 13388250853181440371690101)
                    ·
                      refine ⟨1255148517485760034845947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13388250853181440371690101 1255148517485760034845947)
                      ·
                        rfl

theorem cell23_2444393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_2444393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444393 prefixEnd_2444393 := by exact prefixLift 2444393
  have htrace : WordTrace (prefixWord ++ tailWord_2444393) baseStart_2444393 baseEnd_2444393 := by
    simpa [prefixWord, tailWord_2444393, baseEnd_2444393] using wordTrace_append hprefix tailTrace_2444393
  have hstable : (prefixWord ++ tailWord_2444393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444393).length < 2 ^ (prefixWord ++ tailWord_2444393).sum := by decide
  have hdescent : baseEnd_2444393 < baseStart_2444393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444413 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 7]
def baseStart_2444413 : Nat := 118140960795 + 2444413 * 2 ^ 59
def prefixEnd_2444413 : Nat := 4983230072969 + 3 ^ 40 * 2444413 * 2
def baseEnd_2444413 : Nat := 139462087455427772955095

theorem tailTrace_2444413 : CollatzResearch.WordTrace tailWord_2444413 prefixEnd_2444413 139462087455427772955095 := by
  unfold tailWord_2444413
  simp only [CollatzResearch.WordTrace]
  refine ⟨89155066493316648348825893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59436710995544432232550595 89155066493316648348825893)
  ·
    refine ⟨16716574967496871565404855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89155066493316648348825893 16716574967496871565404855)
    ·
      refine ⟨25074862451245307348107283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16716574967496871565404855 25074862451245307348107283)
      ·
        refine ⟨37612293676867961022160925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25074862451245307348107283 37612293676867961022160925)
        ·
          refine ⟨14104610128825485383310347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37612293676867961022160925 14104610128825485383310347)
          ·
            refine ⟨21156915193238228074965521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14104610128825485383310347 21156915193238228074965521)
            ·
              refine ⟨15867686394928671056224141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21156915193238228074965521 15867686394928671056224141)
              ·
                refine ⟨5950382398098251646084053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15867686394928671056224141 5950382398098251646084053)
                ·
                  refine ⟨139462087455427772955095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5950382398098251646084053 139462087455427772955095)
                  ·
                    rfl

theorem cell23_2444413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_2444413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444413 prefixEnd_2444413 := by exact prefixLift 2444413
  have htrace : WordTrace (prefixWord ++ tailWord_2444413) baseStart_2444413 baseEnd_2444413 := by
    simpa [prefixWord, tailWord_2444413, baseEnd_2444413] using wordTrace_append hprefix tailTrace_2444413
  have hstable : (prefixWord ++ tailWord_2444413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444413).length < 2 ^ (prefixWord ++ tailWord_2444413).sum := by decide
  have hdescent : baseEnd_2444413 < baseStart_2444413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444420 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2444420 : Nat := 118140960795 + 2444420 * 2 ^ 59
def prefixEnd_2444420 : Nat := 4983230072969 + 3 ^ 40 * 2444420 * 2
def baseEnd_2444420 : Nat := 1255162381463431429208323

theorem tailTrace_2444420 : CollatzResearch.WordTrace tailWord_2444420 prefixEnd_2444420 1255162381463431429208323 := by
  unfold tailWord_2444420
  simp only [CollatzResearch.WordTrace]
  refine ⟨44577660902145644272165357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59436881202860859029553809 44577660902145644272165357)
  ·
    refine ⟨16716622838304616602062009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44577660902145644272165357 16716622838304616602062009)
    ·
      refine ⟨12537467128728462451546507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16716622838304616602062009 12537467128728462451546507)
      ·
        refine ⟨18806200693092693677319761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12537467128728462451546507 18806200693092693677319761)
        ·
          refine ⟨14104650519819520257989821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18806200693092693677319761 14104650519819520257989821)
          ·
            refine ⟨5289243944932320096746183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14104650519819520257989821 5289243944932320096746183)
            ·
              refine ⟨7933865917398480145119275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289243944932320096746183 7933865917398480145119275)
              ·
                refine ⟨11900798876097720217678913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7933865917398480145119275 11900798876097720217678913)
                ·
                  refine ⟨8925599157073290163259185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11900798876097720217678913 8925599157073290163259185)
                  ·
                    refine ⟨6694199367804967622444389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8925599157073290163259185 6694199367804967622444389)
                    ·
                      refine ⟨1255162381463431429208323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6694199367804967622444389 1255162381463431429208323)
                      ·
                        rfl

theorem cell23_2444420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2444420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444420 prefixEnd_2444420 := by exact prefixLift 2444420
  have htrace : WordTrace (prefixWord ++ tailWord_2444420) baseStart_2444420 baseEnd_2444420 := by
    simpa [prefixWord, tailWord_2444420, baseEnd_2444420] using wordTrace_append hprefix tailTrace_2444420
  have hstable : (prefixWord ++ tailWord_2444420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444420).length < 2 ^ (prefixWord ++ tailWord_2444420).sum := by decide
  have hdescent : baseEnd_2444420 < baseStart_2444420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444424 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2444424 : Nat := 118140960795 + 2444424 * 2 ^ 59
def prefixEnd_2444424 : Nat := 4983230072969 + 3 ^ 40 * 2444424 * 2
def baseEnd_2444424 : Nat := 1255164435386049413558305

theorem tailTrace_2444424 : CollatzResearch.WordTrace tailWord_2444424 prefixEnd_2444424 1255164435386049413558305 := by
  unfold tailWord_2444424
  simp only [CollatzResearch.WordTrace]
  refine ⟨44577733848138398613738163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59436978464184531484984217 44577733848138398613738163)
  ·
    refine ⟨66866600772207597920607245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44577733848138398613738163 66866600772207597920607245)
    ·
      refine ⟨25074975289577849220227717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66866600772207597920607245 25074975289577849220227717)
      ·
        refine ⟨4701557866795846728792697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25074975289577849220227717 4701557866795846728792697)
        ·
          refine ⟨3526168400096885046594523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4701557866795846728792697 3526168400096885046594523)
          ·
            refine ⟨5289252600145327569891785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526168400096885046594523 5289252600145327569891785)
            ·
              refine ⟨3966939450108995677418839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5289252600145327569891785 3966939450108995677418839)
              ·
                refine ⟨5950409175163493516128259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966939450108995677418839 5950409175163493516128259)
                ·
                  refine ⟨8925613762745240274192389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5950409175163493516128259 8925613762745240274192389)
                  ·
                    refine ⟨1673552580514732551411073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8925613762745240274192389 1673552580514732551411073)
                    ·
                      refine ⟨1255164435386049413558305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673552580514732551411073 1255164435386049413558305)
                      ·
                        rfl

theorem cell23_2444424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2444424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444424 prefixEnd_2444424 := by exact prefixLift 2444424
  have htrace : WordTrace (prefixWord ++ tailWord_2444424) baseStart_2444424 baseEnd_2444424 := by
    simpa [prefixWord, tailWord_2444424, baseEnd_2444424] using wordTrace_append hprefix tailTrace_2444424
  have hstable : (prefixWord ++ tailWord_2444424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444424).length < 2 ^ (prefixWord ++ tailWord_2444424).sum := by decide
  have hdescent : baseEnd_2444424 < baseStart_2444424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444430 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_2444430 : Nat := 118140960795 + 2444430 * 2 ^ 59
def prefixEnd_2444430 : Nat := 4983230072969 + 3 ^ 40 * 2444430 * 2
def baseEnd_2444430 : Nat := 139463057363330710009253

theorem tailTrace_2444430 : CollatzResearch.WordTrace tailWord_2444430 prefixEnd_2444430 139463057363330710009253 := by
  unfold tailWord_2444430
  simp only [CollatzResearch.WordTrace]
  refine ⟨11144460816781882531524343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59437124356170040168129829 11144460816781882531524343)
  ·
    refine ⟨16716691225172823797286515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11144460816781882531524343 16716691225172823797286515)
    ·
      refine ⟨25075036837759235695929773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16716691225172823797286515 25075036837759235695929773)
      ·
        refine ⟨9403138814159713385973665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25075036837759235695929773 9403138814159713385973665)
        ·
          refine ⟨7052354110619785039480249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9403138814159713385973665 7052354110619785039480249)
          ·
            refine ⟨5289265582964838779610187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7052354110619785039480249 5289265582964838779610187)
            ·
              refine ⟨7933898374447258169415281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289265582964838779610187 7933898374447258169415281)
              ·
                refine ⟨5950423780835443627061461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7933898374447258169415281 5950423780835443627061461)
                ·
                  refine ⟨139463057363330710009253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5950423780835443627061461 139463057363330710009253)
                  ·
                    rfl

theorem cell23_2444430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_2444430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444430 prefixEnd_2444430 := by exact prefixLift 2444430
  have htrace : WordTrace (prefixWord ++ tailWord_2444430) baseStart_2444430 baseEnd_2444430 := by
    simpa [prefixWord, tailWord_2444430, baseEnd_2444430] using wordTrace_append hprefix tailTrace_2444430
  have hstable : (prefixWord ++ tailWord_2444430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444430).length < 2 ^ (prefixWord ++ tailWord_2444430).sum := by decide
  have hdescent : baseEnd_2444430 < baseStart_2444430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444458 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2444458 : Nat := 118140960795 + 2444458 * 2 ^ 59
def prefixEnd_2444458 : Nat := 4983230072969 + 3 ^ 40 * 2444458 * 2
def baseEnd_2444458 : Nat := 1255181893728302280533149

theorem tailTrace_2444458 : CollatzResearch.WordTrace tailWord_2444458 prefixEnd_2444458 1255181893728302280533149 := by
  unfold tailWord_2444458
  simp only [CollatzResearch.WordTrace]
  refine ⟨22289176944538405258553507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59437805185435747356142685 22289176944538405258553507)
  ·
    refine ⟨33433765416807607887830261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22289176944538405258553507 33433765416807607887830261)
    ·
      refine ⟨3134415507825713239484087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33433765416807607887830261 3134415507825713239484087)
      ·
        refine ⟨4701623261738569859226131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3134415507825713239484087 4701623261738569859226131)
        ·
          refine ⟨7052434892607854788839197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701623261738569859226131 7052434892607854788839197)
          ·
            refine ⟨2644663084727945545814699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7052434892607854788839197 2644663084727945545814699)
            ·
              refine ⟨3966994627091918318722049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644663084727945545814699 3966994627091918318722049)
              ·
                refine ⟨2975245970318938739041537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966994627091918318722049 2975245970318938739041537)
                ·
                  refine ⟨2231434477739204054281153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2975245970318938739041537 2231434477739204054281153)
                  ·
                    refine ⟨1673575858304403040710865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2231434477739204054281153 1673575858304403040710865)
                    ·
                      refine ⟨1255181893728302280533149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673575858304403040710865 1255181893728302280533149)
                      ·
                        rfl

theorem cell23_2444458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2444458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444458 prefixEnd_2444458 := by exact prefixLift 2444458
  have htrace : WordTrace (prefixWord ++ tailWord_2444458) baseStart_2444458 baseEnd_2444458 := by
    simpa [prefixWord, tailWord_2444458, baseEnd_2444458] using wordTrace_append hprefix tailTrace_2444458
  have hstable : (prefixWord ++ tailWord_2444458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444458).length < 2 ^ (prefixWord ++ tailWord_2444458).sum := by decide
  have hdescent : baseEnd_2444458 < baseStart_2444458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444503 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 8]
def baseStart_2444503 : Nat := 118140960795 + 2444503 * 2 ^ 59
def prefixEnd_2444503 : Nat := 4983230072969 + 3 ^ 40 * 2444503 * 2
def baseEnd_2444503 : Nat := 139467222261972733830049

theorem tailTrace_2444503 : CollatzResearch.WordTrace tailWord_2444503 prefixEnd_2444503 139467222261972733830049 := by
  unfold tailWord_2444503
  simp only [CollatzResearch.WordTrace]
  refine ⟨89158349062990593719602163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59438899375327062479734775 89158349062990593719602163)
  ·
    refine ⟨133737523594485890579403245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89158349062990593719602163 133737523594485890579403245)
    ·
      refine ⟨50151571347932208967276217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133737523594485890579403245 50151571347932208967276217)
      ·
        refine ⟨37613678510949156725457163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50151571347932208967276217 37613678510949156725457163)
        ·
          refine ⟨56420517766423735088185745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37613678510949156725457163 56420517766423735088185745)
          ·
            refine ⟨42315388324817801316139309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56420517766423735088185745 42315388324817801316139309)
            ·
              refine ⟨15868270621806675493552241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42315388324817801316139309 15868270621806675493552241)
              ·
                refine ⟨11901202966355006620164181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15868270621806675493552241 11901202966355006620164181)
                ·
                  refine ⟨139467222261972733830049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11901202966355006620164181 139467222261972733830049)
                  ·
                    rfl

theorem cell23_2444503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 8].length) (baseStart_2444503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444503 prefixEnd_2444503 := by exact prefixLift 2444503
  have htrace : WordTrace (prefixWord ++ tailWord_2444503) baseStart_2444503 baseEnd_2444503 := by
    simpa [prefixWord, tailWord_2444503, baseEnd_2444503] using wordTrace_append hprefix tailTrace_2444503
  have hstable : (prefixWord ++ tailWord_2444503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444503).length < 2 ^ (prefixWord ++ tailWord_2444503).sum := by decide
  have hdescent : baseEnd_2444503 < baseStart_2444503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444520 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 6]
def baseStart_2444520 : Nat := 118140960795 + 2444520 * 2 ^ 59
def prefixEnd_2444520 : Nat := 4983230072969 + 3 ^ 40 * 2444520 * 2
def baseEnd_2444520 : Nat := 139468192169875670884207

theorem tailTrace_2444520 : CollatzResearch.WordTrace tailWord_2444520 prefixEnd_2444520 139468192169875670884207 := by
  unfold tailWord_2444520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44579484551964502811485507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59439312735952670415314009 44579484551964502811485507)
  ·
    refine ⟨66869226827946754217228261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44579484551964502811485507 66869226827946754217228261)
    ·
      refine ⟨12537980030240016415730299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66869226827946754217228261 12537980030240016415730299)
      ·
        refine ⟨18806970045360024623595449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12537980030240016415730299 18806970045360024623595449)
        ·
          refine ⟨14105227534020018467696587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18806970045360024623595449 14105227534020018467696587)
          ·
            refine ⟨21157841301030027701544881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14105227534020018467696587 21157841301030027701544881)
            ·
              refine ⟨15868380975772520776158661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21157841301030027701544881 15868380975772520776158661)
              ·
                refine ⟨2975321432957347645529749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15868380975772520776158661 2975321432957347645529749)
                ·
                  refine ⟨139468192169875670884207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2975321432957347645529749 139468192169875670884207)
                  ·
                    rfl

theorem cell23_2444520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 6].length) (baseStart_2444520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444520 prefixEnd_2444520 := by exact prefixLift 2444520
  have htrace : WordTrace (prefixWord ++ tailWord_2444520) baseStart_2444520 baseEnd_2444520 := by
    simpa [prefixWord, tailWord_2444520, baseEnd_2444520] using wordTrace_append hprefix tailTrace_2444520
  have hstable : (prefixWord ++ tailWord_2444520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444520).length < 2 ^ (prefixWord ++ tailWord_2444520).sum := by decide
  have hdescent : baseEnd_2444520 < baseStart_2444520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444580 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_2444580 : Nat := 118140960795 + 2444580 * 2 ^ 59
def prefixEnd_2444580 : Nat := 4983230072969 + 3 ^ 40 * 2444580 * 2
def baseEnd_2444580 : Nat := 418414846122716934402529

theorem tailTrace_2444580 : CollatzResearch.WordTrace tailWord_2444580 prefixEnd_2444580 418414846122716934402529 := by
  unfold tailWord_2444580
  simp only [CollatzResearch.WordTrace]
  refine ⟨44580578741855817935077597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59440771655807757246770129 44580578741855817935077597)
  ·
    refine ⟨16717717028195931725654099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44580578741855817935077597 16717717028195931725654099)
    ·
      refine ⟨25076575542293897588481149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16717717028195931725654099 25076575542293897588481149)
      ·
        refine ⟨9403715828360211595680431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25076575542293897588481149 9403715828360211595680431)
        ·
          refine ⟨14105573742540317393520647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9403715828360211595680431 14105573742540317393520647)
          ·
            refine ⟨21158360613810476090280971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14105573742540317393520647 21158360613810476090280971)
            ·
              refine ⟨31737540920715714135421457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21158360613810476090280971 31737540920715714135421457)
              ·
                refine ⟨23803155690536785601566093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31737540920715714135421457 23803155690536785601566093)
                ·
                  refine ⟨8926183383951294600587285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23803155690536785601566093 8926183383951294600587285)
                  ·
                    refine ⟨418414846122716934402529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8926183383951294600587285 418414846122716934402529)
                    ·
                      rfl

theorem cell23_2444580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_2444580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444580 prefixEnd_2444580 := by exact prefixLift 2444580
  have htrace : WordTrace (prefixWord ++ tailWord_2444580) baseStart_2444580 baseEnd_2444580 := by
    simpa [prefixWord, tailWord_2444580, baseEnd_2444580] using wordTrace_append hprefix tailTrace_2444580
  have hstable : (prefixWord ++ tailWord_2444580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444580).length < 2 ^ (prefixWord ++ tailWord_2444580).sum := by decide
  have hdescent : baseEnd_2444580 < baseStart_2444580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444581 : List Nat := [1, 3, 1, 2, 4, 2, 1, 4, 1, 1, 3]
def baseStart_2444581 : Nat := 118140960795 + 2444581 * 2 ^ 59
def prefixEnd_2444581 : Nat := 4983230072969 + 3 ^ 40 * 2444581 * 2
def baseEnd_2444581 : Nat := 1255245051848805299295083

theorem tailTrace_2444581 : CollatzResearch.WordTrace tailWord_2444581 prefixEnd_2444581 1255245051848805299295083 := by
  unfold tailWord_2444581
  simp only [CollatzResearch.WordTrace]
  refine ⟨89161193956708013040941597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59440795971138675360627731 89161193956708013040941597)
  ·
    refine ⟨33435447733765504890353099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89161193956708013040941597 33435447733765504890353099)
    ·
      refine ⟨50153171600648257335529649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33435447733765504890353099 50153171600648257335529649)
      ·
        refine ⟨37614878700486193001647237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50153171600648257335529649 37614878700486193001647237)
        ·
          refine ⟨7052789756341161187808857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37614878700486193001647237 7052789756341161187808857)
          ·
            refine ⟨5289592317255870890856643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7052789756341161187808857 5289592317255870890856643)
            ·
              refine ⟨7934388475883806336284965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289592317255870890856643 7934388475883806336284965)
              ·
                refine ⟨1487697839228213688053431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7934388475883806336284965 1487697839228213688053431)
                ·
                  refine ⟨2231546758842320532080147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487697839228213688053431 2231546758842320532080147)
                  ·
                    refine ⟨3347320138263480798120221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2231546758842320532080147 3347320138263480798120221)
                    ·
                      refine ⟨1255245051848805299295083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3347320138263480798120221 1255245051848805299295083)
                      ·
                        rfl

theorem cell23_2444581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_2444581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444581 prefixEnd_2444581 := by exact prefixLift 2444581
  have htrace : WordTrace (prefixWord ++ tailWord_2444581) baseStart_2444581 baseEnd_2444581 := by
    simpa [prefixWord, tailWord_2444581, baseEnd_2444581] using wordTrace_append hprefix tailTrace_2444581
  have hstable : (prefixWord ++ tailWord_2444581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444581).length < 2 ^ (prefixWord ++ tailWord_2444581).sum := by decide
  have hdescent : baseEnd_2444581 < baseStart_2444581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444597 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_2444597 : Nat := 118140960795 + 2444597 * 2 ^ 59
def prefixEnd_2444597 : Nat := 4983230072969 + 3 ^ 40 * 2444597 * 2
def baseEnd_2444597 : Nat := 418417755846425745565003

theorem tailTrace_2444597 : CollatzResearch.WordTrace tailWord_2444597 prefixEnd_2444597 418417755846425745565003 := by
  unfold tailWord_2444597
  simp only [CollatzResearch.WordTrace]
  refine ⟨89161777524650047773524045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59441185016433365182349363 89161777524650047773524045)
  ·
    refine ⟨33435666571743767915071517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89161777524650047773524045 33435666571743767915071517)
    ·
      refine ⟨12538374964403912968151819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33435666571743767915071517 12538374964403912968151819)
      ·
        refine ⟨18807562446605869452227729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12538374964403912968151819 18807562446605869452227729)
        ·
          refine ⟨14105671834954402089170797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18807562446605869452227729 14105671834954402089170797)
          ·
            refine ⟨5289626938107900783439049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14105671834954402089170797 5289626938107900783439049)
            ·
              refine ⟨3967220203580925587579287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5289626938107900783439049 3967220203580925587579287)
              ·
                refine ⟨5950830305371388381368931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967220203580925587579287 5950830305371388381368931)
                ·
                  refine ⟨8926245458057082572053397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5950830305371388381368931 8926245458057082572053397)
                  ·
                    refine ⟨418417755846425745565003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8926245458057082572053397 418417755846425745565003)
                    ·
                      rfl

theorem cell23_2444597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_2444597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444597 prefixEnd_2444597 := by exact prefixLift 2444597
  have htrace : WordTrace (prefixWord ++ tailWord_2444597) baseStart_2444597 baseEnd_2444597 := by
    simpa [prefixWord, tailWord_2444597, baseEnd_2444597] using wordTrace_append hprefix tailTrace_2444597
  have hstable : (prefixWord ++ tailWord_2444597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444597).length < 2 ^ (prefixWord ++ tailWord_2444597).sum := by decide
  have hdescent : baseEnd_2444597 < baseStart_2444597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444598 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2444598 : Nat := 118140960795 + 2444598 * 2 ^ 59
def prefixEnd_2444598 : Nat := 4983230072969 + 3 ^ 40 * 2444598 * 2
def baseEnd_2444598 : Nat := 1255253781019931732782505

theorem tailTrace_2444598 : CollatzResearch.WordTrace tailWord_2444598 prefixEnd_2444598 1255253781019931732782505 := by
  unfold tailWord_2444598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5572613374852901559019403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59441209331764283296206965 5572613374852901559019403)
  ·
    refine ⟨8358920062279352338529105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5572613374852901559019403 8358920062279352338529105)
    ·
      refine ⟨6269190046709514253896829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8358920062279352338529105 6269190046709514253896829)
      ·
        refine ⟨2350946267516067845211311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6269190046709514253896829 2350946267516067845211311)
        ·
          refine ⟨3526419401274101767816967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350946267516067845211311 3526419401274101767816967)
          ·
            refine ⟨5289629101911152651725451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526419401274101767816967 5289629101911152651725451)
            ·
              refine ⟨7934443652866728977588177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5289629101911152651725451 7934443652866728977588177)
              ·
                refine ⟨5950832739650046733191133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7934443652866728977588177 5950832739650046733191133)
                ·
                  refine ⟨2231562277368767524946675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5950832739650046733191133 2231562277368767524946675)
                  ·
                    refine ⟨3347343416053151287420013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2231562277368767524946675 3347343416053151287420013)
                    ·
                      refine ⟨1255253781019931732782505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3347343416053151287420013 1255253781019931732782505)
                      ·
                        rfl

theorem cell23_2444598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2444598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444598 prefixEnd_2444598 := by exact prefixLift 2444598
  have htrace : WordTrace (prefixWord ++ tailWord_2444598) baseStart_2444598 baseEnd_2444598 := by
    simpa [prefixWord, tailWord_2444598, baseEnd_2444598] using wordTrace_append hprefix tailTrace_2444598
  have hstable : (prefixWord ++ tailWord_2444598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444598).length < 2 ^ (prefixWord ++ tailWord_2444598).sum := by decide
  have hdescent : baseEnd_2444598 < baseStart_2444598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444604 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_2444604 : Nat := 118140960795 + 2444604 * 2 ^ 59
def prefixEnd_2444604 : Nat := 4983230072969 + 3 ^ 40 * 2444604 * 2
def baseEnd_2444604 : Nat := 1255256861903858709307477

theorem tailTrace_2444604 : CollatzResearch.WordTrace tailWord_2444604 prefixEnd_2444604 1255256861903858709307477 := by
  unfold tailWord_2444604
  simp only [CollatzResearch.WordTrace]
  refine ⟨44581016417812343984514433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59441355223749791979352577 44581016417812343984514433)
  ·
    refine ⟨33435762313359257988385825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44581016417812343984514433 33435762313359257988385825)
    ·
      refine ⟨25076821735019443491289369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33435762313359257988385825 25076821735019443491289369)
      ·
        refine ⟨18807616301264582618467027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25076821735019443491289369 18807616301264582618467027)
        ·
          refine ⟨28211424451896873927700541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18807616301264582618467027 28211424451896873927700541)
          ·
            refine ⟨10579284169461327722887703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28211424451896873927700541 10579284169461327722887703)
            ·
              refine ⟨15868926254191991584331555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10579284169461327722887703 15868926254191991584331555)
              ·
                refine ⟨23803389381287987376497333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15868926254191991584331555 23803389381287987376497333)
                ·
                  refine ⟨2231567754495748816546625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23803389381287987376497333 2231567754495748816546625)
                  ·
                    refine ⟨1673675815871811612409969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2231567754495748816546625 1673675815871811612409969)
                    ·
                      refine ⟨1255256861903858709307477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673675815871811612409969 1255256861903858709307477)
                      ·
                        rfl

theorem cell23_2444604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_2444604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444604 prefixEnd_2444604 := by exact prefixLift 2444604
  have htrace : WordTrace (prefixWord ++ tailWord_2444604) baseStart_2444604 baseEnd_2444604 := by
    simpa [prefixWord, tailWord_2444604, baseEnd_2444604] using wordTrace_append hprefix tailTrace_2444604
  have hstable : (prefixWord ++ tailWord_2444604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444604).length < 2 ^ (prefixWord ++ tailWord_2444604).sum := by decide
  have hdescent : baseEnd_2444604 < baseStart_2444604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444607 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 3]
def baseStart_2444607 : Nat := 118140960795 + 2444607 * 2 ^ 59
def prefixEnd_2444607 : Nat := 4983230072969 + 3 ^ 40 * 2444607 * 2
def baseEnd_2444607 : Nat := 1255258402345822197569963

theorem tailTrace_2444607 : CollatzResearch.WordTrace tailWord_2444607 prefixEnd_2444607 1255258402345822197569963 := by
  unfold tailWord_2444607
  simp only [CollatzResearch.WordTrace]
  refine ⟨89162142254613819481388075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59441428169742546320925383 89162142254613819481388075)
  ·
    refine ⟨133743213381920729222082113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89162142254613819481388075 133743213381920729222082113)
    ·
      refine ⟨100307410036440546916561585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133743213381920729222082113 100307410036440546916561585)
      ·
        refine ⟨75230557527330410187421189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100307410036440546916561585 75230557527330410187421189)
        ·
          refine ⟨14105729536374451910141473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75230557527330410187421189 14105729536374451910141473)
          ·
            refine ⟨10579297152280838932606105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14105729536374451910141473 10579297152280838932606105)
            ·
              refine ⟨7934472864210629199454579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10579297152280838932606105 7934472864210629199454579)
              ·
                refine ⟨11901709296315943799181869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7934472864210629199454579 11901709296315943799181869)
                ·
                  refine ⟨4463140986118478924693201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11901709296315943799181869 4463140986118478924693201)
                  ·
                    refine ⟨3347355739588859193519901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4463140986118478924693201 3347355739588859193519901)
                    ·
                      refine ⟨1255258402345822197569963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3347355739588859193519901 1255258402345822197569963)
                      ·
                        rfl

theorem cell23_2444607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_2444607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444607 prefixEnd_2444607 := by exact prefixLift 2444607
  have htrace : WordTrace (prefixWord ++ tailWord_2444607) baseStart_2444607 baseEnd_2444607 := by
    simpa [prefixWord, tailWord_2444607, baseEnd_2444607] using wordTrace_append hprefix tailTrace_2444607
  have hstable : (prefixWord ++ tailWord_2444607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444607).length < 2 ^ (prefixWord ++ tailWord_2444607).sum := by decide
  have hdescent : baseEnd_2444607 < baseStart_2444607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444661 : List Nat := [1, 3, 4, 1, 4, 1, 2, 7]
def baseStart_2444661 : Nat := 118140960795 + 2444661 * 2 ^ 59
def prefixEnd_2444661 : Nat := 4983230072969 + 3 ^ 40 * 2444661 * 2
def baseEnd_2444661 : Nat := 46492078900043147640545

theorem tailTrace_2444661 : CollatzResearch.WordTrace tailWord_2444661 prefixEnd_2444661 46492078900043147640545 := by
  unfold tailWord_2444661
  simp only [CollatzResearch.WordTrace]
  refine ⟨89164111796418186703853837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59442741197612124469235891 89164111796418186703853837)
  ·
    refine ⟨33436541923656820013945189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89164111796418186703853837 33436541923656820013945189)
    ·
      refine ⟨6269351610685653752614723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33436541923656820013945189 6269351610685653752614723)
      ·
        refine ⟨9404027416028480628922085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6269351610685653752614723 9404027416028480628922085)
        ·
          refine ⟨1763255140505340117922891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9404027416028480628922085 1763255140505340117922891)
          ·
            refine ⟨2644882710758010176884337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763255140505340117922891 2644882710758010176884337)
            ·
              refine ⟨1983662033068507632663253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644882710758010176884337 1983662033068507632663253)
              ·
                refine ⟨46492078900043147640545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1983662033068507632663253 46492078900043147640545)
                ·
                  rfl

theorem cell23_2444661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 7].length) (baseStart_2444661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444661 prefixEnd_2444661 := by exact prefixLift 2444661
  have htrace : WordTrace (prefixWord ++ tailWord_2444661) baseStart_2444661 baseEnd_2444661 := by
    simpa [prefixWord, tailWord_2444661, baseEnd_2444661] using wordTrace_append hprefix tailTrace_2444661
  have hstable : (prefixWord ++ tailWord_2444661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444661).length < 2 ^ (prefixWord ++ tailWord_2444661).sum := by decide
  have hdescent : baseEnd_2444661 < baseStart_2444661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444734 : List Nat := [4, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_2444734 : Nat := 118140960795 + 2444734 * 2 ^ 59
def prefixEnd_2444734 : Nat := 4983230072969 + 3 ^ 40 * 2444734 * 2
def baseEnd_2444734 : Nat := 139480401598771466742431

theorem tailTrace_2444734 : CollatzResearch.WordTrace tailWord_2444734 prefixEnd_2444734 139480401598771466742431 := by
  unfold tailWord_2444734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11145846790644215021407657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59444516216769146780840837 11145846790644215021407657)
  ·
    refine ⟨8359385092983161266055743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11145846790644215021407657 8359385092983161266055743)
    ·
      refine ⟨12539077639474741899083615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8359385092983161266055743 12539077639474741899083615)
      ·
        refine ⟨18808616459212112848625423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12539077639474741899083615 18808616459212112848625423)
        ·
          refine ⟨28212924688818169272938135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18808616459212112848625423 28212924688818169272938135)
          ·
            refine ⟨42319387033227253909407203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28212924688818169272938135 42319387033227253909407203)
            ·
              refine ⟨63479080549840880864110805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42319387033227253909407203 63479080549840880864110805)
              ·
                refine ⟨1487790950386895645252597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63479080549840880864110805 1487790950386895645252597)
                ·
                  refine ⟨139480401598771466742431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487790950386895645252597 139480401598771466742431)
                  ·
                    rfl

theorem cell23_2444734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_2444734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444734 prefixEnd_2444734 := by exact prefixLift 2444734
  have htrace : WordTrace (prefixWord ++ tailWord_2444734) baseStart_2444734 baseEnd_2444734 := by
    simpa [prefixWord, tailWord_2444734, baseEnd_2444734] using wordTrace_append hprefix tailTrace_2444734
  have hstable : (prefixWord ++ tailWord_2444734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444734).length < 2 ^ (prefixWord ++ tailWord_2444734).sum := by decide
  have hdescent : baseEnd_2444734 < baseStart_2444734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444747 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 2, 5]
def baseStart_2444747 : Nat := 118140960795 + 2444747 * 2 ^ 59
def prefixEnd_2444747 : Nat := 4983230072969 + 3 ^ 40 * 2444747 * 2
def baseEnd_2444747 : Nat := 418443429879150549939773

theorem tailTrace_2444747 : CollatzResearch.WordTrace tailWord_2444747 prefixEnd_2444747 418443429879150549939773 := by
  unfold tailWord_2444747
  simp only [CollatzResearch.WordTrace]
  refine ⟨89167248474106623391484495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59444832316071082260989663 89167248474106623391484495)
  ·
    refine ⟨133750872711159935087226743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89167248474106623391484495 133750872711159935087226743)
    ·
      refine ⟨200626309066739902630840115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133750872711159935087226743 200626309066739902630840115)
      ·
        refine ⟨300939463600109853946260173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200626309066739902630840115 300939463600109853946260173)
        ·
          refine ⟨112852298850041195229847565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300939463600109853946260173 112852298850041195229847565)
          ·
            refine ⟨42319612068765448211192837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112852298850041195229847565 42319612068765448211192837)
            ·
              refine ⟨7934927262893521539598657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42319612068765448211192837 7934927262893521539598657)
              ·
                refine ⟨5951195447170141154698993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7934927262893521539598657 5951195447170141154698993)
                ·
                  refine ⟨4463396585377605866024245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951195447170141154698993 4463396585377605866024245)
                  ·
                    refine ⟨418443429879150549939773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4463396585377605866024245 418443429879150549939773)
                    ·
                      rfl

theorem cell23_2444747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 5].length) (baseStart_2444747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444747 prefixEnd_2444747 := by exact prefixLift 2444747
  have htrace : WordTrace (prefixWord ++ tailWord_2444747) baseStart_2444747 baseEnd_2444747 := by
    simpa [prefixWord, tailWord_2444747, baseEnd_2444747] using wordTrace_append hprefix tailTrace_2444747
  have hstable : (prefixWord ++ tailWord_2444747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444747).length < 2 ^ (prefixWord ++ tailWord_2444747).sum := by decide
  have hdescent : baseEnd_2444747 < baseStart_2444747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444757 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2444757 : Nat := 118140960795 + 2444757 * 2 ^ 59
def prefixEnd_2444757 : Nat := 4983230072969 + 3 ^ 40 * 2444757 * 2
def baseEnd_2444757 : Nat := 1255335424443996610694273

theorem tailTrace_2444757 : CollatzResearch.WordTrace tailWord_2444757 prefixEnd_2444757 1255335424443996610694273 := by
  unfold tailWord_2444757
  simp only [CollatzResearch.WordTrace]
  refine ⟨89167613204070395099348525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59445075469380263399565683 89167613204070395099348525)
  ·
    refine ⟨33437854951526398162255697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89167613204070395099348525 33437854951526398162255697)
    ·
      refine ⟨25078391213644798621691773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33437854951526398162255697 25078391213644798621691773)
      ·
        refine ⟨9404396705116799483134415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25078391213644798621691773 9404396705116799483134415)
        ·
          refine ⟨14106595057675199224701623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9404396705116799483134415 14106595057675199224701623)
          ·
            refine ⟨21159892586512798837052435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14106595057675199224701623 21159892586512798837052435)
            ·
              refine ⟨31739838879769198255578653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21159892586512798837052435 31739838879769198255578653)
              ·
                refine ⟨11902439579913449345841995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31739838879769198255578653 11902439579913449345841995)
                ·
                  refine ⟨17853659369870174018762993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11902439579913449345841995 17853659369870174018762993)
                  ·
                    refine ⟨13390244527402630514072245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17853659369870174018762993 13390244527402630514072245)
                    ·
                      refine ⟨1255335424443996610694273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13390244527402630514072245 1255335424443996610694273)
                      ·
                        rfl

theorem cell23_2444757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2444757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444757 prefixEnd_2444757 := by exact prefixLift 2444757
  have htrace : WordTrace (prefixWord ++ tailWord_2444757) baseStart_2444757 baseEnd_2444757 := by
    simpa [prefixWord, tailWord_2444757, baseEnd_2444757] using wordTrace_append hprefix tailTrace_2444757
  have hstable : (prefixWord ++ tailWord_2444757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444757).length < 2 ^ (prefixWord ++ tailWord_2444757).sum := by decide
  have hdescent : baseEnd_2444757 < baseStart_2444757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444767 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_2444767 : Nat := 118140960795 + 2444767 * 2 ^ 59
def prefixEnd_2444767 : Nat := 4983230072969 + 3 ^ 40 * 2444767 * 2
def baseEnd_2444767 : Nat := 1255340559250541571569227

theorem tailTrace_2444767 : CollatzResearch.WordTrace tailWord_2444767 prefixEnd_2444767 1255340559250541571569227 := by
  unfold tailWord_2444767
  simp only [CollatzResearch.WordTrace]
  refine ⟨89167977934034166807212555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59445318622689444538141703 89167977934034166807212555)
  ·
    refine ⟨133751966901051250210818833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89167977934034166807212555 133751966901051250210818833)
    ·
      refine ⟨100313975175788437658114125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133751966901051250210818833 100313975175788437658114125)
      ·
        refine ⟨37617740690920664121792797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100313975175788437658114125 37617740690920664121792797)
        ·
          refine ⟨14106652759095249045672299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37617740690920664121792797 14106652759095249045672299)
          ·
            refine ⟨21159979138642873568508449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14106652759095249045672299 21159979138642873568508449)
            ·
              refine ⟨15869984353982155176381337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21159979138642873568508449 15869984353982155176381337)
              ·
                refine ⟨11902488265486616382286003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15869984353982155176381337 11902488265486616382286003)
                ·
                  refine ⟨17853732398229924573429005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11902488265486616382286003 17853732398229924573429005)
                  ·
                    refine ⟨6695149649336221715035877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17853732398229924573429005 6695149649336221715035877)
                    ·
                      refine ⟨1255340559250541571569227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6695149649336221715035877 1255340559250541571569227)
                      ·
                        rfl

theorem cell23_2444767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_2444767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444767 prefixEnd_2444767 := by exact prefixLift 2444767
  have htrace : WordTrace (prefixWord ++ tailWord_2444767) baseStart_2444767 baseEnd_2444767 := by
    simpa [prefixWord, tailWord_2444767, baseEnd_2444767] using wordTrace_append hprefix tailTrace_2444767
  have hstable : (prefixWord ++ tailWord_2444767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444767).length < 2 ^ (prefixWord ++ tailWord_2444767).sum := by decide
  have hdescent : baseEnd_2444767 < baseStart_2444767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444784 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4]
def baseStart_2444784 : Nat := 118140960795 + 2444784 * 2 ^ 59
def prefixEnd_2444784 : Nat := 4983230072969 + 3 ^ 40 * 2444784 * 2
def baseEnd_2444784 : Nat := 1255349288421668005056649

theorem tailTrace_2444784 : CollatzResearch.WordTrace tailWord_2444784 prefixEnd_2444784 1255349288421668005056649 := by
  unfold tailWord_2444784
  simp only [CollatzResearch.WordTrace]
  refine ⟨44584298987486289355290703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59445731983315052473720937 44584298987486289355290703)
  ·
    refine ⟨66876448481229434032936055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44584298987486289355290703 66876448481229434032936055)
    ·
      refine ⟨100314672721844151049404083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66876448481229434032936055 100314672721844151049404083)
      ·
        refine ⟨150472009082766226574106125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100314672721844151049404083 150472009082766226574106125)
        ·
          refine ⟨56427003406037334965289797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150472009082766226574106125 56427003406037334965289797)
          ·
            refine ⟨10580063138632000305991837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56427003406037334965289797 10580063138632000305991837)
            ·
              refine ⟨3967523676987000114746939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10580063138632000305991837 3967523676987000114746939)
              ·
                refine ⟨5951285515480500172120409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967523676987000114746939 5951285515480500172120409)
                ·
                  refine ⟨4463464136610375129090307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5951285515480500172120409 4463464136610375129090307)
                  ·
                    refine ⟨6695196204915562693635461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4463464136610375129090307 6695196204915562693635461)
                    ·
                      refine ⟨1255349288421668005056649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6695196204915562693635461 1255349288421668005056649)
                      ·
                        rfl

theorem cell23_2444784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_2444784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444784 prefixEnd_2444784 := by exact prefixLift 2444784
  have htrace : WordTrace (prefixWord ++ tailWord_2444784) baseStart_2444784 baseEnd_2444784 := by
    simpa [prefixWord, tailWord_2444784, baseEnd_2444784] using wordTrace_append hprefix tailTrace_2444784
  have hstable : (prefixWord ++ tailWord_2444784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444784).length < 2 ^ (prefixWord ++ tailWord_2444784).sum := by decide
  have hdescent : baseEnd_2444784 < baseStart_2444784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444797 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_2444797 : Nat := 118140960795 + 2444797 * 2 ^ 59
def prefixEnd_2444797 : Nat := 4983230072969 + 3 ^ 40 * 2444797 * 2
def baseEnd_2444797 : Nat := 1255355963670176454194089

theorem tailTrace_2444797 : CollatzResearch.WordTrace tailWord_2444797 prefixEnd_2444797 1255355963670176454194089 := by
  unfold tailWord_2444797
  simp only [CollatzResearch.WordTrace]
  refine ⟨89169072123925481930804645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59446048082616987953869763 89169072123925481930804645)
  ·
    refine ⟨16719201023236027862025871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89169072123925481930804645 16719201023236027862025871)
    ·
      refine ⟨25078801534854041793038807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16719201023236027862025871 25078801534854041793038807)
      ·
        refine ⟨37618202302281062689558211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25078801534854041793038807 37618202302281062689558211)
        ·
          refine ⟨56427303453421594034337317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37618202302281062689558211 56427303453421594034337317)
          ·
            refine ⟨10580119397516548881438247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56427303453421594034337317 10580119397516548881438247)
            ·
              refine ⟨15870179096274823322157371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10580119397516548881438247 15870179096274823322157371)
              ·
                refine ⟨23805268644412234983236057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15870179096274823322157371 23805268644412234983236057)
                ·
                  refine ⟨17853951483309176237427043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23805268644412234983236057 17853951483309176237427043)
                  ·
                    refine ⟨26780927224963764356140565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17853951483309176237427043 26780927224963764356140565)
                    ·
                      refine ⟨1255355963670176454194089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26780927224963764356140565 1255355963670176454194089)
                      ·
                        rfl

theorem cell23_2444797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_2444797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444797 prefixEnd_2444797 := by exact prefixLift 2444797
  have htrace : WordTrace (prefixWord ++ tailWord_2444797) baseStart_2444797 baseEnd_2444797 := by
    simpa [prefixWord, tailWord_2444797, baseEnd_2444797] using wordTrace_append hprefix tailTrace_2444797
  have hstable : (prefixWord ++ tailWord_2444797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444797).length < 2 ^ (prefixWord ++ tailWord_2444797).sum := by decide
  have hdescent : baseEnd_2444797 < baseStart_2444797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444811 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 3, 4]
def baseStart_2444811 : Nat := 118140960795 + 2444811 * 2 ^ 59
def prefixEnd_2444811 : Nat := 4983230072969 + 3 ^ 40 * 2444811 * 2
def baseEnd_2444811 : Nat := 418454384133113133139675

theorem tailTrace_2444811 : CollatzResearch.WordTrace tailWord_2444811 prefixEnd_2444811 418454384133113133139675 := by
  unfold tailWord_2444811
  simp only [CollatzResearch.WordTrace]
  refine ⟨89169582745874762321814287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59446388497249841547876191 89169582745874762321814287)
  ·
    refine ⟨133754374118812143482721431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89169582745874762321814287 133754374118812143482721431)
    ·
      refine ⟨200631561178218215224082147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133754374118812143482721431 200631561178218215224082147)
      ·
        refine ⟨300947341767327322836123221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200631561178218215224082147 300947341767327322836123221)
        ·
          refine ⟨3526726661335867064485819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 300947341767327322836123221 3526726661335867064485819)
          ·
            refine ⟨5290089992003800596728729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526726661335867064485819 5290089992003800596728729)
            ·
              refine ⟨3967567494002850447546547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290089992003800596728729 3967567494002850447546547)
              ·
                refine ⟨5951351241004275671319821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967567494002850447546547 5951351241004275671319821)
                ·
                  refine ⟨2231756715376603376744933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5951351241004275671319821 2231756715376603376744933)
                  ·
                    refine ⟨418454384133113133139675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2231756715376603376744933 418454384133113133139675)
                    ·
                      rfl

theorem cell23_2444811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 4].length) (baseStart_2444811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444811 prefixEnd_2444811 := by exact prefixLift 2444811
  have htrace : WordTrace (prefixWord ++ tailWord_2444811) baseStart_2444811 baseEnd_2444811 := by
    simpa [prefixWord, tailWord_2444811, baseEnd_2444811] using wordTrace_append hprefix tailTrace_2444811
  have hstable : (prefixWord ++ tailWord_2444811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444811).length < 2 ^ (prefixWord ++ tailWord_2444811).sum := by decide
  have hdescent : baseEnd_2444811 < baseStart_2444811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444874 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_2444874 : Nat := 118140960795 + 2444874 * 2 ^ 59
def prefixEnd_2444874 : Nat := 4983230072969 + 3 ^ 40 * 2444874 * 2
def baseEnd_2444874 : Nat := 1255395501680572652931235

theorem tailTrace_2444874 : CollatzResearch.WordTrace tailWord_2444874 prefixEnd_2444874 1255395501680572652931235 := by
  unfold tailWord_2444874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22292970136161631020339419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59447920363097682720905117 22292970136161631020339419)
  ·
    refine ⟨33439455204242446530509129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22292970136161631020339419 33439455204242446530509129)
    ·
      refine ⟨25079591403181834897881847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33439455204242446530509129 25079591403181834897881847)
      ·
        refine ⟨37619387104772752346822771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25079591403181834897881847 37619387104772752346822771)
        ·
          refine ⟨56429080657159128520234157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37619387104772752346822771 56429080657159128520234157)
          ·
            refine ⟨21160905246434673195087809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56429080657159128520234157 21160905246434673195087809)
            ·
              refine ⟨15870678934826004896315857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21160905246434673195087809 15870678934826004896315857)
              ·
                refine ⟨11903009201119503672236893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15870678934826004896315857 11903009201119503672236893)
                ·
                  refine ⟨4463628450419813877088835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11903009201119503672236893 4463628450419813877088835)
                  ·
                    refine ⟨6695442675629720815633253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4463628450419813877088835 6695442675629720815633253)
                    ·
                      refine ⟨1255395501680572652931235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6695442675629720815633253 1255395501680572652931235)
                      ·
                        rfl

theorem cell23_2444874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_2444874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444874 prefixEnd_2444874 := by exact prefixLift 2444874
  have htrace : WordTrace (prefixWord ++ tailWord_2444874) baseStart_2444874 baseEnd_2444874 := by
    simpa [prefixWord, tailWord_2444874, baseEnd_2444874] using wordTrace_append hprefix tailTrace_2444874
  have hstable : (prefixWord ++ tailWord_2444874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444874).length < 2 ^ (prefixWord ++ tailWord_2444874).sum := by decide
  have hdescent : baseEnd_2444874 < baseStart_2444874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444884 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_2444884 : Nat := 118140960795 + 2444884 * 2 ^ 59
def prefixEnd_2444884 : Nat := 4983230072969 + 3 ^ 40 * 2444884 * 2
def baseEnd_2444884 : Nat := 418466878829039204602063

theorem tailTrace_2444884 : CollatzResearch.WordTrace tailWord_2444884 prefixEnd_2444884 418466878829039204602063 := by
  unfold tailWord_2444884
  simp only [CollatzResearch.WordTrace]
  refine ⟨44586122637305147894610853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59448163516406863859481137 44586122637305147894610853)
  ·
    refine ⟨8359897994494715230239535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44586122637305147894610853 8359897994494715230239535)
    ·
      refine ⟨12539846991742072845359303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8359897994494715230239535 12539846991742072845359303)
      ·
        refine ⟨18809770487613109268038955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12539846991742072845359303 18809770487613109268038955)
        ·
          refine ⟨28214655731419663902058433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18809770487613109268038955 28214655731419663902058433)
          ·
            refine ⟨21160991798564747926543825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28214655731419663902058433 21160991798564747926543825)
            ·
              refine ⟨15870743848923560944907869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21160991798564747926543825 15870743848923560944907869)
              ·
                refine ⟨5951528943346335354340451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15870743848923560944907869 5951528943346335354340451)
                ·
                  refine ⟨8927293415019503031510677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5951528943346335354340451 8927293415019503031510677)
                  ·
                    refine ⟨418466878829039204602063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8927293415019503031510677 418466878829039204602063)
                    ·
                      rfl

theorem cell23_2444884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_2444884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444884 prefixEnd_2444884 := by exact prefixLift 2444884
  have htrace : WordTrace (prefixWord ++ tailWord_2444884) baseStart_2444884 baseEnd_2444884 := by
    simpa [prefixWord, tailWord_2444884, baseEnd_2444884] using wordTrace_append hprefix tailTrace_2444884
  have hstable : (prefixWord ++ tailWord_2444884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444884).length < 2 ^ (prefixWord ++ tailWord_2444884).sum := by decide
  have hdescent : baseEnd_2444884 < baseStart_2444884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444897 : List Nat := [1, 2, 3, 1, 1, 3, 1, 11]
def baseStart_2444897 : Nat := 118140960795 + 2444897 * 2 ^ 59
def prefixEnd_2444897 : Nat := 4983230072969 + 3 ^ 40 * 2444897 * 2
def baseEnd_2444897 : Nat := 46496567101319483812727

theorem tailTrace_2444897 : CollatzResearch.WordTrace tailWord_2444897 prefixEnd_2444897 46496567101319483812727 := by
  unfold tailWord_2444897
  simp only [CollatzResearch.WordTrace]
  refine ⟨89172719423563199009444945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59448479615708799339629963 89172719423563199009444945)
  ·
    refine ⟨66879539567672399257083709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89172719423563199009444945 66879539567672399257083709)
    ·
      refine ⟨25079827337877149721406391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66879539567672399257083709 25079827337877149721406391)
      ·
        refine ⟨37619741006815724582109587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25079827337877149721406391 37619741006815724582109587)
        ·
          refine ⟨56429611510223586873164381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37619741006815724582109587 56429611510223586873164381)
          ·
            refine ⟨21161104316333845077436643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56429611510223586873164381 21161104316333845077436643)
            ·
              refine ⟨31741656474500767616154965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21161104316333845077436643 31741656474500767616154965)
              ·
                refine ⟨46496567101319483812727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31741656474500767616154965 46496567101319483812727)
                ·
                  rfl

theorem cell23_2444897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 11].length) (baseStart_2444897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444897 prefixEnd_2444897 := by exact prefixLift 2444897
  have htrace : WordTrace (prefixWord ++ tailWord_2444897) baseStart_2444897 baseEnd_2444897 := by
    simpa [prefixWord, tailWord_2444897, baseEnd_2444897] using wordTrace_append hprefix tailTrace_2444897
  have hstable : (prefixWord ++ tailWord_2444897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444897).length < 2 ^ (prefixWord ++ tailWord_2444897).sum := by decide
  have hdescent : baseEnd_2444897 < baseStart_2444897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444918 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_2444918 : Nat := 118140960795 + 2444918 * 2 ^ 59
def prefixEnd_2444918 : Nat := 4983230072969 + 3 ^ 40 * 2444918 * 2
def baseEnd_2444918 : Nat := 418472698276456826927011

theorem tailTrace_2444918 : CollatzResearch.WordTrace tailWord_2444918 prefixEnd_2444918 418472698276456826927011 := by
  unfold tailWord_2444918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573342834780444974747463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59448990237658079730639605 5573342834780444974747463)
  ·
    refine ⟨8360014252170667462121195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5573342834780444974747463 8360014252170667462121195)
    ·
      refine ⟨12540021378256001193181793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8360014252170667462121195 12540021378256001193181793)
      ·
        refine ⟨9405016033692000894886345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12540021378256001193181793 9405016033692000894886345)
        ·
          refine ⟨7053762025269000671164759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9405016033692000894886345 7053762025269000671164759)
          ·
            refine ⟨10580643037903501006747139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053762025269000671164759 10580643037903501006747139)
            ·
              refine ⟨15870964556855251510120709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10580643037903501006747139 15870964556855251510120709)
              ·
                refine ⟨2975805854410359658147633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15870964556855251510120709 2975805854410359658147633)
                ·
                  refine ⟨2231854390807769743610725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2975805854410359658147633 2231854390807769743610725)
                  ·
                    refine ⟨418472698276456826927011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2231854390807769743610725 418472698276456826927011)
                    ·
                      rfl

theorem cell23_2444918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_2444918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444918 prefixEnd_2444918 := by exact prefixLift 2444918
  have htrace : WordTrace (prefixWord ++ tailWord_2444918) baseStart_2444918 baseEnd_2444918 := by
    simpa [prefixWord, tailWord_2444918, baseEnd_2444918] using wordTrace_append hprefix tailTrace_2444918
  have hstable : (prefixWord ++ tailWord_2444918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444918).length < 2 ^ (prefixWord ++ tailWord_2444918).sum := by decide
  have hdescent : baseEnd_2444918 < baseStart_2444918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444924 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_2444924 : Nat := 118140960795 + 2444924 * 2 ^ 59
def prefixEnd_2444924 : Nat := 4983230072969 + 3 ^ 40 * 2444924 * 2
def baseEnd_2444924 : Nat := 1255421175713297457306005

theorem tailTrace_2444924 : CollatzResearch.WordTrace tailWord_2444924 prefixEnd_2444924 1255421175713297457306005 := by
  unfold tailWord_2444924
  simp only [CollatzResearch.WordTrace]
  refine ⟨44586852097232691310338913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59449136129643588413785217 44586852097232691310338913)
  ·
    refine ⟨33440139072924518482754185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44586852097232691310338913 33440139072924518482754185)
    ·
      refine ⟨25080104304693388862065639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33440139072924518482754185 25080104304693388862065639)
      ·
        refine ⟨37620156457040083293098459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25080104304693388862065639 37620156457040083293098459)
        ·
          refine ⟨56430234685560124939647689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37620156457040083293098459 56430234685560124939647689)
          ·
            refine ⟨42322676014170093704735767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56430234685560124939647689 42322676014170093704735767)
            ·
              refine ⟨63484014021255140557103651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42322676014170093704735767 63484014021255140557103651)
              ·
                refine ⟨95226021031882710835655477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63484014021255140557103651 95226021031882710835655477)
                ·
                  refine ⟨8927439471739004140842701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95226021031882710835655477 8927439471739004140842701)
                  ·
                    refine ⟨3347789801902126552816013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8927439471739004140842701 3347789801902126552816013)
                    ·
                      refine ⟨1255421175713297457306005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3347789801902126552816013 1255421175713297457306005)
                      ·
                        rfl

theorem cell23_2444924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_2444924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444924 prefixEnd_2444924 := by exact prefixLift 2444924
  have htrace : WordTrace (prefixWord ++ tailWord_2444924) baseStart_2444924 baseEnd_2444924 := by
    simpa [prefixWord, tailWord_2444924, baseEnd_2444924] using wordTrace_append hprefix tailTrace_2444924
  have hstable : (prefixWord ++ tailWord_2444924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444924).length < 2 ^ (prefixWord ++ tailWord_2444924).sum := by decide
  have hdescent : baseEnd_2444924 < baseStart_2444924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444947 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10]
def baseStart_2444947 : Nat := 118140960795 + 2444947 * 2 ^ 59
def prefixEnd_2444947 : Nat := 4983230072969 + 3 ^ 40 * 2444947 * 2
def baseEnd_2444947 : Nat := 1255432985768350867318399

theorem tailTrace_2444947 : CollatzResearch.WordTrace tailWord_2444947 prefixEnd_2444947 1255432985768350867318399 := by
  unfold tailWord_2444947
  simp only [CollatzResearch.WordTrace]
  refine ⟨89174543073382057548765095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59449695382254705032510063 89174543073382057548765095)
  ·
    refine ⟨133761814610073086323147643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89174543073382057548765095 133761814610073086323147643)
    ·
      refine ⟨200642721915109629484721465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133761814610073086323147643 200642721915109629484721465)
      ·
        refine ⟨150482041436332222113541099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200642721915109629484721465 150482041436332222113541099)
        ·
          refine ⟨225723062154498333170311649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150482041436332222113541099 225723062154498333170311649)
          ·
            refine ⟨169292296615873749877733737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225723062154498333170311649 169292296615873749877733737)
            ·
              refine ⟨126969222461905312408300303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169292296615873749877733737 126969222461905312408300303)
              ·
                refine ⟨190453833692857968612450455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126969222461905312408300303 190453833692857968612450455)
                ·
                  refine ⟨285680750539286952918675683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190453833692857968612450455 285680750539286952918675683)
                  ·
                    refine ⟨428521125808930429378013525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 285680750539286952918675683 428521125808930429378013525)
                    ·
                      refine ⟨1255432985768350867318399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 428521125808930429378013525 1255432985768350867318399)
                      ·
                        rfl

theorem cell23_2444947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_2444947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444947 prefixEnd_2444947 := by exact prefixLift 2444947
  have htrace : WordTrace (prefixWord ++ tailWord_2444947) baseStart_2444947 baseEnd_2444947 := by
    simpa [prefixWord, tailWord_2444947, baseEnd_2444947] using wordTrace_append hprefix tailTrace_2444947
  have hstable : (prefixWord ++ tailWord_2444947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444947).length < 2 ^ (prefixWord ++ tailWord_2444947).sum := by decide
  have hdescent : baseEnd_2444947 < baseStart_2444947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444948 : List Nat := [2, 4, 2, 2, 2, 1, 3, 7]
def baseStart_2444948 : Nat := 118140960795 + 2444948 * 2 ^ 59
def prefixEnd_2444948 : Nat := 4983230072969 + 3 ^ 40 * 2444948 * 2
def baseEnd_2444948 : Nat := 46497537009222420866885

theorem tailTrace_2444948 : CollatzResearch.WordTrace tailWord_2444948 prefixEnd_2444948 46497537009222420866885 := by
  unfold tailWord_2444948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44587289773189217359775749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59449719697585623146367665 44587289773189217359775749)
  ·
    refine ⟨8360116832472978254957953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44587289773189217359775749 8360116832472978254957953)
    ·
      refine ⟨6270087624354733691218465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8360116832472978254957953 6270087624354733691218465)
      ·
        refine ⟨4702565718266050268413849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6270087624354733691218465 4702565718266050268413849)
        ·
          refine ⟨3526924288699537701310387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4702565718266050268413849 3526924288699537701310387)
          ·
            refine ⟨5290386433049306551965581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526924288699537701310387 5290386433049306551965581)
            ·
              refine ⟨1983894912393489956987093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5290386433049306551965581 1983894912393489956987093)
              ·
                refine ⟨46497537009222420866885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1983894912393489956987093 46497537009222420866885)
                ·
                  rfl

theorem cell23_2444948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 7].length) (baseStart_2444948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444948 prefixEnd_2444948 := by exact prefixLift 2444948
  have htrace : WordTrace (prefixWord ++ tailWord_2444948) baseStart_2444948 baseEnd_2444948 := by
    simpa [prefixWord, tailWord_2444948, baseEnd_2444948] using wordTrace_append hprefix tailTrace_2444948
  have hstable : (prefixWord ++ tailWord_2444948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444948).length < 2 ^ (prefixWord ++ tailWord_2444948).sum := by decide
  have hdescent : baseEnd_2444948 < baseStart_2444948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444958 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2444958 : Nat := 118140960795 + 2444958 * 2 ^ 59
def prefixEnd_2444958 : Nat := 4983230072969 + 3 ^ 40 * 2444958 * 2
def baseEnd_2444958 : Nat := 1255438634055550324280849

theorem tailTrace_2444958 : CollatzResearch.WordTrace tailWord_2444958 prefixEnd_2444958 1255438634055550324280849 := by
  unfold tailWord_2444958
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146868034542775803426941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59449962850894804284943685 11146868034542775803426941)
  ·
    refine ⟨4180075512953540926285103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11146868034542775803426941 4180075512953540926285103)
    ·
      refine ⟨6270113269430311389427655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4180075512953540926285103 6270113269430311389427655)
      ·
        refine ⟨9405169904145467084141483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6270113269430311389427655 9405169904145467084141483)
        ·
          refine ⟨14107754856218200626212225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9405169904145467084141483 14107754856218200626212225)
          ·
            refine ⟨10580816142163650469659169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14107754856218200626212225 10580816142163650469659169)
            ·
              refine ⟨7935612106622737852244377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10580816142163650469659169 7935612106622737852244377)
              ·
                refine ⟨5951709079967053389183283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7935612106622737852244377 5951709079967053389183283)
                ·
                  refine ⟨8927563619950580083774925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5951709079967053389183283 8927563619950580083774925)
                  ·
                    refine ⟨3347836357481467531415597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8927563619950580083774925 3347836357481467531415597)
                    ·
                      refine ⟨1255438634055550324280849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3347836357481467531415597 1255438634055550324280849)
                      ·
                        rfl

theorem cell23_2444958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2444958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444958 prefixEnd_2444958 := by exact prefixLift 2444958
  have htrace : WordTrace (prefixWord ++ tailWord_2444958) baseStart_2444958 baseEnd_2444958 := by
    simpa [prefixWord, tailWord_2444958, baseEnd_2444958] using wordTrace_append hprefix tailTrace_2444958
  have hstable : (prefixWord ++ tailWord_2444958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444958).length < 2 ^ (prefixWord ++ tailWord_2444958).sum := by decide
  have hdescent : baseEnd_2444958 < baseStart_2444958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444959 : List Nat := [1, 1, 2, 7, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2444959 : Nat := 118140960795 + 2444959 * 2 ^ 59
def prefixEnd_2444959 : Nat := 4983230072969 + 3 ^ 40 * 2444959 * 2
def baseEnd_2444959 : Nat := 1255439147536204820368345

theorem tailTrace_2444959 : CollatzResearch.WordTrace tailWord_2444959 prefixEnd_2444959 1255439147536204820368345 := by
  unfold tailWord_2444959
  simp only [CollatzResearch.WordTrace]
  refine ⟨89174980749338583598201931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59449987166225722398801287 89174980749338583598201931)
  ·
    refine ⟨133762471124007875397302897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89174980749338583598201931 133762471124007875397302897)
    ·
      refine ⟨100321853343005906547977173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133762471124007875397302897 100321853343005906547977173)
      ·
        refine ⟨2351293437726700934718215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 100321853343005906547977173 2351293437726700934718215)
        ·
          refine ⟨3526940156590051402077323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351293437726700934718215 3526940156590051402077323)
          ·
            refine ⟨5290410234885077103115985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526940156590051402077323 5290410234885077103115985)
            ·
              refine ⟨3967807676163807827336989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290410234885077103115985 3967807676163807827336989)
              ·
                refine ⟨1487927878561427935251371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3967807676163807827336989 1487927878561427935251371)
                ·
                  refine ⟨2231891817842141902877057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487927878561427935251371 2231891817842141902877057)
                  ·
                    refine ⟨1673918863381606427157793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2231891817842141902877057 1673918863381606427157793)
                    ·
                      refine ⟨1255439147536204820368345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673918863381606427157793 1255439147536204820368345)
                      ·
                        rfl

theorem cell23_2444959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2444959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444959 prefixEnd_2444959 := by exact prefixLift 2444959
  have htrace : WordTrace (prefixWord ++ tailWord_2444959) baseStart_2444959 baseEnd_2444959 := by
    simpa [prefixWord, tailWord_2444959, baseEnd_2444959] using wordTrace_append hprefix tailTrace_2444959
  have hstable : (prefixWord ++ tailWord_2444959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444959).length < 2 ^ (prefixWord ++ tailWord_2444959).sum := by decide
  have hdescent : baseEnd_2444959 < baseStart_2444959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2444984 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_2444984 : Nat := 118140960795 + 2444984 * 2 ^ 59
def prefixEnd_2444984 : Nat := 4983230072969 + 3 ^ 40 * 2444984 * 2
def baseEnd_2444984 : Nat := 1255451984552567222555729

theorem tailTrace_2444984 : CollatzResearch.WordTrace tailWord_2444984 prefixEnd_2444984 1255451984552567222555729 := by
  unfold tailWord_2444984
  simp only [CollatzResearch.WordTrace]
  refine ⟨44587946287124006433931003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59450595049498675245241337 44587946287124006433931003)
  ·
    refine ⟨66881919430686009650896505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44587946287124006433931003 66881919430686009650896505)
    ·
      refine ⟨50161439573014507238172379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66881919430686009650896505 50161439573014507238172379)
      ·
        refine ⟨75242159359521760857258569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50161439573014507238172379 75242159359521760857258569)
        ·
          refine ⟨56431619519641320642943927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75242159359521760857258569 56431619519641320642943927)
          ·
            refine ⟨84647429279461980964415891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56431619519641320642943927 84647429279461980964415891)
            ·
              refine ⟨126971143919192971446623837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84647429279461980964415891 126971143919192971446623837)
              ·
                refine ⟨47614178969697364292483939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126971143919192971446623837 47614178969697364292483939)
                ·
                  refine ⟨71421268454546046438725909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47614178969697364292483939 71421268454546046438725909)
                  ·
                    refine ⟨3347871958806845926815277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71421268454546046438725909 3347871958806845926815277)
                    ·
                      refine ⟨1255451984552567222555729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3347871958806845926815277 1255451984552567222555729)
                      ·
                        rfl

theorem cell23_2444984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_2444984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2444984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2444984 prefixEnd_2444984 := by exact prefixLift 2444984
  have htrace : WordTrace (prefixWord ++ tailWord_2444984) baseStart_2444984 baseEnd_2444984 := by
    simpa [prefixWord, tailWord_2444984, baseEnd_2444984] using wordTrace_append hprefix tailTrace_2444984
  have hstable : (prefixWord ++ tailWord_2444984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2444984).length < 2 ^ (prefixWord ++ tailWord_2444984).sum := by decide
  have hdescent : baseEnd_2444984 < baseStart_2444984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2444984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445071 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 3, 6, 2]
def baseStart_2445071 : Nat := 118140960795 + 2445071 * 2 ^ 59
def prefixEnd_2445071 : Nat := 4983230072969 + 3 ^ 40 * 2445071 * 2
def baseEnd_2445071 : Nat := 1255496657369508382167829

theorem tailTrace_2445071 : CollatzResearch.WordTrace tailWord_2445071 prefixEnd_2445071 1255496657369508382167829 := by
  unfold tailWord_2445071
  simp only [CollatzResearch.WordTrace]
  refine ⟨89179065724932826726279067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59452710483288551150852711 89179065724932826726279067)
  ·
    refine ⟨133768598587399240089418601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89179065724932826726279067 133768598587399240089418601)
    ·
      refine ⟨100326448940549430067063951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133768598587399240089418601 100326448940549430067063951)
      ·
        refine ⟨150489673410824145100595927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100326448940549430067063951 150489673410824145100595927)
        ·
          refine ⟨225734510116236217650893891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150489673410824145100595927 225734510116236217650893891)
          ·
            refine ⟨338601765174354326476340837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225734510116236217650893891 338601765174354326476340837)
            ·
              refine ⟨63487830970191436214313907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338601765174354326476340837 63487830970191436214313907)
              ·
                refine ⟨95231746455287154321470861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63487830970191436214313907 95231746455287154321470861)
                ·
                  refine ⟨35711904920732682870551573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95231746455287154321470861 35711904920732682870551573)
                  ·
                    refine ⟨1673995543159344509557105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35711904920732682870551573 1673995543159344509557105)
                    ·
                      refine ⟨1255496657369508382167829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1673995543159344509557105 1255496657369508382167829)
                      ·
                        rfl

theorem cell23_2445071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 6, 2].length) (baseStart_2445071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445071 prefixEnd_2445071 := by exact prefixLift 2445071
  have htrace : WordTrace (prefixWord ++ tailWord_2445071) baseStart_2445071 baseEnd_2445071 := by
    simpa [prefixWord, tailWord_2445071, baseEnd_2445071] using wordTrace_append hprefix tailTrace_2445071
  have hstable : (prefixWord ++ tailWord_2445071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445071).length < 2 ^ (prefixWord ++ tailWord_2445071).sum := by decide
  have hdescent : baseEnd_2445071 < baseStart_2445071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445088 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2445088 : Nat := 118140960795 + 2445088 * 2 ^ 59
def prefixEnd_2445088 : Nat := 4983230072969 + 3 ^ 40 * 2445088 * 2
def baseEnd_2445088 : Nat := 1255505386540634815655251

theorem tailTrace_2445088 : CollatzResearch.WordTrace tailWord_2445088 prefixEnd_2445088 1255505386540634815655251 := by
  unfold tailWord_2445088
  simp only [CollatzResearch.WordTrace]
  refine ⟨44589842882935619314823959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59453123843914159086431945 44589842882935619314823959)
  ·
    refine ⟨66884764324403428972235939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44589842882935619314823959 66884764324403428972235939)
    ·
      refine ⟨100327146486605143458353909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66884764324403428972235939 100327146486605143458353909)
      ·
        refine ⟨9405669983119232199220679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100327146486605143458353909 9405669983119232199220679)
        ·
          refine ⟨14108504974678848298831019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9405669983119232199220679 14108504974678848298831019)
          ·
            refine ⟨21162757462018272448246529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14108504974678848298831019 21162757462018272448246529)
            ·
              refine ⟨15872068096513704336184897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21162757462018272448246529 15872068096513704336184897)
              ·
                refine ⟨11904051072385278252138673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15872068096513704336184897 11904051072385278252138673)
                ·
                  refine ⟨8928038304288958689104005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11904051072385278252138673 8928038304288958689104005)
                  ·
                    refine ⟨1674007182054179754207001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8928038304288958689104005 1674007182054179754207001)
                    ·
                      refine ⟨1255505386540634815655251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674007182054179754207001 1255505386540634815655251)
                      ·
                        rfl

theorem cell23_2445088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2445088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445088 prefixEnd_2445088 := by exact prefixLift 2445088
  have htrace : WordTrace (prefixWord ++ tailWord_2445088) baseStart_2445088 baseEnd_2445088 := by
    simpa [prefixWord, tailWord_2445088, baseEnd_2445088] using wordTrace_append hprefix tailTrace_2445088
  have hstable : (prefixWord ++ tailWord_2445088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445088).length < 2 ^ (prefixWord ++ tailWord_2445088).sum := by decide
  have hdescent : baseEnd_2445088 < baseStart_2445088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445132 : List Nat := [2, 2, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_2445132 : Nat := 118140960795 + 2445132 * 2 ^ 59
def prefixEnd_2445132 : Nat := 4983230072969 + 3 ^ 40 * 2445132 * 2
def baseEnd_2445132 : Nat := 418509326563144214501683

theorem tailTrace_2445132 : CollatzResearch.WordTrace tailWord_2445132 prefixEnd_2445132 418509326563144214501683 := by
  unfold tailWord_2445132
  simp only [CollatzResearch.WordTrace]
  refine ⟨44590645288855917072124825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59454193718474556096166433 44590645288855917072124825)
  ·
    refine ⟨33442983966641937804093619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44590645288855917072124825 33442983966641937804093619)
    ·
      refine ⟨50164475949962906706140429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33442983966641937804093619 50164475949962906706140429)
      ·
        refine ⟨18811678481236090014802661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50164475949962906706140429 18811678481236090014802661)
        ·
          refine ⟨3527189715231766877775499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18811678481236090014802661 3527189715231766877775499)
          ·
            refine ⟨5290784572847650316663249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527189715231766877775499 5290784572847650316663249)
            ·
              refine ⟨3968088429635737737497437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290784572847650316663249 3968088429635737737497437)
              ·
                refine ⟨1488033161113401651561539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3968088429635737737497437 1488033161113401651561539)
                ·
                  refine ⟨2232049741670102477342309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488033161113401651561539 2232049741670102477342309)
                  ·
                    refine ⟨418509326563144214501683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232049741670102477342309 418509326563144214501683)
                    ·
                      rfl

theorem cell23_2445132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_2445132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445132 prefixEnd_2445132 := by exact prefixLift 2445132
  have htrace : WordTrace (prefixWord ++ tailWord_2445132) baseStart_2445132 baseEnd_2445132 := by
    simpa [prefixWord, tailWord_2445132, baseEnd_2445132] using wordTrace_append hprefix tailTrace_2445132
  have hstable : (prefixWord ++ tailWord_2445132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445132).length < 2 ^ (prefixWord ++ tailWord_2445132).sum := by decide
  have hdescent : baseEnd_2445132 < baseStart_2445132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445161 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_2445161 : Nat := 118140960795 + 2445161 * 2 ^ 59
def prefixEnd_2445161 : Nat := 4983230072969 + 3 ^ 40 * 2445161 * 2
def baseEnd_2445161 : Nat := 1255542870628413030042415

theorem tailTrace_2445161 : CollatzResearch.WordTrace tailWord_2445161 prefixEnd_2445161 1255542870628413030042415 := by
  unfold tailWord_2445161
  simp only [CollatzResearch.WordTrace]
  refine ⟨89182348294606772097055337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59454898863071181398036891 89182348294606772097055337)
  ·
    refine ⟨66886761220955079072791503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89182348294606772097055337 66886761220955079072791503)
    ·
      refine ⟨100330141831432618609187255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66886761220955079072791503 100330141831432618609187255)
      ·
        refine ⟨150495212747148927913780883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100330141831432618609187255 150495212747148927913780883)
        ·
          refine ⟨225742819120723391870671325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150495212747148927913780883 225742819120723391870671325)
          ·
            refine ⟨84653557170271271951501747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225742819120723391870671325 84653557170271271951501747)
            ·
              refine ⟨126980335755406907927252621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84653557170271271951501747 126980335755406907927252621)
              ·
                refine ⟨47617625908277590472719733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126980335755406907927252621 47617625908277590472719733)
                ·
                  refine ⟨4464152428901024106817475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47617625908277590472719733 4464152428901024106817475)
                  ·
                    refine ⟨6696228643351536160226213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4464152428901024106817475 6696228643351536160226213)
                    ·
                      refine ⟨1255542870628413030042415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6696228643351536160226213 1255542870628413030042415)
                      ·
                        rfl

theorem cell23_2445161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_2445161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445161 prefixEnd_2445161 := by exact prefixLift 2445161
  have htrace : WordTrace (prefixWord ++ tailWord_2445161) baseStart_2445161 baseEnd_2445161 := by
    simpa [prefixWord, tailWord_2445161, baseEnd_2445161] using wordTrace_append hprefix tailTrace_2445161
  have hstable : (prefixWord ++ tailWord_2445161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445161).length < 2 ^ (prefixWord ++ tailWord_2445161).sum := by decide
  have hdescent : baseEnd_2445161 < baseStart_2445161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445162 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 6]
def baseStart_2445162 : Nat := 118140960795 + 2445162 * 2 ^ 59
def prefixEnd_2445162 : Nat := 4983230072969 + 3 ^ 40 * 2445162 * 2
def baseEnd_2445162 : Nat := 139504820456563058458879

theorem tailTrace_2445162 : CollatzResearch.WordTrace tailWord_2445162 prefixEnd_2445162 139504820456563058458879 := by
  unfold tailWord_2445162
  simp only [CollatzResearch.WordTrace]
  refine ⟨22295596191900787316960435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59454923178402099511894493 22295596191900787316960435)
  ·
    refine ⟨33443394287851180975440653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22295596191900787316960435 33443394287851180975440653)
    ·
      refine ⟨12541272857944192865790245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33443394287851180975440653 12541272857944192865790245)
      ·
        refine ⟨2351488660864536162335671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12541272857944192865790245 2351488660864536162335671)
        ·
          refine ⟨3527232991296804243503507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351488660864536162335671 3527232991296804243503507)
          ·
            refine ⟨5290849486945206365255261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527232991296804243503507 5290849486945206365255261)
            ·
              refine ⟨1984068557604452386970723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5290849486945206365255261 1984068557604452386970723)
              ·
                refine ⟨2976102836406678580456085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984068557604452386970723 2976102836406678580456085)
                ·
                  refine ⟨139504820456563058458879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2976102836406678580456085 139504820456563058458879)
                  ·
                    rfl

theorem cell23_2445162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_2445162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445162 prefixEnd_2445162 := by exact prefixLift 2445162
  have htrace : WordTrace (prefixWord ++ tailWord_2445162) baseStart_2445162 baseEnd_2445162 := by
    simpa [prefixWord, tailWord_2445162, baseEnd_2445162] using wordTrace_append hprefix tailTrace_2445162
  have hstable : (prefixWord ++ tailWord_2445162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445162).length < 2 ^ (prefixWord ++ tailWord_2445162).sum := by decide
  have hdescent : baseEnd_2445162 < baseStart_2445162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445178 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_2445178 : Nat := 118140960795 + 2445178 * 2 ^ 59
def prefixEnd_2445178 : Nat := 4983230072969 + 3 ^ 40 * 2445178 * 2
def baseEnd_2445178 : Nat := 1255551599799539463529837

theorem tailTrace_2445178 : CollatzResearch.WordTrace tailWord_2445178 prefixEnd_2445178 1255551599799539463529837 := by
  unfold tailWord_2445178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22295742083886296000106047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59455312223696789333616125 22295742083886296000106047)
  ·
    refine ⟨33443613125829444000159071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22295742083886296000106047 33443613125829444000159071)
    ·
      refine ⟨50165419688744166000238607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33443613125829444000159071 50165419688744166000238607)
      ·
        refine ⟨75248129533116249000357911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50165419688744166000238607 75248129533116249000357911)
        ·
          refine ⟨112872194299674373500536867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75248129533116249000357911 112872194299674373500536867)
          ·
            refine ⟨169308291449511560250805301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112872194299674373500536867 169308291449511560250805301)
            ·
              refine ⟨15872652323391708773512997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169308291449511560250805301 15872652323391708773512997)
              ·
                refine ⟨2976122310635945395033687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15872652323391708773512997 2976122310635945395033687)
                ·
                  refine ⟨4464183465953918092550531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976122310635945395033687 4464183465953918092550531)
                  ·
                    refine ⟨6696275198930877138825797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4464183465953918092550531 6696275198930877138825797)
                    ·
                      refine ⟨1255551599799539463529837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6696275198930877138825797 1255551599799539463529837)
                      ·
                        rfl

theorem cell23_2445178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_2445178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445178 prefixEnd_2445178 := by exact prefixLift 2445178
  have htrace : WordTrace (prefixWord ++ tailWord_2445178) baseStart_2445178 baseEnd_2445178 := by
    simpa [prefixWord, tailWord_2445178, baseEnd_2445178] using wordTrace_append hprefix tailTrace_2445178
  have hstable : (prefixWord ++ tailWord_2445178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445178).length < 2 ^ (prefixWord ++ tailWord_2445178).sum := by decide
  have hdescent : baseEnd_2445178 < baseStart_2445178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445181 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_2445181 : Nat := 118140960795 + 2445181 * 2 ^ 59
def prefixEnd_2445181 : Nat := 4983230072969 + 3 ^ 40 * 2445181 * 2
def baseEnd_2445181 : Nat := 1255553140241502951792323

theorem tailTrace_2445181 : CollatzResearch.WordTrace tailWord_2445181 prefixEnd_2445181 1255553140241502951792323 := by
  unfold tailWord_2445181
  simp only [CollatzResearch.WordTrace]
  refine ⟨89183077754534315512783397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59455385169689543675188931 89183077754534315512783397)
  ·
    refine ⟨16721827078975184158646887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89183077754534315512783397 16721827078975184158646887)
    ·
      refine ⟨25082740618462776237970331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16721827078975184158646887 25082740618462776237970331)
      ·
        refine ⟨37624110927694164356955497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25082740618462776237970331 37624110927694164356955497)
        ·
          refine ⟨28218083195770623267716623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37624110927694164356955497 28218083195770623267716623)
          ·
            refine ⟨42327124793655934901574935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28218083195770623267716623 42327124793655934901574935)
            ·
              refine ⟨63490687190483902352362403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42327124793655934901574935 63490687190483902352362403)
              ·
                refine ⟨95236030785725853528543605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63490687190483902352362403 95236030785725853528543605)
                ·
                  refine ⟨8928377886161798768300963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95236030785725853528543605 8928377886161798768300963)
                  ·
                    refine ⟨13392566829242698152451445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8928377886161798768300963 13392566829242698152451445)
                    ·
                      refine ⟨1255553140241502951792323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13392566829242698152451445 1255553140241502951792323)
                      ·
                        rfl

theorem cell23_2445181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_2445181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445181 prefixEnd_2445181 := by exact prefixLift 2445181
  have htrace : WordTrace (prefixWord ++ tailWord_2445181) baseStart_2445181 baseEnd_2445181 := by
    simpa [prefixWord, tailWord_2445181, baseEnd_2445181] using wordTrace_append hprefix tailTrace_2445181
  have hstable : (prefixWord ++ tailWord_2445181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445181).length < 2 ^ (prefixWord ++ tailWord_2445181).sum := by decide
  have hdescent : baseEnd_2445181 < baseStart_2445181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445182 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2445182 : Nat := 118140960795 + 2445182 * 2 ^ 59
def prefixEnd_2445182 : Nat := 4983230072969 + 3 ^ 40 * 2445182 * 2
def baseEnd_2445182 : Nat := 1255553653722157447879819

theorem tailTrace_2445182 : CollatzResearch.WordTrace tailWord_2445182 prefixEnd_2445182 1255553653722157447879819 := by
  unfold tailWord_2445182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11147889278441336585446225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59455409485020461789046533 11147889278441336585446225)
  ·
    refine ⟨8360916958831002439084669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11147889278441336585446225 8360916958831002439084669)
    ·
      refine ⟨3135343859561625914656751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8360916958831002439084669 3135343859561625914656751)
      ·
        refine ⟨4703015789342438871985127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135343859561625914656751 4703015789342438871985127)
        ·
          refine ⟨7054523684013658307977691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703015789342438871985127 7054523684013658307977691)
          ·
            refine ⟨10581785526020487461966537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7054523684013658307977691 10581785526020487461966537)
            ·
              refine ⟨7936339144515365596474903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10581785526020487461966537 7936339144515365596474903)
              ·
                refine ⟨11904508716773048394712355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7936339144515365596474903 11904508716773048394712355)
                ·
                  refine ⟨17856763075159572592068533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11904508716773048394712355 17856763075159572592068533)
                  ·
                    refine ⟨1674071538296209930506425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17856763075159572592068533 1674071538296209930506425)
                    ·
                      refine ⟨1255553653722157447879819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674071538296209930506425 1255553653722157447879819)
                      ·
                        rfl

theorem cell23_2445182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2445182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445182 prefixEnd_2445182 := by exact prefixLift 2445182
  have htrace : WordTrace (prefixWord ++ tailWord_2445182) baseStart_2445182 baseEnd_2445182 := by
    simpa [prefixWord, tailWord_2445182, baseEnd_2445182] using wordTrace_append hprefix tailTrace_2445182
  have hstable : (prefixWord ++ tailWord_2445182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445182).length < 2 ^ (prefixWord ++ tailWord_2445182).sum := by decide
  have hdescent : baseEnd_2445182 < baseStart_2445182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445188 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_2445188 : Nat := 118140960795 + 2445188 * 2 ^ 59
def prefixEnd_2445188 : Nat := 4983230072969 + 3 ^ 40 * 2445188 * 2
def baseEnd_2445188 : Nat := 418518911535361474801597

theorem tailTrace_2445188 : CollatzResearch.WordTrace tailWord_2445188 prefixEnd_2445188 418518911535361474801597 := by
  unfold tailWord_2445188
  simp only [CollatzResearch.WordTrace]
  refine ⟨44591666532754477854144109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59455555377005970472192145 44591666532754477854144109)
  ·
    refine ⟨16721874949782929195304041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44591666532754477854144109 16721874949782929195304041)
    ·
      refine ⟨12541406212337196896478031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16721874949782929195304041 12541406212337196896478031)
      ·
        refine ⟨18812109318505795344717047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12541406212337196896478031 18812109318505795344717047)
        ·
          refine ⟨28218163977758693017075571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18812109318505795344717047 28218163977758693017075571)
          ·
            refine ⟨42327245966638039525613357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28218163977758693017075571 42327245966638039525613357)
            ·
              refine ⟨15872717237489264822105009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42327245966638039525613357 15872717237489264822105009)
              ·
                refine ⟨11904537928116948616578757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15872717237489264822105009 11904537928116948616578757)
                ·
                  refine ⟨2232100861521927865608517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11904537928116948616578757 2232100861521927865608517)
                  ·
                    refine ⟨418518911535361474801597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232100861521927865608517 418518911535361474801597)
                    ·
                      rfl

theorem cell23_2445188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_2445188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445188 prefixEnd_2445188 := by exact prefixLift 2445188
  have htrace : WordTrace (prefixWord ++ tailWord_2445188) baseStart_2445188 baseEnd_2445188 := by
    simpa [prefixWord, tailWord_2445188, baseEnd_2445188] using wordTrace_append hprefix tailTrace_2445188
  have hstable : (prefixWord ++ tailWord_2445188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445188).length < 2 ^ (prefixWord ++ tailWord_2445188).sum := by decide
  have hdescent : baseEnd_2445188 < baseStart_2445188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445245 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2445245 : Nat := 118140960795 + 2445245 * 2 ^ 59
def prefixEnd_2445245 : Nat := 4983230072969 + 3 ^ 40 * 2445245 * 2
def baseEnd_2445245 : Nat := 1255586003003390701392029

theorem tailTrace_2445245 : CollatzResearch.WordTrace tailWord_2445245 prefixEnd_2445245 1255586003003390701392029 := by
  unfold tailWord_2445245
  simp only [CollatzResearch.WordTrace]
  refine ⟨89185412026302454443113189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59456941350868302962075459 89185412026302454443113189)
  ·
    refine ⟨16722264754931710208083723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89185412026302454443113189 16722264754931710208083723)
    ·
      refine ⟨25083397132397565312125585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16722264754931710208083723 25083397132397565312125585)
      ·
        refine ⟨18812547849298173984094189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25083397132397565312125585 18812547849298173984094189)
        ·
          refine ⟨7054705443486815244035321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18812547849298173984094189 7054705443486815244035321)
          ·
            refine ⟨5291029082615111433026491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7054705443486815244035321 5291029082615111433026491)
            ·
              refine ⟨7936543623922667149539737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291029082615111433026491 7936543623922667149539737)
              ·
                refine ⟨5952407717942000362154803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7936543623922667149539737 5952407717942000362154803)
                ·
                  refine ⟨8928611576913000543232205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5952407717942000362154803 8928611576913000543232205)
                  ·
                    refine ⟨3348229341342375203712077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8928611576913000543232205 3348229341342375203712077)
                    ·
                      refine ⟨1255586003003390701392029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3348229341342375203712077 1255586003003390701392029)
                      ·
                        rfl

theorem cell23_2445245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2445245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445245 prefixEnd_2445245 := by exact prefixLift 2445245
  have htrace : WordTrace (prefixWord ++ tailWord_2445245) baseStart_2445245 baseEnd_2445245 := by
    simpa [prefixWord, tailWord_2445245, baseEnd_2445245] using wordTrace_append hprefix tailTrace_2445245
  have hstable : (prefixWord ++ tailWord_2445245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445245).length < 2 ^ (prefixWord ++ tailWord_2445245).sum := by decide
  have hdescent : baseEnd_2445245 < baseStart_2445245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445251 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4]
def baseStart_2445251 : Nat := 118140960795 + 2445251 * 2 ^ 59
def prefixEnd_2445251 : Nat := 4983230072969 + 3 ^ 40 * 2445251 * 2
def baseEnd_2445251 : Nat := 1255589083887317677917001

theorem tailTrace_2445251 : CollatzResearch.WordTrace tailWord_2445251 prefixEnd_2445251 1255589083887317677917001 := by
  unfold tailWord_2445251
  simp only [CollatzResearch.WordTrace]
  refine ⟨89185630864280717467831607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59457087242853811645221071 89185630864280717467831607)
  ·
    refine ⟨133778446296421076201747411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89185630864280717467831607 133778446296421076201747411)
    ·
      refine ⟨200667669444631614302621117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133778446296421076201747411 200667669444631614302621117)
      ·
        refine ⟨75250376041736855363482919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200667669444631614302621117 75250376041736855363482919)
        ·
          refine ⟨112875564062605283045224379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75250376041736855363482919 112875564062605283045224379)
          ·
            refine ⟨169313346093907924567836569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112875564062605283045224379 169313346093907924567836569)
            ·
              refine ⟨126985009570430943425877427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169313346093907924567836569 126985009570430943425877427)
              ·
                refine ⟨190477514355646415138816141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126985009570430943425877427 190477514355646415138816141)
                ·
                  refine ⟨71429067883367405677056053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190477514355646415138816141 71429067883367405677056053)
                  ·
                    refine ⟨6696475114065694282224005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71429067883367405677056053 6696475114065694282224005)
                    ·
                      refine ⟨1255589083887317677917001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6696475114065694282224005 1255589083887317677917001)
                      ·
                        rfl

theorem cell23_2445251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_2445251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445251 prefixEnd_2445251 := by exact prefixLift 2445251
  have htrace : WordTrace (prefixWord ++ tailWord_2445251) baseStart_2445251 baseEnd_2445251 := by
    simpa [prefixWord, tailWord_2445251, baseEnd_2445251] using wordTrace_append hprefix tailTrace_2445251
  have hstable : (prefixWord ++ tailWord_2445251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445251).length < 2 ^ (prefixWord ++ tailWord_2445251).sum := by decide
  have hdescent : baseEnd_2445251 < baseStart_2445251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445262 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_2445262 : Nat := 118140960795 + 2445262 * 2 ^ 59
def prefixEnd_2445262 : Nat := 4983230072969 + 3 ^ 40 * 2445262 * 2
def baseEnd_2445262 : Nat := 1255594732174517134879451

theorem tailTrace_2445262 : CollatzResearch.WordTrace tailWord_2445262 prefixEnd_2445262 1255594732174517134879451 := by
  unfold tailWord_2445262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148254008405108293310255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59457354711493910897654693 11148254008405108293310255)
  ·
    refine ⟨16722381012607662439965383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11148254008405108293310255 16722381012607662439965383)
    ·
      refine ⟨25083571518911493659948075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16722381012607662439965383 25083571518911493659948075)
      ·
        refine ⟨37625357278367240489922113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25083571518911493659948075 37625357278367240489922113)
        ·
          refine ⟨28219017958775430367441585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37625357278367240489922113 28219017958775430367441585)
          ·
            refine ⟨21164263469081572775581189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28219017958775430367441585 21164263469081572775581189)
            ·
              refine ⟨3968299400452794895421473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21164263469081572775581189 3968299400452794895421473)
              ·
                refine ⟨2976224550339596171566105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968299400452794895421473 2976224550339596171566105)
                ·
                  refine ⟨2232168412754697128674579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976224550339596171566105 2232168412754697128674579)
                  ·
                    refine ⟨3348252619132045693011869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2232168412754697128674579 3348252619132045693011869)
                    ·
                      refine ⟨1255594732174517134879451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3348252619132045693011869 1255594732174517134879451)
                      ·
                        rfl

theorem cell23_2445262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_2445262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445262 prefixEnd_2445262 := by exact prefixLift 2445262
  have htrace : WordTrace (prefixWord ++ tailWord_2445262) baseStart_2445262 baseEnd_2445262 := by
    simpa [prefixWord, tailWord_2445262, baseEnd_2445262] using wordTrace_append hprefix tailTrace_2445262
  have hstable : (prefixWord ++ tailWord_2445262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445262).length < 2 ^ (prefixWord ++ tailWord_2445262).sum := by decide
  have hdescent : baseEnd_2445262 < baseStart_2445262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445268 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2445268 : Nat := 118140960795 + 2445268 * 2 ^ 59
def prefixEnd_2445268 : Nat := 4983230072969 + 3 ^ 40 * 2445268 * 2
def baseEnd_2445268 : Nat := 1255597813058444111404423

theorem tailTrace_2445268 : CollatzResearch.WordTrace tailWord_2445268 prefixEnd_2445268 1255597813058444111404423 := by
  unfold tailWord_2445268
  simp only [CollatzResearch.WordTrace]
  refine ⟨44593125452609564685600229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59457500603479419580800305 44593125452609564685600229)
  ·
    refine ⟨8361211022364293378550043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44593125452609564685600229 8361211022364293378550043)
    ·
      refine ⟨12541816533546440067825065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8361211022364293378550043 12541816533546440067825065)
      ·
        refine ⟨9406362400159830050868799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12541816533546440067825065 9406362400159830050868799)
        ·
          refine ⟨14109543600239745076303199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9406362400159830050868799 14109543600239745076303199)
          ·
            refine ⟨21164315400359617614454799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14109543600239745076303199 21164315400359617614454799)
            ·
              refine ⟨31746473100539426421682199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21164315400359617614454799 31746473100539426421682199)
              ·
                refine ⟨47619709650809139632523299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31746473100539426421682199 47619709650809139632523299)
                ·
                  refine ⟨71429564476213709448784949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47619709650809139632523299 71429564476213709448784949)
                  ·
                    refine ⟨6696521669645035260823589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71429564476213709448784949 6696521669645035260823589)
                    ·
                      refine ⟨1255597813058444111404423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6696521669645035260823589 1255597813058444111404423)
                      ·
                        rfl

theorem cell23_2445268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2445268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445268 prefixEnd_2445268 := by exact prefixLift 2445268
  have htrace : WordTrace (prefixWord ++ tailWord_2445268) baseStart_2445268 baseEnd_2445268 := by
    simpa [prefixWord, tailWord_2445268, baseEnd_2445268] using wordTrace_append hprefix tailTrace_2445268
  have hstable : (prefixWord ++ tailWord_2445268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445268).length < 2 ^ (prefixWord ++ tailWord_2445268).sum := by decide
  have hdescent : baseEnd_2445268 < baseStart_2445268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445288 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_2445288 : Nat := 118140960795 + 2445288 * 2 ^ 59
def prefixEnd_2445288 : Nat := 4983230072969 + 3 ^ 40 * 2445288 * 2
def baseEnd_2445288 : Nat := 1255608082671534033154331

theorem tailTrace_2445288 : CollatzResearch.WordTrace tailWord_2445288 prefixEnd_2445288 1255608082671534033154331 := by
  unfold tailWord_2445288
  simp only [CollatzResearch.WordTrace]
  refine ⟨44593490182573336393464259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59457986910097781857952345 44593490182573336393464259)
  ·
    refine ⟨66890235273860004590196389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44593490182573336393464259 66890235273860004590196389)
    ·
      refine ⟨12541919113848750860661823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66890235273860004590196389 12541919113848750860661823)
      ·
        refine ⟨18812878670773126290992735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12541919113848750860661823 18812878670773126290992735)
        ·
          refine ⟨28219318006159689436489103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18812878670773126290992735 28219318006159689436489103)
          ·
            refine ⟨42328977009239534154733655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28219318006159689436489103 42328977009239534154733655)
            ·
              refine ⟨63493465513859301232100483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42328977009239534154733655 63493465513859301232100483)
              ·
                refine ⟨95240198270788951848150725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63493465513859301232100483 95240198270788951848150725)
                ·
                  refine ⟨17857537175772928471528261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95240198270788951848150725 17857537175772928471528261)
                  ·
                    refine ⟨3348288220457424088411549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17857537175772928471528261 3348288220457424088411549)
                    ·
                      refine ⟨1255608082671534033154331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3348288220457424088411549 1255608082671534033154331)
                      ·
                        rfl

theorem cell23_2445288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_2445288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445288 prefixEnd_2445288 := by exact prefixLift 2445288
  have htrace : WordTrace (prefixWord ++ tailWord_2445288) baseStart_2445288 baseEnd_2445288 := by
    simpa [prefixWord, tailWord_2445288, baseEnd_2445288] using wordTrace_append hprefix tailTrace_2445288
  have hstable : (prefixWord ++ tailWord_2445288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445288).length < 2 ^ (prefixWord ++ tailWord_2445288).sum := by decide
  have hdescent : baseEnd_2445288 < baseStart_2445288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445319 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_2445319 : Nat := 118140960795 + 2445319 * 2 ^ 59
def prefixEnd_2445319 : Nat := 4983230072969 + 3 ^ 40 * 2445319 * 2
def baseEnd_2445319 : Nat := 1255624000571823411866689

theorem tailTrace_2445319 : CollatzResearch.WordTrace tailWord_2445319 prefixEnd_2445319 1255624000571823411866689 := by
  unfold tailWord_2445319
  simp only [CollatzResearch.WordTrace]
  refine ⟨89188111028034365081307011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59458740685356243387538007 89188111028034365081307011)
  ·
    refine ⟨133782166542051547621960517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89188111028034365081307011 133782166542051547621960517)
    ·
      refine ⟨25084156226634665179117597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133782166542051547621960517 25084156226634665179117597)
      ·
        refine ⟨9406558584987999442169099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25084156226634665179117597 9406558584987999442169099)
        ·
          refine ⟨14109837877481999163253649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9406558584987999442169099 14109837877481999163253649)
          ·
            refine ⟨10582378408111499372440237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14109837877481999163253649 10582378408111499372440237)
            ·
              refine ⟨3968391903041812264665089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10582378408111499372440237 3968391903041812264665089)
              ·
                refine ⟨2976293927281359198498817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968391903041812264665089 2976293927281359198498817)
                ·
                  refine ⟨2232220445461019398874113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976293927281359198498817 2232220445461019398874113)
                  ·
                    refine ⟨1674165334095764549155585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232220445461019398874113 1674165334095764549155585)
                    ·
                      refine ⟨1255624000571823411866689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674165334095764549155585 1255624000571823411866689)
                      ·
                        rfl

theorem cell23_2445319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_2445319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445319 prefixEnd_2445319 := by exact prefixLift 2445319
  have htrace : WordTrace (prefixWord ++ tailWord_2445319) baseStart_2445319 baseEnd_2445319 := by
    simpa [prefixWord, tailWord_2445319, baseEnd_2445319] using wordTrace_append hprefix tailTrace_2445319
  have hstable : (prefixWord ++ tailWord_2445319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445319).length < 2 ^ (prefixWord ++ tailWord_2445319).sum := by decide
  have hdescent : baseEnd_2445319 < baseStart_2445319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445338 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_2445338 : Nat := 118140960795 + 2445338 * 2 ^ 59
def prefixEnd_2445338 : Nat := 4983230072969 + 3 ^ 40 * 2445338 * 2
def baseEnd_2445338 : Nat := 418544585568086279176367

theorem tailTrace_2445338 : CollatzResearch.WordTrace tailWord_2445338 prefixEnd_2445338 418544585568086279176367 := by
  unfold tailWord_2445338
  simp only [CollatzResearch.WordTrace]
  refine ⟨22297201003741382831562167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59459202676643687550832445 22297201003741382831562167)
  ·
    refine ⟨33445801505612074247343251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22297201003741382831562167 33445801505612074247343251)
    ·
      refine ⟨50168702258418111371014877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33445801505612074247343251 50168702258418111371014877)
      ·
        refine ⟨18813263346906791764130579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50168702258418111371014877 18813263346906791764130579)
        ·
          refine ⟨28219895020360187646195869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18813263346906791764130579 28219895020360187646195869)
          ·
            refine ⟨10582460632635070367323451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28219895020360187646195869 10582460632635070367323451)
            ·
              refine ⟨15873690948952605550985177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10582460632635070367323451 15873690948952605550985177)
              ·
                refine ⟨11905268211714454163238883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15873690948952605550985177 11905268211714454163238883)
                ·
                  refine ⟨17857902317571681244858325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11905268211714454163238883 17857902317571681244858325)
                  ·
                    refine ⟨418544585568086279176367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17857902317571681244858325 418544585568086279176367)
                    ·
                      rfl

theorem cell23_2445338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_2445338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445338 prefixEnd_2445338 := by exact prefixLift 2445338
  have htrace : WordTrace (prefixWord ++ tailWord_2445338) baseStart_2445338 baseEnd_2445338 := by
    simpa [prefixWord, tailWord_2445338, baseEnd_2445338] using wordTrace_append hprefix tailTrace_2445338
  have hstable : (prefixWord ++ tailWord_2445338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445338).length < 2 ^ (prefixWord ++ tailWord_2445338).sum := by decide
  have hdescent : baseEnd_2445338 < baseStart_2445338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445375 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 4, 4, 2]
def baseStart_2445375 : Nat := 118140960795 + 2445375 * 2 ^ 59
def prefixEnd_2445375 : Nat := 4983230072969 + 3 ^ 40 * 2445375 * 2
def baseEnd_2445375 : Nat := 1255652755488475192766431

theorem tailTrace_2445375 : CollatzResearch.WordTrace tailWord_2445375 prefixEnd_2445375 1255652755488475192766431 := by
  unfold tailWord_2445375
  simp only [CollatzResearch.WordTrace]
  refine ⟨89190153515831486645345579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59460102343887657763563719 89190153515831486645345579)
  ·
    refine ⟨133785230273747229968018369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89190153515831486645345579 133785230273747229968018369)
    ·
      refine ⟨100338922705310422476013777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133785230273747229968018369 100338922705310422476013777)
      ·
        refine ⟨75254192028982816857010333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100338922705310422476013777 75254192028982816857010333)
        ·
          refine ⟨28220322010868556321378875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75254192028982816857010333 28220322010868556321378875)
          ·
            refine ⟨42330483016302834482068313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28220322010868556321378875 42330483016302834482068313)
            ·
              refine ⟨31747862262227125861551235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42330483016302834482068313 31747862262227125861551235)
              ·
                refine ⟨47621793393340688792326853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31747862262227125861551235 47621793393340688792326853)
                ·
                  refine ⟨8929086261251379148561285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47621793393340688792326853 8929086261251379148561285)
                  ·
                    refine ⟨1674203673984633590355241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8929086261251379148561285 1674203673984633590355241)
                    ·
                      refine ⟨1255652755488475192766431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674203673984633590355241 1255652755488475192766431)
                      ·
                        rfl

theorem cell23_2445375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_2445375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445375 prefixEnd_2445375 := by exact prefixLift 2445375
  have htrace : WordTrace (prefixWord ++ tailWord_2445375) baseStart_2445375 baseEnd_2445375 := by
    simpa [prefixWord, tailWord_2445375, baseEnd_2445375] using wordTrace_append hprefix tailTrace_2445375
  have hstable : (prefixWord ++ tailWord_2445375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445375).length < 2 ^ (prefixWord ++ tailWord_2445375).sum := by decide
  have hdescent : baseEnd_2445375 < baseStart_2445375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445382 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2445382 : Nat := 118140960795 + 2445382 * 2 ^ 59
def prefixEnd_2445382 : Nat := 4983230072969 + 3 ^ 40 * 2445382 * 2
def baseEnd_2445382 : Nat := 1255656349853056665378899

theorem tailTrace_2445382 : CollatzResearch.WordTrace tailWord_2445382 prefixEnd_2445382 1255656349853056665378899 := by
  unfold tailWord_2445382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787200275837691463776575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59460272551204084560566933 2787200275837691463776575)
  ·
    refine ⟨4180800413756537195664863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2787200275837691463776575 4180800413756537195664863)
    ·
      refine ⟨6271200620634805793497295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4180800413756537195664863 6271200620634805793497295)
      ·
        refine ⟨9406800930952208690245943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6271200620634805793497295 9406800930952208690245943)
        ·
          refine ⟨14110201396428313035368915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9406800930952208690245943 14110201396428313035368915)
          ·
            refine ⟨21165302094642469553053373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14110201396428313035368915 21165302094642469553053373)
            ·
              refine ⟨7936988285490926082395015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21165302094642469553053373 7936988285490926082395015)
              ·
                refine ⟨11905482428236389123592523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7936988285490926082395015 11905482428236389123592523)
                ·
                  refine ⟨17858223642354583685388785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11905482428236389123592523 17858223642354583685388785)
                  ·
                    refine ⟨13393667731765937764041589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17858223642354583685388785 13393667731765937764041589)
                    ·
                      refine ⟨1255656349853056665378899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13393667731765937764041589 1255656349853056665378899)
                      ·
                        rfl

theorem cell23_2445382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2445382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445382 prefixEnd_2445382 := by exact prefixLift 2445382
  have htrace : WordTrace (prefixWord ++ tailWord_2445382) baseStart_2445382 baseEnd_2445382 := by
    simpa [prefixWord, tailWord_2445382, baseEnd_2445382] using wordTrace_append hprefix tailTrace_2445382
  have hstable : (prefixWord ++ tailWord_2445382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445382).length < 2 ^ (prefixWord ++ tailWord_2445382).sum := by decide
  have hdescent : baseEnd_2445382 < baseStart_2445382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445388 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2445388 : Nat := 118140960795 + 2445388 * 2 ^ 59
def prefixEnd_2445388 : Nat := 4983230072969 + 3 ^ 40 * 2445388 * 2
def baseEnd_2445388 : Nat := 1255659430736983641903871

theorem tailTrace_2445388 : CollatzResearch.WordTrace tailWord_2445388 prefixEnd_2445388 1255659430736983641903871 := by
  unfold tailWord_2445388
  simp only [CollatzResearch.WordTrace]
  refine ⟨44595313832392194932784409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59460418443189593243712545 44595313832392194932784409)
  ·
    refine ⟨33446485374294146199588307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44595313832392194932784409 33446485374294146199588307)
    ·
      refine ⟨50169728061441219299382461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33446485374294146199588307 50169728061441219299382461)
      ·
        refine ⟨18813648023040457237268423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50169728061441219299382461 18813648023040457237268423)
        ·
          refine ⟨28220472034560685855902635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18813648023040457237268423 28220472034560685855902635)
          ·
            refine ⟨42330708051841028783853953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28220472034560685855902635 42330708051841028783853953)
            ·
              refine ⟨31748031038880771587890465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42330708051841028783853953 31748031038880771587890465)
              ·
                refine ⟨23811023279160578690917849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31748031038880771587890465 23811023279160578690917849)
                ·
                  refine ⟨17858267459370434018188387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23811023279160578690917849 17858267459370434018188387)
                  ·
                    refine ⟨26787401189055651027282581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17858267459370434018188387 26787401189055651027282581)
                    ·
                      refine ⟨1255659430736983641903871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26787401189055651027282581 1255659430736983641903871)
                      ·
                        rfl

theorem cell23_2445388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2445388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445388 prefixEnd_2445388 := by exact prefixLift 2445388
  have htrace : WordTrace (prefixWord ++ tailWord_2445388) baseStart_2445388 baseEnd_2445388 := by
    simpa [prefixWord, tailWord_2445388, baseEnd_2445388] using wordTrace_append hprefix tailTrace_2445388
  have hstable : (prefixWord ++ tailWord_2445388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445388).length < 2 ^ (prefixWord ++ tailWord_2445388).sum := by decide
  have hdescent : baseEnd_2445388 < baseStart_2445388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445406 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2445406 : Nat := 118140960795 + 2445406 * 2 ^ 59
def prefixEnd_2445406 : Nat := 4983230072969 + 3 ^ 40 * 2445406 * 2
def baseEnd_2445406 : Nat := 418556224462921523826263

theorem tailTrace_2445406 : CollatzResearch.WordTrace tailWord_2445406 prefixEnd_2445406 418556224462921523826263 := by
  unfold tailWord_2445406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148910522339897367465509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59460856119146119293149381 11148910522339897367465509)
  ·
    refine ⟨2090420722938730756399783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11148910522339897367465509 2090420722938730756399783)
    ·
      refine ⟨3135631084408096134599675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090420722938730756399783 3135631084408096134599675)
      ·
        refine ⟨4703446626612144201899513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135631084408096134599675 4703446626612144201899513)
        ·
          refine ⟨3527584969959108151424635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4703446626612144201899513 3527584969959108151424635)
          ·
            refine ⟨5291377454938662227136953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527584969959108151424635 5291377454938662227136953)
            ·
              refine ⟨3968533091203996670352715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5291377454938662227136953 3968533091203996670352715)
              ·
                refine ⟨5952799636805995005529073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968533091203996670352715 5952799636805995005529073)
                ·
                  refine ⟨4464599727604496254146805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5952799636805995005529073 4464599727604496254146805)
                  ·
                    refine ⟨418556224462921523826263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4464599727604496254146805 418556224462921523826263)
                    ·
                      rfl

theorem cell23_2445406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2445406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445406 prefixEnd_2445406 := by exact prefixLift 2445406
  have htrace : WordTrace (prefixWord ++ tailWord_2445406) baseStart_2445406 baseEnd_2445406 := by
    simpa [prefixWord, tailWord_2445406, baseEnd_2445406] using wordTrace_append hprefix tailTrace_2445406
  have hstable : (prefixWord ++ tailWord_2445406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445406).length < 2 ^ (prefixWord ++ tailWord_2445406).sum := by decide
  have hdescent : baseEnd_2445406 < baseStart_2445406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445435 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 5, 5, 2]
def baseStart_2445435 : Nat := 118140960795 + 2445435 * 2 ^ 59
def prefixEnd_2445435 : Nat := 4983230072969 + 3 ^ 40 * 2445435 * 2
def baseEnd_2445435 : Nat := 1255683564327744958016155

theorem tailTrace_2445435 : CollatzResearch.WordTrace tailWord_2445435 prefixEnd_2445435 1255683564327744958016155 := by
  unfold tailWord_2445435
  simp only [CollatzResearch.WordTrace]
  refine ⟨89192341895614116892529759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59461561263742744595019839 89192341895614116892529759)
  ·
    refine ⟨133788512843421175338794639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89192341895614116892529759 133788512843421175338794639)
    ·
      refine ⟨200682769265131763008191959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133788512843421175338794639 200682769265131763008191959)
      ·
        refine ⟨301024153897697644512287939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200682769265131763008191959 301024153897697644512287939)
        ·
          refine ⟨451536230846546466768431909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301024153897697644512287939 451536230846546466768431909)
          ·
            refine ⟨84663043283727462519080983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 451536230846546466768431909 84663043283727462519080983)
            ·
              refine ⟨126994564925591193778621475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84663043283727462519080983 126994564925591193778621475)
              ·
                refine ⟨190491847388386790667932213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126994564925591193778621475 190491847388386790667932213)
                ·
                  refine ⟨17858610692661261625118645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190491847388386790667932213 17858610692661261625118645)
                  ·
                    refine ⟨1674244752436993277354873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17858610692661261625118645 1674244752436993277354873)
                    ·
                      refine ⟨1255683564327744958016155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674244752436993277354873 1255683564327744958016155)
                      ·
                        rfl

theorem cell23_2445435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 5, 2].length) (baseStart_2445435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445435 prefixEnd_2445435 := by exact prefixLift 2445435
  have htrace : WordTrace (prefixWord ++ tailWord_2445435) baseStart_2445435 baseEnd_2445435 := by
    simpa [prefixWord, tailWord_2445435, baseEnd_2445435] using wordTrace_append hprefix tailTrace_2445435
  have hstable : (prefixWord ++ tailWord_2445435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445435).length < 2 ^ (prefixWord ++ tailWord_2445435).sum := by decide
  have hdescent : baseEnd_2445435 < baseStart_2445435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445436 : List Nat := [2, 2, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_2445436 : Nat := 118140960795 + 2445436 * 2 ^ 59
def prefixEnd_2445436 : Nat := 4983230072969 + 3 ^ 40 * 2445436 * 2
def baseEnd_2445436 : Nat := 418561359269466484701217

theorem tailTrace_2445436 : CollatzResearch.WordTrace tailWord_2445436 prefixEnd_2445436 418561359269466484701217 := by
  unfold tailWord_2445436
  simp only [CollatzResearch.WordTrace]
  refine ⟨44596189184305247031658081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59461585579073662708877441 44596189184305247031658081)
  ·
    refine ⟨33447141888228935273743561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44596189184305247031658081 33447141888228935273743561)
    ·
      refine ⟨25085356416171701455307671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33447141888228935273743561 25085356416171701455307671)
      ·
        refine ⟨37628034624257552182961507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25085356416171701455307671 37628034624257552182961507)
        ·
          refine ⟨56442051936386328274442261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37628034624257552182961507 56442051936386328274442261)
          ·
            refine ⟨2645721184518109137864481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56442051936386328274442261 2645721184518109137864481)
            ·
              refine ⟨1984290888388581853398361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645721184518109137864481 1984290888388581853398361)
              ·
                refine ⟨1488218166291436390048771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984290888388581853398361 1488218166291436390048771)
                ·
                  refine ⟨2232327249437154585073157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488218166291436390048771 2232327249437154585073157)
                  ·
                    refine ⟨418561359269466484701217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232327249437154585073157 418561359269466484701217)
                    ·
                      rfl

theorem cell23_2445436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_2445436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445436 prefixEnd_2445436 := by exact prefixLift 2445436
  have htrace : WordTrace (prefixWord ++ tailWord_2445436) baseStart_2445436 baseEnd_2445436 := by
    simpa [prefixWord, tailWord_2445436, baseEnd_2445436] using wordTrace_append hprefix tailTrace_2445436
  have hstable : (prefixWord ++ tailWord_2445436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445436).length < 2 ^ (prefixWord ++ tailWord_2445436).sum := by decide
  have hdescent : baseEnd_2445436 < baseStart_2445436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445445 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_2445445 : Nat := 118140960795 + 2445445 * 2 ^ 59
def prefixEnd_2445445 : Nat := 4983230072969 + 3 ^ 40 * 2445445 * 2
def baseEnd_2445445 : Nat := 418562899711429972963703

theorem tailTrace_2445445 : CollatzResearch.WordTrace tailWord_2445445 prefixEnd_2445445 418562899711429972963703 := by
  unfold tailWord_2445445
  simp only [CollatzResearch.WordTrace]
  refine ⟨89192706625577888600393789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59461804417051925733595859 89192706625577888600393789)
  ·
    refine ⟨33447264984591708225147671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89192706625577888600393789 33447264984591708225147671)
    ·
      refine ⟨50170897476887562337721507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33447264984591708225147671 50170897476887562337721507)
      ·
        refine ⟨75256346215331343506582261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50170897476887562337721507 75256346215331343506582261)
        ·
          refine ⟨7055282457687313453742087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75256346215331343506582261 7055282457687313453742087)
          ·
            refine ⟨10582923686530970180613131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7055282457687313453742087 10582923686530970180613131)
            ·
              refine ⟨15874385529796455270919697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10582923686530970180613131 15874385529796455270919697)
              ·
                refine ⟨11905789147347341453189773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15874385529796455270919697 11905789147347341453189773)
                ·
                  refine ⟨4464670930255253044946165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11905789147347341453189773 4464670930255253044946165)
                  ·
                    refine ⟨418562899711429972963703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4464670930255253044946165 418562899711429972963703)
                    ·
                      rfl

theorem cell23_2445445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_2445445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445445 prefixEnd_2445445 := by exact prefixLift 2445445
  have htrace : WordTrace (prefixWord ++ tailWord_2445445) baseStart_2445445 baseEnd_2445445 := by
    simpa [prefixWord, tailWord_2445445, baseEnd_2445445] using wordTrace_append hprefix tailTrace_2445445
  have hstable : (prefixWord ++ tailWord_2445445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445445).length < 2 ^ (prefixWord ++ tailWord_2445445).sum := by decide
  have hdescent : baseEnd_2445445 < baseStart_2445445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445469 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_2445469 : Nat := 118140960795 + 2445469 * 2 ^ 59
def prefixEnd_2445469 : Nat := 4983230072969 + 3 ^ 40 * 2445469 * 2
def baseEnd_2445469 : Nat := 1255701022669997824990999

theorem tailTrace_2445469 : CollatzResearch.WordTrace tailWord_2445469 prefixEnd_2445469 1255701022669997824990999 := by
  unfold tailWord_2445469
  simp only [CollatzResearch.WordTrace]
  refine ⟨89193581977490940699267461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59462387984993960466178307 89193581977490940699267461)
  ·
    refine ⟨16723796620779551381112649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89193581977490940699267461 16723796620779551381112649)
    ·
      refine ⟨12542847465584663535834487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16723796620779551381112649 12542847465584663535834487)
      ·
        refine ⟨18814271198376995303751731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12542847465584663535834487 18814271198376995303751731)
        ·
          refine ⟨28221406797565492955627597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18814271198376995303751731 28221406797565492955627597)
          ·
            refine ⟨10583027549087059858360349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28221406797565492955627597 10583027549087059858360349)
            ·
              refine ⟨3968635330907647446885131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10583027549087059858360349 3968635330907647446885131)
              ·
                refine ⟨5952952996361471170327697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968635330907647446885131 5952952996361471170327697)
                ·
                  refine ⟨4464714747271103377745773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5952952996361471170327697 4464714747271103377745773)
                  ·
                    refine ⟨1674268030226663766654665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4464714747271103377745773 1674268030226663766654665)
                    ·
                      refine ⟨1255701022669997824990999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674268030226663766654665 1255701022669997824990999)
                      ·
                        rfl

theorem cell23_2445469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_2445469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445469 prefixEnd_2445469 := by exact prefixLift 2445469
  have htrace : WordTrace (prefixWord ++ tailWord_2445469) baseStart_2445469 baseEnd_2445469 := by
    simpa [prefixWord, tailWord_2445469, baseEnd_2445469] using wordTrace_append hprefix tailTrace_2445469
  have hstable : (prefixWord ++ tailWord_2445469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445469).length < 2 ^ (prefixWord ++ tailWord_2445469).sum := by decide
  have hdescent : baseEnd_2445469 < baseStart_2445469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445479 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2445479 : Nat := 118140960795 + 2445479 * 2 ^ 59
def prefixEnd_2445479 : Nat := 4983230072969 + 3 ^ 40 * 2445479 * 2
def baseEnd_2445479 : Nat := 418568719158847595288651

theorem tailTrace_2445479 : CollatzResearch.WordTrace tailWord_2445479 prefixEnd_2445479 418568719158847595288651 := by
  unfold tailWord_2445479
  simp only [CollatzResearch.WordTrace]
  refine ⟨89193946707454712407131491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59462631138303141604754327 89193946707454712407131491)
  ·
    refine ⟨133790920061182068610697237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89193946707454712407131491 133790920061182068610697237)
    ·
      refine ⟨6271449377867909466126433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133790920061182068610697237 6271449377867909466126433)
      ·
        refine ⟨4703587033400932099594825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6271449377867909466126433 4703587033400932099594825)
        ·
          refine ⟨3527690275050699074696119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4703587033400932099594825 3527690275050699074696119)
          ·
            refine ⟨5291535412576048612044179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527690275050699074696119 5291535412576048612044179)
            ·
              refine ⟨7937303118864072918066269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5291535412576048612044179 7937303118864072918066269)
              ·
                refine ⟨2976488669574027344274851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7937303118864072918066269 2976488669574027344274851)
                ·
                  refine ⟨4464733004361041016412277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976488669574027344274851 4464733004361041016412277)
                  ·
                    refine ⟨418568719158847595288651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4464733004361041016412277 418568719158847595288651)
                    ·
                      rfl

theorem cell23_2445479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2445479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445479 prefixEnd_2445479 := by exact prefixLift 2445479
  have htrace : WordTrace (prefixWord ++ tailWord_2445479) baseStart_2445479 baseEnd_2445479 := by
    simpa [prefixWord, tailWord_2445479, baseEnd_2445479] using wordTrace_append hprefix tailTrace_2445479
  have hstable : (prefixWord ++ tailWord_2445479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445479).length < 2 ^ (prefixWord ++ tailWord_2445479).sum := by decide
  have hdescent : baseEnd_2445479 < baseStart_2445479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445499 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 3, 2, 2]
def baseStart_2445499 : Nat := 118140960795 + 2445499 * 2 ^ 59
def prefixEnd_2445499 : Nat := 4983230072969 + 3 ^ 40 * 2445499 * 2
def baseEnd_2445499 : Nat := 1255716427089632707615861

theorem tailTrace_2445499 : CollatzResearch.WordTrace tailWord_2445499 prefixEnd_2445499 1255716427089632707615861 := by
  unfold tailWord_2445499
  simp only [CollatzResearch.WordTrace]
  refine ⟨89194676167382255822859551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59463117444921503881906367 89194676167382255822859551)
  ·
    refine ⟨133792014251073383734289327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89194676167382255822859551 133792014251073383734289327)
    ·
      refine ⟨200688021376610075601433991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133792014251073383734289327 200688021376610075601433991)
      ·
        refine ⟨301032032064915113402150987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200688021376610075601433991 301032032064915113402150987)
        ·
          refine ⟨451548048097372670103226481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301032032064915113402150987 451548048097372670103226481)
          ·
            refine ⟨338661036073029502577419861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451548048097372670103226481 338661036073029502577419861)
            ·
              refine ⟨3968684016480814483329139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 338661036073029502577419861 3968684016480814483329139)
              ·
                refine ⟨5953026024721221724993709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3968684016480814483329139 5953026024721221724993709)
                ·
                  refine ⟨2232384759270458146872641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5953026024721221724993709 2232384759270458146872641)
                  ·
                    refine ⟨1674288569452843610154481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232384759270458146872641 1674288569452843610154481)
                    ·
                      refine ⟨1255716427089632707615861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674288569452843610154481 1255716427089632707615861)
                      ·
                        rfl

theorem cell23_2445499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 2, 2].length) (baseStart_2445499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445499 prefixEnd_2445499 := by exact prefixLift 2445499
  have htrace : WordTrace (prefixWord ++ tailWord_2445499) baseStart_2445499 baseEnd_2445499 := by
    simpa [prefixWord, tailWord_2445499, baseEnd_2445499] using wordTrace_append hprefix tailTrace_2445499
  have hstable : (prefixWord ++ tailWord_2445499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445499).length < 2 ^ (prefixWord ++ tailWord_2445499).sum := by decide
  have hdescent : baseEnd_2445499 < baseStart_2445499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445516 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2445516 : Nat := 118140960795 + 2445516 * 2 ^ 59
def prefixEnd_2445516 : Nat := 4983230072969 + 3 ^ 40 * 2445516 * 2
def baseEnd_2445516 : Nat := 1255725156260759141103283

theorem tailTrace_2445516 : CollatzResearch.WordTrace tailWord_2445516 prefixEnd_2445516 1255725156260759141103283 := by
  unfold tailWord_2445516
  simp only [CollatzResearch.WordTrace]
  refine ⟨44597648104160333863114201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59463530805547111817485601 44597648104160333863114201)
  ·
    refine ⟨33448236078120250397335651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44597648104160333863114201 33448236078120250397335651)
    ·
      refine ⟨50172354117180375596003477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33448236078120250397335651 50172354117180375596003477)
      ·
        refine ⟨2351829099242830106062663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50172354117180375596003477 2351829099242830106062663)
        ·
          refine ⟨3527743648864245159093995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351829099242830106062663 3527743648864245159093995)
          ·
            refine ⟨5291615473296367738640993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3527743648864245159093995 5291615473296367738640993)
            ·
              refine ⟨3968711604972275803980745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5291615473296367738640993 3968711604972275803980745)
              ·
                refine ⟨2976533703729206852985559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968711604972275803980745 2976533703729206852985559)
                ·
                  refine ⟨4464800555593810279478339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976533703729206852985559 4464800555593810279478339)
                  ·
                    refine ⟨6697200833390715419217509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4464800555593810279478339 6697200833390715419217509)
                    ·
                      refine ⟨1255725156260759141103283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6697200833390715419217509 1255725156260759141103283)
                      ·
                        rfl

theorem cell23_2445516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2445516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445516 prefixEnd_2445516 := by exact prefixLift 2445516
  have htrace : WordTrace (prefixWord ++ tailWord_2445516) baseStart_2445516 baseEnd_2445516 := by
    simpa [prefixWord, tailWord_2445516, baseEnd_2445516] using wordTrace_append hprefix tailTrace_2445516
  have hstable : (prefixWord ++ tailWord_2445516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445516).length < 2 ^ (prefixWord ++ tailWord_2445516).sum := by decide
  have hdescent : baseEnd_2445516 < baseStart_2445516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445522 : List Nat := [3, 2, 2, 2, 1, 2, 4, 7]
def baseStart_2445522 : Nat := 118140960795 + 2445522 * 2 ^ 59
def prefixEnd_2445522 : Nat := 4983230072969 + 3 ^ 40 * 2445522 * 2
def baseEnd_2445522 : Nat := 46508453227580967319565

theorem tailTrace_2445522 : CollatzResearch.WordTrace tailWord_2445522 prefixEnd_2445522 46508453227580967319565 := by
  unfold tailWord_2445522
  simp only [CollatzResearch.WordTrace]
  refine ⟨22298878761574732687736705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59463676697532620500631213 22298878761574732687736705)
  ·
    refine ⟨16724159071181049515802529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22298878761574732687736705 16724159071181049515802529)
    ·
      refine ⟨12543119303385787136851897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16724159071181049515802529 12543119303385787136851897)
      ·
        refine ⟨9407339477539340352638923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12543119303385787136851897 9407339477539340352638923)
        ·
          refine ⟨14111009216309010528958385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407339477539340352638923 14111009216309010528958385)
          ·
            refine ⟨10583256912231757896718789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14111009216309010528958385 10583256912231757896718789)
            ·
              refine ⟨1984360671043454605634773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10583256912231757896718789 1984360671043454605634773)
              ·
                refine ⟨46508453227580967319565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1984360671043454605634773 46508453227580967319565)
                ·
                  rfl

theorem cell23_2445522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 7].length) (baseStart_2445522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445522 prefixEnd_2445522 := by exact prefixLift 2445522
  have htrace : WordTrace (prefixWord ++ tailWord_2445522) baseStart_2445522 baseEnd_2445522 := by
    simpa [prefixWord, tailWord_2445522, baseEnd_2445522] using wordTrace_append hprefix tailTrace_2445522
  have hstable : (prefixWord ++ tailWord_2445522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445522).length < 2 ^ (prefixWord ++ tailWord_2445522).sum := by decide
  have hdescent : baseEnd_2445522 < baseStart_2445522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445539 : List Nat := [1, 1, 1, 8, 2, 1, 9]
def baseStart_2445539 : Nat := 118140960795 + 2445539 * 2 ^ 59
def prefixEnd_2445539 : Nat := 4983230072969 + 3 ^ 40 * 2445539 * 2
def baseEnd_2445539 : Nat := 15502925510071759890317

theorem tailTrace_2445539 : CollatzResearch.WordTrace tailWord_2445539 prefixEnd_2445539 15502925510071759890317 := by
  unfold tailWord_2445539
  simp only [CollatzResearch.WordTrace]
  refine ⟨89196135087237342654315671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59464090058158228436210447 89196135087237342654315671)
  ·
    refine ⟨133794202630856013981473507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89196135087237342654315671 133794202630856013981473507)
    ·
      refine ⟨200691303946284020972210261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133794202630856013981473507 200691303946284020972210261)
      ·
        refine ⟨2351851218120515870768089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 200691303946284020972210261 2351851218120515870768089)
        ·
          refine ⟨1763888413590386903076067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351851218120515870768089 1763888413590386903076067)
          ·
            refine ⟨2645832620385580354614101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763888413590386903076067 2645832620385580354614101)
            ·
              refine ⟨15502925510071759890317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2645832620385580354614101 15502925510071759890317)
              ·
                rfl

theorem cell23_2445539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 9].length) (baseStart_2445539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445539 prefixEnd_2445539 := by exact prefixLift 2445539
  have htrace : WordTrace (prefixWord ++ tailWord_2445539) baseStart_2445539 baseEnd_2445539 := by
    simpa [prefixWord, tailWord_2445539, baseEnd_2445539] using wordTrace_append hprefix tailTrace_2445539
  have hstable : (prefixWord ++ tailWord_2445539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445539).length < 2 ^ (prefixWord ++ tailWord_2445539).sum := by decide
  have hdescent : baseEnd_2445539 < baseStart_2445539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445555 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4]
def baseStart_2445555 : Nat := 118140960795 + 2445555 * 2 ^ 59
def prefixEnd_2445555 : Nat := 4983230072969 + 3 ^ 40 * 2445555 * 2
def baseEnd_2445555 : Nat := 1255745182006284488515603

theorem tailTrace_2445555 : CollatzResearch.WordTrace tailWord_2445555 prefixEnd_2445555 1255745182006284488515603 := by
  unfold tailWord_2445555
  simp only [CollatzResearch.WordTrace]
  refine ⟨89196718655179377386898119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59464479103452918257932079 89196718655179377386898119)
  ·
    refine ⟨133795077982769066080347179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89196718655179377386898119 133795077982769066080347179)
    ·
      refine ⟨200692616974153599120520769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133795077982769066080347179 200692616974153599120520769)
      ·
        refine ⟨150519462730615199340390577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200692616974153599120520769 150519462730615199340390577)
        ·
          refine ⟨112889597047961399505292933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150519462730615199340390577 112889597047961399505292933)
          ·
            refine ⟨21166799446492762407242425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112889597047961399505292933 21166799446492762407242425)
            ·
              refine ⟨15875099584869571805431819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21166799446492762407242425 15875099584869571805431819)
              ·
                refine ⟨23812649377304357708147729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15875099584869571805431819 23812649377304357708147729)
                ·
                  refine ⟨17859487032978268281110797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23812649377304357708147729 17859487032978268281110797)
                  ·
                    refine ⟨6697307637366850605416549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17859487032978268281110797 6697307637366850605416549)
                    ·
                      refine ⟨1255745182006284488515603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6697307637366850605416549 1255745182006284488515603)
                      ·
                        rfl

theorem cell23_2445555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_2445555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445555 prefixEnd_2445555 := by exact prefixLift 2445555
  have htrace : WordTrace (prefixWord ++ tailWord_2445555) baseStart_2445555 baseEnd_2445555 := by
    simpa [prefixWord, tailWord_2445555, baseEnd_2445555] using wordTrace_append hprefix tailTrace_2445555
  have hstable : (prefixWord ++ tailWord_2445555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445555).length < 2 ^ (prefixWord ++ tailWord_2445555).sum := by decide
  have hdescent : baseEnd_2445555 < baseStart_2445555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445565 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_2445565 : Nat := 118140960795 + 2445565 * 2 ^ 59
def prefixEnd_2445565 : Nat := 4983230072969 + 3 ^ 40 * 2445565 * 2
def baseEnd_2445565 : Nat := 418583438937609816463519

theorem tailTrace_2445565 : CollatzResearch.WordTrace tailWord_2445565 prefixEnd_2445565 418583438937609816463519 := by
  unfold tailWord_2445565
  simp only [CollatzResearch.WordTrace]
  refine ⟨89197083385143149094762149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59464722256762099396508099 89197083385143149094762149)
  ·
    refine ⟨16724453134714340455267903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89197083385143149094762149 16724453134714340455267903)
    ·
      refine ⟨25086679702071510682901855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16724453134714340455267903 25086679702071510682901855)
      ·
        refine ⟨37630019553107266024352783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25086679702071510682901855 37630019553107266024352783)
        ·
          refine ⟨56445029329660899036529175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37630019553107266024352783 56445029329660899036529175)
          ·
            refine ⟨84667543994491348554793763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56445029329660899036529175 84667543994491348554793763)
            ·
              refine ⟨127001315991737022832190645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84667543994491348554793763 127001315991737022832190645)
              ·
                refine ⟨11906373374225345890517873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127001315991737022832190645 11906373374225345890517873)
                ·
                  refine ⟨8929780030669009417888405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11906373374225345890517873 8929780030669009417888405)
                  ·
                    refine ⟨418583438937609816463519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8929780030669009417888405 418583438937609816463519)
                    ·
                      rfl

theorem cell23_2445565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_2445565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445565 prefixEnd_2445565 := by exact prefixLift 2445565
  have htrace : WordTrace (prefixWord ++ tailWord_2445565) baseStart_2445565 baseEnd_2445565 := by
    simpa [prefixWord, tailWord_2445565, baseEnd_2445565] using wordTrace_append hprefix tailTrace_2445565
  have hstable : (prefixWord ++ tailWord_2445565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445565).length < 2 ^ (prefixWord ++ tailWord_2445565).sum := by decide
  have hdescent : baseEnd_2445565 < baseStart_2445565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445566 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2445566 : Nat := 118140960795 + 2445566 * 2 ^ 59
def prefixEnd_2445566 : Nat := 4983230072969 + 3 ^ 40 * 2445566 * 2
def baseEnd_2445566 : Nat := 1255750830293483945478053

theorem tailTrace_2445566 : CollatzResearch.WordTrace tailWord_2445566 prefixEnd_2445566 1255750830293483945478053 := by
  unfold tailWord_2445566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149639982267440783193569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59464746572093017510365701 11149639982267440783193569)
  ·
    refine ⟨8362229986700580587395177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11149639982267440783193569 8362229986700580587395177)
    ·
      refine ⟨6271672490025435440546383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8362229986700580587395177 6271672490025435440546383)
      ·
        refine ⟨9407508735038153160819575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6271672490025435440546383 9407508735038153160819575)
        ·
          refine ⟨14111263102557229741229363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9407508735038153160819575 14111263102557229741229363)
          ·
            refine ⟨21166894653835844611844045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14111263102557229741229363 21166894653835844611844045)
            ·
              refine ⟨7937585495188441729441517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21166894653835844611844045 7937585495188441729441517)
              ·
                refine ⟨2976594560695665648540569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7937585495188441729441517 2976594560695665648540569)
                ·
                  refine ⟨2232445920521749236405427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976594560695665648540569 2232445920521749236405427)
                  ·
                    refine ⟨3348668880782623854608141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2232445920521749236405427 3348668880782623854608141)
                    ·
                      refine ⟨1255750830293483945478053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3348668880782623854608141 1255750830293483945478053)
                      ·
                        rfl

theorem cell23_2445566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2445566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445566 prefixEnd_2445566 := by exact prefixLift 2445566
  have htrace : WordTrace (prefixWord ++ tailWord_2445566) baseStart_2445566 baseEnd_2445566 := by
    simpa [prefixWord, tailWord_2445566, baseEnd_2445566] using wordTrace_append hprefix tailTrace_2445566
  have hstable : (prefixWord ++ tailWord_2445566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445566).length < 2 ^ (prefixWord ++ tailWord_2445566).sum := by decide
  have hdescent : baseEnd_2445566 < baseStart_2445566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445576 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_2445576 : Nat := 118140960795 + 2445576 * 2 ^ 59
def prefixEnd_2445576 : Nat := 4983230072969 + 3 ^ 40 * 2445576 * 2
def baseEnd_2445576 : Nat := 1255755965100028906353007

theorem tailTrace_2445576 : CollatzResearch.WordTrace tailWord_2445576 prefixEnd_2445576 1255755965100028906353007 := by
  unfold tailWord_2445576
  simp only [CollatzResearch.WordTrace]
  refine ⟨44598742294051648986706291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59464989725402198648941721 44598742294051648986706291)
  ·
    refine ⟨66898113441077473480059437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44598742294051648986706291 66898113441077473480059437)
    ·
      refine ⟨25086792540404052555022289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66898113441077473480059437 25086792540404052555022289)
      ·
        refine ⟨18815094405303039416266717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25086792540404052555022289 18815094405303039416266717)
        ·
          refine ⟨7055660401988639781100019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18815094405303039416266717 7055660401988639781100019)
          ·
            refine ⟨10583490602982959671650029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7055660401988639781100019 10583490602982959671650029)
            ·
              refine ⟨3968808976118609876868761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10583490602982959671650029 3968808976118609876868761)
              ·
                refine ⟨2976606732088957407651571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968808976118609876868761 2976606732088957407651571)
                ·
                  refine ⟨4464910098133436111477357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976606732088957407651571 4464910098133436111477357)
                  ·
                    refine ⟨1674341286800038541804009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4464910098133436111477357 1674341286800038541804009)
                    ·
                      refine ⟨1255755965100028906353007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674341286800038541804009 1255755965100028906353007)
                      ·
                        rfl

theorem cell23_2445576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_2445576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445576 prefixEnd_2445576 := by exact prefixLift 2445576
  have htrace : WordTrace (prefixWord ++ tailWord_2445576) baseStart_2445576 baseEnd_2445576 := by
    simpa [prefixWord, tailWord_2445576, baseEnd_2445576] using wordTrace_append hprefix tailTrace_2445576
  have hstable : (prefixWord ++ tailWord_2445576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445576).length < 2 ^ (prefixWord ++ tailWord_2445576).sum := by decide
  have hdescent : baseEnd_2445576 < baseStart_2445576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445589 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_2445589 : Nat := 118140960795 + 2445589 * 2 ^ 59
def prefixEnd_2445589 : Nat := 4983230072969 + 3 ^ 40 * 2445589 * 2
def baseEnd_2445589 : Nat := 1255762640348537355490447

theorem tailTrace_2445589 : CollatzResearch.WordTrace tailWord_2445589 prefixEnd_2445589 1255762640348537355490447 := by
  unfold tailWord_2445589
  simp only [CollatzResearch.WordTrace]
  refine ⟨89197958737056201193635821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59465305824704134129090547 89197958737056201193635821)
  ·
    refine ⟨33449234526396075447613433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89197958737056201193635821 33449234526396075447613433)
    ·
      refine ⟨25086925894797056585710075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33449234526396075447613433 25086925894797056585710075)
      ·
        refine ⟨37630388842195584878565113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25086925894797056585710075 37630388842195584878565113)
        ·
          refine ⟨28222791631646688658923835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37630388842195584878565113 28222791631646688658923835)
          ·
            refine ⟨42334187447470032988385753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28222791631646688658923835 42334187447470032988385753)
            ·
              refine ⟨31750640585602524741289315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42334187447470032988385753 31750640585602524741289315)
              ·
                refine ⟨47625960878403787111933973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31750640585602524741289315 47625960878403787111933973)
                ·
                  refine ⟨2232466916175177520871905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47625960878403787111933973 2232466916175177520871905)
                  ·
                    refine ⟨1674350187131383140653929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232466916175177520871905 1674350187131383140653929)
                    ·
                      refine ⟨1255762640348537355490447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674350187131383140653929 1255762640348537355490447)
                      ·
                        rfl

theorem cell23_2445589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_2445589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445589 prefixEnd_2445589 := by exact prefixLift 2445589
  have htrace : WordTrace (prefixWord ++ tailWord_2445589) baseStart_2445589 baseEnd_2445589 := by
    simpa [prefixWord, tailWord_2445589, baseEnd_2445589] using wordTrace_append hprefix tailTrace_2445589
  have hstable : (prefixWord ++ tailWord_2445589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445589).length < 2 ^ (prefixWord ++ tailWord_2445589).sum := by decide
  have hdescent : baseEnd_2445589 < baseStart_2445589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445635 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7]
def baseStart_2445635 : Nat := 118140960795 + 2445635 * 2 ^ 59
def prefixEnd_2445635 : Nat := 4983230072969 + 3 ^ 40 * 2445635 * 2
def baseEnd_2445635 : Nat := 1255786260458644175515235

theorem tailTrace_2445635 : CollatzResearch.WordTrace tailWord_2445635 prefixEnd_2445635 1255786260458644175515235 := by
  unfold tailWord_2445635
  simp only [CollatzResearch.WordTrace]
  refine ⟨89199636494889551049810359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59466424329926367366540239 89199636494889551049810359)
  ·
    refine ⟨133799454742334326574715539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89199636494889551049810359 133799454742334326574715539)
    ·
      refine ⟨200699182113501489862073309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133799454742334326574715539 200699182113501489862073309)
      ·
        refine ⟨75262193292563058698277491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200699182113501489862073309 75262193292563058698277491)
        ·
          refine ⟨112893289938844588047416237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75262193292563058698277491 112893289938844588047416237)
          ·
            refine ⟨42334983727066720517781089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112893289938844588047416237 42334983727066720517781089)
            ·
              refine ⟨31751237795300040388335817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42334983727066720517781089 31751237795300040388335817)
              ·
                refine ⟨23813428346475030291251863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31751237795300040388335817 23813428346475030291251863)
                ·
                  refine ⟨35720142519712545436877795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23813428346475030291251863 35720142519712545436877795)
                  ·
                    refine ⟨53580213779568818155316693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35720142519712545436877795 53580213779568818155316693)
                    ·
                      refine ⟨1255786260458644175515235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53580213779568818155316693 1255786260458644175515235)
                      ·
                        rfl

theorem cell23_2445635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_2445635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445635 prefixEnd_2445635 := by exact prefixLift 2445635
  have htrace : WordTrace (prefixWord ++ tailWord_2445635) baseStart_2445635 baseEnd_2445635 := by
    simpa [prefixWord, tailWord_2445635, baseEnd_2445635] using wordTrace_append hprefix tailTrace_2445635
  have hstable : (prefixWord ++ tailWord_2445635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445635).length < 2 ^ (prefixWord ++ tailWord_2445635).sum := by decide
  have hdescent : baseEnd_2445635 < baseStart_2445635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445736 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 6]
def baseStart_2445736 : Nat := 118140960795 + 2445736 * 2 ^ 59
def prefixEnd_2445736 : Nat := 4983230072969 + 3 ^ 40 * 2445736 * 2
def baseEnd_2445736 : Nat := 139537569111638697816919

theorem tailTrace_2445736 : CollatzResearch.WordTrace tailWord_2445736 prefixEnd_2445736 139537569111638697816919 := by
  unfold tailWord_2445736
  simp only [CollatzResearch.WordTrace]
  refine ⟨44601660133761822649618531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59468880178349096866158041 44601660133761822649618531)
  ·
    refine ⟨66902490200642733974427797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44601660133761822649618531 66902490200642733974427797)
    ·
      refine ⟨3136054228155128155051303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66902490200642733974427797 3136054228155128155051303)
      ·
        refine ⟨4704081342232692232576955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136054228155128155051303 4704081342232692232576955)
        ·
          refine ⟨7056122013349038348865433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704081342232692232576955 7056122013349038348865433)
          ·
            refine ⟨5292091510011778761649075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7056122013349038348865433 5292091510011778761649075)
            ·
              refine ⟨7938137265017668142473613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292091510011778761649075 7938137265017668142473613)
              ·
                refine ⟨2976801474381625553427605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7938137265017668142473613 2976801474381625553427605)
                ·
                  refine ⟨139537569111638697816919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2976801474381625553427605 139537569111638697816919)
                  ·
                    rfl

theorem cell23_2445736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 6].length) (baseStart_2445736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445736 prefixEnd_2445736 := by exact prefixLift 2445736
  have htrace : WordTrace (prefixWord ++ tailWord_2445736) baseStart_2445736 baseEnd_2445736 := by
    simpa [prefixWord, tailWord_2445736, baseEnd_2445736] using wordTrace_append hprefix tailTrace_2445736
  have hstable : (prefixWord ++ tailWord_2445736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445736).length < 2 ^ (prefixWord ++ tailWord_2445736).sum := by decide
  have hdescent : baseEnd_2445736 < baseStart_2445736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445769 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 4]
def baseStart_2445769 : Nat := 118140960795 + 2445769 * 2 ^ 59
def prefixEnd_2445769 : Nat := 4983230072969 + 3 ^ 40 * 2445769 * 2
def baseEnd_2445769 : Nat := 1255855066866346651239619

theorem tailTrace_2445769 : CollatzResearch.WordTrace tailWord_2445769 prefixEnd_2445769 1255855066866346651239619 := by
  unfold tailWord_2445769
  simp only [CollatzResearch.WordTrace]
  refine ⟨89204523876404091935188361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59469682584269394623458907 89204523876404091935188361)
  ·
    refine ⟨66903392907303068951391271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89204523876404091935188361 66903392907303068951391271)
    ·
      refine ⟨100355089360954603427086907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66903392907303068951391271 100355089360954603427086907)
      ·
        refine ⟨150532634041431905140630361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100355089360954603427086907 150532634041431905140630361)
        ·
          refine ⟨112899475531073928855472771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150532634041431905140630361 112899475531073928855472771)
          ·
            refine ⟨169349213296610893283209157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112899475531073928855472771 169349213296610893283209157)
            ·
              refine ⟨31752977493114542490601717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169349213296610893283209157 31752977493114542490601717)
              ·
                refine ⟨2976841639979488358493911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31752977493114542490601717 2976841639979488358493911)
                ·
                  refine ⟨4465262459969232537740867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976841639979488358493911 4465262459969232537740867)
                  ·
                    refine ⟨6697893689953848806611301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4465262459969232537740867 6697893689953848806611301)
                    ·
                      refine ⟨1255855066866346651239619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6697893689953848806611301 1255855066866346651239619)
                      ·
                        rfl

theorem cell23_2445769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_2445769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445769 prefixEnd_2445769 := by exact prefixLift 2445769
  have htrace : WordTrace (prefixWord ++ tailWord_2445769) baseStart_2445769 baseEnd_2445769 := by
    simpa [prefixWord, tailWord_2445769, baseEnd_2445769] using wordTrace_append hprefix tailTrace_2445769
  have hstable : (prefixWord ++ tailWord_2445769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445769).length < 2 ^ (prefixWord ++ tailWord_2445769).sum := by decide
  have hdescent : baseEnd_2445769 < baseStart_2445769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445780 : List Nat := [2, 4, 1, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_2445780 : Nat := 118140960795 + 2445780 * 2 ^ 59
def prefixEnd_2445780 : Nat := 4983230072969 + 3 ^ 40 * 2445780 * 2
def baseEnd_2445780 : Nat := 1255860715153546108202069

theorem tailTrace_2445780 : CollatzResearch.WordTrace tailWord_2445780 prefixEnd_2445780 1255860715153546108202069 := by
  unfold tailWord_2445780
  simp only [CollatzResearch.WordTrace]
  refine ⟨44602462539682120406919397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59469950052909493875892529 44602462539682120406919397)
  ·
    refine ⟨8362961726190397576297387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44602462539682120406919397 8362961726190397576297387)
    ·
      refine ⟨12544442589285596364446081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8362961726190397576297387 12544442589285596364446081)
      ·
        refine ⟨9408331941964197273334561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12544442589285596364446081 9408331941964197273334561)
        ·
          refine ⟨7056248956473147955000921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9408331941964197273334561 7056248956473147955000921)
          ·
            refine ⟨5292186717354860966250691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7056248956473147955000921 5292186717354860966250691)
            ·
              refine ⟨7938280076032291449376037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292186717354860966250691 7938280076032291449376037)
              ·
                refine ⟨1488427514256054646758007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7938280076032291449376037 1488427514256054646758007)
                ·
                  refine ⟨2232641271384081970137011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488427514256054646758007 2232641271384081970137011)
                  ·
                    refine ⟨3348961907076122955205517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2232641271384081970137011 3348961907076122955205517)
                    ·
                      refine ⟨1255860715153546108202069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3348961907076122955205517 1255860715153546108202069)
                      ·
                        rfl

theorem cell23_2445780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_2445780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445780 prefixEnd_2445780 := by exact prefixLift 2445780
  have htrace : WordTrace (prefixWord ++ tailWord_2445780) baseStart_2445780 baseEnd_2445780 := by
    simpa [prefixWord, tailWord_2445780, baseEnd_2445780] using wordTrace_append hprefix tailTrace_2445780
  have hstable : (prefixWord ++ tailWord_2445780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445780).length < 2 ^ (prefixWord ++ tailWord_2445780).sum := by decide
  have hdescent : baseEnd_2445780 < baseStart_2445780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445789 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2445789 : Nat := 118140960795 + 2445789 * 2 ^ 59
def prefixEnd_2445789 : Nat := 4983230072969 + 3 ^ 40 * 2445789 * 2
def baseEnd_2445789 : Nat := 1255865336479436572989527

theorem tailTrace_2445789 : CollatzResearch.WordTrace tailWord_2445789 prefixEnd_2445789 1255865336479436572989527 := by
  unfold tailWord_2445789
  simp only [CollatzResearch.WordTrace]
  refine ⟨89205253336331635350916421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59470168890887756900610947 89205253336331635350916421)
  ·
    refine ⟨16725985000562181628296829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89205253336331635350916421 16725985000562181628296829)
    ·
      refine ⟨6272244375210818110611311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16725985000562181628296829 6272244375210818110611311)
      ·
        refine ⟨9408366562816227165916967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272244375210818110611311 9408366562816227165916967)
        ·
          refine ⟨14112549844224340748875451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9408366562816227165916967 14112549844224340748875451)
          ·
            refine ⟨21168824766336511123313177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14112549844224340748875451 21168824766336511123313177)
            ·
              refine ⟨15876618574752383342484883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21168824766336511123313177 15876618574752383342484883)
              ·
                refine ⟨23814927862128575013727325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15876618574752383342484883 23814927862128575013727325)
                ·
                  refine ⟨8930597948298215630147747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23814927862128575013727325 8930597948298215630147747)
                  ·
                    refine ⟨13395896922447323445221621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8930597948298215630147747 13395896922447323445221621)
                    ·
                      refine ⟨1255865336479436572989527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13395896922447323445221621 1255865336479436572989527)
                      ·
                        rfl

theorem cell23_2445789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2445789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445789 prefixEnd_2445789 := by exact prefixLift 2445789
  have htrace : WordTrace (prefixWord ++ tailWord_2445789) baseStart_2445789 baseEnd_2445789 := by
    simpa [prefixWord, tailWord_2445789, baseEnd_2445789] using wordTrace_append hprefix tailTrace_2445789
  have hstable : (prefixWord ++ tailWord_2445789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445789).length < 2 ^ (prefixWord ++ tailWord_2445789).sum := by decide
  have hdescent : baseEnd_2445789 < baseStart_2445789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445806 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_2445806 : Nat := 118140960795 + 2445806 * 2 ^ 59
def prefixEnd_2445806 : Nat := 4983230072969 + 3 ^ 40 * 2445806 * 2
def baseEnd_2445806 : Nat := 1255874065650563006476949

theorem tailTrace_2445806 : CollatzResearch.WordTrace tailWord_2445806 prefixEnd_2445806 1255874065650563006476949 := by
  unfold tailWord_2445806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150734172158755906785659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59470582251513364836190181 11150734172158755906785659)
  ·
    refine ⟨16726101258238133860178489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11150734172158755906785659 16726101258238133860178489)
    ·
      refine ⟨12544575943678600395133867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16726101258238133860178489 12544575943678600395133867)
      ·
        refine ⟨18816863915517900592700801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12544575943678600395133867 18816863915517900592700801)
        ·
          refine ⟨14112647936638425444525601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18816863915517900592700801 14112647936638425444525601)
          ·
            refine ⟨10584485952478819083394201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14112647936638425444525601 10584485952478819083394201)
            ·
              refine ⟨7938364464359114312545651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10584485952478819083394201 7938364464359114312545651)
              ·
                refine ⟨11907546696538671468818477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938364464359114312545651 11907546696538671468818477)
                ·
                  refine ⟨4465330011202001800806929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11907546696538671468818477 4465330011202001800806929)
                  ·
                    refine ⟨3348997508401501350605197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4465330011202001800806929 3348997508401501350605197)
                    ·
                      refine ⟨1255874065650563006476949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3348997508401501350605197 1255874065650563006476949)
                      ·
                        rfl

theorem cell23_2445806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_2445806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445806 prefixEnd_2445806 := by exact prefixLift 2445806
  have htrace : WordTrace (prefixWord ++ tailWord_2445806) baseStart_2445806 baseEnd_2445806 := by
    simpa [prefixWord, tailWord_2445806, baseEnd_2445806] using wordTrace_append hprefix tailTrace_2445806
  have hstable : (prefixWord ++ tailWord_2445806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445806).length < 2 ^ (prefixWord ++ tailWord_2445806).sum := by decide
  have hdescent : baseEnd_2445806 < baseStart_2445806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445809 : List Nat := [1, 2, 2, 2, 3, 1, 5, 7]
def baseStart_2445809 : Nat := 118140960795 + 2445809 * 2 ^ 59
def prefixEnd_2445809 : Nat := 4983230072969 + 3 ^ 40 * 2445809 * 2
def baseEnd_2445809 : Nat := 46513911336760240545905

theorem tailTrace_2445809 : CollatzResearch.WordTrace tailWord_2445809 prefixEnd_2445809 46513911336760240545905 := by
  unfold tailWord_2445809
  simp only [CollatzResearch.WordTrace]
  refine ⟨89205982796259178766644481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59470655197506119177762987 89205982796259178766644481)
  ·
    refine ⟨66904487097194384074983361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89205982796259178766644481 66904487097194384074983361)
    ·
      refine ⟨50178365322895788056237521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66904487097194384074983361 50178365322895788056237521)
      ·
        refine ⟨37633773992171841042178141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50178365322895788056237521 37633773992171841042178141)
        ·
          refine ⟨14112665247064440390816803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37633773992171841042178141 14112665247064440390816803)
          ·
            refine ⟨21168997870596660586225205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14112665247064440390816803 21168997870596660586225205)
            ·
              refine ⟨1984593550368436929958613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21168997870596660586225205 1984593550368436929958613)
              ·
                refine ⟨46513911336760240545905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1984593550368436929958613 46513911336760240545905)
                ·
                  rfl

theorem cell23_2445809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 7].length) (baseStart_2445809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445809 prefixEnd_2445809 := by exact prefixLift 2445809
  have htrace : WordTrace (prefixWord ++ tailWord_2445809) baseStart_2445809 baseEnd_2445809 := by
    simpa [prefixWord, tailWord_2445809, baseEnd_2445809] using wordTrace_append hprefix tailTrace_2445809
  have hstable : (prefixWord ++ tailWord_2445809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445809).length < 2 ^ (prefixWord ++ tailWord_2445809).sum := by decide
  have hdescent : baseEnd_2445809 < baseStart_2445809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445826 : List Nat := [3, 4, 1, 2, 2, 1, 10]
def baseStart_2445826 : Nat := 118140960795 + 2445826 * 2 ^ 59
def prefixEnd_2445826 : Nat := 4983230072969 + 3 ^ 40 * 2445826 * 2
def baseEnd_2445826 : Nat := 15504744879798184299097

theorem tailTrace_2445826 : CollatzResearch.WordTrace tailWord_2445826 prefixEnd_2445826 15504744879798184299097 := by
  unfold tailWord_2445826
  simp only [CollatzResearch.WordTrace]
  refine ⟨22301650709299397667503333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59471068558131727113342221 22301650709299397667503333)
  ·
    refine ⟨4181559507993637062656875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22301650709299397667503333 4181559507993637062656875)
    ·
      refine ⟨6272339261990455593985313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4181559507993637062656875 6272339261990455593985313)
      ·
        refine ⟨4704254446492841695488985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6272339261990455593985313 4704254446492841695488985)
        ·
          refine ⟨3528190834869631271616739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4704254446492841695488985 3528190834869631271616739)
          ·
            refine ⟨5292286252304446907425109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528190834869631271616739 5292286252304446907425109)
            ·
              refine ⟨15504744879798184299097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5292286252304446907425109 15504744879798184299097)
              ·
                rfl

theorem cell23_2445826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 10].length) (baseStart_2445826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445826 prefixEnd_2445826 := by exact prefixLift 2445826
  have htrace : WordTrace (prefixWord ++ tailWord_2445826) baseStart_2445826 baseEnd_2445826 := by
    simpa [prefixWord, tailWord_2445826, baseEnd_2445826] using wordTrace_append hprefix tailTrace_2445826
  have hstable : (prefixWord ++ tailWord_2445826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445826).length < 2 ^ (prefixWord ++ tailWord_2445826).sum := by decide
  have hdescent : baseEnd_2445826 < baseStart_2445826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445837 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2445837 : Nat := 118140960795 + 2445837 * 2 ^ 59
def prefixEnd_2445837 : Nat := 4983230072969 + 3 ^ 40 * 2445837 * 2
def baseEnd_2445837 : Nat := 1255889983550852385189307

theorem tailTrace_2445837 : CollatzResearch.WordTrace tailWord_2445837 prefixEnd_2445837 1255889983550852385189307 := by
  unfold tailWord_2445837
  simp only [CollatzResearch.WordTrace]
  refine ⟨89207004040157739548663765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59471336026771826365775843 89207004040157739548663765)
  ·
    refine ⟨2090789157191197020671807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 89207004040157739548663765 2090789157191197020671807)
    ·
      refine ⟨3136183735786795531007711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090789157191197020671807 3136183735786795531007711)
      ·
        refine ⟨4704275603680193296511567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136183735786795531007711 4704275603680193296511567)
        ·
          refine ⟨7056413405520289944767351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704275603680193296511567 7056413405520289944767351)
          ·
            refine ⟨10584620108280434917151027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056413405520289944767351 10584620108280434917151027)
            ·
              refine ⟨15876930162420652375726541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10584620108280434917151027 15876930162420652375726541)
              ·
                refine ⟨5953848810907744640897453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15876930162420652375726541 5953848810907744640897453)
                ·
                  refine ⟨2232693304090404240336545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5953848810907744640897453 2232693304090404240336545)
                  ·
                    refine ⟨1674519978067803180252409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232693304090404240336545 1674519978067803180252409)
                    ·
                      refine ⟨1255889983550852385189307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674519978067803180252409 1255889983550852385189307)
                      ·
                        rfl

theorem cell23_2445837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2445837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445837 prefixEnd_2445837 := by exact prefixLift 2445837
  have htrace : WordTrace (prefixWord ++ tailWord_2445837) baseStart_2445837 baseEnd_2445837 := by
    simpa [prefixWord, tailWord_2445837, baseEnd_2445837] using wordTrace_append hprefix tailTrace_2445837
  have hstable : (prefixWord ++ tailWord_2445837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445837).length < 2 ^ (prefixWord ++ tailWord_2445837).sum := by decide
  have hdescent : baseEnd_2445837 < baseStart_2445837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445853 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2445853 : Nat := 118140960795 + 2445853 * 2 ^ 59
def prefixEnd_2445853 : Nat := 4983230072969 + 3 ^ 40 * 2445853 * 2
def baseEnd_2445853 : Nat := 1255898199241324322589233

theorem tailTrace_2445853 : CollatzResearch.WordTrace tailWord_2445853 prefixEnd_2445853 1255898199241324322589233 := by
  unfold tailWord_2445853
  simp only [CollatzResearch.WordTrace]
  refine ⟨89207587608099774281246213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59471725072066516187497475 89207587608099774281246213)
  ·
    refine ⟨16726422676518707677733665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89207587608099774281246213 16726422676518707677733665)
    ·
      refine ⟨12544817007389030758300249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16726422676518707677733665 12544817007389030758300249)
      ·
        refine ⟨9408612755541773068725187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12544817007389030758300249 9408612755541773068725187)
        ·
          refine ⟨14112919133312659603087781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9408612755541773068725187 14112919133312659603087781)
          ·
            refine ⟨2646172337496123675578959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14112919133312659603087781 2646172337496123675578959)
            ·
              refine ⟨3969258506244185513368439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646172337496123675578959 3969258506244185513368439)
              ·
                refine ⟨5953887759366278270052659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969258506244185513368439 5953887759366278270052659)
                ·
                  refine ⟨8930831639049417405078989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5953887759366278270052659 8930831639049417405078989)
                  ·
                    refine ⟨3349061864643531526904621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8930831639049417405078989 3349061864643531526904621)
                    ·
                      refine ⟨1255898199241324322589233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3349061864643531526904621 1255898199241324322589233)
                      ·
                        rfl

theorem cell23_2445853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2445853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445853 prefixEnd_2445853 := by exact prefixLift 2445853
  have htrace : WordTrace (prefixWord ++ tailWord_2445853) baseStart_2445853 baseEnd_2445853 := by
    simpa [prefixWord, tailWord_2445853, baseEnd_2445853] using wordTrace_append hprefix tailTrace_2445853
  have hstable : (prefixWord ++ tailWord_2445853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445853).length < 2 ^ (prefixWord ++ tailWord_2445853).sum := by decide
  have hdescent : baseEnd_2445853 < baseStart_2445853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445860 : List Nat := [2, 3, 1, 5, 2, 1, 2, 7]
def baseStart_2445860 : Nat := 118140960795 + 2445860 * 2 ^ 59
def prefixEnd_2445860 : Nat := 4983230072969 + 3 ^ 40 * 2445860 * 2
def baseEnd_2445860 : Nat := 46514881244663177600063

theorem tailTrace_2445860 : CollatzResearch.WordTrace tailWord_2445860 prefixEnd_2445860 46514881244663177600063 := by
  unfold tailWord_2445860
  simp only [CollatzResearch.WordTrace]
  refine ⟨44603921459537207238375517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59471895279382942984500689 44603921459537207238375517)
  ·
    refine ⟨16726470547326452714390819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44603921459537207238375517 16726470547326452714390819)
    ·
      refine ⟨25089705820989679071586229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16726470547326452714390819 25089705820989679071586229)
      ·
        refine ⟨2352159920717782412961209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25089705820989679071586229 2352159920717782412961209)
        ·
          refine ⟨1764119940538336809720907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2352159920717782412961209 1764119940538336809720907)
          ·
            refine ⟨2646179910807505214581361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764119940538336809720907 2646179910807505214581361)
            ·
              refine ⟨1984634933105628910936021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2646179910807505214581361 1984634933105628910936021)
              ·
                refine ⟨46514881244663177600063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1984634933105628910936021 46514881244663177600063)
                ·
                  rfl

theorem cell23_2445860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 7].length) (baseStart_2445860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445860 prefixEnd_2445860 := by exact prefixLift 2445860
  have htrace : WordTrace (prefixWord ++ tailWord_2445860) baseStart_2445860 baseEnd_2445860 := by
    simpa [prefixWord, tailWord_2445860, baseEnd_2445860] using wordTrace_append hprefix tailTrace_2445860
  have hstable : (prefixWord ++ tailWord_2445860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445860).length < 2 ^ (prefixWord ++ tailWord_2445860).sum := by decide
  have hdescent : baseEnd_2445860 < baseStart_2445860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445879 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_2445879 : Nat := 118140960795 + 2445879 * 2 ^ 59
def prefixEnd_2445879 : Nat := 4983230072969 + 3 ^ 40 * 2445879 * 2
def baseEnd_2445879 : Nat := 1255911549738341220864113

theorem tailTrace_2445879 : CollatzResearch.WordTrace tailWord_2445879 prefixEnd_2445879 1255911549738341220864113 := by
  unfold tailWord_2445879
  simp only [CollatzResearch.WordTrace]
  refine ⟨89208535906005580721692691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59472357270670387147795127 89208535906005580721692691)
  ·
    refine ⟨133812803859008371082539037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89208535906005580721692691 133812803859008371082539037)
    ·
      refine ⟨50179801447128139155952139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133812803859008371082539037 50179801447128139155952139)
      ·
        refine ⟨75269702170692208733928209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50179801447128139155952139 75269702170692208733928209)
        ·
          refine ⟨56452276628019156550446157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75269702170692208733928209 56452276628019156550446157)
          ·
            refine ⟨21169603735507183706417309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56452276628019156550446157 21169603735507183706417309)
            ·
              refine ⟨7938601400815193889906491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21169603735507183706417309 7938601400815193889906491)
              ·
                refine ⟨11907902101222790834859737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938601400815193889906491 11907902101222790834859737)
                ·
                  refine ⟨8930926575917093126144803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11907902101222790834859737 8930926575917093126144803)
                  ·
                    refine ⟨13396389863875639689217205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8930926575917093126144803 13396389863875639689217205)
                    ·
                      refine ⟨1255911549738341220864113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13396389863875639689217205 1255911549738341220864113)
                      ·
                        rfl

theorem cell23_2445879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_2445879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445879 prefixEnd_2445879 := by exact prefixLift 2445879
  have htrace : WordTrace (prefixWord ++ tailWord_2445879) baseStart_2445879 baseEnd_2445879 := by
    simpa [prefixWord, tailWord_2445879, baseEnd_2445879] using wordTrace_append hprefix tailTrace_2445879
  have hstable : (prefixWord ++ tailWord_2445879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445879).length < 2 ^ (prefixWord ++ tailWord_2445879).sum := by decide
  have hdescent : baseEnd_2445879 < baseStart_2445879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445893 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 4, 2, 2]
def baseStart_2445893 : Nat := 118140960795 + 2445893 * 2 ^ 59
def prefixEnd_2445893 : Nat := 4983230072969 + 3 ^ 40 * 2445893 * 2
def baseEnd_2445893 : Nat := 1255918738467504166089049

theorem tailTrace_2445893 : CollatzResearch.WordTrace tailWord_2445893 prefixEnd_2445893 1255918738467504166089049 := by
  unfold tailWord_2445893
  simp only [CollatzResearch.WordTrace]
  refine ⟨89209046527954861112702333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59472697685303240741801555 89209046527954861112702333)
  ·
    refine ⟨33453392447983072917263375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89209046527954861112702333 33453392447983072917263375)
    ·
      refine ⟨50180088671974609375895063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33453392447983072917263375 50180088671974609375895063)
      ·
        refine ⟨75270133007961914063842595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50180088671974609375895063 75270133007961914063842595)
        ·
          refine ⟨112905199511942871095763893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75270133007961914063842595 112905199511942871095763893)
          ·
            refine ⟨10584862454244644165227865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112905199511942871095763893 10584862454244644165227865)
            ·
              refine ⟨7938646840683483123920899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10584862454244644165227865 7938646840683483123920899)
              ·
                refine ⟨11907970261025224685881349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938646840683483123920899 11907970261025224685881349)
                ·
                  refine ⟨2232744423942229628602753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11907970261025224685881349 2232744423942229628602753)
                  ·
                    refine ⟨1674558317956672221452065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232744423942229628602753 1674558317956672221452065)
                    ·
                      refine ⟨1255918738467504166089049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674558317956672221452065 1255918738467504166089049)
                      ·
                        rfl

theorem cell23_2445893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_2445893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445893 prefixEnd_2445893 := by exact prefixLift 2445893
  have htrace : WordTrace (prefixWord ++ tailWord_2445893) baseStart_2445893 baseEnd_2445893 := by
    simpa [prefixWord, tailWord_2445893, baseEnd_2445893] using wordTrace_append hprefix tailTrace_2445893
  have hstable : (prefixWord ++ tailWord_2445893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445893).length < 2 ^ (prefixWord ++ tailWord_2445893).sum := by decide
  have hdescent : baseEnd_2445893 < baseStart_2445893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445899 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 7]
def baseStart_2445899 : Nat := 118140960795 + 2445899 * 2 ^ 59
def prefixEnd_2445899 : Nat := 4983230072969 + 3 ^ 40 * 2445899 * 2
def baseEnd_2445899 : Nat := 139546868816825682512669

theorem tailTrace_2445899 : CollatzResearch.WordTrace tailWord_2445899 prefixEnd_2445899 139546868816825682512669 := by
  unfold tailWord_2445899
  simp only [CollatzResearch.WordTrace]
  refine ⟨89209265365933124137420751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59472843577288749424947167 89209265365933124137420751)
  ·
    refine ⟨133813898048899686206131127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89209265365933124137420751 133813898048899686206131127)
    ·
      refine ⟨200720847073349529309196691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133813898048899686206131127 200720847073349529309196691)
      ·
        refine ⟨301081270610024293963795037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200720847073349529309196691 301081270610024293963795037)
        ·
          refine ⟨112905476478759110236423139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301081270610024293963795037 112905476478759110236423139)
          ·
            refine ⟨169358214718138665354634709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112905476478759110236423139 169358214718138665354634709)
            ·
              refine ⟨3969333157456374969249251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169358214718138665354634709 3969333157456374969249251)
              ·
                refine ⟨5953999736184562453873877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969333157456374969249251 5953999736184562453873877)
                ·
                  refine ⟨139546868816825682512669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5953999736184562453873877 139546868816825682512669)
                  ·
                    rfl

theorem cell23_2445899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 7].length) (baseStart_2445899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445899 prefixEnd_2445899 := by exact prefixLift 2445899
  have htrace : WordTrace (prefixWord ++ tailWord_2445899) baseStart_2445899 baseEnd_2445899 := by
    simpa [prefixWord, tailWord_2445899, baseEnd_2445899] using wordTrace_append hprefix tailTrace_2445899
  have hstable : (prefixWord ++ tailWord_2445899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445899).length < 2 ^ (prefixWord ++ tailWord_2445899).sum := by decide
  have hdescent : baseEnd_2445899 < baseStart_2445899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445956 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2445956 : Nat := 118140960795 + 2445956 * 2 ^ 59
def prefixEnd_2445956 : Nat := 4983230072969 + 3 ^ 40 * 2445956 * 2
def baseEnd_2445956 : Nat := 1255951087748737419601259

theorem tailTrace_2445956 : CollatzResearch.WordTrace tailWord_2445956 prefixEnd_2445956 1255951087748737419601259 := by
  unfold tailWord_2445956
  simp only [CollatzResearch.WordTrace]
  refine ⟨44605672163363311436122861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59474229551151081914830481 44605672163363311436122861)
  ·
    refine ⟨16727127061261241788546073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44605672163363311436122861 16727127061261241788546073)
    ·
      refine ⟨12545345295945931341409555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16727127061261241788546073 12545345295945931341409555)
      ·
        refine ⟨18818017943918897012114333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12545345295945931341409555 18818017943918897012114333)
        ·
          refine ⟨7056756728969586379542875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18818017943918897012114333 7056756728969586379542875)
          ·
            refine ⟨10585135093454379569314313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056756728969586379542875 10585135093454379569314313)
            ·
              refine ⟨7938851320090784676985735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10585135093454379569314313 7938851320090784676985735)
              ·
                refine ⟨11908276980136177015478603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7938851320090784676985735 11908276980136177015478603)
                ·
                  refine ⟨17862415470204265523217905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11908276980136177015478603 17862415470204265523217905)
                  ·
                    refine ⟨13396811602653199142413429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17862415470204265523217905 13396811602653199142413429)
                    ·
                      refine ⟨1255951087748737419601259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13396811602653199142413429 1255951087748737419601259)
                      ·
                        rfl

theorem cell23_2445956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2445956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445956 prefixEnd_2445956 := by exact prefixLift 2445956
  have htrace : WordTrace (prefixWord ++ tailWord_2445956) baseStart_2445956 baseEnd_2445956 := by
    simpa [prefixWord, tailWord_2445956, baseEnd_2445956] using wordTrace_append hprefix tailTrace_2445956
  have hstable : (prefixWord ++ tailWord_2445956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445956).length < 2 ^ (prefixWord ++ tailWord_2445956).sum := by decide
  have hdescent : baseEnd_2445956 < baseStart_2445956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445966 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2445966 : Nat := 118140960795 + 2445966 * 2 ^ 59
def prefixEnd_2445966 : Nat := 4983230072969 + 3 ^ 40 * 2445966 * 2
def baseEnd_2445966 : Nat := 1255956222555282380476213

theorem tailTrace_2445966 : CollatzResearch.WordTrace tailWord_2445966 prefixEnd_2445966 1255956222555282380476213 := by
  unfold tailWord_2445966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11151463632086299322513719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59474472704460263053406501 11151463632086299322513719)
  ·
    refine ⟨16727195448129448983770579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11151463632086299322513719 16727195448129448983770579)
    ·
      refine ⟨25090793172194173475655869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16727195448129448983770579 25090793172194173475655869)
      ·
        refine ⟨9409047439572815053370951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25090793172194173475655869 9409047439572815053370951)
        ·
          refine ⟨14113571159359222580056427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409047439572815053370951 14113571159359222580056427)
          ·
            refine ⟨21170356739038833870084641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14113571159359222580056427 21170356739038833870084641)
            ·
              refine ⟨15877767554279125402563481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21170356739038833870084641 15877767554279125402563481)
              ·
                refine ⟨11908325665709344051922611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15877767554279125402563481 11908325665709344051922611)
                ·
                  refine ⟨17862488498564016077883917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11908325665709344051922611 17862488498564016077883917)
                  ·
                    refine ⟨6698433186961506029206469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17862488498564016077883917 6698433186961506029206469)
                    ·
                      refine ⟨1255956222555282380476213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6698433186961506029206469 1255956222555282380476213)
                      ·
                        rfl

theorem cell23_2445966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2445966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445966 prefixEnd_2445966 := by exact prefixLift 2445966
  have htrace : WordTrace (prefixWord ++ tailWord_2445966) baseStart_2445966 baseEnd_2445966 := by
    simpa [prefixWord, tailWord_2445966, baseEnd_2445966] using wordTrace_append hprefix tailTrace_2445966
  have hstable : (prefixWord ++ tailWord_2445966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445966).length < 2 ^ (prefixWord ++ tailWord_2445966).sum := by decide
  have hdescent : baseEnd_2445966 < baseStart_2445966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445989 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 8]
def baseStart_2445989 : Nat := 118140960795 + 2445989 * 2 ^ 59
def prefixEnd_2445989 : Nat := 4983230072969 + 3 ^ 40 * 2445989 * 2
def baseEnd_2445989 : Nat := 139552003623370643387623

theorem tailTrace_2445989 : CollatzResearch.WordTrace tailWord_2445989 prefixEnd_2445989 139552003623370643387623 := by
  unfold tailWord_2445989
  simp only [CollatzResearch.WordTrace]
  refine ⟨89212547935607069508197021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59475031957071379672131347 89212547935607069508197021)
  ·
    refine ⟨33454705475852651065573883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89212547935607069508197021 33454705475852651065573883)
    ·
      refine ⟨50182058213778976598360825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33454705475852651065573883 50182058213778976598360825)
      ·
        refine ⟨37636543660334232448770619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50182058213778976598360825 37636543660334232448770619)
        ·
          refine ⟨56454815490501348673155929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37636543660334232448770619 56454815490501348673155929)
          ·
            refine ⟨42341111617876011504866947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56454815490501348673155929 42341111617876011504866947)
            ·
              refine ⟨63511667426814017257300421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42341111617876011504866947 63511667426814017257300421)
              ·
                refine ⟨11908437642527628235743829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63511667426814017257300421 11908437642527628235743829)
                ·
                  refine ⟨139552003623370643387623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11908437642527628235743829 139552003623370643387623)
                  ·
                    rfl

theorem cell23_2445989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_2445989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445989 prefixEnd_2445989 := by exact prefixLift 2445989
  have htrace : WordTrace (prefixWord ++ tailWord_2445989) baseStart_2445989 baseEnd_2445989 := by
    simpa [prefixWord, tailWord_2445989, baseEnd_2445989] using wordTrace_append hprefix tailTrace_2445989
  have hstable : (prefixWord ++ tailWord_2445989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445989).length < 2 ^ (prefixWord ++ tailWord_2445989).sum := by decide
  have hdescent : baseEnd_2445989 < baseStart_2445989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2445993 : List Nat := [1, 2, 1, 1, 1, 1, 2, 9, 1, 4]
def baseStart_2445993 : Nat := 118140960795 + 2445993 * 2 ^ 59
def prefixEnd_2445993 : Nat := 4983230072969 + 3 ^ 40 * 2445993 * 2
def baseEnd_2445993 : Nat := 418656695510984591612863

theorem tailTrace_2445993 : CollatzResearch.WordTrace tailWord_2445993 prefixEnd_2445993 418656695510984591612863 := by
  unfold tailWord_2445993
  simp only [CollatzResearch.WordTrace]
  refine ⟨89212693827592578191342633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59475129218395052127561755 89212693827592578191342633)
  ·
    refine ⟨66909520370694433643506975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89212693827592578191342633 66909520370694433643506975)
    ·
      refine ⟨100364280556041650465260463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66909520370694433643506975 100364280556041650465260463)
      ·
        refine ⟨150546420834062475697890695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100364280556041650465260463 150546420834062475697890695)
        ·
          refine ⟨225819631251093713546836043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150546420834062475697890695 225819631251093713546836043)
          ·
            refine ⟨338729446876640570320254065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225819631251093713546836043 338729446876640570320254065)
            ·
              refine ⟨254047085157480427740190549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338729446876640570320254065 254047085157480427740190549)
              ·
                refine ⟨1488557139594611881290179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 254047085157480427740190549 1488557139594611881290179)
                ·
                  refine ⟨2232835709391917821935269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488557139594611881290179 2232835709391917821935269)
                  ·
                    refine ⟨418656695510984591612863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232835709391917821935269 418656695510984591612863)
                    ·
                      rfl

theorem cell23_2445993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 4].length) (baseStart_2445993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2445993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2445993 prefixEnd_2445993 := by exact prefixLift 2445993
  have htrace : WordTrace (prefixWord ++ tailWord_2445993) baseStart_2445993 baseEnd_2445993 := by
    simpa [prefixWord, tailWord_2445993, baseEnd_2445993] using wordTrace_append hprefix tailTrace_2445993
  have hstable : (prefixWord ++ tailWord_2445993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2445993).length < 2 ^ (prefixWord ++ tailWord_2445993).sum := by decide
  have hdescent : baseEnd_2445993 < baseStart_2445993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2445993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446033 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_2446033 : Nat := 118140960795 + 2446033 * 2 ^ 59
def prefixEnd_2446033 : Nat := 4983230072969 + 3 ^ 40 * 2446033 * 2
def baseEnd_2446033 : Nat := 1255990625759133618338405

theorem tailTrace_2446033 : CollatzResearch.WordTrace tailWord_2446033 prefixEnd_2446033 1255990625759133618338405 := by
  unfold tailWord_2446033
  simp only [CollatzResearch.WordTrace]
  refine ⟨89214152747447665022798753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59476101831631776681865835 89214152747447665022798753)
  ·
    refine ⟨66910614560585748767099065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89214152747447665022798753 66910614560585748767099065)
    ·
      refine ⟨50182960920439311575324299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66910614560585748767099065 50182960920439311575324299)
      ·
        refine ⟨75274441380658967362986449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50182960920439311575324299 75274441380658967362986449)
        ·
          refine ⟨56455831035494225522239837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75274441380658967362986449 56455831035494225522239837)
          ·
            refine ⟨21170936638310334570839939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56455831035494225522239837 21170936638310334570839939)
            ·
              refine ⟨31756404957465501856259909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21170936638310334570839939 31756404957465501856259909)
              ·
                refine ⟨5954325929524781598048733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31756404957465501856259909 5954325929524781598048733)
                ·
                  refine ⟨2232872223571793099268275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5954325929524781598048733 2232872223571793099268275)
                  ·
                    refine ⟨3349308335357689648902413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2232872223571793099268275 3349308335357689648902413)
                    ·
                      refine ⟨1255990625759133618338405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3349308335357689648902413 1255990625759133618338405)
                      ·
                        rfl

theorem cell23_2446033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_2446033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446033 prefixEnd_2446033 := by exact prefixLift 2446033
  have htrace : WordTrace (prefixWord ++ tailWord_2446033) baseStart_2446033 baseEnd_2446033 := by
    simpa [prefixWord, tailWord_2446033, baseEnd_2446033] using wordTrace_append hprefix tailTrace_2446033
  have hstable : (prefixWord ++ tailWord_2446033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446033).length < 2 ^ (prefixWord ++ tailWord_2446033).sum := by decide
  have hdescent : baseEnd_2446033 < baseStart_2446033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446044 : List Nat := [2, 2, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2446044 : Nat := 118140960795 + 2446044 * 2 ^ 59
def prefixEnd_2446044 : Nat := 4983230072969 + 3 ^ 40 * 2446044 * 2
def baseEnd_2446044 : Nat := 418665424682111025100285

theorem tailTrace_2446044 : CollatzResearch.WordTrace tailWord_2446044 prefixEnd_2446044 418665424682111025100285 := by
  unfold tailWord_2446044
  simp only [CollatzResearch.WordTrace]
  refine ⟨44607276975203906950724593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59476369300271875934299457 44607276975203906950724593)
  ·
    refine ⟨33455457731402930213043445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44607276975203906950724593 33455457731402930213043445)
    ·
      refine ⟨3136449162319024707472823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33455457731402930213043445 3136449162319024707472823)
      ·
        refine ⟨4704673743478537061209235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136449162319024707472823 4704673743478537061209235)
        ·
          refine ⟨7057010615217805591813853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704673743478537061209235 7057010615217805591813853)
          ·
            refine ⟨2646378980706677096930195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7057010615217805591813853 2646378980706677096930195)
            ·
              refine ⟨3969568471060015645395293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646378980706677096930195 3969568471060015645395293)
              ·
                refine ⟨1488588176647505867023235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3969568471060015645395293 1488588176647505867023235)
                ·
                  refine ⟨2232882264971258800534853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488588176647505867023235 2232882264971258800534853)
                  ·
                    refine ⟨418665424682111025100285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232882264971258800534853 418665424682111025100285)
                    ·
                      rfl

theorem cell23_2446044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2446044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446044 prefixEnd_2446044 := by exact prefixLift 2446044
  have htrace : WordTrace (prefixWord ++ tailWord_2446044) baseStart_2446044 baseEnd_2446044 := by
    simpa [prefixWord, tailWord_2446044, baseEnd_2446044] using wordTrace_append hprefix tailTrace_2446044
  have hstable : (prefixWord ++ tailWord_2446044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446044).length < 2 ^ (prefixWord ++ tailWord_2446044).sum := by decide
  have hdescent : baseEnd_2446044 < baseStart_2446044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446053 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_2446053 : Nat := 118140960795 + 2446053 * 2 ^ 59
def prefixEnd_2446053 : Nat := 4983230072969 + 3 ^ 40 * 2446053 * 2
def baseEnd_2446053 : Nat := 418666965124074513362771

theorem tailTrace_2446053 : CollatzResearch.WordTrace tailWord_2446053 prefixEnd_2446053 418666965124074513362771 := by
  unfold tailWord_2446053
  simp only [CollatzResearch.WordTrace]
  refine ⟨89214882207375208438526813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59476588138250138959017875 89214882207375208438526813)
  ·
    refine ⟨33455580827765703164447555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89214882207375208438526813 33455580827765703164447555)
    ·
      refine ⟨50183371241648554746671333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33455580827765703164447555 50183371241648554746671333)
      ·
        refine ⟨9409382107809104015000875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50183371241648554746671333 9409382107809104015000875)
        ·
          refine ⟨14114073161713656022501313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409382107809104015000875 14114073161713656022501313)
          ·
            refine ⟨10585554871285242016875985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14114073161713656022501313 10585554871285242016875985)
            ·
              refine ⟨7939166153463931512656989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10585554871285242016875985 7939166153463931512656989)
              ·
                refine ⟨2977187307548974317246371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7939166153463931512656989 2977187307548974317246371)
                ·
                  refine ⟨4465780961323461475869557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977187307548974317246371 4465780961323461475869557)
                  ·
                    refine ⟨418666965124074513362771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4465780961323461475869557 418666965124074513362771)
                    ·
                      rfl

theorem cell23_2446053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_2446053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446053 prefixEnd_2446053 := by exact prefixLift 2446053
  have htrace : WordTrace (prefixWord ++ tailWord_2446053) baseStart_2446053 baseEnd_2446053 := by
    simpa [prefixWord, tailWord_2446053, baseEnd_2446053] using wordTrace_append hprefix tailTrace_2446053
  have hstable : (prefixWord ++ tailWord_2446053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446053).length < 2 ^ (prefixWord ++ tailWord_2446053).sum := by decide
  have hdescent : baseEnd_2446053 < baseStart_2446053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446090 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_2446090 : Nat := 118140960795 + 2446090 * 2 ^ 59
def prefixEnd_2446090 : Nat := 4983230072969 + 3 ^ 40 * 2446090 * 2
def baseEnd_2446090 : Nat := 1256019894156439895325643

theorem tailTrace_2446090 : CollatzResearch.WordTrace tailWord_2446090 prefixEnd_2446090 1256019894156439895325643 := by
  unfold tailWord_2446090
  simp only [CollatzResearch.WordTrace]
  refine ⟨22304057927060290939405931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59477487805494109171749149 22304057927060290939405931)
  ·
    refine ⟨33456086890590436409108897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22304057927060290939405931 33456086890590436409108897)
    ·
      refine ⟨25092065167942827306831673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33456086890590436409108897 25092065167942827306831673)
      ·
        refine ⟨18819048875957120480123755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25092065167942827306831673 18819048875957120480123755)
        ·
          refine ⟨28228573313935680720185633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18819048875957120480123755 28228573313935680720185633)
          ·
            refine ⟨21171429985451760540139225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28228573313935680720185633 21171429985451760540139225)
            ·
              refine ⟨15878572489088820405104419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21171429985451760540139225 15878572489088820405104419)
              ·
                refine ⟨23817858733633230607656629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15878572489088820405104419 23817858733633230607656629)
                ·
                  refine ⟨2232924256278115369467809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23817858733633230607656629 2232924256278115369467809)
                  ·
                    refine ⟨1674693192208586527100857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2232924256278115369467809 1674693192208586527100857)
                    ·
                      refine ⟨1256019894156439895325643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674693192208586527100857 1256019894156439895325643)
                      ·
                        rfl

theorem cell23_2446090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_2446090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446090 prefixEnd_2446090 := by exact prefixLift 2446090
  have htrace : WordTrace (prefixWord ++ tailWord_2446090) baseStart_2446090 baseEnd_2446090 := by
    simpa [prefixWord, tailWord_2446090, baseEnd_2446090] using wordTrace_append hprefix tailTrace_2446090
  have hstable : (prefixWord ++ tailWord_2446090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446090).length < 2 ^ (prefixWord ++ tailWord_2446090).sum := by decide
  have hdescent : baseEnd_2446090 < baseStart_2446090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446167 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 1, 3, 2]
def baseStart_2446167 : Nat := 118140960795 + 2446167 * 2 ^ 59
def prefixEnd_2446167 : Nat := 4983230072969 + 3 ^ 40 * 2446167 * 2
def baseEnd_2446167 : Nat := 1256059432166836094062789

theorem tailTrace_2446167 : CollatzResearch.WordTrace tailWord_2446167 prefixEnd_2446167 1256059432166836094062789 := by
  unfold tailWord_2446167
  simp only [CollatzResearch.WordTrace]
  refine ⟨89219040128962205908176755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59479360085974803938784503 89219040128962205908176755)
  ·
    refine ⟨133828560193443308862265133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89219040128962205908176755 133828560193443308862265133)
    ·
      refine ⟨50185710072541240823349425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133828560193443308862265133 50185710072541240823349425)
      ·
        refine ⟨37639282554405930617512069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50185710072541240823349425 37639282554405930617512069)
        ·
          refine ⟨7057365478951111990783513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37639282554405930617512069 7057365478951111990783513)
          ·
            refine ⟨5293024109213333993087635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7057365478951111990783513 5293024109213333993087635)
            ·
              refine ⟨7939536163820000989631453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293024109213333993087635 7939536163820000989631453)
              ·
                refine ⟨2977326061432500371111795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7939536163820000989631453 2977326061432500371111795)
                ·
                  refine ⟨4465989092148750556667693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977326061432500371111795 4465989092148750556667693)
                  ·
                    refine ⟨1674745909555781458750385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4465989092148750556667693 1674745909555781458750385)
                    ·
                      refine ⟨1256059432166836094062789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674745909555781458750385 1256059432166836094062789)
                      ·
                        rfl

theorem cell23_2446167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_2446167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446167 prefixEnd_2446167 := by exact prefixLift 2446167
  have htrace : WordTrace (prefixWord ++ tailWord_2446167) baseStart_2446167 baseEnd_2446167 := by
    simpa [prefixWord, tailWord_2446167, baseEnd_2446167] using wordTrace_append hprefix tailTrace_2446167
  have hstable : (prefixWord ++ tailWord_2446167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446167).length < 2 ^ (prefixWord ++ tailWord_2446167).sum := by decide
  have hdescent : baseEnd_2446167 < baseStart_2446167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446193 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_2446193 : Nat := 118140960795 + 2446193 * 2 ^ 59
def prefixEnd_2446193 : Nat := 4983230072969 + 3 ^ 40 * 2446193 * 2
def baseEnd_2446193 : Nat := 1256072782663852992337669

theorem tailTrace_2446193 : CollatzResearch.WordTrace tailWord_2446193 prefixEnd_2446193 1256072782663852992337669 := by
  unfold tailWord_2446193
  simp only [CollatzResearch.WordTrace]
  refine ⟨89219988426868012348623233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59479992284578674899082155 89219988426868012348623233)
  ·
    refine ⟨66914991320151009261467425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89219988426868012348623233 66914991320151009261467425)
    ·
      refine ⟨50186243490113256946100569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66914991320151009261467425 50186243490113256946100569)
      ·
        refine ⟨37639682617584942709575427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50186243490113256946100569 37639682617584942709575427)
        ·
          refine ⟨56459523926377414064363141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37639682617584942709575427 56459523926377414064363141)
          ·
            refine ⟨10586160736195765137068089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56459523926377414064363141 10586160736195765137068089)
            ·
              refine ⟨7939620552146823852801067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10586160736195765137068089 7939620552146823852801067)
              ·
                refine ⟨11909430828220235779201601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7939620552146823852801067 11909430828220235779201601)
                ·
                  refine ⟨8932073121165176834401201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11909430828220235779201601 8932073121165176834401201)
                  ·
                    refine ⟨6699054840873882625800901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8932073121165176834401201 6699054840873882625800901)
                    ·
                      refine ⟨1256072782663852992337669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6699054840873882625800901 1256072782663852992337669)
                      ·
                        rfl

theorem cell23_2446193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_2446193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446193 prefixEnd_2446193 := by exact prefixLift 2446193
  have htrace : WordTrace (prefixWord ++ tailWord_2446193) baseStart_2446193 baseEnd_2446193 := by
    simpa [prefixWord, tailWord_2446193, baseEnd_2446193] using wordTrace_append hprefix tailTrace_2446193
  have hstable : (prefixWord ++ tailWord_2446193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446193).length < 2 ^ (prefixWord ++ tailWord_2446193).sum := by decide
  have hdescent : baseEnd_2446193 < baseStart_2446193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446197 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2446197 : Nat := 118140960795 + 2446197 * 2 ^ 59
def prefixEnd_2446197 : Nat := 4983230072969 + 3 ^ 40 * 2446197 * 2
def baseEnd_2446197 : Nat := 1256074836586470976687651

theorem tailTrace_2446197 : CollatzResearch.WordTrace tailWord_2446197 prefixEnd_2446197 1256074836586470976687651 := by
  unfold tailWord_2446197
  simp only [CollatzResearch.WordTrace]
  refine ⟨89220134318853521031768845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59480089545902347354512563 89220134318853521031768845)
  ·
    refine ⟨33457550369570070386913317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89220134318853521031768845 33457550369570070386913317)
    ·
      refine ⟨6273290694294388197546247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33457550369570070386913317 6273290694294388197546247)
      ·
        refine ⟨9409936041441582296319371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6273290694294388197546247 9409936041441582296319371)
        ·
          refine ⟨14114904062162373444479057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409936041441582296319371 14114904062162373444479057)
          ·
            refine ⟨10586178046621780083359293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14114904062162373444479057 10586178046621780083359293)
            ·
              refine ⟨3969816767483167531259735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10586178046621780083359293 3969816767483167531259735)
              ·
                refine ⟨5954725151224751296889603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969816767483167531259735 5954725151224751296889603)
                ·
                  refine ⟨8932087726837126945334405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5954725151224751296889603 8932087726837126945334405)
                  ·
                    refine ⟨1674766448781961302250201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8932087726837126945334405 1674766448781961302250201)
                    ·
                      refine ⟨1256074836586470976687651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674766448781961302250201 1256074836586470976687651)
                      ·
                        rfl

theorem cell23_2446197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2446197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446197 prefixEnd_2446197 := by exact prefixLift 2446197
  have htrace : WordTrace (prefixWord ++ tailWord_2446197) baseStart_2446197 baseEnd_2446197 := by
    simpa [prefixWord, tailWord_2446197, baseEnd_2446197] using wordTrace_append hprefix tailTrace_2446197
  have hstable : (prefixWord ++ tailWord_2446197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446197).length < 2 ^ (prefixWord ++ tailWord_2446197).sum := by decide
  have hdescent : baseEnd_2446197 < baseStart_2446197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446220 : List Nat := [2, 2, 1, 2, 1, 2, 5, 3, 5]
def baseStart_2446220 : Nat := 118140960795 + 2446220 * 2 ^ 59
def prefixEnd_2446220 : Nat := 4983230072969 + 3 ^ 40 * 2446220 * 2
def baseEnd_2446220 : Nat := 139565182960169376300005

theorem tailTrace_2446220 : CollatzResearch.WordTrace tailWord_2446220 prefixEnd_2446220 139565182960169376300005 := by
  unfold tailWord_2446220
  simp only [CollatzResearch.WordTrace]
  refine ⟨44610486598885097979928057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59480648798513463973237409 44610486598885097979928057)
  ·
    refine ⟨33457864949163823484946043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44610486598885097979928057 33457864949163823484946043)
    ·
      refine ⟨50186797423745735227419065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33457864949163823484946043 50186797423745735227419065)
      ·
        refine ⟨37640098067809301420564299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50186797423745735227419065 37640098067809301420564299)
        ·
          refine ⟨56460147101713952130846449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37640098067809301420564299 56460147101713952130846449)
          ·
            refine ⟨42345110326285464098134837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56460147101713952130846449 42345110326285464098134837)
            ·
              refine ⟨3969854093089262259200141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42345110326285464098134837 3969854093089262259200141)
              ·
                refine ⟨1488695284908473347200053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3969854093089262259200141 1488695284908473347200053)
                ·
                  refine ⟨139565182960169376300005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1488695284908473347200053 139565182960169376300005)
                  ·
                    rfl

theorem cell23_2446220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_2446220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446220 prefixEnd_2446220 := by exact prefixLift 2446220
  have htrace : WordTrace (prefixWord ++ tailWord_2446220) baseStart_2446220 baseEnd_2446220 := by
    simpa [prefixWord, tailWord_2446220, baseEnd_2446220] using wordTrace_append hprefix tailTrace_2446220
  have hstable : (prefixWord ++ tailWord_2446220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446220).length < 2 ^ (prefixWord ++ tailWord_2446220).sum := by decide
  have hdescent : baseEnd_2446220 < baseStart_2446220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446237 : List Nat := [1, 4, 2, 1, 2, 1, 5, 2, 5]
def baseStart_2446237 : Nat := 118140960795 + 2446237 * 2 ^ 59
def prefixEnd_2446237 : Nat := 4983230072969 + 3 ^ 40 * 2446237 * 2
def baseEnd_2446237 : Nat := 139566152868072313354163

theorem tailTrace_2446237 : CollatzResearch.WordTrace tailWord_2446237 prefixEnd_2446237 139566152868072313354163 := by
  unfold tailWord_2446237
  simp only [CollatzResearch.WordTrace]
  refine ⟨89221593238708607863224965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59481062159139071908816643 89221593238708607863224965)
  ·
    refine ⟨16729048732257863974354681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89221593238708607863224965 16729048732257863974354681)
    ·
      refine ⟨12546786549193397980766011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16729048732257863974354681 12546786549193397980766011)
      ·
        refine ⟨18820179823790096971149017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12546786549193397980766011 18820179823790096971149017)
        ·
          refine ⟨14115134867842572728361763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18820179823790096971149017 14115134867842572728361763)
          ·
            refine ⟨21172702301763859092542645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14115134867842572728361763 21172702301763859092542645)
            ·
              refine ⟨1984940840790361789925873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21172702301763859092542645 1984940840790361789925873)
              ·
                refine ⟨1488705630592771342444405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984940840790361789925873 1488705630592771342444405)
                ·
                  refine ⟨139566152868072313354163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1488705630592771342444405 139566152868072313354163)
                  ·
                    rfl

theorem cell23_2446237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_2446237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446237 prefixEnd_2446237 := by exact prefixLift 2446237
  have htrace : WordTrace (prefixWord ++ tailWord_2446237) baseStart_2446237 baseEnd_2446237 := by
    simpa [prefixWord, tailWord_2446237, baseEnd_2446237] using wordTrace_append hprefix tailTrace_2446237
  have hstable : (prefixWord ++ tailWord_2446237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446237).length < 2 ^ (prefixWord ++ tailWord_2446237).sum := by decide
  have hdescent : baseEnd_2446237 < baseStart_2446237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446333 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2446333 : Nat := 118140960795 + 2446333 * 2 ^ 59
def prefixEnd_2446333 : Nat := 4983230072969 + 3 ^ 40 * 2446333 * 2
def baseEnd_2446333 : Nat := 1256144669955482444587025

theorem tailTrace_2446333 : CollatzResearch.WordTrace tailWord_2446333 prefixEnd_2446333 1256144669955482444587025 := by
  unfold tailWord_2446333
  simp only [CollatzResearch.WordTrace]
  refine ⟨89225094646360816258719653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59483396430907210839146435 89225094646360816258719653)
  ·
    refine ⟨16729705246192653048509935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89225094646360816258719653 16729705246192653048509935)
    ·
      refine ⟨25094557869288979572764903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16729705246192653048509935 25094557869288979572764903)
      ·
        refine ⟨37641836803933469359147355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25094557869288979572764903 37641836803933469359147355)
        ·
          refine ⟨56462755205900204038721033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37641836803933469359147355 56462755205900204038721033)
          ·
            refine ⟨42347066404425153029040775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56462755205900204038721033 42347066404425153029040775)
            ·
              refine ⟨63520599606637729543561163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42347066404425153029040775 63520599606637729543561163)
              ·
                refine ⟨95280899409956594315341745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63520599606637729543561163 95280899409956594315341745)
                ·
                  refine ⟨71460674557467445736506309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95280899409956594315341745 71460674557467445736506309)
                  ·
                    refine ⟨13398876479525146075594933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71460674557467445736506309 13398876479525146075594933)
                    ·
                      refine ⟨1256144669955482444587025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13398876479525146075594933 1256144669955482444587025)
                      ·
                        rfl

theorem cell23_2446333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2446333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446333 prefixEnd_2446333 := by exact prefixLift 2446333
  have htrace : WordTrace (prefixWord ++ tailWord_2446333) baseStart_2446333 baseEnd_2446333 := by
    simpa [prefixWord, tailWord_2446333, baseEnd_2446333] using wordTrace_append hprefix tailTrace_2446333
  have hstable : (prefixWord ++ tailWord_2446333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446333).length < 2 ^ (prefixWord ++ tailWord_2446333).sum := by decide
  have hdescent : baseEnd_2446333 < baseStart_2446333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446353 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 3, 6]
def baseStart_2446353 : Nat := 118140960795 + 2446353 * 2 ^ 59
def prefixEnd_2446353 : Nat := 4983230072969 + 3 ^ 40 * 2446353 * 2
def baseEnd_2446353 : Nat := 418718313189524122112311

theorem tailTrace_2446353 : CollatzResearch.WordTrace tailWord_2446353 prefixEnd_2446353 418718313189524122112311 := by
  unfold tailWord_2446353
  simp only [CollatzResearch.WordTrace]
  refine ⟨89225824106288359674447713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59483882737525573116298475 89225824106288359674447713)
  ·
    refine ⟨66919368079716269755835785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89225824106288359674447713 66919368079716269755835785)
    ·
      refine ⟨50189526059787202316876839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66919368079716269755835785 50189526059787202316876839)
      ·
        refine ⟨75284289089680803475315259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50189526059787202316876839 75284289089680803475315259)
        ·
          refine ⟨112926433634521205212972889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75284289089680803475315259 112926433634521205212972889)
          ·
            refine ⟨84694825225890903909729667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112926433634521205212972889 84694825225890903909729667)
            ·
              refine ⟨127042237838836355864594501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84694825225890903909729667 127042237838836355864594501)
              ·
                refine ⟨23820419594781816724611469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127042237838836355864594501 23820419594781816724611469)
                ·
                  refine ⟨8932657348043181271729301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23820419594781816724611469 8932657348043181271729301)
                  ·
                    refine ⟨418718313189524122112311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8932657348043181271729301 418718313189524122112311)
                    ·
                      rfl

theorem cell23_2446353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_2446353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446353 prefixEnd_2446353 := by exact prefixLift 2446353
  have htrace : WordTrace (prefixWord ++ tailWord_2446353) baseStart_2446353 baseEnd_2446353 := by
    simpa [prefixWord, tailWord_2446353, baseEnd_2446353] using wordTrace_append hprefix tailTrace_2446353
  have hstable : (prefixWord ++ tailWord_2446353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446353).length < 2 ^ (prefixWord ++ tailWord_2446353).sum := by decide
  have hdescent : baseEnd_2446353 < baseStart_2446353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446388 : List Nat := [2, 5, 1, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2446388 : Nat := 118140960795 + 2446388 * 2 ^ 59
def prefixEnd_2446388 : Nat := 4983230072969 + 3 ^ 40 * 2446388 * 2
def baseEnd_2446388 : Nat := 1256172911391479729399273

theorem tailTrace_2446388 : CollatzResearch.WordTrace tailWord_2446388 prefixEnd_2446388 1256172911391479729399273 := by
  unfold tailWord_2446388
  simp only [CollatzResearch.WordTrace]
  refine ⟨44613550330580780325985909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59484733774107707101314545 44613550330580780325985909)
  ·
    refine ⟨4182520343491948155561179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44613550330580780325985909 4182520343491948155561179)
    ·
      refine ⟨6273780515237922233341769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182520343491948155561179 6273780515237922233341769)
      ·
        refine ⟨4705335386428441675006327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6273780515237922233341769 4705335386428441675006327)
        ·
          refine ⟨7058003079642662512509491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705335386428441675006327 7058003079642662512509491)
          ·
            refine ⟨10587004619463993768764237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058003079642662512509491 10587004619463993768764237)
            ·
              refine ⟨3970126732298997663286589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10587004619463993768764237 3970126732298997663286589)
              ·
                refine ⟨1488797524612124123732471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3970126732298997663286589 1488797524612124123732471)
                ·
                  refine ⟨2233196286918186185598707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488797524612124123732471 2233196286918186185598707)
                  ·
                    refine ⟨3349794430377279278398061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2233196286918186185598707 3349794430377279278398061)
                    ·
                      refine ⟨1256172911391479729399273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3349794430377279278398061 1256172911391479729399273)
                      ·
                        rfl

theorem cell23_2446388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2446388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446388 prefixEnd_2446388 := by exact prefixLift 2446388
  have htrace : WordTrace (prefixWord ++ tailWord_2446388) baseStart_2446388 baseEnd_2446388 := by
    simpa [prefixWord, tailWord_2446388, baseEnd_2446388] using wordTrace_append hprefix tailTrace_2446388
  have hstable : (prefixWord ++ tailWord_2446388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446388).length < 2 ^ (prefixWord ++ tailWord_2446388).sum := by decide
  have hdescent : baseEnd_2446388 < baseStart_2446388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446397 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2446397 : Nat := 118140960795 + 2446397 * 2 ^ 59
def prefixEnd_2446397 : Nat := 4983230072969 + 3 ^ 40 * 2446397 * 2
def baseEnd_2446397 : Nat := 1256177532717370194186731

theorem tailTrace_2446397 : CollatzResearch.WordTrace tailWord_2446397 prefixEnd_2446397 1256177532717370194186731 := by
  unfold tailWord_2446397
  simp only [CollatzResearch.WordTrace]
  refine ⟨89227428918128955189049445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59484952612085970126032963 89227428918128955189049445)
  ·
    refine ⟨16730142922149179097946771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89227428918128955189049445 16730142922149179097946771)
    ·
      refine ⟨25095214383223768646920157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16730142922149179097946771 25095214383223768646920157)
      ·
        refine ⟨9410705393708913242595059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25095214383223768646920157 9410705393708913242595059)
        ·
          refine ⟨14116058090563369863892589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9410705393708913242595059 14116058090563369863892589)
          ·
            refine ⟨5293521783961263698959721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14116058090563369863892589 5293521783961263698959721)
            ·
              refine ⟨3970141337970947774219791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5293521783961263698959721 3970141337970947774219791)
              ·
                refine ⟨5955212006956421661329687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970141337970947774219791 5955212006956421661329687)
                ·
                  refine ⟨8932818010434632491994531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5955212006956421661329687 8932818010434632491994531)
                  ·
                    refine ⟨13399227015651948737991797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8932818010434632491994531 13399227015651948737991797)
                    ·
                      refine ⟨1256177532717370194186731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13399227015651948737991797 1256177532717370194186731)
                      ·
                        rfl

theorem cell23_2446397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2446397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446397 prefixEnd_2446397 := by exact prefixLift 2446397
  have htrace : WordTrace (prefixWord ++ tailWord_2446397) baseStart_2446397 baseEnd_2446397 := by
    simpa [prefixWord, tailWord_2446397, baseEnd_2446397] using wordTrace_append hprefix tailTrace_2446397
  have hstable : (prefixWord ++ tailWord_2446397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446397).length < 2 ^ (prefixWord ++ tailWord_2446397).sum := by decide
  have hdescent : baseEnd_2446397 < baseStart_2446397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446460 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_2446460 : Nat := 118140960795 + 2446460 * 2 ^ 59
def prefixEnd_2446460 : Nat := 4983230072969 + 3 ^ 40 * 2446460 * 2
def baseEnd_2446460 : Nat := 418736627332867815899647

theorem tailTrace_2446460 : CollatzResearch.WordTrace tailWord_2446460 prefixEnd_2446460 418736627332867815899647 := by
  unfold tailWord_2446460
  simp only [CollatzResearch.WordTrace]
  refine ⟨44614863358450358474296417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59486484477933811299061889 44614863358450358474296417)
  ·
    refine ⟨33461147518837768855722313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44614863358450358474296417 33461147518837768855722313)
    ·
      refine ⟨25095860639128326641791735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33461147518837768855722313 25095860639128326641791735)
      ·
        refine ⟨37643790958692489962687603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25095860639128326641791735 37643790958692489962687603)
        ·
          refine ⟨56465686438038734944031405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37643790958692489962687603 56465686438038734944031405)
          ·
            refine ⟨21174632414264525604011777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56465686438038734944031405 21174632414264525604011777)
            ·
              refine ⟨15880974310698394203008833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21174632414264525604011777 15880974310698394203008833)
              ·
                refine ⟨11910730733023795652256625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15880974310698394203008833 11910730733023795652256625)
                ·
                  refine ⟨8933048049767846739192469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11910730733023795652256625 8933048049767846739192469)
                  ·
                    refine ⟨418736627332867815899647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8933048049767846739192469 418736627332867815899647)
                    ·
                      rfl

theorem cell23_2446460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_2446460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446460 prefixEnd_2446460 := by exact prefixLift 2446460
  have htrace : WordTrace (prefixWord ++ tailWord_2446460) baseStart_2446460 baseEnd_2446460 := by
    simpa [prefixWord, tailWord_2446460, baseEnd_2446460] using wordTrace_append hprefix tailTrace_2446460
  have hstable : (prefixWord ++ tailWord_2446460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446460).length < 2 ^ (prefixWord ++ tailWord_2446460).sum := by decide
  have hdescent : baseEnd_2446460 < baseStart_2446460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446467 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 3, 4, 2]
def baseStart_2446467 : Nat := 118140960795 + 2446467 * 2 ^ 59
def prefixEnd_2446467 : Nat := 4983230072969 + 3 ^ 40 * 2446467 * 2
def baseEnd_2446467 : Nat := 1256213476363184920311409

theorem tailTrace_2446467 : CollatzResearch.WordTrace tailWord_2446467 prefixEnd_2446467 1256213476363184920311409 := by
  unfold tailWord_2446467
  simp only [CollatzResearch.WordTrace]
  refine ⟨89229982027875357144097655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59486654685250238096065103 89229982027875357144097655)
  ·
    refine ⟨133844973041813035716146483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89229982027875357144097655 133844973041813035716146483)
    ·
      refine ⟨200767459562719553574219725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133844973041813035716146483 200767459562719553574219725)
      ·
        refine ⟨75287797336019832590332397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200767459562719553574219725 75287797336019832590332397)
        ·
          refine ⟨28232924001007437221374649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75287797336019832590332397 28232924001007437221374649)
          ·
            refine ⟨21174693000755577916030987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28232924001007437221374649 21174693000755577916030987)
            ·
              refine ⟨31762039501133366874046481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21174693000755577916030987 31762039501133366874046481)
              ·
                refine ⟨23821529625850025155534861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31762039501133366874046481 23821529625850025155534861)
                ·
                  refine ⟨8933073609693759433325573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23821529625850025155534861 8933073609693759433325573)
                  ·
                    refine ⟨1674951301817579893748545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8933073609693759433325573 1674951301817579893748545)
                    ·
                      refine ⟨1256213476363184920311409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674951301817579893748545 1256213476363184920311409)
                      ·
                        rfl

theorem cell23_2446467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_2446467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446467 prefixEnd_2446467 := by exact prefixLift 2446467
  have htrace : WordTrace (prefixWord ++ tailWord_2446467) baseStart_2446467 baseEnd_2446467 := by
    simpa [prefixWord, tailWord_2446467, baseEnd_2446467] using wordTrace_append hprefix tailTrace_2446467
  have hstable : (prefixWord ++ tailWord_2446467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446467).length < 2 ^ (prefixWord ++ tailWord_2446467).sum := by decide
  have hdescent : baseEnd_2446467 < baseStart_2446467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446524 : List Nat := [2, 2, 2, 3, 2, 1, 2, 4, 5]
def baseStart_2446524 : Nat := 118140960795 + 2446524 * 2 ^ 59
def prefixEnd_2446524 : Nat := 4983230072969 + 3 ^ 40 * 2446524 * 2
def baseEnd_2446524 : Nat := 139582527195610133033183

theorem tailTrace_2446524 : CollatzResearch.WordTrace tailWord_2446524 prefixEnd_2446524 139582527195610133033183 := by
  unfold tailWord_2446524
  simp only [CollatzResearch.WordTrace]
  refine ⟨44616030494334427939461313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59488040659112570585948417 44616030494334427939461313)
  ·
    refine ⟨33462022870750820954595985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44616030494334427939461313 33462022870750820954595985)
    ·
      refine ⟨25096517153063115715946989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33462022870750820954595985 25096517153063115715946989)
      ·
        refine ⟨9411193932398668393480121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25096517153063115715946989 9411193932398668393480121)
        ·
          refine ⟨7058395449299001295110091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9411193932398668393480121 7058395449299001295110091)
          ·
            refine ⟨10587593173948501942665137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058395449299001295110091 10587593173948501942665137)
            ·
              refine ⟨7940694880461376456998853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10587593173948501942665137 7940694880461376456998853)
              ·
                refine ⟨1488880290086508085687285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7940694880461376456998853 1488880290086508085687285)
                ·
                  refine ⟨139582527195610133033183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1488880290086508085687285 139582527195610133033183)
                  ·
                    rfl

theorem cell23_2446524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_2446524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446524 prefixEnd_2446524 := by exact prefixLift 2446524
  have htrace : WordTrace (prefixWord ++ tailWord_2446524) baseStart_2446524 baseEnd_2446524 := by
    simpa [prefixWord, tailWord_2446524, baseEnd_2446524] using wordTrace_append hprefix tailTrace_2446524
  have hstable : (prefixWord ++ tailWord_2446524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446524).length < 2 ^ (prefixWord ++ tailWord_2446524).sum := by decide
  have hdescent : baseEnd_2446524 < baseStart_2446524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446527 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 7, 2]
def baseStart_2446527 : Nat := 118140960795 + 2446527 * 2 ^ 59
def prefixEnd_2446527 : Nat := 4983230072969 + 3 ^ 40 * 2446527 * 2
def baseEnd_2446527 : Nat := 1256244285202454685561133

theorem tailTrace_2446527 : CollatzResearch.WordTrace tailWord_2446527 prefixEnd_2446527 1256244285202454685561133 := by
  unfold tailWord_2446527
  simp only [CollatzResearch.WordTrace]
  refine ⟨89232170407657987391281835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59488113605105324927521223 89232170407657987391281835)
  ·
    refine ⟨133848255611486981086922753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89232170407657987391281835 133848255611486981086922753)
    ·
      refine ⟨100386191708615235815192065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133848255611486981086922753 100386191708615235815192065)
      ·
        refine ⟨75289643781461426861394049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100386191708615235815192065 75289643781461426861394049)
        ·
          refine ⟨56467232836096070146045537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75289643781461426861394049 56467232836096070146045537)
          ·
            refine ⟨42350424627072052609534153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56467232836096070146045537 42350424627072052609534153)
            ·
              refine ⟨31762818470304039457150615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42350424627072052609534153 31762818470304039457150615)
              ·
                refine ⟨47644227705456059185725923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31762818470304039457150615 47644227705456059185725923)
                ·
                  refine ⟨71466341558184088778588885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47644227705456059185725923 71466341558184088778588885)
                  ·
                    refine ⟨1674992380269939580748177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 71466341558184088778588885 1674992380269939580748177)
                    ·
                      refine ⟨1256244285202454685561133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1674992380269939580748177 1256244285202454685561133)
                      ·
                        rfl

theorem cell23_2446527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_2446527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446527 prefixEnd_2446527 := by exact prefixLift 2446527
  have htrace : WordTrace (prefixWord ++ tailWord_2446527) baseStart_2446527 baseEnd_2446527 := by
    simpa [prefixWord, tailWord_2446527, baseEnd_2446527] using wordTrace_append hprefix tailTrace_2446527
  have hstable : (prefixWord ++ tailWord_2446527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446527).length < 2 ^ (prefixWord ++ tailWord_2446527).sum := by decide
  have hdescent : baseEnd_2446527 < baseStart_2446527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446574 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_2446574 : Nat := 118140960795 + 2446574 * 2 ^ 59
def prefixEnd_2446574 : Nat := 4983230072969 + 3 ^ 40 * 2446574 * 2
def baseEnd_2446574 : Nat := 1256268418793216001673417

theorem tailTrace_2446574 : CollatzResearch.WordTrace tailWord_2446574 prefixEnd_2446574 1256268418793216001673417 := by
  unfold tailWord_2446574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11154235579810964302280347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59489256425658476278828517 11154235579810964302280347)
  ·
    refine ⟨16731353369716446453420521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11154235579810964302280347 16731353369716446453420521)
    ·
      refine ⟨12548515027287334840065391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16731353369716446453420521 12548515027287334840065391)
      ·
        refine ⟨18822772540931002260098087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12548515027287334840065391 18822772540931002260098087)
        ·
          refine ⟨28234158811396503390147131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18822772540931002260098087 28234158811396503390147131)
          ·
            refine ⟨42351238217094755085220697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28234158811396503390147131 42351238217094755085220697)
            ·
              refine ⟨31763428662821066313915523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42351238217094755085220697 31763428662821066313915523)
              ·
                refine ⟨47645142994231599470873285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31763428662821066313915523 47645142994231599470873285)
                ·
                  refine ⟨8933464311418424900788741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47645142994231599470873285 8933464311418424900788741)
                  ·
                    refine ⟨1675024558390954668897889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8933464311418424900788741 1675024558390954668897889)
                    ·
                      refine ⟨1256268418793216001673417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675024558390954668897889 1256268418793216001673417)
                      ·
                        rfl

theorem cell23_2446574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_2446574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446574 prefixEnd_2446574 := by exact prefixLift 2446574
  have htrace : WordTrace (prefixWord ++ tailWord_2446574) baseStart_2446574 baseEnd_2446574 := by
    simpa [prefixWord, tailWord_2446574, baseEnd_2446574] using wordTrace_append hprefix tailTrace_2446574
  have hstable : (prefixWord ++ tailWord_2446574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446574).length < 2 ^ (prefixWord ++ tailWord_2446574).sum := by decide
  have hdescent : baseEnd_2446574 < baseStart_2446574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446597 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 6]
def baseStart_2446597 : Nat := 118140960795 + 2446597 * 2 ^ 59
def prefixEnd_2446597 : Nat := 4983230072969 + 3 ^ 40 * 2446597 * 2
def baseEnd_2446597 : Nat := 139586692094252156853979

theorem tailTrace_2446597 : CollatzResearch.WordTrace tailWord_2446597 prefixEnd_2446597 139586692094252156853979 := by
  unfold tailWord_2446597
  simp only [CollatzResearch.WordTrace]
  refine ⟨89234723517404389346330045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59489815678269592897553363 89234723517404389346330045)
  ·
    refine ⟨33463021319026646004873767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89234723517404389346330045 33463021319026646004873767)
    ·
      refine ⟨50194531978539969007310651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33463021319026646004873767 50194531978539969007310651)
      ·
        refine ⟨75291797967809953510965977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50194531978539969007310651 75291797967809953510965977)
        ·
          refine ⟨56468848475857465133224483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75291797967809953510965977 56468848475857465133224483)
          ·
            refine ⟨84703272713786197699836725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56468848475857465133224483 84703272713786197699836725)
            ·
              refine ⟨7940931816917456034359693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84703272713786197699836725 7940931816917456034359693)
              ·
                refine ⟨2977849431344046012884885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7940931816917456034359693 2977849431344046012884885)
                ·
                  refine ⟨139586692094252156853979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2977849431344046012884885 139586692094252156853979)
                  ·
                    rfl

theorem cell23_2446597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_2446597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446597 prefixEnd_2446597 := by exact prefixLift 2446597
  have htrace : WordTrace (prefixWord ++ tailWord_2446597) baseStart_2446597 baseEnd_2446597 := by
    simpa [prefixWord, tailWord_2446597, baseEnd_2446597] using wordTrace_append hprefix tailTrace_2446597
  have hstable : (prefixWord ++ tailWord_2446597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446597).length < 2 ^ (prefixWord ++ tailWord_2446597).sum := by decide
  have hdescent : baseEnd_2446597 < baseStart_2446597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446644 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_2446644 : Nat := 118140960795 + 2446644 * 2 ^ 59
def prefixEnd_2446644 : Nat := 4983230072969 + 3 ^ 40 * 2446644 * 2
def baseEnd_2446644 : Nat := 418768120813010242599365

theorem tailTrace_2446644 : CollatzResearch.WordTrace tailWord_2446644 prefixEnd_2446644 418768120813010242599365 := by
  unfold tailWord_2446644
  simp only [CollatzResearch.WordTrace]
  refine ⟨44618218874117058186645493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59490958498822744248860657 44618218874117058186645493)
  ·
    refine ⟨4182958019448474204998015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44618218874117058186645493 4182958019448474204998015)
    ·
      refine ⟨6274437029172711307497023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182958019448474204998015 6274437029172711307497023)
      ·
        refine ⟨9411655543759066961245535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6274437029172711307497023 9411655543759066961245535)
        ·
          refine ⟨14117483315638600441868303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9411655543759066961245535 14117483315638600441868303)
          ·
            refine ⟨21176224973457900662802455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14117483315638600441868303 21176224973457900662802455)
            ·
              refine ⟨31764337460186850994203683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21176224973457900662802455 31764337460186850994203683)
              ·
                refine ⟨47646506190280276491305525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31764337460186850994203683 47646506190280276491305525)
                ·
                  refine ⟨4466859955338775921059893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47646506190280276491305525 4466859955338775921059893)
                  ·
                    refine ⟨418768120813010242599365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4466859955338775921059893 418768120813010242599365)
                    ·
                      rfl

theorem cell23_2446644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_2446644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446644 prefixEnd_2446644 := by exact prefixLift 2446644
  have htrace : WordTrace (prefixWord ++ tailWord_2446644) baseStart_2446644 baseEnd_2446644 := by
    simpa [prefixWord, tailWord_2446644, baseEnd_2446644] using wordTrace_append hprefix tailTrace_2446644
  have hstable : (prefixWord ++ tailWord_2446644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446644).length < 2 ^ (prefixWord ++ tailWord_2446644).sum := by decide
  have hdescent : baseEnd_2446644 < baseStart_2446644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446662 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2446662 : Nat := 118140960795 + 2446662 * 2 ^ 59
def prefixEnd_2446662 : Nat := 4983230072969 + 3 ^ 40 * 2446662 * 2
def baseEnd_2446662 : Nat := 1256313605090811657373013

theorem tailTrace_2446662 : CollatzResearch.WordTrace tailWord_2446662 prefixEnd_2446662 1256313605090811657373013 := by
  unfold tailWord_2446662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788659195692778295232695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59491396174779270298297493 2788659195692778295232695)
  ·
    refine ⟨4182988793539167442849043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788659195692778295232695 4182988793539167442849043)
    ·
      refine ⟨6274483190308751164273565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182988793539167442849043 6274483190308751164273565)
      ·
        refine ⟨2352931196365781686602587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6274483190308751164273565 2352931196365781686602587)
        ·
          refine ⟨3529396794548672529903881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352931196365781686602587 3529396794548672529903881)
          ·
            refine ⟨2647047595911504397427911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529396794548672529903881 2647047595911504397427911)
            ·
              refine ⟨3970571393867256596141867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647047595911504397427911 3970571393867256596141867)
              ·
                refine ⟨5955857090800884894212801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970571393867256596141867 5955857090800884894212801)
                ·
                  refine ⟨4466892818100663670659601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5955857090800884894212801 4466892818100663670659601)
                  ·
                    refine ⟨3350169613575497752994701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4466892818100663670659601 3350169613575497752994701)
                    ·
                      refine ⟨1256313605090811657373013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350169613575497752994701 1256313605090811657373013)
                      ·
                        rfl

theorem cell23_2446662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2446662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446662 prefixEnd_2446662 := by exact prefixLift 2446662
  have htrace : WordTrace (prefixWord ++ tailWord_2446662) baseStart_2446662 baseEnd_2446662 := by
    simpa [prefixWord, tailWord_2446662, baseEnd_2446662] using wordTrace_append hprefix tailTrace_2446662
  have hstable : (prefixWord ++ tailWord_2446662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446662).length < 2 ^ (prefixWord ++ tailWord_2446662).sum := by decide
  have hdescent : baseEnd_2446662 < baseStart_2446662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446664 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_2446664 : Nat := 118140960795 + 2446664 * 2 ^ 59
def prefixEnd_2446664 : Nat := 4983230072969 + 3 ^ 40 * 2446664 * 2
def baseEnd_2446664 : Nat := 1256314632052120649548003

theorem tailTrace_2446664 : CollatzResearch.WordTrace tailWord_2446664 prefixEnd_2446664 1256314632052120649548003 := by
  unfold tailWord_2446664
  simp only [CollatzResearch.WordTrace]
  refine ⟨44618583604080829894509523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59491444805441106526012697 44618583604080829894509523)
  ·
    refine ⟨66927875406121244841764285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44618583604080829894509523 66927875406121244841764285)
    ·
      refine ⟨25097953277295466815661607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66927875406121244841764285 25097953277295466815661607)
      ·
        refine ⟨37646929915943200223492411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25097953277295466815661607 37646929915943200223492411)
        ·
          refine ⟨56470394873914800335238617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37646929915943200223492411 56470394873914800335238617)
          ·
            refine ⟨42352796155436100251428963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56470394873914800335238617 42352796155436100251428963)
            ·
              refine ⟨63529194233154150377143445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42352796155436100251428963 63529194233154150377143445)
              ·
                refine ⟨2977930979679100798928599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63529194233154150377143445 2977930979679100798928599)
                ·
                  refine ⟨4466896469518651198392899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977930979679100798928599 4466896469518651198392899)
                  ·
                    refine ⟨6700344704277976797589349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466896469518651198392899 6700344704277976797589349)
                    ·
                      refine ⟨1256314632052120649548003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6700344704277976797589349 1256314632052120649548003)
                      ·
                        rfl

theorem cell23_2446664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_2446664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446664 prefixEnd_2446664 := by exact prefixLift 2446664
  have htrace : WordTrace (prefixWord ++ tailWord_2446664) baseStart_2446664 baseEnd_2446664 := by
    simpa [prefixWord, tailWord_2446664, baseEnd_2446664] using wordTrace_append hprefix tailTrace_2446664
  have hstable : (prefixWord ++ tailWord_2446664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446664).length < 2 ^ (prefixWord ++ tailWord_2446664).sum := by decide
  have hdescent : baseEnd_2446664 < baseStart_2446664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446668 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 2, 3, 2]
def baseStart_2446668 : Nat := 118140960795 + 2446668 * 2 ^ 59
def prefixEnd_2446668 : Nat := 4983230072969 + 3 ^ 40 * 2446668 * 2
def baseEnd_2446668 : Nat := 1256316685974738633897985

theorem tailTrace_2446668 : CollatzResearch.WordTrace tailWord_2446668 prefixEnd_2446668 1256316685974738633897985 := by
  unfold tailWord_2446668
  simp only [CollatzResearch.WordTrace]
  refine ⟨44618656550073584236082329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59491542066764778981443105 44618656550073584236082329)
  ·
    refine ⟨33463992412555188177061747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44618656550073584236082329 33463992412555188177061747)
    ·
      refine ⟨50195988618832782265592621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33463992412555188177061747 50195988618832782265592621)
      ·
        refine ⟨18823495732062293349597233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50195988618832782265592621 18823495732062293349597233)
        ·
          refine ⟨14117621799046720012197925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18823495732062293349597233 14117621799046720012197925)
          ·
            refine ⟨2647054087321260002287111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14117621799046720012197925 2647054087321260002287111)
            ·
              refine ⟨3970581130981890003430667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647054087321260002287111 3970581130981890003430667)
              ·
                refine ⟨5955871696472835005146001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970581130981890003430667 5955871696472835005146001)
                ·
                  refine ⟨4466903772354626253859501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5955871696472835005146001 4466903772354626253859501)
                  ·
                    refine ⟨1675088914632984845197313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4466903772354626253859501 1675088914632984845197313)
                    ·
                      refine ⟨1256316685974738633897985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675088914632984845197313 1256316685974738633897985)
                      ·
                        rfl

theorem cell23_2446668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_2446668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446668 prefixEnd_2446668 := by exact prefixLift 2446668
  have htrace : WordTrace (prefixWord ++ tailWord_2446668) baseStart_2446668 baseEnd_2446668 := by
    simpa [prefixWord, tailWord_2446668, baseEnd_2446668] using wordTrace_append hprefix tailTrace_2446668
  have hstable : (prefixWord ++ tailWord_2446668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446668).length < 2 ^ (prefixWord ++ tailWord_2446668).sum := by decide
  have hdescent : baseEnd_2446668 < baseStart_2446668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446674 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2446674 : Nat := 118140960795 + 2446674 * 2 ^ 59
def prefixEnd_2446674 : Nat := 4983230072969 + 3 ^ 40 * 2446674 * 2
def baseEnd_2446674 : Nat := 418773255619555203474319

theorem tailTrace_2446674 : CollatzResearch.WordTrace tailWord_2446674 prefixEnd_2446674 418773255619555203474319 := by
  unfold tailWord_2446674
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309382984531357874220769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59491687958750287664588717 22309382984531357874220769)
  ·
    refine ⟨16732037238398518405665577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22309382984531357874220769 16732037238398518405665577)
    ·
      refine ⟨12549027928798888804249183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16732037238398518405665577 12549027928798888804249183)
      ·
        refine ⟨18823541893198333206373775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12549027928798888804249183 18823541893198333206373775)
        ·
          refine ⟨28235312839797499809560663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18823541893198333206373775 28235312839797499809560663)
          ·
            refine ⟨42352969259696249714340995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28235312839797499809560663 42352969259696249714340995)
            ·
              refine ⟨63529453889544374571511493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42352969259696249714340995 63529453889544374571511493)
              ·
                refine ⟨11911772604289570232158405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63529453889544374571511493 11911772604289570232158405)
                ·
                  refine ⟨2233457363304294418529701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11911772604289570232158405 2233457363304294418529701)
                  ·
                    refine ⟨418773255619555203474319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2233457363304294418529701 418773255619555203474319)
                    ·
                      rfl

theorem cell23_2446674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2446674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446674 prefixEnd_2446674 := by exact prefixLift 2446674
  have htrace : WordTrace (prefixWord ++ tailWord_2446674) baseStart_2446674 baseEnd_2446674 := by
    simpa [prefixWord, tailWord_2446674, baseEnd_2446674] using wordTrace_append hprefix tailTrace_2446674
  have hstable : (prefixWord ++ tailWord_2446674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446674).length < 2 ^ (prefixWord ++ tailWord_2446674).sum := by decide
  have hdescent : baseEnd_2446674 < baseStart_2446674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446681 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 1, 1, 4]
def baseStart_2446681 : Nat := 118140960795 + 2446681 * 2 ^ 59
def prefixEnd_2446681 : Nat := 4983230072969 + 3 ^ 40 * 2446681 * 2
def baseEnd_2446681 : Nat := 1256323361223247083035425

theorem tailTrace_2446681 : CollatzResearch.WordTrace tailWord_2446681 prefixEnd_2446681 1256323361223247083035425 := by
  unfold tailWord_2446681
  simp only [CollatzResearch.WordTrace]
  refine ⟨89237787249100071692387897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59491858166066714461591931 89237787249100071692387897)
  ·
    refine ⟨66928340436825053769290923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89237787249100071692387897 66928340436825053769290923)
    ·
      refine ⟨100392510655237580653936385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66928340436825053769290923 100392510655237580653936385)
      ·
        refine ⟨75294382991428185490452289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100392510655237580653936385 75294382991428185490452289)
        ·
          refine ⟨56470787243571139117839217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75294382991428185490452289 56470787243571139117839217)
          ·
            refine ⟨42353090432678354338379413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56470787243571139117839217 42353090432678354338379413)
            ·
              refine ⟨1985301114031797859611535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42353090432678354338379413 1985301114031797859611535)
              ·
                refine ⟨2977951671047696789417303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985301114031797859611535 2977951671047696789417303)
                ·
                  refine ⟨4466927506571545184125955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977951671047696789417303 4466927506571545184125955)
                  ·
                    refine ⟨6700391259857317776188933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466927506571545184125955 6700391259857317776188933)
                    ·
                      refine ⟨1256323361223247083035425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6700391259857317776188933 1256323361223247083035425)
                      ·
                        rfl

theorem cell23_2446681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_2446681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446681 prefixEnd_2446681 := by exact prefixLift 2446681
  have htrace : WordTrace (prefixWord ++ tailWord_2446681) baseStart_2446681 baseEnd_2446681 := by
    simpa [prefixWord, tailWord_2446681, baseEnd_2446681] using wordTrace_append hprefix tailTrace_2446681
  have hstable : (prefixWord ++ tailWord_2446681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446681).length < 2 ^ (prefixWord ++ tailWord_2446681).sum := by decide
  have hdescent : baseEnd_2446681 < baseStart_2446681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446691 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 2, 4]
def baseStart_2446691 : Nat := 118140960795 + 2446691 * 2 ^ 59
def prefixEnd_2446691 : Nat := 4983230072969 + 3 ^ 40 * 2446691 * 2
def baseEnd_2446691 : Nat := 418776165343264014636793

theorem tailTrace_2446691 : CollatzResearch.WordTrace tailWord_2446691 prefixEnd_2446691 418776165343264014636793 := by
  unfold tailWord_2446691
  simp only [CollatzResearch.WordTrace]
  refine ⟨89238151979063843400251927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59492101319375895600167951 89238151979063843400251927)
  ·
    refine ⟨133857227968595765100377891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89238151979063843400251927 133857227968595765100377891)
    ·
      refine ⟨200785841952893647650566837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133857227968595765100377891 200785841952893647650566837)
      ·
        refine ⟨18823672683083779467240641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200785841952893647650566837 18823672683083779467240641)
        ·
          refine ⟨14117754512312834600430481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18823672683083779467240641 14117754512312834600430481)
          ·
            refine ⟨10588315884234625950322861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14117754512312834600430481 10588315884234625950322861)
            ·
              refine ⟨3970618456587984731371073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10588315884234625950322861 3970618456587984731371073)
              ·
                refine ⟨2977963842440988548528305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970618456587984731371073 2977963842440988548528305)
                ·
                  refine ⟨2233472881830741411396229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2977963842440988548528305 2233472881830741411396229)
                  ·
                    refine ⟨418776165343264014636793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2233472881830741411396229 418776165343264014636793)
                    ·
                      rfl

theorem cell23_2446691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 4].length) (baseStart_2446691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446691 prefixEnd_2446691 := by exact prefixLift 2446691
  have htrace : WordTrace (prefixWord ++ tailWord_2446691) baseStart_2446691 baseEnd_2446691 := by
    simpa [prefixWord, tailWord_2446691, baseEnd_2446691] using wordTrace_append hprefix tailTrace_2446691
  have hstable : (prefixWord ++ tailWord_2446691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446691).length < 2 ^ (prefixWord ++ tailWord_2446691).sum := by decide
  have hdescent : baseEnd_2446691 < baseStart_2446691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446738 : List Nat := [3, 2, 3, 3, 2, 1, 9]
def baseStart_2446738 : Nat := 118140960795 + 2446738 * 2 ^ 59
def prefixEnd_2446738 : Nat := 4983230072969 + 3 ^ 40 * 2446738 * 2
def baseEnd_2446738 : Nat := 15510526291611769876823

theorem tailTrace_2446738 : CollatzResearch.WordTrace tailWord_2446738 prefixEnd_2446738 15510526291611769876823 := by
  unfold tailWord_2446738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309966552473392606803217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59493244139929046951475245 22309966552473392606803217)
  ·
    refine ⟨16732474914355044455102413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22309966552473392606803217 16732474914355044455102413)
    ·
      refine ⟨6274678092883141670663405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16732474914355044455102413 6274678092883141670663405)
      ·
        refine ⟨2353004284831178126498777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6274678092883141670663405 2353004284831178126498777)
        ·
          refine ⟨1764753213623383594874083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2353004284831178126498777 1764753213623383594874083)
          ·
            refine ⟨2647129820435075392311125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764753213623383594874083 2647129820435075392311125)
            ·
              refine ⟨15510526291611769876823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2647129820435075392311125 15510526291611769876823)
              ·
                rfl

theorem cell23_2446738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 9].length) (baseStart_2446738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446738 prefixEnd_2446738 := by exact prefixLift 2446738
  have htrace : WordTrace (prefixWord ++ tailWord_2446738) baseStart_2446738 baseEnd_2446738 := by
    simpa [prefixWord, tailWord_2446738, baseEnd_2446738] using wordTrace_append hprefix tailTrace_2446738
  have hstable : (prefixWord ++ tailWord_2446738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446738).length < 2 ^ (prefixWord ++ tailWord_2446738).sum := by decide
  have hdescent : baseEnd_2446738 < baseStart_2446738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446765 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2446765 : Nat := 118140960795 + 2446765 * 2 ^ 59
def prefixEnd_2446765 : Nat := 4983230072969 + 3 ^ 40 * 2446765 * 2
def baseEnd_2446765 : Nat := 1256366493598224754385039

theorem tailTrace_2446765 : CollatzResearch.WordTrace tailWord_2446765 prefixEnd_2446765 1256366493598224754385039 := by
  unfold tailWord_2446765
  simp only [CollatzResearch.WordTrace]
  refine ⟨89240850980795754038445749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59493900653863836025630499 89240850980795754038445749)
  ·
    refine ⟨8366329779449601941104289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89240850980795754038445749 8366329779449601941104289)
    ·
      refine ⟨6274747334587201455828217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8366329779449601941104289 6274747334587201455828217)
      ·
        refine ⟨4706060500940401091871163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6274747334587201455828217 4706060500940401091871163)
        ·
          refine ⟨7059090751410601637806745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706060500940401091871163 7059090751410601637806745)
          ·
            refine ⟨5294318063557951228355059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7059090751410601637806745 5294318063557951228355059)
            ·
              refine ⟨7941477095336926842532589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294318063557951228355059 7941477095336926842532589)
              ·
                refine ⟨2978053910751347565949721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7941477095336926842532589 2978053910751347565949721)
                ·
                  refine ⟨2233540433063510674462291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2978053910751347565949721 2233540433063510674462291)
                  ·
                    refine ⟨3350310649595266011693437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2233540433063510674462291 3350310649595266011693437)
                    ·
                      refine ⟨1256366493598224754385039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350310649595266011693437 1256366493598224754385039)
                      ·
                        rfl

theorem cell23_2446765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2446765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446765 prefixEnd_2446765 := by exact prefixLift 2446765
  have htrace : WordTrace (prefixWord ++ tailWord_2446765) baseStart_2446765 baseEnd_2446765 := by
    simpa [prefixWord, tailWord_2446765, baseEnd_2446765] using wordTrace_append hprefix tailTrace_2446765
  have hstable : (prefixWord ++ tailWord_2446765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446765).length < 2 ^ (prefixWord ++ tailWord_2446765).sum := by decide
  have hdescent : baseEnd_2446765 < baseStart_2446765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446767 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_2446767 : Nat := 118140960795 + 2446767 * 2 ^ 59
def prefixEnd_2446767 : Nat := 4983230072969 + 3 ^ 40 * 2446767 * 2
def baseEnd_2446767 : Nat := 1256367520559533746560029

theorem tailTrace_2446767 : CollatzResearch.WordTrace tailWord_2446767 prefixEnd_2446767 1256367520559533746560029 := by
  unfold tailWord_2446767
  simp only [CollatzResearch.WordTrace]
  refine ⟨89240923926788508380018555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59493949284525672253345703 89240923926788508380018555)
  ·
    refine ⟨133861385890182762570027833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89240923926788508380018555 133861385890182762570027833)
    ·
      refine ⟨100396039417637071927520875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133861385890182762570027833 100396039417637071927520875)
      ·
        refine ⟨150594059126455607891281313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100396039417637071927520875 150594059126455607891281313)
        ·
          refine ⟨112945544344841705918460985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150594059126455607891281313 112945544344841705918460985)
          ·
            refine ⟨84709158258631279438845739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112945544344841705918460985 84709158258631279438845739)
            ·
              refine ⟨127063737387946919158268609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84709158258631279438845739 127063737387946919158268609)
              ·
                refine ⟨95297803040960189368701457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127063737387946919158268609 95297803040960189368701457)
                ·
                  refine ⟨71473352280720142026526093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95297803040960189368701457 71473352280720142026526093)
                  ·
                    refine ⟨26802507105270053259947285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71473352280720142026526093 26802507105270053259947285)
                    ·
                      refine ⟨1256367520559533746560029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26802507105270053259947285 1256367520559533746560029)
                      ·
                        rfl

theorem cell23_2446767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_2446767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446767 prefixEnd_2446767 := by exact prefixLift 2446767
  have htrace : WordTrace (prefixWord ++ tailWord_2446767) baseStart_2446767 baseEnd_2446767 := by
    simpa [prefixWord, tailWord_2446767, baseEnd_2446767] using wordTrace_append hprefix tailTrace_2446767
  have hstable : (prefixWord ++ tailWord_2446767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446767).length < 2 ^ (prefixWord ++ tailWord_2446767).sum := by decide
  have hdescent : baseEnd_2446767 < baseStart_2446767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446786 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_2446786 : Nat := 118140960795 + 2446786 * 2 ^ 59
def prefixEnd_2446786 : Nat := 4983230072969 + 3 ^ 40 * 2446786 * 2
def baseEnd_2446786 : Nat := 1256377276691969172222443

theorem tailTrace_2446786 : CollatzResearch.WordTrace tailWord_2446786 prefixEnd_2446786 1256377276691969172222443 := by
  unfold tailWord_2446786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22310404228429918656240053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59494411275813116416640141 22310404228429918656240053)
  ·
    refine ⟨2091600396415304874022505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22310404228429918656240053 2091600396415304874022505)
    ·
      refine ⟨1568700297311478655516879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2091600396415304874022505 1568700297311478655516879)
      ·
        refine ⟨2353050445967217983275319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568700297311478655516879 2353050445967217983275319)
        ·
          refine ⟨3529575668950826974912979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353050445967217983275319 3529575668950826974912979)
          ·
            refine ⟨5294363503426240462369469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3529575668950826974912979 5294363503426240462369469)
            ·
              refine ⟨1985386313784840173388551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5294363503426240462369469 1985386313784840173388551)
              ·
                refine ⟨2978079470677260260082827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985386313784840173388551 2978079470677260260082827)
                ·
                  refine ⟨4467119206015890390124241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978079470677260260082827 4467119206015890390124241)
                  ·
                    refine ⟨3350339404511917792593181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4467119206015890390124241 3350339404511917792593181)
                    ·
                      refine ⟨1256377276691969172222443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350339404511917792593181 1256377276691969172222443)
                      ·
                        rfl

theorem cell23_2446786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_2446786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446786 prefixEnd_2446786 := by exact prefixLift 2446786
  have htrace : WordTrace (prefixWord ++ tailWord_2446786) baseStart_2446786 baseEnd_2446786 := by
    simpa [prefixWord, tailWord_2446786, baseEnd_2446786] using wordTrace_append hprefix tailTrace_2446786
  have hstable : (prefixWord ++ tailWord_2446786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446786).length < 2 ^ (prefixWord ++ tailWord_2446786).sum := by decide
  have hdescent : baseEnd_2446786 < baseStart_2446786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446788 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_2446788 : Nat := 118140960795 + 2446788 * 2 ^ 59
def prefixEnd_2446788 : Nat := 4983230072969 + 3 ^ 40 * 2446788 * 2
def baseEnd_2446788 : Nat := 1256378303653278164397433

theorem tailTrace_2446788 : CollatzResearch.WordTrace tailWord_2446788 prefixEnd_2446788 1256378303653278164397433 := by
  unfold tailWord_2446788
  simp only [CollatzResearch.WordTrace]
  refine ⟨44620844929856214483266509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59494459906474952644355345 44620844929856214483266509)
  ·
    refine ⟨16732816848696080431224941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44620844929856214483266509 16732816848696080431224941)
    ·
      refine ⟨6274806318261030161709353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16732816848696080431224941 6274806318261030161709353)
      ·
        refine ⟨4706104738695772621282015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6274806318261030161709353 4706104738695772621282015)
        ·
          refine ⟨7059157108043658931923023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706104738695772621282015 7059157108043658931923023)
          ·
            refine ⟨10588735662065488397884535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7059157108043658931923023 10588735662065488397884535)
            ·
              refine ⟨15883103493098232596826803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10588735662065488397884535 15883103493098232596826803)
              ·
                refine ⟨23824655239647348895240205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15883103493098232596826803 23824655239647348895240205)
                ·
                  refine ⟨8934245714867755835715077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23824655239647348895240205 8934245714867755835715077)
                  ·
                    refine ⟨1675171071537704219196577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8934245714867755835715077 1675171071537704219196577)
                    ·
                      refine ⟨1256378303653278164397433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675171071537704219196577 1256378303653278164397433)
                      ·
                        rfl

theorem cell23_2446788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_2446788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446788 prefixEnd_2446788 := by exact prefixLift 2446788
  have htrace : WordTrace (prefixWord ++ tailWord_2446788) baseStart_2446788 baseEnd_2446788 := by
    simpa [prefixWord, tailWord_2446788, baseEnd_2446788] using wordTrace_append hprefix tailTrace_2446788
  have hstable : (prefixWord ++ tailWord_2446788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446788).length < 2 ^ (prefixWord ++ tailWord_2446788).sum := by decide
  have hdescent : baseEnd_2446788 < baseStart_2446788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446805 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_2446805 : Nat := 118140960795 + 2446805 * 2 ^ 59
def prefixEnd_2446805 : Nat := 4983230072969 + 3 ^ 40 * 2446805 * 2
def baseEnd_2446805 : Nat := 1256387032824404597884855

theorem tailTrace_2446805 : CollatzResearch.WordTrace tailWord_2446805 prefixEnd_2446805 1256387032824404597884855 := by
  unfold tailWord_2446805
  simp only [CollatzResearch.WordTrace]
  refine ⟨89242309900650840869901869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59494873267100560579934579 89242309900650840869901869)
  ·
    refine ⟨33465866212744065326213201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89242309900650840869901869 33465866212744065326213201)
    ·
      refine ⟨25099399659558048994659901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33465866212744065326213201 25099399659558048994659901)
      ·
        refine ⟨9412274872334268372997463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25099399659558048994659901 9412274872334268372997463)
        ·
          refine ⟨14118412308501402559496195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9412274872334268372997463 14118412308501402559496195)
          ·
            refine ⟨21177618462752103839244293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14118412308501402559496195 21177618462752103839244293)
            ·
              refine ⟨3970803461766019469858305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21177618462752103839244293 3970803461766019469858305)
              ·
                refine ⟨2978102596324514602393729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970803461766019469858305 2978102596324514602393729)
                ·
                  refine ⟨2233576947243385951795297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2978102596324514602393729 2233576947243385951795297)
                  ·
                    refine ⟨1675182710432539463846473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2233576947243385951795297 1675182710432539463846473)
                    ·
                      refine ⟨1256387032824404597884855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675182710432539463846473 1256387032824404597884855)
                      ·
                        rfl

theorem cell23_2446805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_2446805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446805 prefixEnd_2446805 := by exact prefixLift 2446805
  have htrace : WordTrace (prefixWord ++ tailWord_2446805) baseStart_2446805 baseEnd_2446805 := by
    simpa [prefixWord, tailWord_2446805, baseEnd_2446805] using wordTrace_append hprefix tailTrace_2446805
  have hstable : (prefixWord ++ tailWord_2446805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446805).length < 2 ^ (prefixWord ++ tailWord_2446805).sum := by decide
  have hdescent : baseEnd_2446805 < baseStart_2446805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446821 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2446821 : Nat := 118140960795 + 2446821 * 2 ^ 59
def prefixEnd_2446821 : Nat := 4983230072969 + 3 ^ 40 * 2446821 * 2
def baseEnd_2446821 : Nat := 1256395248514876535284781

theorem tailTrace_2446821 : CollatzResearch.WordTrace tailWord_2446821 prefixEnd_2446821 1256395248514876535284781 := by
  unfold tailWord_2446821
  simp only [CollatzResearch.WordTrace]
  refine ⟨89242893468592875602484317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59495262312395250401656211 89242893468592875602484317)
  ·
    refine ⟨33466085050722328350931619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89242893468592875602484317 33466085050722328350931619)
    ·
      refine ⟨50199127576083492526397429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33466085050722328350931619 50199127576083492526397429)
      ·
        refine ⟨4706168210257827424349759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50199127576083492526397429 4706168210257827424349759)
        ·
          refine ⟨7059252315386741136524639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706168210257827424349759 7059252315386741136524639)
          ·
            refine ⟨10588878473080111704786959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7059252315386741136524639 10588878473080111704786959)
            ·
              refine ⟨15883317709620167557180439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10588878473080111704786959 15883317709620167557180439)
              ·
                refine ⟨23824976564430251335770659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15883317709620167557180439 23824976564430251335770659)
                ·
                  refine ⟨35737464846645377003655989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23824976564430251335770659 35737464846645377003655989)
                  ·
                    refine ⟨3350387329373004094092749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35737464846645377003655989 3350387329373004094092749)
                    ·
                      refine ⟨1256395248514876535284781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350387329373004094092749 1256395248514876535284781)
                      ·
                        rfl

theorem cell23_2446821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2446821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446821 prefixEnd_2446821 := by exact prefixLift 2446821
  have htrace : WordTrace (prefixWord ++ tailWord_2446821) baseStart_2446821 baseEnd_2446821 := by
    simpa [prefixWord, tailWord_2446821, baseEnd_2446821] using wordTrace_append hprefix tailTrace_2446821
  have hstable : (prefixWord ++ tailWord_2446821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446821).length < 2 ^ (prefixWord ++ tailWord_2446821).sum := by decide
  have hdescent : baseEnd_2446821 < baseStart_2446821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446824 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2446824 : Nat := 118140960795 + 2446824 * 2 ^ 59
def prefixEnd_2446824 : Nat := 4983230072969 + 3 ^ 40 * 2446824 * 2
def baseEnd_2446824 : Nat := 418798929652280007849089

theorem tailTrace_2446824 : CollatzResearch.WordTrace tailWord_2446824 prefixEnd_2446824 418798929652280007849089 := by
  unfold tailWord_2446824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44621501443791003557421763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59495335258388004743229017 44621501443791003557421763)
  ·
    refine ⟨66932252165686505336132645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44621501443791003557421763 66932252165686505336132645)
    ·
      refine ⟨12549797281066219750524871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66932252165686505336132645 12549797281066219750524871)
      ·
        refine ⟨18824695921599329625787307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12549797281066219750524871 18824695921599329625787307)
        ·
          refine ⟨28237043882398994438680961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18824695921599329625787307 28237043882398994438680961)
          ·
            refine ⟨21177782911799245829010721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28237043882398994438680961 21177782911799245829010721)
            ·
              refine ⟨15883337183849434371758041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21177782911799245829010721 15883337183849434371758041)
              ·
                refine ⟨11912502887887075778818531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15883337183849434371758041 11912502887887075778818531)
                ·
                  refine ⟨17868754331830613668227797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11912502887887075778818531 17868754331830613668227797)
                  ·
                    refine ⟨418798929652280007849089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17868754331830613668227797 418798929652280007849089)
                    ·
                      rfl

theorem cell23_2446824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2446824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446824 prefixEnd_2446824 := by exact prefixLift 2446824
  have htrace : WordTrace (prefixWord ++ tailWord_2446824) baseStart_2446824 baseEnd_2446824 := by
    simpa [prefixWord, tailWord_2446824, baseEnd_2446824] using wordTrace_append hprefix tailTrace_2446824
  have hstable : (prefixWord ++ tailWord_2446824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446824).length < 2 ^ (prefixWord ++ tailWord_2446824).sum := by decide
  have hdescent : baseEnd_2446824 < baseStart_2446824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446874 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2446874 : Nat := 118140960795 + 2446874 * 2 ^ 59
def prefixEnd_2446874 : Nat := 4983230072969 + 3 ^ 40 * 2446874 * 2
def baseEnd_2446874 : Nat := 1256422462989564827922037

theorem tailTrace_2446874 : CollatzResearch.WordTrace tailWord_2446874 prefixEnd_2446874 1256422462989564827922037 := by
  unfold tailWord_2446874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22311206634350216413540919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59496551024933910436109117 22311206634350216413540919)
  ·
    refine ⟨33466809951525324620311379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22311206634350216413540919 33466809951525324620311379)
    ·
      refine ⟨50200214927287986930467069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33466809951525324620311379 50200214927287986930467069)
      ·
        refine ⟨18825080597732995098925151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50200214927287986930467069 18825080597732995098925151)
        ·
          refine ⟨28237620896599492648387727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18825080597732995098925151 28237620896599492648387727)
          ·
            refine ⟨42356431344899238972581591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28237620896599492648387727 42356431344899238972581591)
            ·
              refine ⟨63534647017348858458872387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42356431344899238972581591 63534647017348858458872387)
              ·
                refine ⟨95301970526023287688308581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63534647017348858458872387 95301970526023287688308581)
                ·
                  refine ⟨17869119473629366441557859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95301970526023287688308581 17869119473629366441557859)
                  ·
                    refine ⟨26803679210444049662336789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17869119473629366441557859 26803679210444049662336789)
                    ·
                      refine ⟨1256422462989564827922037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26803679210444049662336789 1256422462989564827922037)
                      ·
                        rfl

theorem cell23_2446874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2446874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446874 prefixEnd_2446874 := by exact prefixLift 2446874
  have htrace : WordTrace (prefixWord ++ tailWord_2446874) baseStart_2446874 baseEnd_2446874 := by
    simpa [prefixWord, tailWord_2446874, baseEnd_2446874] using wordTrace_append hprefix tailTrace_2446874
  have hstable : (prefixWord ++ tailWord_2446874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446874).length < 2 ^ (prefixWord ++ tailWord_2446874).sum := by decide
  have hdescent : baseEnd_2446874 < baseStart_2446874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446881 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2446881 : Nat := 118140960795 + 2446881 * 2 ^ 59
def prefixEnd_2446881 : Nat := 4983230072969 + 3 ^ 40 * 2446881 * 2
def baseEnd_2446881 : Nat := 1256426057354146300534505

theorem tailTrace_2446881 : CollatzResearch.WordTrace tailWord_2446881 prefixEnd_2446881 1256426057354146300534505 := by
  unfold tailWord_2446881
  simp only [CollatzResearch.WordTrace]
  refine ⟨89245081848375505849668497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59496721232250337233112331 89245081848375505849668497)
  ·
    refine ⟨66933811386281629387251373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89245081848375505849668497 66933811386281629387251373)
    ·
      refine ⟨25100179269855611020219265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66933811386281629387251373 25100179269855611020219265)
      ·
        refine ⟨18825134452391708265164449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25100179269855611020219265 18825134452391708265164449)
        ·
          refine ⟨14118850839293781198873337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18825134452391708265164449 14118850839293781198873337)
          ·
            refine ⟨10589138129470335899155003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14118850839293781198873337 10589138129470335899155003)
            ·
              refine ⟨15883707194205503848732505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10589138129470335899155003 15883707194205503848732505)
              ·
                refine ⟨11912780395654127886549379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15883707194205503848732505 11912780395654127886549379)
                ·
                  refine ⟨17869170593481191829824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11912780395654127886549379 17869170593481191829824069)
                  ·
                    refine ⟨3350469486277723468092013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17869170593481191829824069 3350469486277723468092013)
                    ·
                      refine ⟨1256426057354146300534505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350469486277723468092013 1256426057354146300534505)
                      ·
                        rfl

theorem cell23_2446881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2446881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446881 prefixEnd_2446881 := by exact prefixLift 2446881
  have htrace : WordTrace (prefixWord ++ tailWord_2446881) baseStart_2446881 baseEnd_2446881 := by
    simpa [prefixWord, tailWord_2446881, baseEnd_2446881] using wordTrace_append hprefix tailTrace_2446881
  have hstable : (prefixWord ++ tailWord_2446881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446881).length < 2 ^ (prefixWord ++ tailWord_2446881).sum := by decide
  have hdescent : baseEnd_2446881 < baseStart_2446881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
