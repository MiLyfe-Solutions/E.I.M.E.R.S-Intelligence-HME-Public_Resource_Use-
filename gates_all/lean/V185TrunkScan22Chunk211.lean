import V185TrunkScan22Chunk210

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1881649 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1881649 : Nat := 118140960795 + 1881649 * 2 ^ 59
def prefixEnd_1881649 : Nat := 4983230072969 + 3 ^ 40 * 1881649 * 2
def baseEnd_1881649 : Nat := 644126906701342515555973

theorem tailTrace_1881649 : CollatzResearch.WordTrace tailWord_1881649 prefixEnd_1881649 644126906701342515555973 := by
  unfold tailWord_1881649
  simp only [CollatzResearch.WordTrace]
  refine ⟨68629377160114507909528001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45752918106743005273018667 68629377160114507909528001)
  ·
    refine ⟨51472032870085880932146001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68629377160114507909528001 51472032870085880932146001)
    ·
      refine ⟨38604024652564410699109501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51472032870085880932146001 38604024652564410699109501)
      ·
        refine ⟨14476509244711654012166063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38604024652564410699109501 14476509244711654012166063)
        ·
          refine ⟨21714763867067481018249095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14476509244711654012166063 21714763867067481018249095)
          ·
            refine ⟨32572145800601221527373643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21714763867067481018249095 32572145800601221527373643)
            ·
              refine ⟨48858218700901832291060465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32572145800601221527373643 48858218700901832291060465)
              ·
                refine ⟨36643664025676374218295349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48858218700901832291060465 36643664025676374218295349)
                ·
                  refine ⟨3435343502407160082965189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36643664025676374218295349 3435343502407160082965189)
                  ·
                    refine ⟨644126906701342515555973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435343502407160082965189 644126906701342515555973)
                    ·
                      rfl

theorem cell22_1881649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1881649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881649 prefixEnd_1881649 := by exact prefixLift 1881649
  have htrace : WordTrace (prefixWord ++ tailWord_1881649) baseStart_1881649 baseEnd_1881649 := by
    simpa [prefixWord, tailWord_1881649, baseEnd_1881649] using wordTrace_append hprefix tailTrace_1881649
  have hstable : (prefixWord ++ tailWord_1881649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881649).length < 2 ^ (prefixWord ++ tailWord_1881649).sum := by decide
  have hdescent : baseEnd_1881649 < baseStart_1881649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881670 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1881670 : Nat := 118140960795 + 1881670 * 2 ^ 59
def prefixEnd_1881670 : Nat := 4983230072969 + 3 ^ 40 * 1881670 * 2
def baseEnd_1881670 : Nat := 214711365143501820260303

theorem tailTrace_1881670 : CollatzResearch.WordTrace tailWord_1881670 prefixEnd_1881670 214711365143501820260303 := by
  unfold tailWord_1881670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144691971657450890501327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45753428728692285664028309 2144691971657450890501327)
  ·
    refine ⟨3217037957486176335751991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2144691971657450890501327 3217037957486176335751991)
    ·
      refine ⟨4825556936229264503627987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3217037957486176335751991 4825556936229264503627987)
      ·
        refine ⟨7238335404343896755441981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4825556936229264503627987 7238335404343896755441981)
        ·
          refine ⟨2714375776628961283290743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7238335404343896755441981 2714375776628961283290743)
          ·
            refine ⟨4071563664943441924936115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714375776628961283290743 4071563664943441924936115)
            ·
              refine ⟨6107345497415162887404173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071563664943441924936115 6107345497415162887404173)
              ·
                refine ⟨2290254561530686082776565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6107345497415162887404173 2290254561530686082776565)
                ·
                  refine ⟨214711365143501820260303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290254561530686082776565 214711365143501820260303)
                  ·
                    rfl

theorem cell22_1881670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1881670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881670 prefixEnd_1881670 := by exact prefixLift 1881670
  have htrace : WordTrace (prefixWord ++ tailWord_1881670) baseStart_1881670 baseEnd_1881670 := by
    simpa [prefixWord, tailWord_1881670, baseEnd_1881670] using wordTrace_append hprefix tailTrace_1881670
  have hstable : (prefixWord ++ tailWord_1881670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881670).length < 2 ^ (prefixWord ++ tailWord_1881670).sum := by decide
  have hdescent : baseEnd_1881670 < baseStart_1881670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881679 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 1, 5]
def baseStart_1881679 : Nat := 118140960795 + 1881679 * 2 ^ 59
def prefixEnd_1881679 : Nat := 4983230072969 + 3 ^ 40 * 1881679 * 2
def baseEnd_1881679 : Nat := 644137176314432437305881

theorem tailTrace_1881679 : CollatzResearch.WordTrace tailWord_1881679 prefixEnd_1881679 644137176314432437305881 := by
  unfold tailWord_1881679
  simp only [CollatzResearch.WordTrace]
  refine ⟨68630471350005823033120091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45753647566670548688746727 68630471350005823033120091)
  ·
    refine ⟨102945707025008734549680137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68630471350005823033120091 102945707025008734549680137)
    ·
      refine ⟨77209280268756550912260103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102945707025008734549680137 77209280268756550912260103)
      ·
        refine ⟨115813920403134826368390155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77209280268756550912260103 115813920403134826368390155)
        ·
          refine ⟨173720880604702239552585233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115813920403134826368390155 173720880604702239552585233)
          ·
            refine ⟨130290660453526679664438925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173720880604702239552585233 130290660453526679664438925)
            ·
              refine ⟨48858997670072504874164597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130290660453526679664438925 48858997670072504874164597)
              ·
                refine ⟨4580531031569297331952931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48858997670072504874164597 4580531031569297331952931)
                ·
                  refine ⟨6870796547353945997929397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4580531031569297331952931 6870796547353945997929397)
                  ·
                    refine ⟨644137176314432437305881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6870796547353945997929397 644137176314432437305881)
                    ·
                      rfl

theorem cell22_1881679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_1881679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881679 prefixEnd_1881679 := by exact prefixLift 1881679
  have htrace : WordTrace (prefixWord ++ tailWord_1881679) baseStart_1881679 baseEnd_1881679 := by
    simpa [prefixWord, tailWord_1881679, baseEnd_1881679] using wordTrace_append hprefix tailTrace_1881679
  have hstable : (prefixWord ++ tailWord_1881679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881679).length < 2 ^ (prefixWord ++ tailWord_1881679).sum := by decide
  have hdescent : baseEnd_1881679 < baseStart_1881679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881709 : List Nat := [1, 5, 1, 1, 14]
def baseStart_1881709 : Nat := 118140960795 + 1881709 * 2 ^ 59
def prefixEnd_1881709 : Nat := 4983230072969 + 3 ^ 40 * 1881709 * 2
def baseEnd_1881709 : Nat := 2650812534681161971423

theorem tailTrace_1881709 : CollatzResearch.WordTrace tailWord_1881709 prefixEnd_1881709 2650812534681161971423 := by
  unfold tailWord_1881709
  simp only [CollatzResearch.WordTrace]
  refine ⟨68631565539897138156712181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45754377026598092104474787 68631565539897138156712181)
  ·
    refine ⟨6434209269365356702191767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68631565539897138156712181 6434209269365356702191767)
    ·
      refine ⟨9651313904048035053287651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434209269365356702191767 9651313904048035053287651)
      ·
        refine ⟨14476970856072052579931477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9651313904048035053287651 14476970856072052579931477)
        ·
          refine ⟨2650812534681161971423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 14476970856072052579931477 2650812534681161971423)
          ·
            rfl

theorem cell22_1881709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 14].length) (baseStart_1881709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881709 prefixEnd_1881709 := by exact prefixLift 1881709
  have htrace : WordTrace (prefixWord ++ tailWord_1881709) baseStart_1881709 baseEnd_1881709 := by
    simpa [prefixWord, tailWord_1881709, baseEnd_1881709] using wordTrace_append hprefix tailTrace_1881709
  have hstable : (prefixWord ++ tailWord_1881709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881709).length < 2 ^ (prefixWord ++ tailWord_1881709).sum := by decide
  have hdescent : baseEnd_1881709 < baseStart_1881709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881724 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1881724 : Nat := 118140960795 + 1881724 * 2 ^ 59
def prefixEnd_1881724 : Nat := 4983230072969 + 3 ^ 40 * 1881724 * 2
def baseEnd_1881724 : Nat := 644152580734067319930743

theorem tailTrace_1881724 : CollatzResearch.WordTrace tailWord_1881724 prefixEnd_1881724 644152580734067319930743 := by
  unfold tailWord_1881724
  simp only [CollatzResearch.WordTrace]
  refine ⟨34316056317421397859254113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45754741756561863812338817 34316056317421397859254113)
  ·
    refine ⟨25737042238066048394440585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34316056317421397859254113 25737042238066048394440585)
    ·
      refine ⟨19302781678549536295830439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25737042238066048394440585 19302781678549536295830439)
      ·
        refine ⟨28954172517824304443745659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19302781678549536295830439 28954172517824304443745659)
        ·
          refine ⟨43431258776736456665618489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28954172517824304443745659 43431258776736456665618489)
          ·
            refine ⟨32573444082552342499213867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43431258776736456665618489 32573444082552342499213867)
            ·
              refine ⟨48860166123828513748820801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32573444082552342499213867 48860166123828513748820801)
              ·
                refine ⟨36645124592871385311615601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48860166123828513748820801 36645124592871385311615601)
                ·
                  refine ⟨27483843444653538983711701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36645124592871385311615601 27483843444653538983711701)
                  ·
                    refine ⟨644152580734067319930743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27483843444653538983711701 644152580734067319930743)
                    ·
                      rfl

theorem cell22_1881724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1881724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881724 prefixEnd_1881724 := by exact prefixLift 1881724
  have htrace : WordTrace (prefixWord ++ tailWord_1881724) baseStart_1881724 baseEnd_1881724 := by
    simpa [prefixWord, tailWord_1881724, baseEnd_1881724] using wordTrace_append hprefix tailTrace_1881724
  have hstable : (prefixWord ++ tailWord_1881724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881724).length < 2 ^ (prefixWord ++ tailWord_1881724).sum := by decide
  have hdescent : baseEnd_1881724 < baseStart_1881724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881739 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 2, 6]
def baseStart_1881739 : Nat := 118140960795 + 1881739 * 2 ^ 59
def prefixEnd_1881739 : Nat := 4983230072969 + 3 ^ 40 * 1881739 * 2
def baseEnd_1881739 : Nat := 644157715540612280805697

theorem tailTrace_1881739 : CollatzResearch.WordTrace tailWord_1881739 prefixEnd_1881739 644157715540612280805697 := by
  unfold tailWord_1881739
  simp only [CollatzResearch.WordTrace]
  refine ⟨68632659729788453280304271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45755106486525635520202847 68632659729788453280304271)
  ·
    refine ⟨102948989594682679920456407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68632659729788453280304271 102948989594682679920456407)
    ·
      refine ⟨154423484392024019880684611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102948989594682679920456407 154423484392024019880684611)
      ·
        refine ⟨231635226588036029821026917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154423484392024019880684611 231635226588036029821026917)
        ·
          refine ⟨43431604985256755591442547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231635226588036029821026917 43431604985256755591442547)
          ·
            refine ⟨65147407477885133387163821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43431604985256755591442547 65147407477885133387163821)
            ·
              refine ⟨24430277804206925020186433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65147407477885133387163821 24430277804206925020186433)
              ·
                refine ⟨18322708353155193765139825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24430277804206925020186433 18322708353155193765139825)
                ·
                  refine ⟨13742031264866395323854869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18322708353155193765139825 13742031264866395323854869)
                  ·
                    refine ⟨644157715540612280805697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13742031264866395323854869 644157715540612280805697)
                    ·
                      rfl

theorem cell22_1881739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_1881739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881739 prefixEnd_1881739 := by exact prefixLift 1881739
  have htrace : WordTrace (prefixWord ++ tailWord_1881739) baseStart_1881739 baseEnd_1881739 := by
    simpa [prefixWord, tailWord_1881739, baseEnd_1881739] using wordTrace_append hprefix tailTrace_1881739
  have hstable : (prefixWord ++ tailWord_1881739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881739).length < 2 ^ (prefixWord ++ tailWord_1881739).sum := by decide
  have hdescent : baseEnd_1881739 < baseStart_1881739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881786 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1881786 : Nat := 118140960795 + 1881786 * 2 ^ 59
def prefixEnd_1881786 : Nat := 4983230072969 + 3 ^ 40 * 1881786 * 2
def baseEnd_1881786 : Nat := 644173804601119824880553

theorem tailTrace_1881786 : CollatzResearch.WordTrace tailWord_1881786 prefixEnd_1881786 644173804601119824880553 := by
  unfold tailWord_1881786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158593490154545076816303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45756249307078786871510141 17158593490154545076816303)
  ·
    refine ⟨25737890235231817615224455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17158593490154545076816303 25737890235231817615224455)
    ·
      refine ⟨38606835352847726422836683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25737890235231817615224455 38606835352847726422836683)
      ·
        refine ⟨57910253029271589634255025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38606835352847726422836683 57910253029271589634255025)
        ·
          refine ⟨43432689771953692225691269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57910253029271589634255025 43432689771953692225691269)
          ·
            refine ⟨8143629332241317292317113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43432689771953692225691269 8143629332241317292317113)
            ·
              refine ⟨6107721999180987969237835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143629332241317292317113 6107721999180987969237835)
              ·
                refine ⟨9161582998771481953856753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107721999180987969237835 9161582998771481953856753)
                ·
                  refine ⟨6871187249078611465392565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9161582998771481953856753 6871187249078611465392565)
                  ·
                    refine ⟨644173804601119824880553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6871187249078611465392565 644173804601119824880553)
                    ·
                      rfl

theorem cell22_1881786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1881786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881786 prefixEnd_1881786 := by exact prefixLift 1881786
  have htrace : WordTrace (prefixWord ++ tailWord_1881786) baseStart_1881786 baseEnd_1881786 := by
    simpa [prefixWord, tailWord_1881786, baseEnd_1881786] using wordTrace_append hprefix tailTrace_1881786
  have hstable : (prefixWord ++ tailWord_1881786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881786).length < 2 ^ (prefixWord ++ tailWord_1881786).sum := by decide
  have hdescent : baseEnd_1881786 < baseStart_1881786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881794 : List Nat := [3, 5, 1, 2, 1, 2, 2, 6]
def baseStart_1881794 : Nat := 118140960795 + 1881794 * 2 ^ 59
def prefixEnd_1881794 : Nat := 4983230072969 + 3 ^ 40 * 1881794 * 2
def baseEnd_1881794 : Nat := 71575171462734496742281

theorem tailTrace_1881794 : CollatzResearch.WordTrace tailWord_1881794 prefixEnd_1881794 71575171462734496742281 := by
  unfold tailWord_1881794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158666436147299418389109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45756443829726131782370957 17158666436147299418389109)
  ·
    refine ⟨1608624978388809320473979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17158666436147299418389109 1608624978388809320473979)
    ·
      refine ⟨2412937467583213980710969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1608624978388809320473979 2412937467583213980710969)
      ·
        refine ⟨1809703100687410485533227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2412937467583213980710969 1809703100687410485533227)
        ·
          refine ⟨2714554651031115728299841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809703100687410485533227 2714554651031115728299841)
          ·
            refine ⟨2035915988273336796224881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2714554651031115728299841 2035915988273336796224881)
            ·
              refine ⟨1526936991205002597168661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035915988273336796224881 1526936991205002597168661)
              ·
                refine ⟨71575171462734496742281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1526936991205002597168661 71575171462734496742281)
                ·
                  rfl

theorem cell22_1881794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_1881794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881794 prefixEnd_1881794 := by exact prefixLift 1881794
  have htrace : WordTrace (prefixWord ++ tailWord_1881794) baseStart_1881794 baseEnd_1881794 := by
    simpa [prefixWord, tailWord_1881794, baseEnd_1881794] using wordTrace_append hprefix tailTrace_1881794
  have hstable : (prefixWord ++ tailWord_1881794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881794).length < 2 ^ (prefixWord ++ tailWord_1881794).sum := by decide
  have hdescent : baseEnd_1881794 < baseStart_1881794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881818 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_1881818 : Nat := 118140960795 + 1881818 * 2 ^ 59
def prefixEnd_1881818 : Nat := 4983230072969 + 3 ^ 40 * 1881818 * 2
def baseEnd_1881818 : Nat := 644184758855082408080455

theorem tailTrace_1881818 : CollatzResearch.WordTrace tailWord_1881818 prefixEnd_1881818 644184758855082408080455 := by
  unfold tailWord_1881818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158885274125562443107527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45757027397668166514953405 17158885274125562443107527)
  ·
    refine ⟨25738327911188343664661291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17158885274125562443107527 25738327911188343664661291)
    ·
      refine ⟨38607491866782515496991937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25738327911188343664661291 38607491866782515496991937)
      ·
        refine ⟨28955618900086886622743953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38607491866782515496991937 28955618900086886622743953)
        ·
          refine ⟨21716714175065164967057965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28955618900086886622743953 21716714175065164967057965)
          ·
            refine ⟨8143767815649436862646737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21716714175065164967057965 8143767815649436862646737)
            ·
              refine ⟨6107825861737077646985053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143767815649436862646737 6107825861737077646985053)
              ·
                refine ⟨2290434698151404117619395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6107825861737077646985053 2290434698151404117619395)
                ·
                  refine ⟨3435652047227106176429093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290434698151404117619395 3435652047227106176429093)
                  ·
                    refine ⟨644184758855082408080455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435652047227106176429093 644184758855082408080455)
                    ·
                      rfl

theorem cell22_1881818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_1881818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881818 prefixEnd_1881818 := by exact prefixLift 1881818
  have htrace : WordTrace (prefixWord ++ tailWord_1881818) baseStart_1881818 baseEnd_1881818 := by
    simpa [prefixWord, tailWord_1881818, baseEnd_1881818] using wordTrace_append hprefix tailTrace_1881818
  have hstable : (prefixWord ++ tailWord_1881818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881818).length < 2 ^ (prefixWord ++ tailWord_1881818).sum := by decide
  have hdescent : baseEnd_1881818 < baseStart_1881818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881891 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 2, 6]
def baseStart_1881891 : Nat := 118140960795 + 1881891 * 2 ^ 59
def prefixEnd_1881891 : Nat := 4983230072969 + 3 ^ 40 * 1881891 * 2
def baseEnd_1881891 : Nat := 644209748246934551005231

theorem tailTrace_1881891 : CollatzResearch.WordTrace tailWord_1881891 prefixEnd_1881891 644209748246934551005231 := by
  unfold tailWord_1881891
  simp only [CollatzResearch.WordTrace]
  refine ⟨68638203625237783239837527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45758802416825188826558351 68638203625237783239837527)
  ·
    refine ⟨102957305437856674859756291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68638203625237783239837527 102957305437856674859756291)
    ·
      refine ⟨154435958156785012289634437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102957305437856674859756291 154435958156785012289634437)
      ·
        refine ⟨28956742154397189804306457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154435958156785012289634437 28956742154397189804306457)
        ·
          refine ⟨21717556615797892353229843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28956742154397189804306457 21717556615797892353229843)
          ·
            refine ⟨32576334923696838529844765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21717556615797892353229843 32576334923696838529844765)
            ·
              refine ⟨12216125596386314448691787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32576334923696838529844765 12216125596386314448691787)
              ·
                refine ⟨18324188394579471673037681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12216125596386314448691787 18324188394579471673037681)
                ·
                  refine ⟨13743141295934603754778261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18324188394579471673037681 13743141295934603754778261)
                  ·
                    refine ⟨644209748246934551005231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13743141295934603754778261 644209748246934551005231)
                    ·
                      rfl

theorem cell22_1881891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_1881891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881891 prefixEnd_1881891 := by exact prefixLift 1881891
  have htrace : WordTrace (prefixWord ++ tailWord_1881891) baseStart_1881891 baseEnd_1881891 := by
    simpa [prefixWord, tailWord_1881891, baseEnd_1881891] using wordTrace_append hprefix tailTrace_1881891
  have hstable : (prefixWord ++ tailWord_1881891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881891).length < 2 ^ (prefixWord ++ tailWord_1881891).sum := by decide
  have hdescent : baseEnd_1881891 < baseStart_1881891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881938 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1881938 : Nat := 118140960795 + 1881938 * 2 ^ 59
def prefixEnd_1881938 : Nat := 4983230072969 + 3 ^ 40 * 1881938 * 2
def baseEnd_1881938 : Nat := 644225837307442095080087

theorem tailTrace_1881938 : CollatzResearch.WordTrace tailWord_1881938 prefixEnd_1881938 644225837307442095080087 := by
  unfold tailWord_1881938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159979464016877566699617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45759945237378340177865645 17159979464016877566699617)
  ·
    refine ⟨12869984598012658175024713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17159979464016877566699617 12869984598012658175024713)
    ·
      refine ⟨9652488448509493631268535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12869984598012658175024713 9652488448509493631268535)
      ·
        refine ⟨14478732672764240446902803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652488448509493631268535 14478732672764240446902803)
        ·
          refine ⟨21718099009146360670354205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14478732672764240446902803 21718099009146360670354205)
          ·
            refine ⟨8144287128429885251382827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21718099009146360670354205 8144287128429885251382827)
            ·
              refine ⟨12216430692644827877074241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8144287128429885251382827 12216430692644827877074241)
              ·
                refine ⟨9162323019483620907805681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12216430692644827877074241 9162323019483620907805681)
                ·
                  refine ⟨6871742264612715680854261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9162323019483620907805681 6871742264612715680854261)
                  ·
                    refine ⟨644225837307442095080087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6871742264612715680854261 644225837307442095080087)
                    ·
                      rfl

theorem cell22_1881938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1881938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881938 prefixEnd_1881938 := by exact prefixLift 1881938
  have htrace : WordTrace (prefixWord ++ tailWord_1881938) baseStart_1881938 baseEnd_1881938 := by
    simpa [prefixWord, tailWord_1881938, baseEnd_1881938] using wordTrace_append hprefix tailTrace_1881938
  have hstable : (prefixWord ++ tailWord_1881938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881938).length < 2 ^ (prefixWord ++ tailWord_1881938).sum := by decide
  have hdescent : baseEnd_1881938 < baseStart_1881938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1881940 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 5]
def baseStart_1881940 : Nat := 118140960795 + 1881940 * 2 ^ 59
def prefixEnd_1881940 : Nat := 4983230072969 + 3 ^ 40 * 1881940 * 2
def baseEnd_1881940 : Nat := 214742173982771585510027

theorem tailTrace_1881940 : CollatzResearch.WordTrace tailWord_1881940 prefixEnd_1881940 214742173982771585510027 := by
  unfold tailWord_1881940
  simp only [CollatzResearch.WordTrace]
  refine ⟨34319995401030132304185637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45759993868040176405580849 34319995401030132304185637)
  ·
    refine ⟨6434999137693149807034807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34319995401030132304185637 6434999137693149807034807)
    ·
      refine ⟨9652498706539724710552211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434999137693149807034807 9652498706539724710552211)
      ·
        refine ⟨14478748059809587065828317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652498706539724710552211 14478748059809587065828317)
        ·
          refine ⟨5429530522428595149685619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14478748059809587065828317 5429530522428595149685619)
          ·
            refine ⟨8144295783642892724528429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429530522428595149685619 8144295783642892724528429)
            ·
              refine ⟨3054110918866084771698161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8144295783642892724528429 3054110918866084771698161)
              ·
                refine ⟨2290583189149563578773621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054110918866084771698161 2290583189149563578773621)
                ·
                  refine ⟨214742173982771585510027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290583189149563578773621 214742173982771585510027)
                  ·
                    rfl

theorem cell22_1881940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_1881940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1881940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1881940 prefixEnd_1881940 := by exact prefixLift 1881940
  have htrace : WordTrace (prefixWord ++ tailWord_1881940) baseStart_1881940 baseEnd_1881940 := by
    simpa [prefixWord, tailWord_1881940, baseEnd_1881940] using wordTrace_append hprefix tailTrace_1881940
  have hstable : (prefixWord ++ tailWord_1881940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1881940).length < 2 ^ (prefixWord ++ tailWord_1881940).sum := by decide
  have hdescent : baseEnd_1881940 < baseStart_1881940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1881940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882002 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1882002 : Nat := 118140960795 + 1882002 * 2 ^ 59
def prefixEnd_1882002 : Nat := 4983230072969 + 3 ^ 40 * 1882002 * 2
def baseEnd_1882002 : Nat := 214749248605122420493297

theorem tailTrace_1882002 : CollatzResearch.WordTrace tailWord_1882002 prefixEnd_1882002 214749248605122420493297 := by
  unfold tailWord_1882002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17160563031958912299282065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45761501418557099464752173 17160563031958912299282065)
  ·
    refine ⟨12870422273969184224461549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17160563031958912299282065 12870422273969184224461549)
    ·
      refine ⟨4826408352738444084173081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12870422273969184224461549 4826408352738444084173081)
      ·
        refine ⟨3619806264553833063129811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4826408352738444084173081 3619806264553833063129811)
        ·
          refine ⟨5429709396830749594694717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619806264553833063129811 5429709396830749594694717)
          ·
            refine ⟨2036141023811531098010519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5429709396830749594694717 2036141023811531098010519)
            ·
              refine ⟨3054211535717296647015779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036141023811531098010519 3054211535717296647015779)
              ·
                refine ⟨4581317303575944970523669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054211535717296647015779 4581317303575944970523669)
                ·
                  refine ⟨214749248605122420493297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4581317303575944970523669 214749248605122420493297)
                  ·
                    rfl

theorem cell22_1882002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1882002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882002 prefixEnd_1882002 := by exact prefixLift 1882002
  have htrace : WordTrace (prefixWord ++ tailWord_1882002) baseStart_1882002 baseEnd_1882002 := by
    simpa [prefixWord, tailWord_1882002, baseEnd_1882002] using wordTrace_append hprefix tailTrace_1882002
  have hstable : (prefixWord ++ tailWord_1882002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882002).length < 2 ^ (prefixWord ++ tailWord_1882002).sum := by decide
  have hdescent : baseEnd_1882002 < baseStart_1882002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882013 : List Nat := [1, 4, 2, 1, 2, 2, 1, 9]
def baseStart_1882013 : Nat := 118140960795 + 1882013 * 2 ^ 59
def prefixEnd_1882013 : Nat := 4983230072969 + 3 ^ 40 * 1882013 * 2
def baseEnd_1882013 : Nat := 71583501260018544383873

theorem tailTrace_1882013 : CollatzResearch.WordTrace tailWord_1882013 prefixEnd_1882013 71583501260018544383873 := by
  unfold tailWord_1882013
  simp only [CollatzResearch.WordTrace]
  refine ⟨68642653330795798075778693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45761768887197198717185795 68642653330795798075778693)
  ·
    refine ⟨12870497499524212139208505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68642653330795798075778693 12870497499524212139208505)
    ·
      refine ⟨9652873124643159104406379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12870497499524212139208505 9652873124643159104406379)
      ·
        refine ⟨14479309686964738656609569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652873124643159104406379 14479309686964738656609569)
        ·
          refine ⟨10859482265223553992457177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14479309686964738656609569 10859482265223553992457177)
          ·
            refine ⟨8144611698917665494342883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10859482265223553992457177 8144611698917665494342883)
            ·
              refine ⟨12216917548376498241514325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8144611698917665494342883 12216917548376498241514325)
              ·
                refine ⟨71583501260018544383873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12216917548376498241514325 71583501260018544383873)
                ·
                  rfl

theorem cell22_1882013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 9].length) (baseStart_1882013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882013 prefixEnd_1882013 := by exact prefixLift 1882013
  have htrace : WordTrace (prefixWord ++ tailWord_1882013) baseStart_1882013 baseEnd_1882013 := by
    simpa [prefixWord, tailWord_1882013, baseEnd_1882013] using wordTrace_append hprefix tailTrace_1882013
  have hstable : (prefixWord ++ tailWord_1882013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882013).length < 2 ^ (prefixWord ++ tailWord_1882013).sum := by decide
  have hdescent : baseEnd_1882013 < baseStart_1882013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882058 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_1882058 : Nat := 118140960795 + 1882058 * 2 ^ 59
def prefixEnd_1882058 : Nat := 4983230072969 + 3 ^ 40 * 1882058 * 2
def baseEnd_1882058 : Nat := 214755638586600594026573

theorem tailTrace_1882058 : CollatzResearch.WordTrace tailWord_1882058 prefixEnd_1882058 214755638586600594026573 := by
  unfold tailWord_1882058
  simp only [CollatzResearch.WordTrace]
  refine ⟨17161073653908192690291707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45762863077088513840777885 17161073653908192690291707)
  ·
    refine ⟨25741610480862289035437561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17161073653908192690291707 25741610480862289035437561)
    ·
      refine ⟨19306207860646716776578171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25741610480862289035437561 19306207860646716776578171)
      ·
        refine ⟨28959311790970075164867257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19306207860646716776578171 28959311790970075164867257)
        ·
          refine ⟨21719483843227556373650443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28959311790970075164867257 21719483843227556373650443)
          ·
            refine ⟨32579225764841334560475665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21719483843227556373650443 32579225764841334560475665)
            ·
              refine ⟨24434419323631000920356749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32579225764841334560475665 24434419323631000920356749)
              ·
                refine ⟨9162907246361625345133781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24434419323631000920356749 9162907246361625345133781)
                ·
                  refine ⟨214755638586600594026573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9162907246361625345133781 214755638586600594026573)
                  ·
                    rfl

theorem cell22_1882058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_1882058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882058 prefixEnd_1882058 := by exact prefixLift 1882058
  have htrace : WordTrace (prefixWord ++ tailWord_1882058) baseStart_1882058 baseEnd_1882058 := by
    simpa [prefixWord, tailWord_1882058, baseEnd_1882058] using wordTrace_append hprefix tailTrace_1882058
  have hstable : (prefixWord ++ tailWord_1882058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882058).length < 2 ^ (prefixWord ++ tailWord_1882058).sum := by decide
  have hdescent : baseEnd_1882058 < baseStart_1882058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882120 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 6]
def baseStart_1882120 : Nat := 118140960795 + 1882120 * 2 ^ 59
def prefixEnd_1882120 : Nat := 4983230072969 + 3 ^ 40 * 1882120 * 2
def baseEnd_1882120 : Nat := 214762713208951429009843

theorem tailTrace_1882120 : CollatzResearch.WordTrace tailWord_1882120 prefixEnd_1882120 214762713208951429009843 := by
  unfold tailWord_1882120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34323277970704077674961907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45764370627605436899949209 34323277970704077674961907)
  ·
    refine ⟨51484916956056116512442861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34323277970704077674961907 51484916956056116512442861)
    ·
      refine ⟨19306843858521043692166073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51484916956056116512442861 19306843858521043692166073)
      ·
        refine ⟨14480132893890782769124555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19306843858521043692166073 14480132893890782769124555)
        ·
          refine ⟨21720199340836174153686833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14480132893890782769124555 21720199340836174153686833)
          ·
            refine ⟨16290149505627130615265125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21720199340836174153686833 16290149505627130615265125)
            ·
              refine ⟨3054403032305086990362211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16290149505627130615265125 3054403032305086990362211)
              ·
                refine ⟨4581604548457630485543317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054403032305086990362211 4581604548457630485543317)
                ·
                  refine ⟨214762713208951429009843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4581604548457630485543317 214762713208951429009843)
                  ·
                    rfl

theorem cell22_1882120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_1882120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882120 prefixEnd_1882120 := by exact prefixLift 1882120
  have htrace : WordTrace (prefixWord ++ tailWord_1882120) baseStart_1882120 baseEnd_1882120 := by
    simpa [prefixWord, tailWord_1882120, baseEnd_1882120] using wordTrace_append hprefix tailTrace_1882120
  have hstable : (prefixWord ++ tailWord_1882120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882120).length < 2 ^ (prefixWord ++ tailWord_1882120).sum := by decide
  have hdescent : baseEnd_1882120 < baseStart_1882120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882154 : List Nat := [3, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_1882154 : Nat := 118140960795 + 1882154 * 2 ^ 59
def prefixEnd_1882154 : Nat := 4983230072969 + 3 ^ 40 * 1882154 * 2
def baseEnd_1882154 : Nat := 214766592840563177226475

theorem tailTrace_1882154 : CollatzResearch.WordTrace tailWord_1882154 prefixEnd_1882154 214766592840563177226475 := by
  unfold tailWord_1882154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17161949005821244789165379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45765197348856652771107677 17161949005821244789165379)
  ·
    refine ⟨25742923508731867183748069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17161949005821244789165379 25742923508731867183748069)
    ·
      refine ⟨4826798157887225096952763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25742923508731867183748069 4826798157887225096952763)
      ·
        refine ⟨7240197236830837645429145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826798157887225096952763 7240197236830837645429145)
        ·
          refine ⟨5430147927623128234071859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7240197236830837645429145 5430147927623128234071859)
          ·
            refine ⟨8145221891434692351107789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430147927623128234071859 8145221891434692351107789)
            ·
              refine ⟨3054458209288009631665421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8145221891434692351107789 3054458209288009631665421)
              ·
                refine ⟨1145421828483003611874533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3054458209288009631665421 1145421828483003611874533)
                ·
                  refine ⟨214766592840563177226475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145421828483003611874533 214766592840563177226475)
                  ·
                    rfl

theorem cell22_1882154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_1882154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882154 prefixEnd_1882154 := by exact prefixLift 1882154
  have htrace : WordTrace (prefixWord ++ tailWord_1882154) baseStart_1882154 baseEnd_1882154 := by
    simpa [prefixWord, tailWord_1882154, baseEnd_1882154] using wordTrace_append hprefix tailTrace_1882154
  have hstable : (prefixWord ++ tailWord_1882154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882154).length < 2 ^ (prefixWord ++ tailWord_1882154).sum := by decide
  have hdescent : baseEnd_1882154 < baseStart_1882154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882225 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1882225 : Nat := 118140960795 + 1882225 * 2 ^ 59
def prefixEnd_1882225 : Nat := 4983230072969 + 3 ^ 40 * 1882225 * 2
def baseEnd_1882225 : Nat := 644324083272669013154207

theorem tailTrace_1882225 : CollatzResearch.WordTrace tailWord_1882225 prefixEnd_1882225 644324083272669013154207 := by
  unfold tailWord_1882225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68650385606027758282496129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45766923737351838854997419 68650385606027758282496129)
  ·
    refine ⟨51487789204520818711872097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68650385606027758282496129 51487789204520818711872097)
    ·
      refine ⟨38615841903390614033904073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51487789204520818711872097 38615841903390614033904073)
      ·
        refine ⟨28961881427542960525428055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38615841903390614033904073 28961881427542960525428055)
        ·
          refine ⟨43442822141314440788142083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28961881427542960525428055 43442822141314440788142083)
          ·
            refine ⟨65164233211971661182213125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43442822141314440788142083 65164233211971661182213125)
            ·
              refine ⟨12218293727244686471664961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65164233211971661182213125 12218293727244686471664961)
              ·
                refine ⟨9163720295433514853748721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12218293727244686471664961 9163720295433514853748721)
                ·
                  refine ⟨6872790221575136140311541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9163720295433514853748721 6872790221575136140311541)
                  ·
                    refine ⟨644324083272669013154207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6872790221575136140311541 644324083272669013154207)
                    ·
                      rfl

theorem cell22_1882225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1882225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882225 prefixEnd_1882225 := by exact prefixLift 1882225
  have htrace : WordTrace (prefixWord ++ tailWord_1882225) baseStart_1882225 baseEnd_1882225 := by
    simpa [prefixWord, tailWord_1882225, baseEnd_1882225] using wordTrace_append hprefix tailTrace_1882225
  have hstable : (prefixWord ++ tailWord_1882225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882225).length < 2 ^ (prefixWord ++ tailWord_1882225).sum := by decide
  have hdescent : baseEnd_1882225 < baseStart_1882225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882231 : List Nat := [1, 1, 3, 1, 1, 5, 4, 2, 1, 3]
def baseStart_1882231 : Nat := 118140960795 + 1882231 * 2 ^ 59
def prefixEnd_1882231 : Nat := 4983230072969 + 3 ^ 40 * 1882231 * 2
def baseEnd_1882231 : Nat := 644326137195286997504189

theorem tailTrace_1882231 : CollatzResearch.WordTrace tailWord_1882231 prefixEnd_1882231 644326137195286997504189 := by
  unfold tailWord_1882231
  simp only [CollatzResearch.WordTrace]
  refine ⟨68650604444006021307214547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45767069629337347538143031 68650604444006021307214547)
  ·
    refine ⟨102975906666009031960821821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68650604444006021307214547 102975906666009031960821821)
    ·
      refine ⟨38615964999753386985308183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102975906666009031960821821 38615964999753386985308183)
      ·
        refine ⟨57923947499630080477962275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38615964999753386985308183 57923947499630080477962275)
        ·
          refine ⟨86885921249445120716943413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57923947499630080477962275 86885921249445120716943413)
          ·
            refine ⟨8145555117135480067213445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86885921249445120716943413 8145555117135480067213445)
            ·
              refine ⟨1527291584462902512602521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8145555117135480067213445 1527291584462902512602521)
              ·
                refine ⟨1145468688347176884451891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527291584462902512602521 1145468688347176884451891)
                ·
                  refine ⟨1718203032520765326677837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145468688347176884451891 1718203032520765326677837)
                  ·
                    refine ⟨644326137195286997504189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718203032520765326677837 644326137195286997504189)
                    ·
                      rfl

theorem cell22_1882231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_1882231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882231 prefixEnd_1882231 := by exact prefixLift 1882231
  have htrace : WordTrace (prefixWord ++ tailWord_1882231) baseStart_1882231 baseEnd_1882231 := by
    simpa [prefixWord, tailWord_1882231, baseEnd_1882231] using wordTrace_append hprefix tailTrace_1882231
  have hstable : (prefixWord ++ tailWord_1882231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882231).length < 2 ^ (prefixWord ++ tailWord_1882231).sum := by decide
  have hdescent : baseEnd_1882231 < baseStart_1882231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882289 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 6]
def baseStart_1882289 : Nat := 118140960795 + 1882289 * 2 ^ 59
def prefixEnd_1882289 : Nat := 4983230072969 + 3 ^ 40 * 1882289 * 2
def baseEnd_1882289 : Nat := 214781997260198059851337

theorem tailTrace_1882289 : CollatzResearch.WordTrace tailWord_1882289 prefixEnd_1882289 214781997260198059851337 := by
  unfold tailWord_1882289
  simp only [CollatzResearch.WordTrace]
  refine ⟨68652719877795897212825921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45768479918530598141883947 68652719877795897212825921)
  ·
    refine ⟨51489539908346922909619441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68652719877795897212825921 51489539908346922909619441)
    ·
      refine ⟨38617154931260192182214581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51489539908346922909619441 38617154931260192182214581)
      ·
        refine ⟨3620358274805643017082617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38617154931260192182214581 3620358274805643017082617)
        ·
          refine ⟨2715268706104232262811963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620358274805643017082617 2715268706104232262811963)
          ·
            refine ⟨4072903059156348394217945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715268706104232262811963 4072903059156348394217945)
            ·
              refine ⟨3054677294367261295663459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072903059156348394217945 3054677294367261295663459)
              ·
                refine ⟨4582015941550891943495189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054677294367261295663459 4582015941550891943495189)
                ·
                  refine ⟨214781997260198059851337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4582015941550891943495189 214781997260198059851337)
                  ·
                    rfl

theorem cell22_1882289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_1882289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882289 prefixEnd_1882289 := by exact prefixLift 1882289
  have htrace : WordTrace (prefixWord ++ tailWord_1882289) baseStart_1882289 baseEnd_1882289 := by
    simpa [prefixWord, tailWord_1882289, baseEnd_1882289] using wordTrace_append hprefix tailTrace_1882289
  have hstable : (prefixWord ++ tailWord_1882289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882289).length < 2 ^ (prefixWord ++ tailWord_1882289).sum := by decide
  have hdescent : baseEnd_1882289 < baseStart_1882289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882304 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 1, 5]
def baseStart_1882304 : Nat := 118140960795 + 1882304 * 2 ^ 59
def prefixEnd_1882304 : Nat := 4983230072969 + 3 ^ 40 * 1882304 * 2
def baseEnd_1882304 : Nat := 644351126587139140428965

theorem tailTrace_1882304 : CollatzResearch.WordTrace tailWord_1882304 prefixEnd_1882304 644351126587139140428965 := by
  unfold tailWord_1882304
  simp only [CollatzResearch.WordTrace]
  refine ⟨34326633486370777387310983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45768844648494369849747977 34326633486370777387310983)
  ·
    refine ⟨51489950229556166080966475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34326633486370777387310983 51489950229556166080966475)
    ·
      refine ⟨77234925344334249121449713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51489950229556166080966475 77234925344334249121449713)
      ·
        refine ⟨57926194008250686841087285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77234925344334249121449713 57926194008250686841087285)
        ·
          refine ⟨5430580688273501891351933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57926194008250686841087285 5430580688273501891351933)
          ·
            refine ⟨2036467758102563209256975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5430580688273501891351933 2036467758102563209256975)
            ·
              refine ⟨3054701637153844813885463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036467758102563209256975 3054701637153844813885463)
              ·
                refine ⟨4582052455730767220828195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054701637153844813885463 4582052455730767220828195)
                ·
                  refine ⟨6873078683596150831242293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582052455730767220828195 6873078683596150831242293)
                  ·
                    refine ⟨644351126587139140428965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6873078683596150831242293 644351126587139140428965)
                    ·
                      rfl

theorem cell22_1882304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_1882304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882304 prefixEnd_1882304 := by exact prefixLift 1882304
  have htrace : WordTrace (prefixWord ++ tailWord_1882304) baseStart_1882304 baseEnd_1882304 := by
    simpa [prefixWord, tailWord_1882304, baseEnd_1882304] using wordTrace_append hprefix tailTrace_1882304
  have hstable : (prefixWord ++ tailWord_1882304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882304).length < 2 ^ (prefixWord ++ tailWord_1882304).sum := by decide
  have hdescent : baseEnd_1882304 < baseStart_1882304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882306 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1882306 : Nat := 118140960795 + 1882306 * 2 ^ 59
def prefixEnd_1882306 : Nat := 4983230072969 + 3 ^ 40 * 1882306 * 2
def baseEnd_1882306 : Nat := 214783937076003933959653

theorem tailTrace_1882306 : CollatzResearch.WordTrace tailWord_1882306 prefixEnd_1882306 214783937076003933959653 := by
  unfold tailWord_1882306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17163334979683577279048693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45768893279156206077463181 17163334979683577279048693)
  ·
    refine ⟨1609062654345335369910815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17163334979683577279048693 1609062654345335369910815)
    ·
      refine ⟨2413593981518003054866223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1609062654345335369910815 2413593981518003054866223)
      ·
        refine ⟨3620390972277004582299335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413593981518003054866223 3620390972277004582299335)
        ·
          refine ⟨5430586458415506873449003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620390972277004582299335 5430586458415506873449003)
          ·
            refine ⟨8145879687623260310173505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430586458415506873449003 8145879687623260310173505)
            ·
              refine ⟨6109409765717445232630129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145879687623260310173505 6109409765717445232630129)
              ·
                refine ⟨4582057324288083924472597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109409765717445232630129 4582057324288083924472597)
                ·
                  refine ⟨214783937076003933959653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4582057324288083924472597 214783937076003933959653)
                  ·
                    rfl

theorem cell22_1882306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1882306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882306 prefixEnd_1882306 := by exact prefixLift 1882306
  have htrace : WordTrace (prefixWord ++ tailWord_1882306) baseStart_1882306 baseEnd_1882306 := by
    simpa [prefixWord, tailWord_1882306, baseEnd_1882306] using wordTrace_append hprefix tailTrace_1882306
  have hstable : (prefixWord ++ tailWord_1882306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882306).length < 2 ^ (prefixWord ++ tailWord_1882306).sum := by decide
  have hdescent : baseEnd_1882306 < baseStart_1882306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882315 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 2, 7]
def baseStart_1882315 : Nat := 118140960795 + 1882315 * 2 ^ 59
def prefixEnd_1882315 : Nat := 4983230072969 + 3 ^ 40 * 1882315 * 2
def baseEnd_1882315 : Nat := 644354892111938778403931

theorem tailTrace_1882315 : CollatzResearch.WordTrace tailWord_1882315 prefixEnd_1882315 644354892111938778403931 := by
  unfold tailWord_1882315
  simp only [CollatzResearch.WordTrace]
  refine ⟨68653668175701703653272399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45769112117134469102181599 68653668175701703653272399)
  ·
    refine ⟨102980502263552555479908599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68653668175701703653272399 102980502263552555479908599)
    ·
      refine ⟨154470753395328833219862899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102980502263552555479908599 154470753395328833219862899)
      ·
        refine ⟨231706130092993249829794349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154470753395328833219862899 231706130092993249829794349)
        ·
          refine ⟨86889798784872468686172881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231706130092993249829794349 86889798784872468686172881)
          ·
            refine ⟨65167349088654351514629661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86889798784872468686172881 65167349088654351514629661)
            ·
              refine ⟨24437755908245381817986123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65167349088654351514629661 24437755908245381817986123)
              ·
                refine ⟨36656633862368072726979185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24437755908245381817986123 36656633862368072726979185)
                ·
                  refine ⟨27492475396776054545234389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36656633862368072726979185 27492475396776054545234389)
                  ·
                    refine ⟨644354892111938778403931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27492475396776054545234389 644354892111938778403931)
                    ·
                      rfl

theorem cell22_1882315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_1882315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882315 prefixEnd_1882315 := by exact prefixLift 1882315
  have htrace : WordTrace (prefixWord ++ tailWord_1882315) baseStart_1882315 baseEnd_1882315 := by
    simpa [prefixWord, tailWord_1882315, baseEnd_1882315] using wordTrace_append hprefix tailTrace_1882315
  have hstable : (prefixWord ++ tailWord_1882315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882315).length < 2 ^ (prefixWord ++ tailWord_1882315).sum := by decide
  have hdescent : baseEnd_1882315 < baseStart_1882315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882400 : List Nat := [2, 1, 1, 5, 2, 3, 2, 2, 1, 3]
def baseStart_1882400 : Nat := 118140960795 + 1882400 * 2 ^ 59
def prefixEnd_1882400 : Nat := 4983230072969 + 3 ^ 40 * 1882400 * 2
def baseEnd_1882400 : Nat := 644383989349026890028671

theorem tailTrace_1882400 : CollatzResearch.WordTrace tailWord_1882400 prefixEnd_1882400 644383989349026890028671 := by
  unfold tailWord_1882400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34328384190196881585058327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45771178920262508780077769 34328384190196881585058327)
  ·
    refine ⟨51492576285295322377587491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34328384190196881585058327 51492576285295322377587491)
    ·
      refine ⟨77238864427942983566381237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51492576285295322377587491 77238864427942983566381237)
      ·
        refine ⟨7241143540119654709348241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77238864427942983566381237 7241143540119654709348241)
        ·
          refine ⟨5430857655089741032011181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7241143540119654709348241 5430857655089741032011181)
          ·
            refine ⟨2036571620658652887004193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5430857655089741032011181 2036571620658652887004193)
            ·
              refine ⟨1527428715493989665253145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036571620658652887004193 1527428715493989665253145)
              ·
                refine ⟨1145571536620492248939859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527428715493989665253145 1145571536620492248939859)
                ·
                  refine ⟨1718357304930738373409789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1145571536620492248939859 1718357304930738373409789)
                  ·
                    refine ⟨644383989349026890028671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718357304930738373409789 644383989349026890028671)
                    ·
                      rfl

theorem cell22_1882400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 3].length) (baseStart_1882400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882400 prefixEnd_1882400 := by exact prefixLift 1882400
  have htrace : WordTrace (prefixWord ++ tailWord_1882400) baseStart_1882400 baseEnd_1882400 := by
    simpa [prefixWord, tailWord_1882400, baseEnd_1882400] using wordTrace_append hprefix tailTrace_1882400
  have hstable : (prefixWord ++ tailWord_1882400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882400).length < 2 ^ (prefixWord ++ tailWord_1882400).sum := by decide
  have hdescent : baseEnd_1882400 < baseStart_1882400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882439 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1882439 : Nat := 118140960795 + 1882439 * 2 ^ 59
def prefixEnd_1882439 : Nat := 4983230072969 + 3 ^ 40 * 1882439 * 2
def baseEnd_1882439 : Nat := 644397339846043788303551

theorem tailTrace_1882439 : CollatzResearch.WordTrace tailWord_1882439 prefixEnd_1882439 644397339846043788303551 := by
  unfold tailWord_1882439
  simp only [CollatzResearch.WordTrace]
  refine ⟨68658190827252472830786371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45772127218168315220524247 68658190827252472830786371)
  ·
    refine ⟨102987286240878709246179557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68658190827252472830786371 102987286240878709246179557)
    ·
      refine ⟨19310116170164757983658667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102987286240878709246179557 19310116170164757983658667)
      ·
        refine ⟨28965174255247136975488001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19310116170164757983658667 28965174255247136975488001)
        ·
          refine ⟨21723880691435352731616001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28965174255247136975488001 21723880691435352731616001)
          ·
            refine ⟨16292910518576514548712001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21723880691435352731616001 16292910518576514548712001)
            ·
              refine ⟨12219682888932385911534001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16292910518576514548712001 12219682888932385911534001)
              ·
                refine ⟨9164762166699289433650501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12219682888932385911534001 9164762166699289433650501)
                ·
                  refine ⟨1718392906256116768809469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9164762166699289433650501 1718392906256116768809469)
                  ·
                    refine ⟨644397339846043788303551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718392906256116768809469 644397339846043788303551)
                    ·
                      rfl

theorem cell22_1882439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1882439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882439 prefixEnd_1882439 := by exact prefixLift 1882439
  have htrace : WordTrace (prefixWord ++ tailWord_1882439) baseStart_1882439 baseEnd_1882439 := by
    simpa [prefixWord, tailWord_1882439, baseEnd_1882439] using wordTrace_append hprefix tailTrace_1882439
  have hstable : (prefixWord ++ tailWord_1882439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882439).length < 2 ^ (prefixWord ++ tailWord_1882439).sum := by decide
  have hdescent : baseEnd_1882439 < baseStart_1882439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882512 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_1882512 : Nat := 118140960795 + 1882512 * 2 ^ 59
def prefixEnd_1882512 : Nat := 4983230072969 + 3 ^ 40 * 1882512 * 2
def baseEnd_1882512 : Nat := 644422329237895931228327

theorem tailTrace_1882512 : CollatzResearch.WordTrace tailWord_1882512 prefixEnd_1882512 644422329237895931228327 := by
  unfold tailWord_1882512
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330426677994003149096895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45773902237325337532129193 34330426677994003149096895)
  ·
    refine ⟨51495640016991004723645343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34330426677994003149096895 51495640016991004723645343)
    ·
      refine ⟨77243460025486507085468015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51495640016991004723645343 77243460025486507085468015)
      ·
        refine ⟨115865190038229760628202023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77243460025486507085468015 115865190038229760628202023)
        ·
          refine ⟨173797785057344640942303035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115865190038229760628202023 173797785057344640942303035)
          ·
            refine ⟨260696677586016961413454553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173797785057344640942303035 260696677586016961413454553)
            ·
              refine ⟨195522508189512721060090915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260696677586016961413454553 195522508189512721060090915)
              ·
                refine ⟨293283762284269081590136373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195522508189512721060090915 293283762284269081590136373)
                ·
                  refine ⟨27495352714150226399075285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293283762284269081590136373 27495352714150226399075285)
                  ·
                    refine ⟨644422329237895931228327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27495352714150226399075285 644422329237895931228327)
                    ·
                      rfl

theorem cell22_1882512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_1882512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882512 prefixEnd_1882512 := by exact prefixLift 1882512
  have htrace : WordTrace (prefixWord ++ tailWord_1882512) baseStart_1882512 baseEnd_1882512 := by
    simpa [prefixWord, tailWord_1882512, baseEnd_1882512] using wordTrace_append hprefix tailTrace_1882512
  have hstable : (prefixWord ++ tailWord_1882512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882512).length < 2 ^ (prefixWord ++ tailWord_1882512).sum := by decide
  have hdescent : baseEnd_1882512 < baseStart_1882512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882531 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 5]
def baseStart_1882531 : Nat := 118140960795 + 1882531 * 2 ^ 59
def prefixEnd_1882531 : Nat := 4983230072969 + 3 ^ 40 * 1882531 * 2
def baseEnd_1882531 : Nat := 214809611108728738334423

theorem tailTrace_1882531 : CollatzResearch.WordTrace tailWord_1882531 prefixEnd_1882531 214809611108728738334423 := by
  unfold tailWord_1882531
  simp only [CollatzResearch.WordTrace]
  refine ⟨68661546342919172543135447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45774364228612781695423631 68661546342919172543135447)
  ·
    refine ⟨102992319514378758814703171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68661546342919172543135447 102992319514378758814703171)
    ·
      refine ⟨154488479271568138222054757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102992319514378758814703171 154488479271568138222054757)
      ·
        refine ⟨28966589863419025916635267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154488479271568138222054757 28966589863419025916635267)
        ·
          refine ⟨43449884795128538874952901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28966589863419025916635267 43449884795128538874952901)
          ·
            refine ⟨8146853399086601039053669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43449884795128538874952901 8146853399086601039053669)
            ·
              refine ⟨1527535012328737694822563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8146853399086601039053669 1527535012328737694822563)
              ·
                refine ⟨2291302518493106542233845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527535012328737694822563 2291302518493106542233845)
                ·
                  refine ⟨214809611108728738334423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291302518493106542233845 214809611108728738334423)
                  ·
                    rfl

theorem cell22_1882531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 5].length) (baseStart_1882531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882531 prefixEnd_1882531 := by exact prefixLift 1882531
  have htrace : WordTrace (prefixWord ++ tailWord_1882531) baseStart_1882531 baseEnd_1882531 := by
    simpa [prefixWord, tailWord_1882531, baseEnd_1882531] using wordTrace_append hprefix tailTrace_1882531
  have hstable : (prefixWord ++ tailWord_1882531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882531).length < 2 ^ (prefixWord ++ tailWord_1882531).sum := by decide
  have hdescent : baseEnd_1882531 < baseStart_1882531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882574 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1882574 : Nat := 118140960795 + 1882574 * 2 ^ 59
def prefixEnd_1882574 : Nat := 4983230072969 + 3 ^ 40 * 1882574 * 2
def baseEnd_1882574 : Nat := 644443553104948436178137

theorem tailTrace_1882574 : CollatzResearch.WordTrace tailWord_1882574 prefixEnd_1882574 644443553104948436178137 := by
  unfold tailWord_1882574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582889335220423860868847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45775409787842260591300517 8582889335220423860868847)
  ·
    refine ⟨12874334002830635791303271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8582889335220423860868847 12874334002830635791303271)
    ·
      refine ⟨19311501004245953686954907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12874334002830635791303271 19311501004245953686954907)
      ·
        refine ⟨28967251506368930530432361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19311501004245953686954907 28967251506368930530432361)
        ·
          refine ⟨21725438629776697897824271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28967251506368930530432361 21725438629776697897824271)
          ·
            refine ⟨32588157944665046846736407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21725438629776697897824271 32588157944665046846736407)
            ·
              refine ⟨48882236916997570270104611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32588157944665046846736407 48882236916997570270104611)
              ·
                refine ⟨73323355375496355405156917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48882236916997570270104611 73323355375496355405156917)
                ·
                  refine ⟨6874064566452783319233461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73323355375496355405156917 6874064566452783319233461)
                  ·
                    refine ⟨644443553104948436178137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6874064566452783319233461 644443553104948436178137)
                    ·
                      rfl

theorem cell22_1882574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1882574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882574 prefixEnd_1882574 := by exact prefixLift 1882574
  have htrace : WordTrace (prefixWord ++ tailWord_1882574) baseStart_1882574 baseEnd_1882574 := by
    simpa [prefixWord, tailWord_1882574, baseEnd_1882574] using wordTrace_append hprefix tailTrace_1882574
  have hstable : (prefixWord ++ tailWord_1882574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882574).length < 2 ^ (prefixWord ++ tailWord_1882574).sum := by decide
  have hdescent : baseEnd_1882574 < baseStart_1882574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882591 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 1, 5]
def baseStart_1882591 : Nat := 118140960795 + 1882591 * 2 ^ 59
def prefixEnd_1882591 : Nat := 4983230072969 + 3 ^ 40 * 1882591 * 2
def baseEnd_1882591 : Nat := 644449372552366058503085

theorem tailTrace_1882591 : CollatzResearch.WordTrace tailWord_1882591 prefixEnd_1882591 644449372552366058503085 := by
  unfold tailWord_1882591
  simp only [CollatzResearch.WordTrace]
  refine ⟨68663734722701802790319627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45775823148467868526879751 68663734722701802790319627)
  ·
    refine ⟨102995602084052704185479441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68663734722701802790319627 102995602084052704185479441)
    ·
      refine ⟨77246701563039528139109581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102995602084052704185479441 77246701563039528139109581)
      ·
        refine ⟨28967513086139823052166093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77246701563039528139109581 28967513086139823052166093)
        ·
          refine ⟨10862817407302433644562285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28967513086139823052166093 10862817407302433644562285)
          ·
            refine ⟨4073556527738412616710857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10862817407302433644562285 4073556527738412616710857)
            ·
              refine ⟨3055167395803809462533143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073556527738412616710857 3055167395803809462533143)
              ·
                refine ⟨4582751093705714193799715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055167395803809462533143 4582751093705714193799715)
                ·
                  refine ⟨6874126640558571290699573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582751093705714193799715 6874126640558571290699573)
                  ·
                    refine ⟨644449372552366058503085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6874126640558571290699573 644449372552366058503085)
                    ·
                      rfl

theorem cell22_1882591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_1882591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882591 prefixEnd_1882591 := by exact prefixLift 1882591
  have htrace : WordTrace (prefixWord ++ tailWord_1882591) baseStart_1882591 baseEnd_1882591 := by
    simpa [prefixWord, tailWord_1882591, baseEnd_1882591] using wordTrace_append hprefix tailTrace_1882591
  have hstable : (prefixWord ++ tailWord_1882591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882591).length < 2 ^ (prefixWord ++ tailWord_1882591).sum := by decide
  have hdescent : baseEnd_1882591 < baseStart_1882591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882606 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1882606 : Nat := 118140960795 + 1882606 * 2 ^ 59
def prefixEnd_1882606 : Nat := 4983230072969 + 3 ^ 40 * 1882606 * 2
def baseEnd_1882606 : Nat := 644454507358911019378039

theorem tailTrace_1882606 : CollatzResearch.WordTrace tailWord_1882606 prefixEnd_1882606 644454507358911019378039 := by
  unfold tailWord_1882606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8583035227205932544014459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45776187878431640234743781 8583035227205932544014459)
  ·
    refine ⟨12874552840808898816021689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8583035227205932544014459 12874552840808898816021689)
    ·
      refine ⟨9655914630606674112016267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12874552840808898816021689 9655914630606674112016267)
      ·
        refine ⟨14483871945910011168024401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9655914630606674112016267 14483871945910011168024401)
        ·
          refine ⟨10862903959432508376018301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14483871945910011168024401 10862903959432508376018301)
          ·
            refine ⟨4073588984787190641006863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10862903959432508376018301 4073588984787190641006863)
            ·
              refine ⟨6110383477180785961510295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073588984787190641006863 6110383477180785961510295)
              ·
                refine ⟨9165575215771178942265443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110383477180785961510295 9165575215771178942265443)
                ·
                  refine ⟨13748362823656768413398165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165575215771178942265443 13748362823656768413398165)
                  ·
                    refine ⟨644454507358911019378039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13748362823656768413398165 644454507358911019378039)
                    ·
                      rfl

theorem cell22_1882606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1882606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882606 prefixEnd_1882606 := by exact prefixLift 1882606
  have htrace : WordTrace (prefixWord ++ tailWord_1882606) baseStart_1882606 baseEnd_1882606 := by
    simpa [prefixWord, tailWord_1882606, baseEnd_1882606] using wordTrace_append hprefix tailTrace_1882606
  have hstable : (prefixWord ++ tailWord_1882606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882606).length < 2 ^ (prefixWord ++ tailWord_1882606).sum := by decide
  have hdescent : baseEnd_1882606 < baseStart_1882606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882610 : List Nat := [3, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1882610 : Nat := 118140960795 + 1882610 * 2 ^ 59
def prefixEnd_1882610 : Nat := 4983230072969 + 3 ^ 40 * 1882610 * 2
def baseEnd_1882610 : Nat := 214818625546885447426009

theorem tailTrace_1882610 : CollatzResearch.WordTrace tailWord_1882610 prefixEnd_1882610 214818625546885447426009 := by
  unfold tailWord_1882610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166106927408242258815321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45776285139755312690174189 17166106927408242258815321)
  ·
    refine ⟨12874580195556181694111491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17166106927408242258815321 12874580195556181694111491)
    ·
      refine ⟨19311870293334272541167237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12874580195556181694111491 19311870293334272541167237)
      ·
        refine ⟨3620975680000176101468857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19311870293334272541167237 3620975680000176101468857)
        ·
          refine ⟨2715731760000132076101643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620975680000176101468857 2715731760000132076101643)
          ·
            refine ⟨4073597640000198114152465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715731760000132076101643 4073597640000198114152465)
            ·
              refine ⟨3055198230000148585614349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073597640000198114152465 3055198230000148585614349)
              ·
                refine ⟨1145699336250055719605381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3055198230000148585614349 1145699336250055719605381)
                ·
                  refine ⟨214818625546885447426009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145699336250055719605381 214818625546885447426009)
                  ·
                    rfl

theorem cell22_1882610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1882610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882610 prefixEnd_1882610 := by exact prefixLift 1882610
  have htrace : WordTrace (prefixWord ++ tailWord_1882610) baseStart_1882610 baseEnd_1882610 := by
    simpa [prefixWord, tailWord_1882610, baseEnd_1882610] using wordTrace_append hprefix tailTrace_1882610
  have hstable : (prefixWord ++ tailWord_1882610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882610).length < 2 ^ (prefixWord ++ tailWord_1882610).sum := by decide
  have hdescent : baseEnd_1882610 < baseStart_1882610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882625 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1882625 : Nat := 118140960795 + 1882625 * 2 ^ 59
def prefixEnd_1882625 : Nat := 4983230072969 + 3 ^ 40 * 1882625 * 2
def baseEnd_1882625 : Nat := 644461011447201303152981

theorem tailTrace_1882625 : CollatzResearch.WordTrace tailWord_1882625 prefixEnd_1882625 644461011447201303152981 := by
  unfold tailWord_1882625
  simp only [CollatzResearch.WordTrace]
  refine ⟨68664974804578626597057329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45776649869719084398038219 68664974804578626597057329)
  ·
    refine ⟨51498731103433969947792997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68664974804578626597057329 51498731103433969947792997)
    ·
      refine ⟨9656012081893869365211187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51498731103433969947792997 9656012081893869365211187)
      ·
        refine ⟨14484018122840804047816781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9656012081893869365211187 14484018122840804047816781)
        ·
          refine ⟨5431506796065301517931293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14484018122840804047816781 5431506796065301517931293)
          ·
            refine ⟨2036815048524488069224235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5431506796065301517931293 2036815048524488069224235)
            ·
              refine ⟨3055222572786732103836353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036815048524488069224235 3055222572786732103836353)
              ·
                refine ⟨2291416929590049077877265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055222572786732103836353 2291416929590049077877265)
                ·
                  refine ⟨1718562697192536808407949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2291416929590049077877265 1718562697192536808407949)
                  ·
                    refine ⟨644461011447201303152981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718562697192536808407949 644461011447201303152981)
                    ·
                      rfl

theorem cell22_1882625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1882625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882625 prefixEnd_1882625 := by exact prefixLift 1882625
  have htrace : WordTrace (prefixWord ++ tailWord_1882625) baseStart_1882625 baseEnd_1882625 := by
    simpa [prefixWord, tailWord_1882625, baseEnd_1882625] using wordTrace_append hprefix tailTrace_1882625
  have hstable : (prefixWord ++ tailWord_1882625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882625).length < 2 ^ (prefixWord ++ tailWord_1882625).sum := by decide
  have hdescent : baseEnd_1882625 < baseStart_1882625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882653 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1882653 : Nat := 118140960795 + 1882653 * 2 ^ 59
def prefixEnd_1882653 : Nat := 4983230072969 + 3 ^ 40 * 1882653 * 2
def baseEnd_1882653 : Nat := 644470596419418563452895

theorem tailTrace_1882653 : CollatzResearch.WordTrace tailWord_1882653 prefixEnd_1882653 644470596419418563452895 := by
  unfold tailWord_1882653
  simp only [CollatzResearch.WordTrace]
  refine ⟨68665996048477187379076613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45777330698984791586051075 68665996048477187379076613)
  ·
    refine ⟨12874874259089472633576865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68665996048477187379076613 12874874259089472633576865)
    ·
      refine ⟨9656155694317104475182649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12874874259089472633576865 9656155694317104475182649)
      ·
        refine ⟨7242116770737828356386987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9656155694317104475182649 7242116770737828356386987)
        ·
          refine ⟨10863175156106742534580481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242116770737828356386987 10863175156106742534580481)
          ·
            refine ⟨8147381367080056900935361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10863175156106742534580481 8147381367080056900935361)
            ·
              refine ⟨6110536025310042675701521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8147381367080056900935361 6110536025310042675701521)
              ·
                refine ⟨4582902018982532006776141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6110536025310042675701521 4582902018982532006776141)
                ·
                  refine ⟨1718588257118449502541053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4582902018982532006776141 1718588257118449502541053)
                  ·
                    refine ⟨644470596419418563452895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718588257118449502541053 644470596419418563452895)
                    ·
                      rfl

theorem cell22_1882653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1882653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882653 prefixEnd_1882653 := by exact prefixLift 1882653
  have htrace : WordTrace (prefixWord ++ tailWord_1882653) baseStart_1882653 baseEnd_1882653 := by
    simpa [prefixWord, tailWord_1882653, baseEnd_1882653] using wordTrace_append hprefix tailTrace_1882653
  have hstable : (prefixWord ++ tailWord_1882653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882653).length < 2 ^ (prefixWord ++ tailWord_1882653).sum := by decide
  have hdescent : baseEnd_1882653 < baseStart_1882653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882666 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_1882666 : Nat := 118140960795 + 1882666 * 2 ^ 59
def prefixEnd_1882666 : Nat := 4983230072969 + 3 ^ 40 * 1882666 * 2
def baseEnd_1882666 : Nat := 214825015528363620959285

theorem tailTrace_1882666 : CollatzResearch.WordTrace tailWord_1882666 prefixEnd_1882666 214825015528363620959285 := by
  unfold tailWord_1882666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166617549357522649824963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45777646798286727066199901 17166617549357522649824963)
  ·
    refine ⟨25749926324036283974737445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17166617549357522649824963 25749926324036283974737445)
    ·
      refine ⟨4828111185756803245263271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25749926324036283974737445 4828111185756803245263271)
      ·
        refine ⟨7242166778635204867894907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828111185756803245263271 7242166778635204867894907)
        ·
          refine ⟨10863250167952807301842361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242166778635204867894907 10863250167952807301842361)
          ·
            refine ⟨8147437625964605476381771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10863250167952807301842361 8147437625964605476381771)
            ·
              refine ⟨12221156438946908214572657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8147437625964605476381771 12221156438946908214572657)
              ·
                refine ⟨9165867329210181160929493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12221156438946908214572657 9165867329210181160929493)
                ·
                  refine ⟨214825015528363620959285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9165867329210181160929493 214825015528363620959285)
                  ·
                    rfl

theorem cell22_1882666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_1882666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882666 prefixEnd_1882666 := by exact prefixLift 1882666
  have htrace : WordTrace (prefixWord ++ tailWord_1882666) baseStart_1882666 baseEnd_1882666 := by
    simpa [prefixWord, tailWord_1882666, baseEnd_1882666] using wordTrace_append hprefix tailTrace_1882666
  have hstable : (prefixWord ++ tailWord_1882666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882666).length < 2 ^ (prefixWord ++ tailWord_1882666).sum := by decide
  have hdescent : baseEnd_1882666 < baseStart_1882666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882730 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1882730 : Nat := 118140960795 + 1882730 * 2 ^ 59
def prefixEnd_1882730 : Nat := 4983230072969 + 3 ^ 40 * 1882730 * 2
def baseEnd_1882730 : Nat := 644496955093016029277659

theorem tailTrace_1882730 : CollatzResearch.WordTrace tailWord_1882730 prefixEnd_1882730 644496955093016029277659 := by
  unfold tailWord_1882730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17167201117299557382407411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45779202979465486353086429 17167201117299557382407411)
  ·
    refine ⟨25750801675949336073611117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17167201117299557382407411 25750801675949336073611117)
    ·
      refine ⟨9656550628481001027604169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25750801675949336073611117 9656550628481001027604169)
      ·
        refine ⟨7242412971360750770703127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9656550628481001027604169 7242412971360750770703127)
        ·
          refine ⟨10863619457041126156054691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242412971360750770703127 10863619457041126156054691)
          ·
            refine ⟨16295429185561689234082037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863619457041126156054691 16295429185561689234082037)
            ·
              refine ⟨1527696486146408365695191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16295429185561689234082037 1527696486146408365695191)
              ·
                refine ⟨2291544729219612548542787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527696486146408365695191 2291544729219612548542787)
                ·
                  refine ⟨3437317093829418822814181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291544729219612548542787 3437317093829418822814181)
                  ·
                    refine ⟨644496955093016029277659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3437317093829418822814181 644496955093016029277659)
                    ·
                      rfl

theorem cell22_1882730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1882730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882730 prefixEnd_1882730 := by exact prefixLift 1882730
  have htrace : WordTrace (prefixWord ++ tailWord_1882730) baseStart_1882730 baseEnd_1882730 := by
    simpa [prefixWord, tailWord_1882730, baseEnd_1882730] using wordTrace_append hprefix tailTrace_1882730
  have hstable : (prefixWord ++ tailWord_1882730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882730).length < 2 ^ (prefixWord ++ tailWord_1882730).sum := by decide
  have hdescent : baseEnd_1882730 < baseStart_1882730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882743 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 2, 3]
def baseStart_1882743 : Nat := 118140960795 + 1882743 * 2 ^ 59
def prefixEnd_1882743 : Nat := 4983230072969 + 3 ^ 40 * 1882743 * 2
def baseEnd_1882743 : Nat := 644501405258688328702619

theorem tailTrace_1882743 : CollatzResearch.WordTrace tailWord_1882743 prefixEnd_1882743 644501405258688328702619 := by
  unfold tailWord_1882743
  simp only [CollatzResearch.WordTrace]
  refine ⟨68669278618151132749852883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45779519078767421833235255 68669278618151132749852883)
  ·
    refine ⟨103003917927226699124779325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68669278618151132749852883 103003917927226699124779325)
    ·
      refine ⟨38626469222710012171792247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103003917927226699124779325 38626469222710012171792247)
      ·
        refine ⟨57939703834065018257688371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38626469222710012171792247 57939703834065018257688371)
        ·
          refine ⟨86909555751097527386532557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57939703834065018257688371 86909555751097527386532557)
          ·
            refine ⟨32591083406661572769949709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86909555751097527386532557 32591083406661572769949709)
            ·
              refine ⟨12221656277498089788731141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32591083406661572769949709 12221656277498089788731141)
              ·
                refine ⟨2291560552030891835387089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12221656277498089788731141 2291560552030891835387089)
                ·
                  refine ⟨1718670414023168876540317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2291560552030891835387089 1718670414023168876540317)
                  ·
                    refine ⟨644501405258688328702619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718670414023168876540317 644501405258688328702619)
                    ·
                      rfl

theorem cell22_1882743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_1882743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882743 prefixEnd_1882743 := by exact prefixLift 1882743
  have htrace : WordTrace (prefixWord ++ tailWord_1882743) baseStart_1882743 baseEnd_1882743 := by
    simpa [prefixWord, tailWord_1882743, baseEnd_1882743] using wordTrace_append hprefix tailTrace_1882743
  have hstable : (prefixWord ++ tailWord_1882743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882743).length < 2 ^ (prefixWord ++ tailWord_1882743).sum := by decide
  have hdescent : baseEnd_1882743 < baseStart_1882743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882745 : List Nat := [1, 2, 1, 3, 3, 2, 4, 2, 4]
def baseStart_1882745 : Nat := 118140960795 + 1882745 * 2 ^ 59
def prefixEnd_1882745 : Nat := 4983230072969 + 3 ^ 40 * 1882745 * 2
def baseEnd_1882745 : Nat := 214834029966520330050871

theorem tailTrace_1882745 : CollatzResearch.WordTrace tailWord_1882745 prefixEnd_1882745 214834029966520330050871 := by
  unfold tailWord_1882745
  simp only [CollatzResearch.WordTrace]
  refine ⟨68669351564143887091425689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45779567709429258060950459 68669351564143887091425689)
  ·
    refine ⟨51502013673107915318569267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68669351564143887091425689 51502013673107915318569267)
    ·
      refine ⟨77253020509661872977853901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51502013673107915318569267 77253020509661872977853901)
      ·
        refine ⟨28969882691123202366695213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77253020509661872977853901 28969882691123202366695213)
        ·
          refine ⟨10863706009171200887510705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28969882691123202366695213 10863706009171200887510705)
          ·
            refine ⟨8147779506878400665633029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10863706009171200887510705 8147779506878400665633029)
            ·
              refine ⟨1527708657539700124806193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8147779506878400665633029 1527708657539700124806193)
              ·
                refine ⟨1145781493154775093604645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527708657539700124806193 1145781493154775093604645)
                ·
                  refine ⟨214834029966520330050871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145781493154775093604645 214834029966520330050871)
                  ·
                    rfl

theorem cell22_1882745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_1882745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882745 prefixEnd_1882745 := by exact prefixLift 1882745
  have htrace : WordTrace (prefixWord ++ tailWord_1882745) baseStart_1882745 baseEnd_1882745 := by
    simpa [prefixWord, tailWord_1882745, baseEnd_1882745] using wordTrace_append hprefix tailTrace_1882745
  have hstable : (prefixWord ++ tailWord_1882745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882745).length < 2 ^ (prefixWord ++ tailWord_1882745).sum := by decide
  have hdescent : baseEnd_1882745 < baseStart_1882745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882788 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1882788 : Nat := 118140960795 + 1882788 * 2 ^ 59
def prefixEnd_1882788 : Nat := 4983230072969 + 3 ^ 40 * 1882788 * 2
def baseEnd_1882788 : Nat := 644516809678323211327481

theorem tailTrace_1882788 : CollatzResearch.WordTrace tailWord_1882788 prefixEnd_1882788 644516809678323211327481 := by
  unfold tailWord_1882788
  simp only [CollatzResearch.WordTrace]
  refine ⟨34335459951494052717620509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45780613268658736956827345 34335459951494052717620509)
  ·
    refine ⟨12875797481810269769107691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34335459951494052717620509 12875797481810269769107691)
    ·
      refine ⟨19313696222715404653661537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12875797481810269769107691 19313696222715404653661537)
      ·
        refine ⟨14485272167036553490246153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19313696222715404653661537 14485272167036553490246153)
        ·
          refine ⟨10863954125277415117684615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14485272167036553490246153 10863954125277415117684615)
          ·
            refine ⟨16295931187916122676526923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863954125277415117684615 16295931187916122676526923)
            ·
              refine ⟨24443896781874184014790385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16295931187916122676526923 24443896781874184014790385)
              ·
                refine ⟨18332922586405638011092789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24443896781874184014790385 18332922586405638011092789)
                ·
                  refine ⟨1718711492475528563539949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18332922586405638011092789 1718711492475528563539949)
                  ·
                    refine ⟨644516809678323211327481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718711492475528563539949 644516809678323211327481)
                    ·
                      rfl

theorem cell22_1882788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1882788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882788 prefixEnd_1882788 := by exact prefixLift 1882788
  have htrace : WordTrace (prefixWord ++ tailWord_1882788) baseStart_1882788 baseEnd_1882788 := by
    simpa [prefixWord, tailWord_1882788, baseEnd_1882788] using wordTrace_append hprefix tailTrace_1882788
  have hstable : (prefixWord ++ tailWord_1882788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882788).length < 2 ^ (prefixWord ++ tailWord_1882788).sum := by decide
  have hdescent : baseEnd_1882788 < baseStart_1882788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882805 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1882805 : Nat := 118140960795 + 1882805 * 2 ^ 59
def prefixEnd_1882805 : Nat := 4983230072969 + 3 ^ 40 * 1882805 * 2
def baseEnd_1882805 : Nat := 644522629125740833652429

theorem tailTrace_1882805 : CollatzResearch.WordTrace tailWord_1882805 prefixEnd_1882805 644522629125740833652429 := by
  unfold tailWord_1882805
  simp only [CollatzResearch.WordTrace]
  refine ⟨68671539943926517338609869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45781026629284344892406579 68671539943926517338609869)
  ·
    refine ⟨25751827478972444001978701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68671539943926517338609869 25751827478972444001978701)
    ·
      refine ⟨9656935304614666500742013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25751827478972444001978701 9656935304614666500742013)
      ·
        refine ⟨3621350739230499937778255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9656935304614666500742013 3621350739230499937778255)
        ·
          refine ⟨5432026108845749906667383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621350739230499937778255 5432026108845749906667383)
          ·
            refine ⟨8148039163268624860001075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432026108845749906667383 8148039163268624860001075)
            ·
              refine ⟨12222058744902937290001613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8148039163268624860001075 12222058744902937290001613)
              ·
                refine ⟨4583272029338601483750605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12222058744902937290001613 4583272029338601483750605)
                ·
                  refine ⟨1718727011001975556406477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4583272029338601483750605 1718727011001975556406477)
                  ·
                    refine ⟨644522629125740833652429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718727011001975556406477 644522629125740833652429)
                    ·
                      rfl

theorem cell22_1882805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1882805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882805 prefixEnd_1882805 := by exact prefixLift 1882805
  have htrace : WordTrace (prefixWord ++ tailWord_1882805) baseStart_1882805 baseEnd_1882805 := by
    simpa [prefixWord, tailWord_1882805, baseEnd_1882805] using wordTrace_append hprefix tailTrace_1882805
  have hstable : (prefixWord ++ tailWord_1882805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882805).length < 2 ^ (prefixWord ++ tailWord_1882805).sum := by decide
  have hdescent : baseEnd_1882805 < baseStart_1882805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882863 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 6]
def baseStart_1882863 : Nat := 118140960795 + 1882863 * 2 ^ 59
def prefixEnd_1882863 : Nat := 4983230072969 + 3 ^ 40 * 1882863 * 2
def baseEnd_1882863 : Nat := 214847494570349338567417

theorem tailTrace_1882863 : CollatzResearch.WordTrace tailWord_1882863 prefixEnd_1882863 214847494570349338567417 := by
  unfold tailWord_1882863
  simp only [CollatzResearch.WordTrace]
  refine ⟨68673655377716393244221243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45782436918477595496147495 68673655377716393244221243)
  ·
    refine ⟨103010483066574589866331865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68673655377716393244221243 103010483066574589866331865)
    ·
      refine ⟨77257862299930942399748899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103010483066574589866331865 77257862299930942399748899)
      ·
        refine ⟨115886793449896413599623349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77257862299930942399748899 115886793449896413599623349)
        ·
          refine ⟨10864386885927788774964689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115886793449896413599623349 10864386885927788774964689)
          ·
            refine ⟨8148290164445841581223517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10864386885927788774964689 8148290164445841581223517)
            ·
              refine ⟨3055608811667190592958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148290164445841581223517 3055608811667190592958819)
              ·
                refine ⟨4583413217500785889438229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055608811667190592958819 4583413217500785889438229)
                ·
                  refine ⟨214847494570349338567417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4583413217500785889438229 214847494570349338567417)
                  ·
                    rfl

theorem cell22_1882863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 6].length) (baseStart_1882863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882863 prefixEnd_1882863 := by exact prefixLift 1882863
  have htrace : WordTrace (prefixWord ++ tailWord_1882863) baseStart_1882863 baseEnd_1882863 := by
    simpa [prefixWord, tailWord_1882863, baseEnd_1882863] using wordTrace_append hprefix tailTrace_1882863
  have hstable : (prefixWord ++ tailWord_1882863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882863).length < 2 ^ (prefixWord ++ tailWord_1882863).sum := by decide
  have hdescent : baseEnd_1882863 < baseStart_1882863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882869 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 5]
def baseStart_1882869 : Nat := 118140960795 + 1882869 * 2 ^ 59
def prefixEnd_1882869 : Nat := 4983230072969 + 3 ^ 40 * 1882869 * 2
def baseEnd_1882869 : Nat := 214848179211222000017411

theorem tailTrace_1882869 : CollatzResearch.WordTrace tailWord_1882869 prefixEnd_1882869 214848179211222000017411 := by
  unfold tailWord_1882869
  simp only [CollatzResearch.WordTrace]
  refine ⟨68673874215694656268939661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45782582810463104179293107 68673874215694656268939661)
  ·
    refine ⟨25752702830885496100852373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68673874215694656268939661 25752702830885496100852373)
    ·
      refine ⟨1207157945197757629727455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25752702830885496100852373 1207157945197757629727455)
      ·
        refine ⟨1810736917796636444591183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207157945197757629727455 1810736917796636444591183)
        ·
          refine ⟨2716105376694954666886775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810736917796636444591183 2716105376694954666886775)
          ·
            refine ⟨4074158065042432000330163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716105376694954666886775 4074158065042432000330163)
            ·
              refine ⟨6111237097563648000495245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074158065042432000330163 6111237097563648000495245)
              ·
                refine ⟨2291713911586368000185717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6111237097563648000495245 2291713911586368000185717)
                ·
                  refine ⟨214848179211222000017411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291713911586368000185717 214848179211222000017411)
                  ·
                    rfl

theorem cell22_1882869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_1882869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882869 prefixEnd_1882869 := by exact prefixLift 1882869
  have htrace : WordTrace (prefixWord ++ tailWord_1882869) baseStart_1882869 baseEnd_1882869 := by
    simpa [prefixWord, tailWord_1882869, baseEnd_1882869] using wordTrace_append hprefix tailTrace_1882869
  have hstable : (prefixWord ++ tailWord_1882869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882869).length < 2 ^ (prefixWord ++ tailWord_1882869).sum := by decide
  have hdescent : baseEnd_1882869 < baseStart_1882869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882882 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1882882 : Nat := 118140960795 + 1882882 * 2 ^ 59
def prefixEnd_1882882 : Nat := 4983230072969 + 3 ^ 40 * 1882882 * 2
def baseEnd_1882882 : Nat := 644548987799338299477193

theorem tailTrace_1882882 : CollatzResearch.WordTrace tailWord_1882882 prefixEnd_1882882 644548987799338299477193 := by
  unfold tailWord_1882882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17168587091161889872290725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45782898909765039659441933 17168587091161889872290725)
  ·
    refine ⟨3219110079592854351054511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17168587091161889872290725 3219110079592854351054511)
    ·
      refine ⟨4828665119389281526581767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3219110079592854351054511 4828665119389281526581767)
      ·
        refine ⟨7242997679083922289872651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828665119389281526581767 7242997679083922289872651)
        ·
          refine ⟨10864496518625883434808977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242997679083922289872651 10864496518625883434808977)
          ·
            refine ⟨8148372388969412576106733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10864496518625883434808977 8148372388969412576106733)
            ·
              refine ⟨3055639645863529716040025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148372388969412576106733 3055639645863529716040025)
              ·
                refine ⟨2291729734397647287030019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055639645863529716040025 2291729734397647287030019)
                ·
                  refine ⟨3437594601596470930545029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291729734397647287030019 3437594601596470930545029)
                  ·
                    refine ⟨644548987799338299477193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3437594601596470930545029 644548987799338299477193)
                    ·
                      rfl

theorem cell22_1882882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1882882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882882 prefixEnd_1882882 := by exact prefixLift 1882882
  have htrace : WordTrace (prefixWord ++ tailWord_1882882) baseStart_1882882 baseEnd_1882882 := by
    simpa [prefixWord, tailWord_1882882, baseEnd_1882882] using wordTrace_append hprefix tailTrace_1882882
  have hstable : (prefixWord ++ tailWord_1882882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882882).length < 2 ^ (prefixWord ++ tailWord_1882882).sum := by decide
  have hdescent : baseEnd_1882882 < baseStart_1882882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882912 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 2, 3]
def baseStart_1882912 : Nat := 118140960795 + 1882912 * 2 ^ 59
def prefixEnd_1882912 : Nat := 4983230072969 + 3 ^ 40 * 1882912 * 2
def baseEnd_1882912 : Nat := 644559257412428221227101

theorem tailTrace_1882912 : CollatzResearch.WordTrace tailWord_1882912 prefixEnd_1882912 644559257412428221227101 := by
  unfold tailWord_1882912
  simp only [CollatzResearch.WordTrace]
  refine ⟨34337721277269437306377495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45783628369692583075169993 34337721277269437306377495)
  ·
    refine ⟨51506581915904155959566243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34337721277269437306377495 51506581915904155959566243)
    ·
      refine ⟨77259872873856233939349365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51506581915904155959566243 77259872873856233939349365)
      ·
        refine ⟨7243113081924021931814003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77259872873856233939349365 7243113081924021931814003)
        ·
          refine ⟨10864669622886032897721005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243113081924021931814003 10864669622886032897721005)
          ·
            refine ⟨4074251108582262336645377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10864669622886032897721005 4074251108582262336645377)
            ·
              refine ⟨3055688331436696752484033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4074251108582262336645377 3055688331436696752484033)
              ·
                refine ⟨2291766248577522564363025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055688331436696752484033 2291766248577522564363025)
                ·
                  refine ⟨1718824686433141923272269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2291766248577522564363025 1718824686433141923272269)
                  ·
                    refine ⟨644559257412428221227101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718824686433141923272269 644559257412428221227101)
                    ·
                      rfl

theorem cell22_1882912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_1882912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882912 prefixEnd_1882912 := by exact prefixLift 1882912
  have htrace : WordTrace (prefixWord ++ tailWord_1882912) baseStart_1882912 baseEnd_1882912 := by
    simpa [prefixWord, tailWord_1882912, baseEnd_1882912] using wordTrace_append hprefix tailTrace_1882912
  have hstable : (prefixWord ++ tailWord_1882912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882912).length < 2 ^ (prefixWord ++ tailWord_1882912).sum := by decide
  have hdescent : baseEnd_1882912 < baseStart_1882912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882914 : List Nat := [3, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1882914 : Nat := 118140960795 + 1882914 * 2 ^ 59
def prefixEnd_1882914 : Nat := 4983230072969 + 3 ^ 40 * 1882914 * 2
def baseEnd_1882914 : Nat := 214853314017766960892365

theorem tailTrace_1882914 : CollatzResearch.WordTrace tailWord_1882914 prefixEnd_1882914 214853314017766960892365 := by
  unfold tailWord_1882914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17168878875132907238581949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45783677000354419302885197 17168878875132907238581949)
  ·
    refine ⟨6438329578174840214468231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17168878875132907238581949 6438329578174840214468231)
    ·
      refine ⟨9657494367262260321702347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6438329578174840214468231 9657494367262260321702347)
      ·
        refine ⟨14486241550893390482553521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9657494367262260321702347 14486241550893390482553521)
        ·
          refine ⟨10864681163170042861915141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14486241550893390482553521 10864681163170042861915141)
          ·
            refine ⟨2037127718094383036609089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10864681163170042861915141 2037127718094383036609089)
            ·
              refine ⟨1527845788570787277456817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037127718094383036609089 1527845788570787277456817)
              ·
                refine ⟨1145884341428090458092613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527845788570787277456817 1145884341428090458092613)
                ·
                  refine ⟨214853314017766960892365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1145884341428090458092613 214853314017766960892365)
                  ·
                    rfl

theorem cell22_1882914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1882914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882914 prefixEnd_1882914 := by exact prefixLift 1882914
  have htrace : WordTrace (prefixWord ++ tailWord_1882914) baseStart_1882914 baseEnd_1882914 := by
    simpa [prefixWord, tailWord_1882914, baseEnd_1882914] using wordTrace_append hprefix tailTrace_1882914
  have hstable : (prefixWord ++ tailWord_1882914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882914).length < 2 ^ (prefixWord ++ tailWord_1882914).sum := by decide
  have hdescent : baseEnd_1882914 < baseStart_1882914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882942 : List Nat := [4, 2, 1, 2, 3, 1, 3, 6]
def baseStart_1882942 : Nat := 118140960795 + 1882942 * 2 ^ 59
def prefixEnd_1882942 : Nat := 4983230072969 + 3 ^ 40 * 1882942 * 2
def baseEnd_1882942 : Nat := 71618836336168682553001

theorem tailTrace_1882942 : CollatzResearch.WordTrace tailWord_1882942 prefixEnd_1882942 71618836336168682553001 := by
  unfold tailWord_1882942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584567093053773717043385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45784357829620126490898053 8584567093053773717043385)
  ·
    refine ⟨6438425319790330287782539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8584567093053773717043385 6438425319790330287782539)
    ·
      refine ⟨9657637979685495431673809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6438425319790330287782539 9657637979685495431673809)
      ·
        refine ⟨7243228484764121573755357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9657637979685495431673809 7243228484764121573755357)
        ·
          refine ⟨2716210681786545590158259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7243228484764121573755357 2716210681786545590158259)
          ·
            refine ⟨4074316022679818385237389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716210681786545590158259 4074316022679818385237389)
            ·
              refine ⟨1527868508504931894464021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4074316022679818385237389 1527868508504931894464021)
              ·
                refine ⟨71618836336168682553001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1527868508504931894464021 71618836336168682553001)
                ·
                  rfl

theorem cell22_1882942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_1882942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882942 prefixEnd_1882942 := by exact prefixLift 1882942
  have htrace : WordTrace (prefixWord ++ tailWord_1882942) baseStart_1882942 baseEnd_1882942 := by
    simpa [prefixWord, tailWord_1882942, baseEnd_1882942] using wordTrace_append hprefix tailTrace_1882942
  have hstable : (prefixWord ++ tailWord_1882942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882942).length < 2 ^ (prefixWord ++ tailWord_1882942).sum := by decide
  have hdescent : baseEnd_1882942 < baseStart_1882942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1882970 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_1882970 : Nat := 118140960795 + 1882970 * 2 ^ 59
def prefixEnd_1882970 : Nat := 4983230072969 + 3 ^ 40 * 1882970 * 2
def baseEnd_1882970 : Nat := 214859703999245134425641

theorem tailTrace_1882970 : CollatzResearch.WordTrace tailWord_1882970 prefixEnd_1882970 214859703999245134425641 := by
  unfold tailWord_1882970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17169389497082187629591591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45785038658885833678910909 17169389497082187629591591)
  ·
    refine ⟨25754084245623281444387387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17169389497082187629591591 25754084245623281444387387)
    ·
      refine ⟨38631126368434922166581081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25754084245623281444387387 38631126368434922166581081)
      ·
        refine ⟨28973344776326191624935811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38631126368434922166581081 28973344776326191624935811)
        ·
          refine ⟨43460017164489287437403717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28973344776326191624935811 43460017164489287437403717)
          ·
            refine ⟨8148753218341741394513197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43460017164489287437403717 8148753218341741394513197)
            ·
              refine ⟨3055782456878153022942449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148753218341741394513197 3055782456878153022942449)
              ·
                refine ⟨2291836842658614767206837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055782456878153022942449 2291836842658614767206837)
                ·
                  refine ⟨214859703999245134425641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291836842658614767206837 214859703999245134425641)
                  ·
                    rfl

theorem cell22_1882970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_1882970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1882970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1882970 prefixEnd_1882970 := by exact prefixLift 1882970
  have htrace : WordTrace (prefixWord ++ tailWord_1882970) baseStart_1882970 baseEnd_1882970 := by
    simpa [prefixWord, tailWord_1882970, baseEnd_1882970] using wordTrace_append hprefix tailTrace_1882970
  have hstable : (prefixWord ++ tailWord_1882970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1882970).length < 2 ^ (prefixWord ++ tailWord_1882970).sum := by decide
  have hdescent : baseEnd_1882970 < baseStart_1882970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1882970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883043 : List Nat := [1, 1, 1, 4, 1, 2, 3, 9]
def baseStart_1883043 : Nat := 118140960795 + 1883043 * 2 ^ 59
def prefixEnd_1883043 : Nat := 4983230072969 + 3 ^ 40 * 1883043 * 2
def baseEnd_1883043 : Nat := 71622677932176394022411

theorem tailTrace_1883043 : CollatzResearch.WordTrace tailWord_1883043 prefixEnd_1883043 71622677932176394022411 := by
  unfold tailWord_1883043
  simp only [CollatzResearch.WordTrace]
  refine ⟨68680220517064283985773783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45786813678042855990515855 68680220517064283985773783)
  ·
    refine ⟨103020330775596425978660675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68680220517064283985773783 103020330775596425978660675)
    ·
      refine ⟨154530496163394638967991013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103020330775596425978660675 154530496163394638967991013)
      ·
        refine ⟨28974468030636494806498315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154530496163394638967991013 28974468030636494806498315)
        ·
          refine ⟨43461702045954742209747473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28974468030636494806498315 43461702045954742209747473)
          ·
            refine ⟨32596276534466056657310605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43461702045954742209747473 32596276534466056657310605)
            ·
              refine ⟨12223603700424771246491477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32596276534466056657310605 12223603700424771246491477)
              ·
                refine ⟨71622677932176394022411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12223603700424771246491477 71622677932176394022411)
                ·
                  rfl

theorem cell22_1883043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 9].length) (baseStart_1883043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883043 prefixEnd_1883043 := by exact prefixLift 1883043
  have htrace : WordTrace (prefixWord ++ tailWord_1883043) baseStart_1883043 baseEnd_1883043 := by
    simpa [prefixWord, tailWord_1883043, baseEnd_1883043] using wordTrace_append hprefix tailTrace_1883043
  have hstable : (prefixWord ++ tailWord_1883043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883043).length < 2 ^ (prefixWord ++ tailWord_1883043).sum := by decide
  have hdescent : baseEnd_1883043 < baseStart_1883043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883075 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 5, 3]
def baseStart_1883075 : Nat := 118140960795 + 1883075 * 2 ^ 59
def prefixEnd_1883075 : Nat := 4983230072969 + 3 ^ 40 * 1883075 * 2
def baseEnd_1883075 : Nat := 644615055643550129401601

theorem tailTrace_1883075 : CollatzResearch.WordTrace tailWord_1883075 prefixEnd_1883075 644615055643550129401601 := by
  unfold tailWord_1883075
  simp only [CollatzResearch.WordTrace]
  refine ⟨68681387652948353450938679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45787591768632235633959119 68681387652948353450938679)
  ·
    refine ⟨103022081479422530176408019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68681387652948353450938679 103022081479422530176408019)
    ·
      refine ⟨154533122219133795264612029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103022081479422530176408019 154533122219133795264612029)
      ·
        refine ⟨57949920832175173224229511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154533122219133795264612029 57949920832175173224229511)
        ·
          refine ⟨86924881248262759836344267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57949920832175173224229511 86924881248262759836344267)
          ·
            refine ⟨130387321872394139754516401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86924881248262759836344267 130387321872394139754516401)
            ·
              refine ⟨97790491404295604815887301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130387321872394139754516401 97790491404295604815887301)
              ·
                refine ⟨18335717138305425902978869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97790491404295604815887301 18335717138305425902978869)
                ·
                  refine ⟨1718973481716133678404269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18335717138305425902978869 1718973481716133678404269)
                  ·
                    refine ⟨644615055643550129401601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1718973481716133678404269 644615055643550129401601)
                    ·
                      rfl

theorem cell22_1883075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 3].length) (baseStart_1883075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883075 prefixEnd_1883075 := by exact prefixLift 1883075
  have htrace : WordTrace (prefixWord ++ tailWord_1883075) baseStart_1883075 baseEnd_1883075 := by
    simpa [prefixWord, tailWord_1883075, baseEnd_1883075] using wordTrace_append hprefix tailTrace_1883075
  have hstable : (prefixWord ++ tailWord_1883075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883075).length < 2 ^ (prefixWord ++ tailWord_1883075).sum := by decide
  have hdescent : baseEnd_1883075 < baseStart_1883075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883094 : List Nat := [5, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1883094 : Nat := 118140960795 + 1883094 * 2 ^ 59
def prefixEnd_1883094 : Nat := 4983230072969 + 3 ^ 40 * 1883094 * 2
def baseEnd_1883094 : Nat := 71624617747982268130727

theorem tailTrace_1883094 : CollatzResearch.WordTrace tailWord_1883094 prefixEnd_1883094 71624617747982268130727 := by
  unfold tailWord_1883094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292630039992469980992521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45788053759919679797253557 4292630039992469980992521)
  ·
    refine ⟨3219472529994352485744391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4292630039992469980992521 3219472529994352485744391)
    ·
      refine ⟨4829208794991528728616587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3219472529994352485744391 4829208794991528728616587)
      ·
        refine ⟨7243813192487293092924881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829208794991528728616587 7243813192487293092924881)
        ·
          refine ⟨5432859894365469819693661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7243813192487293092924881 5432859894365469819693661)
          ·
            refine ⟨2037322460387051182385123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5432859894365469819693661 2037322460387051182385123)
            ·
              refine ⟨3055983690580576773577685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037322460387051182385123 3055983690580576773577685)
              ·
                refine ⟨71624617747982268130727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3055983690580576773577685 71624617747982268130727)
                ·
                  rfl

theorem cell22_1883094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1883094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883094 prefixEnd_1883094 := by exact prefixLift 1883094
  have htrace : WordTrace (prefixWord ++ tailWord_1883094) baseStart_1883094 baseEnd_1883094 := by
    simpa [prefixWord, tailWord_1883094, baseEnd_1883094] using wordTrace_append hprefix tailTrace_1883094
  have hstable : (prefixWord ++ tailWord_1883094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883094).length < 2 ^ (prefixWord ++ tailWord_1883094).sum := by decide
  have hdescent : baseEnd_1883094 < baseStart_1883094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883126 : List Nat := [5, 1, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1883126 : Nat := 118140960795 + 1883126 * 2 ^ 59
def prefixEnd_1883126 : Nat := 4983230072969 + 3 ^ 40 * 1883126 * 2
def baseEnd_1883126 : Nat := 644632513985802996376445

theorem tailTrace_1883126 : CollatzResearch.WordTrace tailWord_1883126 prefixEnd_1883126 644632513985802996376445 := by
  unfold tailWord_1883126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292702985985224322565327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45788831850509059440696821 4292702985985224322565327)
  ·
    refine ⟨6439054478977836483847991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4292702985985224322565327 6439054478977836483847991)
    ·
      refine ⟨9658581718466754725771987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439054478977836483847991 9658581718466754725771987)
      ·
        refine ⟨14487872577700132088657981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9658581718466754725771987 14487872577700132088657981)
        ·
          refine ⟨5432952216637549533246743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14487872577700132088657981 5432952216637549533246743)
          ·
            refine ⟨8149428324956324299870115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432952216637549533246743 8149428324956324299870115)
            ·
              refine ⟨12224142487434486449805173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149428324956324299870115 12224142487434486449805173)
              ·
                refine ⟨1146013358196983104669235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12224142487434486449805173 1146013358196983104669235)
                ·
                  refine ⟨1719020037295474657003853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146013358196983104669235 1719020037295474657003853)
                  ·
                    refine ⟨644632513985802996376445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719020037295474657003853 644632513985802996376445)
                    ·
                      rfl

theorem cell22_1883126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1883126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883126 prefixEnd_1883126 := by exact prefixLift 1883126
  have htrace : WordTrace (prefixWord ++ tailWord_1883126) baseStart_1883126 baseEnd_1883126 := by
    simpa [prefixWord, tailWord_1883126, baseEnd_1883126] using wordTrace_append hprefix tailTrace_1883126
  have hstable : (prefixWord ++ tailWord_1883126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883126).length < 2 ^ (prefixWord ++ tailWord_1883126).sum := by decide
  have hdescent : baseEnd_1883126 < baseStart_1883126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883169 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1883169 : Nat := 118140960795 + 1883169 * 2 ^ 59
def prefixEnd_1883169 : Nat := 4983230072969 + 3 ^ 40 * 1883169 * 2
def baseEnd_1883169 : Nat := 644647233764565217551313

theorem tailTrace_1883169 : CollatzResearch.WordTrace tailWord_1883169 prefixEnd_1883169 644647233764565217551313 := by
  unfold tailWord_1883169
  simp only [CollatzResearch.WordTrace]
  refine ⟨68684816114607807504860561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45789877409738538336573707 68684816114607807504860561)
  ·
    refine ⟨51513612085955855628645421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68684816114607807504860561 51513612085955855628645421)
    ·
      refine ⟨19317604532233445860742033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51513612085955855628645421 19317604532233445860742033)
      ·
        refine ⟨14488203399175084395556525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19317604532233445860742033 14488203399175084395556525)
        ·
          refine ⟨5433076274690656648333697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14488203399175084395556525 5433076274690656648333697)
          ·
            refine ⟨4074807206017992486250273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433076274690656648333697 4074807206017992486250273)
            ·
              refine ⟨3056105404513494364687705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4074807206017992486250273 3056105404513494364687705)
              ·
                refine ⟨2292079053385120773515779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056105404513494364687705 2292079053385120773515779)
                ·
                  refine ⟨3438118580077681160273669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292079053385120773515779 3438118580077681160273669)
                  ·
                    refine ⟨644647233764565217551313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3438118580077681160273669 644647233764565217551313)
                    ·
                      rfl

theorem cell22_1883169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1883169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883169 prefixEnd_1883169 := by exact prefixLift 1883169
  have htrace : WordTrace (prefixWord ++ tailWord_1883169) baseStart_1883169 baseEnd_1883169 := by
    simpa [prefixWord, tailWord_1883169, baseEnd_1883169] using wordTrace_append hprefix tailTrace_1883169
  have hstable : (prefixWord ++ tailWord_1883169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883169).length < 2 ^ (prefixWord ++ tailWord_1883169).sum := by decide
  have hdescent : baseEnd_1883169 < baseStart_1883169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883180 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_1883180 : Nat := 118140960795 + 1883180 * 2 ^ 59
def prefixEnd_1883180 : Nat := 4983230072969 + 3 ^ 40 * 1883180 * 2
def baseEnd_1883180 : Nat := 644650999289364855526279

theorem tailTrace_1883180 : CollatzResearch.WordTrace tailWord_1883180 prefixEnd_1883180 644650999289364855526279 := by
  unfold tailWord_1883180
  simp only [CollatzResearch.WordTrace]
  refine ⟨34342608658783978191755497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45790144878378637589007329 34342608658783978191755497)
  ·
    refine ⟨25756956494087983643816623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34342608658783978191755497 25756956494087983643816623)
    ·
      refine ⟨38635434741131975465724935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25756956494087983643816623 38635434741131975465724935)
      ·
        refine ⟨57953152111697963198587403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38635434741131975465724935 57953152111697963198587403)
        ·
          refine ⟨86929728167546944797881105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57953152111697963198587403 86929728167546944797881105)
          ·
            refine ⟨65197296125660208598410829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86929728167546944797881105 65197296125660208598410829)
            ·
              refine ⟨24448986047122578224404061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65197296125660208598410829 24448986047122578224404061)
              ·
                refine ⟨9168369767670966834151523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24448986047122578224404061 9168369767670966834151523)
                ·
                  refine ⟨13752554651506450251227285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9168369767670966834151523 13752554651506450251227285)
                  ·
                    refine ⟨644650999289364855526279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13752554651506450251227285 644650999289364855526279)
                    ·
                      rfl

theorem cell22_1883180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_1883180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883180 prefixEnd_1883180 := by exact prefixLift 1883180
  have htrace : WordTrace (prefixWord ++ tailWord_1883180) baseStart_1883180 baseEnd_1883180 := by
    simpa [prefixWord, tailWord_1883180, baseEnd_1883180] using wordTrace_append hprefix tailTrace_1883180
  have hstable : (prefixWord ++ tailWord_1883180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883180).length < 2 ^ (prefixWord ++ tailWord_1883180).sum := by decide
  have hdescent : baseEnd_1883180 < baseStart_1883180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883182 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1883182 : Nat := 118140960795 + 1883182 * 2 ^ 59
def prefixEnd_1883182 : Nat := 4983230072969 + 3 ^ 40 * 1883182 * 2
def baseEnd_1883182 : Nat := 644651683930237516976273

theorem tailTrace_1883182 : CollatzResearch.WordTrace tailWord_1883182 prefixEnd_1883182 644651683930237516976273 := by
  unfold tailWord_1883182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585661282945088840635475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45790193509040473816722533 8585661282945088840635475)
  ·
    refine ⟨12878491924417633260953213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8585661282945088840635475 12878491924417633260953213)
    ·
      refine ⟨4829434471656612472857455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12878491924417633260953213 4829434471656612472857455)
      ·
        refine ⟨7244151707484918709286183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829434471656612472857455 7244151707484918709286183)
        ·
          refine ⟨10866227561227378063929275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244151707484918709286183 10866227561227378063929275)
          ·
            refine ⟨16299341341841067095893913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866227561227378063929275 16299341341841067095893913)
            ·
              refine ⟨12224506006380800321920435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16299341341841067095893913 12224506006380800321920435)
              ·
                refine ⟨18336759009571200482880653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12224506006380800321920435 18336759009571200482880653)
                ·
                  refine ⟨6876284628589200181080245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18336759009571200482880653 6876284628589200181080245)
                  ·
                    refine ⟨644651683930237516976273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6876284628589200181080245 644651683930237516976273)
                    ·
                      rfl

theorem cell22_1883182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1883182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883182 prefixEnd_1883182 := by exact prefixLift 1883182
  have htrace : WordTrace (prefixWord ++ tailWord_1883182) baseStart_1883182 baseEnd_1883182 := by
    simpa [prefixWord, tailWord_1883182, baseEnd_1883182] using wordTrace_append hprefix tailTrace_1883182
  have hstable : (prefixWord ++ tailWord_1883182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883182).length < 2 ^ (prefixWord ++ tailWord_1883182).sum := by decide
  have hdescent : baseEnd_1883182 < baseStart_1883182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883197 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1883197 : Nat := 118140960795 + 1883197 * 2 ^ 59
def prefixEnd_1883197 : Nat := 4983230072969 + 3 ^ 40 * 1883197 * 2
def baseEnd_1883197 : Nat := 644656818736782477851227

theorem tailTrace_1883197 : CollatzResearch.WordTrace tailWord_1883197 prefixEnd_1883197 644656818736782477851227 := by
  unfold tailWord_1883197
  simp only [CollatzResearch.WordTrace]
  refine ⟨68685837358506368286879845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45790558239004245524586563 68685837358506368286879845)
  ·
    refine ⟨12878594504719944053789971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68685837358506368286879845 12878594504719944053789971)
    ·
      refine ⟨19317891757079916080684957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12878594504719944053789971 19317891757079916080684957)
      ·
        refine ⟨7244209408904968530256859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19317891757079916080684957 7244209408904968530256859)
        ·
          refine ⟨10866314113357452795385289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244209408904968530256859 10866314113357452795385289)
          ·
            refine ⟨8149735585018089596538967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10866314113357452795385289 8149735585018089596538967)
            ·
              refine ⟨12224603377527134394808451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149735585018089596538967 12224603377527134394808451)
              ·
                refine ⟨18336905066290701592212677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12224603377527134394808451 18336905066290701592212677)
                ·
                  refine ⟨3438169699929506548539877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18336905066290701592212677 3438169699929506548539877)
                  ·
                    refine ⟨644656818736782477851227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3438169699929506548539877 644656818736782477851227)
                    ·
                      rfl

theorem cell22_1883197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1883197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883197 prefixEnd_1883197 := by exact prefixLift 1883197
  have htrace : WordTrace (prefixWord ++ tailWord_1883197) baseStart_1883197 baseEnd_1883197 := by
    simpa [prefixWord, tailWord_1883197, baseEnd_1883197] using wordTrace_append hprefix tailTrace_1883197
  have hstable : (prefixWord ++ tailWord_1883197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883197).length < 2 ^ (prefixWord ++ tailWord_1883197).sum := by decide
  have hdescent : baseEnd_1883197 < baseStart_1883197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883201 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 6]
def baseStart_1883201 : Nat := 118140960795 + 1883201 * 2 ^ 59
def prefixEnd_1883201 : Nat := 4983230072969 + 3 ^ 40 * 1883201 * 2
def baseEnd_1883201 : Nat := 214886062672842600250405

theorem tailTrace_1883201 : CollatzResearch.WordTrace tailWord_1883201 prefixEnd_1883201 214886062672842600250405 := by
  unfold tailWord_1883201
  simp only [CollatzResearch.WordTrace]
  refine ⟨68685983250491876970025457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45790655500327917980016971 68685983250491876970025457)
  ·
    refine ⟨51514487437868907727519093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68685983250491876970025457 51514487437868907727519093)
    ·
      refine ⟨4829483197300210099454915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51514487437868907727519093 4829483197300210099454915)
      ·
        refine ⟨7244224795950315149182373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829483197300210099454915 7244224795950315149182373)
        ·
          refine ⟨1358292149240684090471695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7244224795950315149182373 1358292149240684090471695)
          ·
            refine ⟨2037438223861026135707543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358292149240684090471695 2037438223861026135707543)
            ·
              refine ⟨3056157335791539203561315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037438223861026135707543 3056157335791539203561315)
              ·
                refine ⟨4584236003687308805341973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056157335791539203561315 4584236003687308805341973)
                ·
                  refine ⟨214886062672842600250405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4584236003687308805341973 214886062672842600250405)
                  ·
                    rfl

theorem cell22_1883201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_1883201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883201 prefixEnd_1883201 := by exact prefixLift 1883201
  have htrace : WordTrace (prefixWord ++ tailWord_1883201) baseStart_1883201 baseEnd_1883201 := by
    simpa [prefixWord, tailWord_1883201, baseEnd_1883201] using wordTrace_append hprefix tailTrace_1883201
  have hstable : (prefixWord ++ tailWord_1883201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883201).length < 2 ^ (prefixWord ++ tailWord_1883201).sum := by decide
  have hdescent : baseEnd_1883201 < baseStart_1883201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883225 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_1883225 : Nat := 118140960795 + 1883225 * 2 ^ 59
def prefixEnd_1883225 : Nat := 4983230072969 + 3 ^ 40 * 1883225 * 2
def baseEnd_1883225 : Nat := 644666403708999738151141

theorem tailTrace_1883225 : CollatzResearch.WordTrace tailWord_1883225 prefixEnd_1883225 644666403708999738151141 := by
  unfold tailWord_1883225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68686858602404929068899129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45791239068269952712599419 68686858602404929068899129)
  ·
    refine ⟨51515143951803696801674347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68686858602404929068899129 51515143951803696801674347)
    ·
      refine ⟨77272715927705545202511521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51515143951803696801674347 77272715927705545202511521)
      ·
        refine ⟨57954536945779158901883641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77272715927705545202511521 57954536945779158901883641)
        ·
          refine ⟨43465902709334369176412731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57954536945779158901883641 43465902709334369176412731)
          ·
            refine ⟨65198854064001553764619097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43465902709334369176412731 65198854064001553764619097)
            ·
              refine ⟨48899140548001165323464323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65198854064001553764619097 48899140548001165323464323)
              ·
                refine ⟨73348710822001747985196485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48899140548001165323464323 73348710822001747985196485)
                ·
                  refine ⟨13752883279125327747224341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73348710822001747985196485 13752883279125327747224341)
                  ·
                    refine ⟨644666403708999738151141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13752883279125327747224341 644666403708999738151141)
                    ·
                      rfl

theorem cell22_1883225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_1883225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883225 prefixEnd_1883225 := by exact prefixLift 1883225
  have htrace : WordTrace (prefixWord ++ tailWord_1883225) baseStart_1883225 baseEnd_1883225 := by
    simpa [prefixWord, tailWord_1883225, baseEnd_1883225] using wordTrace_append hprefix tailTrace_1883225
  have hstable : (prefixWord ++ tailWord_1883225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883225).length < 2 ^ (prefixWord ++ tailWord_1883225).sum := by decide
  have hdescent : baseEnd_1883225 < baseStart_1883225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883261 : List Nat := [1, 4, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_1883261 : Nat := 118140960795 + 1883261 * 2 ^ 59
def prefixEnd_1883261 : Nat := 4983230072969 + 3 ^ 40 * 1883261 * 2
def baseEnd_1883261 : Nat := 644678727244707644251031

theorem tailTrace_1883261 : CollatzResearch.WordTrace tailWord_1883261 prefixEnd_1883261 644678727244707644251031 := by
  unfold tailWord_1883261
  simp only [CollatzResearch.WordTrace]
  refine ⟨68688171630274507217209637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45792114420183004811473091 68688171630274507217209637)
  ·
    refine ⟨12879032180676470103226807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68688171630274507217209637 12879032180676470103226807)
    ·
      refine ⟨19318548271014705154840211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12879032180676470103226807 19318548271014705154840211)
      ·
        refine ⟨28977822406522057732260317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318548271014705154840211 28977822406522057732260317)
        ·
          refine ⟨10866683402445771649597619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28977822406522057732260317 10866683402445771649597619)
          ·
            refine ⟨16300025103668657474396429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866683402445771649597619 16300025103668657474396429)
            ·
              refine ⟨6112509413875746552898661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16300025103668657474396429 6112509413875746552898661)
              ·
                refine ⟨1146095515101702478668499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6112509413875746552898661 1146095515101702478668499)
                ·
                  refine ⟨1719143272652553718002749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146095515101702478668499 1719143272652553718002749)
                  ·
                    refine ⟨644678727244707644251031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719143272652553718002749 644678727244707644251031)
                    ·
                      rfl

theorem cell22_1883261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_1883261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883261 prefixEnd_1883261 := by exact prefixLift 1883261
  have htrace : WordTrace (prefixWord ++ tailWord_1883261) baseStart_1883261 baseEnd_1883261 := by
    simpa [prefixWord, tailWord_1883261, baseEnd_1883261] using wordTrace_append hprefix tailTrace_1883261
  have hstable : (prefixWord ++ tailWord_1883261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883261).length < 2 ^ (prefixWord ++ tailWord_1883261).sum := by decide
  have hdescent : baseEnd_1883261 < baseStart_1883261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883319 : List Nat := [1, 1, 3, 1, 4, 1, 1, 6, 4]
def baseStart_1883319 : Nat := 118140960795 + 1883319 * 2 ^ 59
def prefixEnd_1883319 : Nat := 4983230072969 + 3 ^ 40 * 1883319 * 2
def baseEnd_1883319 : Nat := 214899527276671608766951

theorem tailTrace_1883319 : CollatzResearch.WordTrace tailWord_1883319 prefixEnd_1883319 214899527276671608766951 := by
  unfold tailWord_1883319
  simp only [CollatzResearch.WordTrace]
  refine ⟨68690287064064383122821011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45793524709376255415214007 68690287064064383122821011)
  ·
    refine ⟨103035430596096574684231517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68690287064064383122821011 103035430596096574684231517)
    ·
      refine ⟨38638286473536215506586819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103035430596096574684231517 38638286473536215506586819)
      ·
        refine ⟨57957429710304323259880229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38638286473536215506586819 57957429710304323259880229)
        ·
          refine ⟨10867018070682060611227543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57957429710304323259880229 10867018070682060611227543)
          ·
            refine ⟨16300527106023090916841315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10867018070682060611227543 16300527106023090916841315)
            ·
              refine ⟨24450790659034636375261973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16300527106023090916841315 24450790659034636375261973)
              ·
                refine ⟨1146130812142248580090405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24450790659034636375261973 1146130812142248580090405)
                ·
                  refine ⟨214899527276671608766951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146130812142248580090405 214899527276671608766951)
                  ·
                    rfl

theorem cell22_1883319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 4].length) (baseStart_1883319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883319 prefixEnd_1883319 := by exact prefixLift 1883319
  have htrace : WordTrace (prefixWord ++ tailWord_1883319) baseStart_1883319 baseEnd_1883319 := by
    simpa [prefixWord, tailWord_1883319, baseEnd_1883319] using wordTrace_append hprefix tailTrace_1883319
  have hstable : (prefixWord ++ tailWord_1883319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883319).length < 2 ^ (prefixWord ++ tailWord_1883319).sum := by decide
  have hdescent : baseEnd_1883319 < baseStart_1883319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883349 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1883349 : Nat := 118140960795 + 1883349 * 2 ^ 59
def prefixEnd_1883349 : Nat := 4983230072969 + 3 ^ 40 * 1883349 * 2
def baseEnd_1883349 : Nat := 644708851443104748050761

theorem tailTrace_1883349 : CollatzResearch.WordTrace tailWord_1883349 prefixEnd_1883349 644708851443104748050761 := by
  unfold tailWord_1883349
  simp only [CollatzResearch.WordTrace]
  refine ⟨68691381253955698246413101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45794254169303798830942067 68691381253955698246413101)
  ·
    refine ⟨25759267970233386842404913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68691381253955698246413101 25759267970233386842404913)
    ·
      refine ⟨19319450977675040131803685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25759267970233386842404913 19319450977675040131803685)
      ·
        refine ⟨3622397058314070024713191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19319450977675040131803685 3622397058314070024713191)
        ·
          refine ⟨5433595587471105037069787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622397058314070024713191 5433595587471105037069787)
          ·
            refine ⟨8150393381206657555604681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433595587471105037069787 8150393381206657555604681)
            ·
              refine ⟨6112795035904993166703511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8150393381206657555604681 6112795035904993166703511)
              ·
                refine ⟨9169192553857489750055267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112795035904993166703511 9169192553857489750055267)
                ·
                  refine ⟨13753788830786234625082901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169192553857489750055267 13753788830786234625082901)
                  ·
                    refine ⟨644708851443104748050761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13753788830786234625082901 644708851443104748050761)
                    ·
                      rfl

theorem cell22_1883349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1883349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883349 prefixEnd_1883349 := by exact prefixLift 1883349
  have htrace : WordTrace (prefixWord ++ tailWord_1883349) baseStart_1883349 baseEnd_1883349 := by
    simpa [prefixWord, tailWord_1883349, baseEnd_1883349] using wordTrace_append hprefix tailTrace_1883349
  have hstable : (prefixWord ++ tailWord_1883349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883349).length < 2 ^ (prefixWord ++ tailWord_1883349).sum := by decide
  have hdescent : baseEnd_1883349 < baseStart_1883349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883377 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1883377 : Nat := 118140960795 + 1883377 * 2 ^ 59
def prefixEnd_1883377 : Nat := 4983230072969 + 3 ^ 40 * 1883377 * 2
def baseEnd_1883377 : Nat := 644718436415322008350675

theorem tailTrace_1883377 : CollatzResearch.WordTrace tailWord_1883377 prefixEnd_1883377 644718436415322008350675 := by
  unfold tailWord_1883377
  simp only [CollatzResearch.WordTrace]
  refine ⟨68692402497854259028432385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45794934998569506018954923 68692402497854259028432385)
  ·
    refine ⟨51519301873390694271324289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68692402497854259028432385 51519301873390694271324289)
    ·
      refine ⟨38639476405043020703493217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51519301873390694271324289 38639476405043020703493217)
      ·
        refine ⟨28979607303782265527619913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38639476405043020703493217 28979607303782265527619913)
        ·
          refine ⟨21734705477836699145714935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28979607303782265527619913 21734705477836699145714935)
          ·
            refine ⟨32602058216755048718572403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21734705477836699145714935 32602058216755048718572403)
            ·
              refine ⟨48903087325132573077858605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32602058216755048718572403 48903087325132573077858605)
              ·
                refine ⟨18338657746924714904196977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48903087325132573077858605 18338657746924714904196977)
                ·
                  refine ⟨13753993310193536178147733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18338657746924714904196977 13753993310193536178147733)
                  ·
                    refine ⟨644718436415322008350675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13753993310193536178147733 644718436415322008350675)
                    ·
                      rfl

theorem cell22_1883377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1883377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883377 prefixEnd_1883377 := by exact prefixLift 1883377
  have htrace : WordTrace (prefixWord ++ tailWord_1883377) baseStart_1883377 baseEnd_1883377 := by
    simpa [prefixWord, tailWord_1883377, baseEnd_1883377] using wordTrace_append hprefix tailTrace_1883377
  have hstable : (prefixWord ++ tailWord_1883377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883377).length < 2 ^ (prefixWord ++ tailWord_1883377).sum := by decide
  have hdescent : baseEnd_1883377 < baseStart_1883377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883407 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 6, 5]
def baseStart_1883407 : Nat := 118140960795 + 1883407 * 2 ^ 59
def prefixEnd_1883407 : Nat := 4983230072969 + 3 ^ 40 * 1883407 * 2
def baseEnd_1883407 : Nat := 644728706028411930100583

theorem tailTrace_1883407 : CollatzResearch.WordTrace tailWord_1883407 prefixEnd_1883407 644728706028411930100583 := by
  unfold tailWord_1883407
  simp only [CollatzResearch.WordTrace]
  refine ⟨68693496687745574152024475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45795664458497049434682983 68693496687745574152024475)
  ·
    refine ⟨103040245031618361228036713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68693496687745574152024475 103040245031618361228036713)
    ·
      refine ⟨77280183773713770921027535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103040245031618361228036713 77280183773713770921027535)
      ·
        refine ⟨115920275660570656381541303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77280183773713770921027535 115920275660570656381541303)
        ·
          refine ⟨173880413490855984572311955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115920275660570656381541303 173880413490855984572311955)
          ·
            refine ⟨260820620236283976858467933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173880413490855984572311955 260820620236283976858467933)
            ·
              refine ⟨97807732588606491321925475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260820620236283976858467933 97807732588606491321925475)
              ·
                refine ⟨146711598882909736982888213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97807732588606491321925475 146711598882909736982888213)
                ·
                  refine ⟨6877106197636393921072885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146711598882909736982888213 6877106197636393921072885)
                  ·
                    refine ⟨644728706028411930100583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6877106197636393921072885 644728706028411930100583)
                    ·
                      rfl

theorem cell22_1883407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_1883407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883407 prefixEnd_1883407 := by exact prefixLift 1883407
  have htrace : WordTrace (prefixWord ++ tailWord_1883407) baseStart_1883407 baseEnd_1883407 := by
    simpa [prefixWord, tailWord_1883407, baseEnd_1883407] using wordTrace_append hprefix tailTrace_1883407
  have hstable : (prefixWord ++ tailWord_1883407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883407).length < 2 ^ (prefixWord ++ tailWord_1883407).sum := by decide
  have hdescent : baseEnd_1883407 < baseStart_1883407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883503 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 2, 3]
def baseStart_1883503 : Nat := 118140960795 + 1883503 * 2 ^ 59
def prefixEnd_1883503 : Nat := 4983230072969 + 3 ^ 40 * 1883503 * 2
def baseEnd_1883503 : Nat := 644761568790299679700289

theorem tailTrace_1883503 : CollatzResearch.WordTrace tailWord_1883503 prefixEnd_1883503 644761568790299679700289 := by
  unfold tailWord_1883503
  simp only [CollatzResearch.WordTrace]
  refine ⟨68696998095397782547519163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45797998730265188365012775 68696998095397782547519163)
  ·
    refine ⟨103045497143096673821278745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68696998095397782547519163 103045497143096673821278745)
    ·
      refine ⟨77284122857322505365959059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103045497143096673821278745 77284122857322505365959059)
      ·
        refine ⟨115926184285983758048938589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77284122857322505365959059 115926184285983758048938589)
        ·
          refine ⟨43472319107243909268351971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115926184285983758048938589 43472319107243909268351971)
          ·
            refine ⟨65208478660865863902527957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43472319107243909268351971 65208478660865863902527957)
            ·
              refine ⟨1528323718614043685215499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65208478660865863902527957 1528323718614043685215499)
              ·
                refine ⟨2292485577921065527823249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528323718614043685215499 2292485577921065527823249)
                ·
                  refine ⟨1719364183440799145867437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292485577921065527823249 1719364183440799145867437)
                  ·
                    refine ⟨644761568790299679700289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719364183440799145867437 644761568790299679700289)
                    ·
                      rfl

theorem cell22_1883503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_1883503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883503 prefixEnd_1883503 := by exact prefixLift 1883503
  have htrace : WordTrace (prefixWord ++ tailWord_1883503) baseStart_1883503 baseEnd_1883503 := by
    simpa [prefixWord, tailWord_1883503, baseEnd_1883503] using wordTrace_append hprefix tailTrace_1883503
  have hstable : (prefixWord ++ tailWord_1883503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883503).length < 2 ^ (prefixWord ++ tailWord_1883503).sum := by decide
  have hdescent : baseEnd_1883503 < baseStart_1883503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883522 : List Nat := [3, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1883522 : Nat := 118140960795 + 1883522 * 2 ^ 59
def prefixEnd_1883522 : Nat := 4983230072969 + 3 ^ 40 * 1883522 * 2
def baseEnd_1883522 : Nat := 214922690959529987825077

theorem tailTrace_1883522 : CollatzResearch.WordTrace tailWord_1883522 prefixEnd_1883522 214922690959529987825077 := by
  unfold tailWord_1883522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17174422770582237198115205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45798460721552632528307213 17174422770582237198115205)
  ·
    refine ⟨3220204269484169474646601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17174422770582237198115205 3220204269484169474646601)
    ·
      refine ⟨2415153202113127105984951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220204269484169474646601 2415153202113127105984951)
      ·
        refine ⟨3622729803169690658977427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415153202113127105984951 3622729803169690658977427)
        ·
          refine ⟨5434094704754535988466141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622729803169690658977427 5434094704754535988466141)
          ·
            refine ⟨2037785514282950995674803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5434094704754535988466141 2037785514282950995674803)
            ·
              refine ⟨3056678271424426493512205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037785514282950995674803 3056678271424426493512205)
              ·
                refine ⟨1146254351784159935067077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3056678271424426493512205 1146254351784159935067077)
                ·
                  refine ⟨214922690959529987825077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146254351784159935067077 214922690959529987825077)
                  ·
                    rfl

theorem cell22_1883522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1883522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883522 prefixEnd_1883522 := by exact prefixLift 1883522
  have htrace : WordTrace (prefixWord ++ tailWord_1883522) baseStart_1883522 baseEnd_1883522 := by
    simpa [prefixWord, tailWord_1883522, baseEnd_1883522] using wordTrace_append hprefix tailTrace_1883522
  have hstable : (prefixWord ++ tailWord_1883522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883522).length < 2 ^ (prefixWord ++ tailWord_1883522).sum := by decide
  have hdescent : baseEnd_1883522 < baseStart_1883522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883638 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1883638 : Nat := 118140960795 + 1883638 * 2 ^ 59
def prefixEnd_1883638 : Nat := 4983230072969 + 3 ^ 40 * 1883638 * 2
def baseEnd_1883638 : Nat := 644807782049204327574875

theorem tailTrace_1883638 : CollatzResearch.WordTrace tailWord_1883638 prefixEnd_1883638 644807782049204327574875 := by
  unfold tailWord_1883638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293870121869293787730223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45801281299939133735789045 4293870121869293787730223)
  ·
    refine ⟨6440805182803940681595335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4293870121869293787730223 6440805182803940681595335)
    ·
      refine ⟨9661207774205911022393003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6440805182803940681595335 9661207774205911022393003)
      ·
        refine ⟨14491811661308866533589505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9661207774205911022393003 14491811661308866533589505)
        ·
          refine ⟨10868858745981649900192129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14491811661308866533589505 10868858745981649900192129)
          ·
            refine ⟨8151644059486237425144097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10868858745981649900192129 8151644059486237425144097)
            ·
              refine ⟨6113733044614678068858073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8151644059486237425144097 6113733044614678068858073)
              ·
                refine ⟨4585299783461008551643555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6113733044614678068858073 4585299783461008551643555)
                ·
                  refine ⟨6877949675191512827465333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585299783461008551643555 6877949675191512827465333)
                  ·
                    refine ⟨644807782049204327574875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6877949675191512827465333 644807782049204327574875)
                    ·
                      rfl

theorem cell22_1883638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1883638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883638 prefixEnd_1883638 := by exact prefixLift 1883638
  have htrace : WordTrace (prefixWord ++ tailWord_1883638) baseStart_1883638 baseEnd_1883638 := by
    simpa [prefixWord, tailWord_1883638, baseEnd_1883638] using wordTrace_append hprefix tailTrace_1883638
  have hstable : (prefixWord ++ tailWord_1883638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883638).length < 2 ^ (prefixWord ++ tailWord_1883638).sum := by decide
  have hdescent : baseEnd_1883638 < baseStart_1883638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883655 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1883655 : Nat := 118140960795 + 1883655 * 2 ^ 59
def prefixEnd_1883655 : Nat := 4983230072969 + 3 ^ 40 * 1883655 * 2
def baseEnd_1883655 : Nat := 644813601496621949899823

theorem tailTrace_1883655 : CollatzResearch.WordTrace tailWord_1883655 prefixEnd_1883655 644813601496621949899823 := by
  unfold tailWord_1883655
  simp only [CollatzResearch.WordTrace]
  refine ⟨68702541990847112507052419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45801694660564741671368279 68702541990847112507052419)
  ·
    refine ⟨103053812986270668760578629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68702541990847112507052419 103053812986270668760578629)
    ·
      refine ⟨19322589934925750392608493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103053812986270668760578629 19322589934925750392608493)
      ·
        refine ⟨7245971225597156397228185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19322589934925750392608493 7245971225597156397228185)
        ·
          refine ⟨5434478419197867297921139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7245971225597156397228185 5434478419197867297921139)
          ·
            refine ⟨8151717628796800946881709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434478419197867297921139 8151717628796800946881709)
            ·
              refine ⟨3056894110798800355080641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8151717628796800946881709 3056894110798800355080641)
              ·
                refine ⟨2292670583099100266310481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056894110798800355080641 2292670583099100266310481)
                ·
                  refine ⟨1719502937324325199732861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292670583099100266310481 1719502937324325199732861)
                  ·
                    refine ⟨644813601496621949899823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719502937324325199732861 644813601496621949899823)
                    ·
                      rfl

theorem cell22_1883655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1883655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883655 prefixEnd_1883655 := by exact prefixLift 1883655
  have htrace : WordTrace (prefixWord ++ tailWord_1883655) baseStart_1883655 baseEnd_1883655 := by
    simpa [prefixWord, tailWord_1883655, baseEnd_1883655] using wordTrace_append hprefix tailTrace_1883655
  have hstable : (prefixWord ++ tailWord_1883655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883655).length < 2 ^ (prefixWord ++ tailWord_1883655).sum := by decide
  have hdescent : baseEnd_1883655 < baseStart_1883655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883672 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 2, 3]
def baseStart_1883672 : Nat := 118140960795 + 1883672 * 2 ^ 59
def prefixEnd_1883672 : Nat := 4983230072969 + 3 ^ 40 * 1883672 * 2
def baseEnd_1883672 : Nat := 644819420944039572224771

theorem tailTrace_1883672 : CollatzResearch.WordTrace tailWord_1883672 prefixEnd_1883672 644819420944039572224771 := by
  unfold tailWord_1883672
  simp only [CollatzResearch.WordTrace]
  refine ⟨34351581015892762205210635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45802108021190349606947513 34351581015892762205210635)
  ·
    refine ⟨51527371523839143307815953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34351581015892762205210635 51527371523839143307815953)
    ·
      refine ⟨38645528642879357480861965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51527371523839143307815953 38645528642879357480861965)
      ·
        refine ⟨14492073241079759055323237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38645528642879357480861965 14492073241079759055323237)
        ·
          refine ⟨2717263732702454822873107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14492073241079759055323237 2717263732702454822873107)
          ·
            refine ⟨4075895599053682234309661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717263732702454822873107 4075895599053682234309661)
            ·
              refine ⟨1528460849645130837866123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4075895599053682234309661 1528460849645130837866123)
              ·
                refine ⟨2292691274467696256799185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528460849645130837866123 2292691274467696256799185)
                ·
                  refine ⟨1719518455850772192599389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2292691274467696256799185 1719518455850772192599389)
                  ·
                    refine ⟨644819420944039572224771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719518455850772192599389 644819420944039572224771)
                    ·
                      rfl

theorem cell22_1883672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_1883672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883672 prefixEnd_1883672 := by exact prefixLift 1883672
  have htrace : WordTrace (prefixWord ++ tailWord_1883672) baseStart_1883672 baseEnd_1883672 := by
    simpa [prefixWord, tailWord_1883672, baseEnd_1883672] using wordTrace_append hprefix tailTrace_1883672
  have hstable : (prefixWord ++ tailWord_1883672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883672).length < 2 ^ (prefixWord ++ tailWord_1883672).sum := by decide
  have hdescent : baseEnd_1883672 < baseStart_1883672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883713 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 5]
def baseStart_1883713 : Nat := 118140960795 + 1883713 * 2 ^ 59
def prefixEnd_1883713 : Nat := 4983230072969 + 3 ^ 40 * 1883713 * 2
def baseEnd_1883713 : Nat := 214944485360643043983215

theorem tailTrace_1883713 : CollatzResearch.WordTrace tailWord_1883713 prefixEnd_1883713 214944485360643043983215 := by
  unfold tailWord_1883713
  simp only [CollatzResearch.WordTrace]
  refine ⟨68704657424636988412663793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45803104949757992275109195 68704657424636988412663793)
  ·
    refine ⟨51528493068477741309497845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68704657424636988412663793 51528493068477741309497845)
    ·
      refine ⟨4830796225169788247765423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51528493068477741309497845 4830796225169788247765423)
      ·
        refine ⟨7246194337754682371648135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4830796225169788247765423 7246194337754682371648135)
        ·
          refine ⟨10869291506632023557472203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246194337754682371648135 10869291506632023557472203)
          ·
            refine ⟨16303937259948035336208305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10869291506632023557472203 16303937259948035336208305)
            ·
              refine ⟨12227952944961026502156229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16303937259948035336208305 12227952944961026502156229)
              ·
                refine ⟨2292741177180192469154293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12227952944961026502156229 2292741177180192469154293)
                ·
                  refine ⟨214944485360643043983215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2292741177180192469154293 214944485360643043983215)
                  ·
                    rfl

theorem cell22_1883713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_1883713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883713 prefixEnd_1883713 := by exact prefixLift 1883713
  have htrace : WordTrace (prefixWord ++ tailWord_1883713) baseStart_1883713 baseEnd_1883713 := by
    simpa [prefixWord, tailWord_1883713, baseEnd_1883713] using wordTrace_append hprefix tailTrace_1883713
  have hstable : (prefixWord ++ tailWord_1883713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883713).length < 2 ^ (prefixWord ++ tailWord_1883713).sum := by decide
  have hdescent : baseEnd_1883713 < baseStart_1883713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883717 : List Nat := [1, 3, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_1883717 : Nat := 118140960795 + 1883717 * 2 ^ 59
def prefixEnd_1883717 : Nat := 4983230072969 + 3 ^ 40 * 1883717 * 2
def baseEnd_1883717 : Nat := 644834825363674454849633

theorem tailTrace_1883717 : CollatzResearch.WordTrace tailWord_1883717 prefixEnd_1883717 644834825363674454849633 := by
  unfold tailWord_1883717
  simp only [CollatzResearch.WordTrace]
  refine ⟨68704803316622497095809405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45803202211081664730539603 68704803316622497095809405)
  ·
    refine ⟨25764301243733436410928527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68704803316622497095809405 25764301243733436410928527)
    ·
      refine ⟨38646451865600154616392791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25764301243733436410928527 38646451865600154616392791)
      ·
        refine ⟨57969677798400231924589187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38646451865600154616392791 57969677798400231924589187)
        ·
          refine ⟨86954516697600347886883781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57969677798400231924589187 86954516697600347886883781)
          ·
            refine ⟨16303971880800065228790709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86954516697600347886883781 16303971880800065228790709)
            ·
              refine ⟨1528497363825006115199129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16303971880800065228790709 1528497363825006115199129)
              ·
                refine ⟨1146373022868754586399347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528497363825006115199129 1146373022868754586399347)
                ·
                  refine ⟨1719559534303131879599021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146373022868754586399347 1719559534303131879599021)
                  ·
                    refine ⟨644834825363674454849633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719559534303131879599021 644834825363674454849633)
                    ·
                      rfl

theorem cell22_1883717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_1883717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883717 prefixEnd_1883717 := by exact prefixLift 1883717
  have htrace : WordTrace (prefixWord ++ tailWord_1883717) baseStart_1883717 baseEnd_1883717 := by
    simpa [prefixWord, tailWord_1883717, baseEnd_1883717] using wordTrace_append hprefix tailTrace_1883717
  have hstable : (prefixWord ++ tailWord_1883717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883717).length < 2 ^ (prefixWord ++ tailWord_1883717).sum := by decide
  have hdescent : baseEnd_1883717 < baseStart_1883717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883726 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1883726 : Nat := 118140960795 + 1883726 * 2 ^ 59
def prefixEnd_1883726 : Nat := 4983230072969 + 3 ^ 40 * 1883726 * 2
def baseEnd_1883726 : Nat := 644837906247601431374605

theorem tailTrace_1883726 : CollatzResearch.WordTrace tailWord_1883726 prefixEnd_1883726 644837906247601431374605 := by
  unfold tailWord_1883726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588141446698736454110879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45803421049059927755258021 8588141446698736454110879)
  ·
    refine ⟨12882212170048104681166319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8588141446698736454110879 12882212170048104681166319)
    ·
      refine ⟨19323318255072157021749479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12882212170048104681166319 19323318255072157021749479)
      ·
        refine ⟨28984977382608235532624219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19323318255072157021749479 28984977382608235532624219)
        ·
          refine ⟨43477466073912353298936329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28984977382608235532624219 43477466073912353298936329)
          ·
            refine ⟨32608099555434264974202247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43477466073912353298936329 32608099555434264974202247)
            ·
              refine ⟨48912149333151397461303371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32608099555434264974202247 48912149333151397461303371)
              ·
                refine ⟨73368223999727096191955057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48912149333151397461303371 73368223999727096191955057)
                ·
                  refine ⟨55026167999795322143966293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73368223999727096191955057 55026167999795322143966293)
                  ·
                    refine ⟨644837906247601431374605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55026167999795322143966293 644837906247601431374605)
                    ·
                      rfl

theorem cell22_1883726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1883726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883726 prefixEnd_1883726 := by exact prefixLift 1883726
  have htrace : WordTrace (prefixWord ++ tailWord_1883726) baseStart_1883726 baseEnd_1883726 := by
    simpa [prefixWord, tailWord_1883726, baseEnd_1883726] using wordTrace_append hprefix tailTrace_1883726
  have hstable : (prefixWord ++ tailWord_1883726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883726).length < 2 ^ (prefixWord ++ tailWord_1883726).sum := by decide
  have hdescent : baseEnd_1883726 < baseStart_1883726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883730 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_1883730 : Nat := 118140960795 + 1883730 * 2 ^ 59
def prefixEnd_1883730 : Nat := 4983230072969 + 3 ^ 40 * 1883730 * 2
def baseEnd_1883730 : Nat := 214946425176448918091531

theorem tailTrace_1883730 : CollatzResearch.WordTrace tailWord_1883730 prefixEnd_1883730 214946425176448918091531 := by
  unfold tailWord_1883730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176319366393850079008161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45803518310383600210688429 17176319366393850079008161)
  ·
    refine ⟨12882239524795387559256121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17176319366393850079008161 12882239524795387559256121)
    ·
      refine ⟨9661679643596540669442091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12882239524795387559256121 9661679643596540669442091)
      ·
        refine ⟨14492519465394811004163137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9661679643596540669442091 14492519465394811004163137)
        ·
          refine ⟨10869389599046108253122353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14492519465394811004163137 10869389599046108253122353)
          ·
            refine ⟨8152042199284581189841765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10869389599046108253122353 8152042199284581189841765)
            ·
              refine ⟨1528507912365858973095331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8152042199284581189841765 1528507912365858973095331)
              ·
                refine ⟨2292761868548788459642997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528507912365858973095331 2292761868548788459642997)
                ·
                  refine ⟨214946425176448918091531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2292761868548788459642997 214946425176448918091531)
                  ·
                    rfl

theorem cell22_1883730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_1883730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883730 prefixEnd_1883730 := by exact prefixLift 1883730
  have htrace : WordTrace (prefixWord ++ tailWord_1883730) baseStart_1883730 baseEnd_1883730 := by
    simpa [prefixWord, tailWord_1883730, baseEnd_1883730] using wordTrace_append hprefix tailTrace_1883730
  have hstable : (prefixWord ++ tailWord_1883730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883730).length < 2 ^ (prefixWord ++ tailWord_1883730).sum := by decide
  have hdescent : baseEnd_1883730 < baseStart_1883730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883790 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1883790 : Nat := 118140960795 + 1883790 * 2 ^ 59
def prefixEnd_1883790 : Nat := 4983230072969 + 3 ^ 40 * 1883790 * 2
def baseEnd_1883790 : Nat := 644859814755526597774409

theorem tailTrace_1883790 : CollatzResearch.WordTrace tailWord_1883790 prefixEnd_1883790 644859814755526597774409 := by
  unfold tailWord_1883790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588433230669753820402103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45804977230238687042144549 8588433230669753820402103)
  ·
    refine ⟨12882649846004630730603155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8588433230669753820402103 12882649846004630730603155)
    ·
      refine ⟨19323974769006946095904733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12882649846004630730603155 19323974769006946095904733)
      ·
        refine ⟨7246490538377604785964275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19323974769006946095904733 7246490538377604785964275)
        ·
          refine ⟨10869735807566407178946413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246490538377604785964275 10869735807566407178946413)
          ·
            refine ⟨4076150927837402692104905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10869735807566407178946413 4076150927837402692104905)
            ·
              refine ⟨3057113195878052019078679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076150927837402692104905 3057113195878052019078679)
              ·
                refine ⟨4585669793817078028618019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057113195878052019078679 4585669793817078028618019)
                ·
                  refine ⟨6878504690725617042927029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585669793817078028618019 6878504690725617042927029)
                  ·
                    refine ⟨644859814755526597774409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6878504690725617042927029 644859814755526597774409)
                    ·
                      rfl

theorem cell22_1883790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1883790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883790 prefixEnd_1883790 := by exact prefixLift 1883790
  have htrace : WordTrace (prefixWord ++ tailWord_1883790) baseStart_1883790 baseEnd_1883790 := by
    simpa [prefixWord, tailWord_1883790, baseEnd_1883790] using wordTrace_append hprefix tailTrace_1883790
  have hstable : (prefixWord ++ tailWord_1883790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883790).length < 2 ^ (prefixWord ++ tailWord_1883790).sum := by decide
  have hdescent : baseEnd_1883790 < baseStart_1883790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883801 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_1883801 : Nat := 118140960795 + 1883801 * 2 ^ 59
def prefixEnd_1883801 : Nat := 4983230072969 + 3 ^ 40 * 1883801 * 2
def baseEnd_1883801 : Nat := 644863580280326235749375

theorem tailTrace_1883801 : CollatzResearch.WordTrace tailWord_1883801 prefixEnd_1883801 644863580280326235749375 := by
  unfold tailWord_1883801
  simp only [CollatzResearch.WordTrace]
  refine ⟨68707867048318179441867257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45805244698878786294578171 68707867048318179441867257)
  ·
    refine ⟨51530900286238634581400443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68707867048318179441867257 51530900286238634581400443)
    ·
      refine ⟨77296350429357951872100665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51530900286238634581400443 77296350429357951872100665)
      ·
        refine ⟨57972262822018463904075499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77296350429357951872100665 57972262822018463904075499)
        ·
          refine ⟨86958394233027695856113249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57972262822018463904075499 86958394233027695856113249)
          ·
            refine ⟨65218795674770771892084937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86958394233027695856113249 65218795674770771892084937)
            ·
              refine ⟨48914096756078078919063703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65218795674770771892084937 48914096756078078919063703)
              ·
                refine ⟨73371145134117118378595555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48914096756078078919063703 73371145134117118378595555)
                ·
                  refine ⟨110056717701175677567893333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73371145134117118378595555 110056717701175677567893333)
                  ·
                    refine ⟨644863580280326235749375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 110056717701175677567893333 644863580280326235749375)
                    ·
                      rfl

theorem cell22_1883801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_1883801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883801 prefixEnd_1883801 := by exact prefixLift 1883801
  have htrace : WordTrace (prefixWord ++ tailWord_1883801) baseStart_1883801 baseEnd_1883801 := by
    simpa [prefixWord, tailWord_1883801, baseEnd_1883801] using wordTrace_append hprefix tailTrace_1883801
  have hstable : (prefixWord ++ tailWord_1883801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883801).length < 2 ^ (prefixWord ++ tailWord_1883801).sum := by decide
  have hdescent : baseEnd_1883801 < baseStart_1883801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883925 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1883925 : Nat := 118140960795 + 1883925 * 2 ^ 59
def prefixEnd_1883925 : Nat := 4983230072969 + 3 ^ 40 * 1883925 * 2
def baseEnd_1883925 : Nat := 644906028014431245648995

theorem tailTrace_1883925 : CollatzResearch.WordTrace tailWord_1883925 prefixEnd_1883925 644906028014431245648995 := by
  unfold tailWord_1883925
  simp only [CollatzResearch.WordTrace]
  refine ⟨68712389699868948619381229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45808259799912632412920819 68712389699868948619381229)
  ·
    refine ⟨25767146137450855732267961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68712389699868948619381229 25767146137450855732267961)
    ·
      refine ⟨19325359603088141799200971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25767146137450855732267961 19325359603088141799200971)
      ·
        refine ⟨28988039404632212698801457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19325359603088141799200971 28988039404632212698801457)
        ·
          refine ⟨21741029553474159524101093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28988039404632212698801457 21741029553474159524101093)
          ·
            refine ⟨4076443041276404910768955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21741029553474159524101093 4076443041276404910768955)
            ·
              refine ⟨6114664561914607366153433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076443041276404910768955 6114664561914607366153433)
              ·
                refine ⟨4585998421435955524615075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6114664561914607366153433 4585998421435955524615075)
                ·
                  refine ⟨6878997632153933286922613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585998421435955524615075 6878997632153933286922613)
                  ·
                    refine ⟨644906028014431245648995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6878997632153933286922613 644906028014431245648995)
                    ·
                      rfl

theorem cell22_1883925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1883925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883925 prefixEnd_1883925 := by exact prefixLift 1883925
  have htrace : WordTrace (prefixWord ++ tailWord_1883925) baseStart_1883925 baseEnd_1883925 := by
    simpa [prefixWord, tailWord_1883925, baseEnd_1883925] using wordTrace_append hprefix tailTrace_1883925
  have hstable : (prefixWord ++ tailWord_1883925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883925).length < 2 ^ (prefixWord ++ tailWord_1883925).sum := by decide
  have hdescent : baseEnd_1883925 < baseStart_1883925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883944 : List Nat := [2, 1, 5, 1, 1, 2, 4, 2, 4]
def baseStart_1883944 : Nat := 118140960795 + 1883944 * 2 ^ 59
def prefixEnd_1883944 : Nat := 4983230072969 + 3 ^ 40 * 1883944 * 2
def baseEnd_1883944 : Nat := 214970844034240509807979

theorem tailTrace_1883944 : CollatzResearch.WordTrace tailWord_1883944 prefixEnd_1883944 214970844034240509807979 := by
  unfold tailWord_1883944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34356541343400057432161443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45808721791200076576215257 34356541343400057432161443)
  ·
    refine ⟨51534812015100086148242165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34356541343400057432161443 51534812015100086148242165)
    ·
      refine ⟨4831388626415633076397703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51534812015100086148242165 4831388626415633076397703)
      ·
        refine ⟨7247082939623449614596555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831388626415633076397703 7247082939623449614596555)
        ·
          refine ⟨10870624409435174421894833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7247082939623449614596555 10870624409435174421894833)
          ·
            refine ⟨8152968307076380816421125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10870624409435174421894833 8152968307076380816421125)
            ·
              refine ⟨1528681557576821403078961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8152968307076380816421125 1528681557576821403078961)
              ·
                refine ⟨1146511168182616052309221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528681557576821403078961 1146511168182616052309221)
                ·
                  refine ⟨214970844034240509807979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146511168182616052309221 214970844034240509807979)
                  ·
                    rfl

theorem cell22_1883944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_1883944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883944 prefixEnd_1883944 := by exact prefixLift 1883944
  have htrace : WordTrace (prefixWord ++ tailWord_1883944) baseStart_1883944 baseEnd_1883944 := by
    simpa [prefixWord, tailWord_1883944, baseEnd_1883944] using wordTrace_append hprefix tailTrace_1883944
  have hstable : (prefixWord ++ tailWord_1883944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883944).length < 2 ^ (prefixWord ++ tailWord_1883944).sum := by decide
  have hdescent : baseEnd_1883944 < baseStart_1883944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1883974 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1883974 : Nat := 118140960795 + 1883974 * 2 ^ 59
def prefixEnd_1883974 : Nat := 4983230072969 + 3 ^ 40 * 1883974 * 2
def baseEnd_1883974 : Nat := 644922801715811451173845

theorem tailTrace_1883974 : CollatzResearch.WordTrace tailWord_1883974 prefixEnd_1883974 644922801715811451173845 := by
  unfold tailWord_1883974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2147318027396607187122343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45809451251127619991943317 2147318027396607187122343)
  ·
    refine ⟨3220977041094910780683515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2147318027396607187122343 3220977041094910780683515)
    ·
      refine ⟨4831465561642366171025273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3220977041094910780683515 4831465561642366171025273)
      ·
        refine ⟨3623599171231774628268955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4831465561642366171025273 3623599171231774628268955)
        ·
          refine ⟨5435398756847661942403433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623599171231774628268955 5435398756847661942403433)
          ·
            refine ⟨4076549067635746456802575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435398756847661942403433 4076549067635746456802575)
            ·
              refine ⟨6114823601453619685203863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076549067635746456802575 6114823601453619685203863)
              ·
                refine ⟨9172235402180429527805795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114823601453619685203863 9172235402180429527805795)
                ·
                  refine ⟨13758353103270644291708693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9172235402180429527805795 13758353103270644291708693)
                  ·
                    refine ⟨644922801715811451173845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13758353103270644291708693 644922801715811451173845)
                    ·
                      rfl

theorem cell22_1883974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1883974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1883974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1883974 prefixEnd_1883974 := by exact prefixLift 1883974
  have htrace : WordTrace (prefixWord ++ tailWord_1883974) baseStart_1883974 baseEnd_1883974 := by
    simpa [prefixWord, tailWord_1883974, baseEnd_1883974] using wordTrace_append hprefix tailTrace_1883974
  have hstable : (prefixWord ++ tailWord_1883974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1883974).length < 2 ^ (prefixWord ++ tailWord_1883974).sum := by decide
  have hdescent : baseEnd_1883974 < baseStart_1883974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1883974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884000 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 7]
def baseStart_1884000 : Nat := 118140960795 + 1884000 * 2 ^ 59
def prefixEnd_1884000 : Nat := 4983230072969 + 3 ^ 40 * 1884000 * 2
def baseEnd_1884000 : Nat := 214977234015718683341255

theorem tailTrace_1884000 : CollatzResearch.WordTrace tailWord_1884000 prefixEnd_1884000 214977234015718683341255 := by
  unfold tailWord_1884000
  simp only [CollatzResearch.WordTrace]
  refine ⟨34357562587298618214180727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45810083449731490952240969 34357562587298618214180727)
  ·
    refine ⟨51536343880947927321271091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34357562587298618214180727 51536343880947927321271091)
    ·
      refine ⟨77304515821421890981906637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51536343880947927321271091 77304515821421890981906637)
      ·
        refine ⟨28989193433033209118214989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77304515821421890981906637 28989193433033209118214989)
        ·
          refine ⟨10870947537387453419330621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28989193433033209118214989 10870947537387453419330621)
          ·
            refine ⟨4076605326520295032248983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10870947537387453419330621 4076605326520295032248983)
            ·
              refine ⟨6114907989780442548373475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076605326520295032248983 6114907989780442548373475)
              ·
                refine ⟨9172361984670663822560213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114907989780442548373475 9172361984670663822560213)
                ·
                  refine ⟨214977234015718683341255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9172361984670663822560213 214977234015718683341255)
                  ·
                    rfl

theorem cell22_1884000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_1884000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884000 prefixEnd_1884000 := by exact prefixLift 1884000
  have htrace : WordTrace (prefixWord ++ tailWord_1884000) baseStart_1884000 baseEnd_1884000 := by
    simpa [prefixWord, tailWord_1884000, baseEnd_1884000] using wordTrace_append hprefix tailTrace_1884000
  have hstable : (prefixWord ++ tailWord_1884000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884000).length < 2 ^ (prefixWord ++ tailWord_1884000).sum := by decide
  have hdescent : baseEnd_1884000 < baseStart_1884000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884004 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_1884004 : Nat := 118140960795 + 1884004 * 2 ^ 59
def prefixEnd_1884004 : Nat := 4983230072969 + 3 ^ 40 * 1884004 * 2
def baseEnd_1884004 : Nat := 644933071328901372923753

theorem tailTrace_1884004 : CollatzResearch.WordTrace tailWord_1884004 prefixEnd_1884004 644933071328901372923753 := by
  unfold tailWord_1884004
  simp only [CollatzResearch.WordTrace]
  refine ⟨34357635533291372555753533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45810180711055163407671377 34357635533291372555753533)
  ·
    refine ⟨12884113324984264708407575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34357635533291372555753533 12884113324984264708407575)
    ·
      refine ⟨19326169987476397062611363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12884113324984264708407575 19326169987476397062611363)
      ·
        refine ⟨28989254981214595593917045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19326169987476397062611363 28989254981214595593917045)
        ·
          refine ⟨2717742654488868336929723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28989254981214595593917045 2717742654488868336929723)
          ·
            refine ⟨4076613981733302505394585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717742654488868336929723 4076613981733302505394585)
            ·
              refine ⟨3057460486299976879045939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076613981733302505394585 3057460486299976879045939)
              ·
                refine ⟨4586190729449965318568909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057460486299976879045939 4586190729449965318568909)
                ·
                  refine ⟨1719821523543736994463341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4586190729449965318568909 1719821523543736994463341)
                  ·
                    refine ⟨644933071328901372923753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719821523543736994463341 644933071328901372923753)
                    ·
                      rfl

theorem cell22_1884004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_1884004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884004 prefixEnd_1884004 := by exact prefixLift 1884004
  have htrace : WordTrace (prefixWord ++ tailWord_1884004) baseStart_1884004 baseEnd_1884004 := by
    simpa [prefixWord, tailWord_1884004, baseEnd_1884004] using wordTrace_append hprefix tailTrace_1884004
  have hstable : (prefixWord ++ tailWord_1884004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884004).length < 2 ^ (prefixWord ++ tailWord_1884004).sum := by decide
  have hdescent : baseEnd_1884004 < baseStart_1884004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884017 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 5]
def baseStart_1884017 : Nat := 118140960795 + 1884017 * 2 ^ 59
def prefixEnd_1884017 : Nat := 4983230072969 + 3 ^ 40 * 1884017 * 2
def baseEnd_1884017 : Nat := 214979173831524557449571

theorem tailTrace_1884017 : CollatzResearch.WordTrace tailWord_1884017 prefixEnd_1884017 214979173831524557449571 := by
  unfold tailWord_1884017
  simp only [CollatzResearch.WordTrace]
  refine ⟨68715745215535648331730305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45810496810357098887820203 68715745215535648331730305)
  ·
    refine ⟨51536808911651736248797729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68715745215535648331730305 51536808911651736248797729)
    ·
      refine ⟨38652606683738802186598297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51536808911651736248797729 38652606683738802186598297)
      ·
        refine ⟨28989455012804101639948723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38652606683738802186598297 28989455012804101639948723)
        ·
          refine ⟨43484182519206152459923085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28989455012804101639948723 43484182519206152459923085)
          ·
            refine ⟨16306568444702307172471157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43484182519206152459923085 16306568444702307172471157)
            ·
              refine ⟨1528740791690841297419171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16306568444702307172471157 1528740791690841297419171)
              ·
                refine ⟨2293111187536261946128757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528740791690841297419171 2293111187536261946128757)
                ·
                  refine ⟨214979173831524557449571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2293111187536261946128757 214979173831524557449571)
                  ·
                    rfl

theorem cell22_1884017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_1884017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884017 prefixEnd_1884017 := by exact prefixLift 1884017
  have htrace : WordTrace (prefixWord ++ tailWord_1884017) baseStart_1884017 baseEnd_1884017 := by
    simpa [prefixWord, tailWord_1884017, baseEnd_1884017] using wordTrace_append hprefix tailTrace_1884017
  have hstable : (prefixWord ++ tailWord_1884017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884017).length < 2 ^ (prefixWord ++ tailWord_1884017).sum := by decide
  have hdescent : baseEnd_1884017 < baseStart_1884017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884120 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_1884120 : Nat := 118140960795 + 1884120 * 2 ^ 59
def prefixEnd_1884120 : Nat := 4983230072969 + 3 ^ 40 * 1884120 * 2
def baseEnd_1884120 : Nat := 644972780499515737023397

theorem tailTrace_1884120 : CollatzResearch.WordTrace tailWord_1884120 prefixEnd_1884120 644972780499515737023397 := by
  unfold tailWord_1884120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34359750967081248461364907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45813001289441664615153209 34359750967081248461364907)
  ·
    refine ⟨51539626450621872692047361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34359750967081248461364907 51539626450621872692047361)
    ·
      refine ⟨38654719837966404519035521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51539626450621872692047361 38654719837966404519035521)
      ·
        refine ⟨28991039878474803389276641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38654719837966404519035521 28991039878474803389276641)
        ·
          refine ⟨21743279908856102541957481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28991039878474803389276641 21743279908856102541957481)
          ·
            refine ⟨16307459931642076906468111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21743279908856102541957481 16307459931642076906468111)
            ·
              refine ⟨24461189897463115359702167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16307459931642076906468111 24461189897463115359702167)
              ·
                refine ⟨36691784846194673039553251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24461189897463115359702167 36691784846194673039553251)
                ·
                  refine ⟨55037677269292009559329877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36691784846194673039553251 55037677269292009559329877)
                  ·
                    refine ⟨644972780499515737023397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55037677269292009559329877 644972780499515737023397)
                    ·
                      rfl

theorem cell22_1884120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_1884120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884120 prefixEnd_1884120 := by exact prefixLift 1884120
  have htrace : WordTrace (prefixWord ++ tailWord_1884120) baseStart_1884120 baseEnd_1884120 := by
    simpa [prefixWord, tailWord_1884120, baseEnd_1884120] using wordTrace_append hprefix tailTrace_1884120
  have hstable : (prefixWord ++ tailWord_1884120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884120).length < 2 ^ (prefixWord ++ tailWord_1884120).sum := by decide
  have hdescent : baseEnd_1884120 < baseStart_1884120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884141 : List Nat := [1, 5, 1, 4, 1, 1, 3, 6]
def baseStart_1884141 : Nat := 118140960795 + 1884141 * 2 ^ 59
def prefixEnd_1884141 : Nat := 4983230072969 + 3 ^ 40 * 1884141 * 2
def baseEnd_1884141 : Nat := 71664441025408742472037

theorem tailTrace_1884141 : CollatzResearch.WordTrace tailWord_1884141 prefixEnd_1884141 71664441025408742472037 := by
  unfold tailWord_1884141
  simp only [CollatzResearch.WordTrace]
  refine ⟨68720267867086417509244277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45813511911390945006162851 68720267867086417509244277)
  ·
    refine ⟨6442525112539351641491651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68720267867086417509244277 6442525112539351641491651)
    ·
      refine ⟨9663787668809027462237477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442525112539351641491651 9663787668809027462237477)
      ·
        refine ⟨1811960187901692649169527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9663787668809027462237477 1811960187901692649169527)
        ·
          refine ⟨2717940281852538973754291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811960187901692649169527 2717940281852538973754291)
          ·
            refine ⟨4076910422778808460631437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717940281852538973754291 4076910422778808460631437)
            ·
              refine ⟨1528841408542053172736789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4076910422778808460631437 1528841408542053172736789)
              ·
                refine ⟨71664441025408742472037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1528841408542053172736789 71664441025408742472037)
                ·
                  rfl

theorem cell22_1884141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 6].length) (baseStart_1884141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884141 prefixEnd_1884141 := by exact prefixLift 1884141
  have htrace : WordTrace (prefixWord ++ tailWord_1884141) baseStart_1884141 baseEnd_1884141 := by
    simpa [prefixWord, tailWord_1884141, baseEnd_1884141] using wordTrace_append hprefix tailTrace_1884141
  have hstable : (prefixWord ++ tailWord_1884141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884141).length < 2 ^ (prefixWord ++ tailWord_1884141).sum := by decide
  have hdescent : baseEnd_1884141 < baseStart_1884141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884156 : List Nat := [2, 2, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_1884156 : Nat := 118140960795 + 1884156 * 2 ^ 59
def prefixEnd_1884156 : Nat := 4983230072969 + 3 ^ 40 * 1884156 * 2
def baseEnd_1884156 : Nat := 644985104035223643123287

theorem tailTrace_1884156 : CollatzResearch.WordTrace tailWord_1884156 prefixEnd_1884156 644985104035223643123287 := by
  unfold tailWord_1884156
  simp only [CollatzResearch.WordTrace]
  refine ⟨34360407481016037535520161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45813876641354716714026881 34360407481016037535520161)
  ·
    refine ⟨25770305610762028151640121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34360407481016037535520161 25770305610762028151640121)
    ·
      refine ⟨19327729208071521113730091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25770305610762028151640121 19327729208071521113730091)
      ·
        refine ⟨28991593812107281670595137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19327729208071521113730091 28991593812107281670595137)
        ·
          refine ⟨21743695359080461252946353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28991593812107281670595137 21743695359080461252946353)
          ·
            refine ⟨16307771519310345939709765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21743695359080461252946353 16307771519310345939709765)
            ·
              refine ⟨3057707159870689863695581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16307771519310345939709765 3057707159870689863695581)
              ·
                refine ⟨1146640184951508698885843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3057707159870689863695581 1146640184951508698885843)
                ·
                  refine ⟨1719960277427263048328765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146640184951508698885843 1719960277427263048328765)
                  ·
                    refine ⟨644985104035223643123287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1719960277427263048328765 644985104035223643123287)
                    ·
                      rfl

theorem cell22_1884156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_1884156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884156 prefixEnd_1884156 := by exact prefixLift 1884156
  have htrace : WordTrace (prefixWord ++ tailWord_1884156) baseStart_1884156 baseEnd_1884156 := by
    simpa [prefixWord, tailWord_1884156, baseEnd_1884156] using wordTrace_append hprefix tailTrace_1884156
  have hstable : (prefixWord ++ tailWord_1884156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884156).length < 2 ^ (prefixWord ++ tailWord_1884156).sum := by decide
  have hdescent : baseEnd_1884156 < baseStart_1884156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884167 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1884167 : Nat := 118140960795 + 1884167 * 2 ^ 59
def prefixEnd_1884167 : Nat := 4983230072969 + 3 ^ 40 * 1884167 * 2
def baseEnd_1884167 : Nat := 644988869560023281098253

theorem tailTrace_1884167 : CollatzResearch.WordTrace tailWord_1884167 prefixEnd_1884167 644988869560023281098253 := by
  unfold tailWord_1884167
  simp only [CollatzResearch.WordTrace]
  refine ⟨68721216164992223949690755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45814144109994815966460503 68721216164992223949690755)
  ·
    refine ⟨103081824247488335924536133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68721216164992223949690755 103081824247488335924536133)
    ·
      refine ⟨19327842046404062985850525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103081824247488335924536133 19327842046404062985850525)
      ·
        refine ⟨7247940767401523619693947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19327842046404062985850525 7247940767401523619693947)
        ·
          refine ⟨10871911151102285429540921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7247940767401523619693947 10871911151102285429540921)
          ·
            refine ⟨8153933363326714072155691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10871911151102285429540921 8153933363326714072155691)
            ·
              refine ⟨12230900044990071108233537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8153933363326714072155691 12230900044990071108233537)
              ·
                refine ⟨9173175033742553331175153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12230900044990071108233537 9173175033742553331175153)
                ·
                  refine ⟨6879881275306914998381365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9173175033742553331175153 6879881275306914998381365)
                  ·
                    refine ⟨644988869560023281098253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6879881275306914998381365 644988869560023281098253)
                    ·
                      rfl

theorem cell22_1884167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1884167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884167 prefixEnd_1884167 := by exact prefixLift 1884167
  have htrace : WordTrace (prefixWord ++ tailWord_1884167) baseStart_1884167 baseEnd_1884167 := by
    simpa [prefixWord, tailWord_1884167, baseEnd_1884167] using wordTrace_append hprefix tailTrace_1884167
  have hstable : (prefixWord ++ tailWord_1884167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884167).length < 2 ^ (prefixWord ++ tailWord_1884167).sum := by decide
  have hdescent : baseEnd_1884167 < baseStart_1884167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884197 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 6]
def baseStart_1884197 : Nat := 118140960795 + 1884197 * 2 ^ 59
def prefixEnd_1884197 : Nat := 4983230072969 + 3 ^ 40 * 1884197 * 2
def baseEnd_1884197 : Nat := 214999713057704400949387

theorem tailTrace_1884197 : CollatzResearch.WordTrace tailWord_1884197 prefixEnd_1884197 214999713057704400949387 := by
  unfold tailWord_1884197
  simp only [CollatzResearch.WordTrace]
  refine ⟨68722310354883539073282845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45814873569922359382188563 68722310354883539073282845)
  ·
    refine ⟨25770866383081327152481067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68722310354883539073282845 25770866383081327152481067)
    ·
      refine ⟨38656299574621990728721601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25770866383081327152481067 38656299574621990728721601)
      ·
        refine ⟨28992224680966493046541201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38656299574621990728721601 28992224680966493046541201)
        ·
          refine ⟨21744168510724869784905901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28992224680966493046541201 21744168510724869784905901)
          ·
            refine ⟨8154063191521826169339713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21744168510724869784905901 8154063191521826169339713)
            ·
              refine ⟨6115547393641369627004785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8154063191521826169339713 6115547393641369627004785)
              ·
                refine ⟨4586660545231027220253589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6115547393641369627004785 4586660545231027220253589)
                ·
                  refine ⟨214999713057704400949387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4586660545231027220253589 214999713057704400949387)
                  ·
                    rfl

theorem cell22_1884197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_1884197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884197 prefixEnd_1884197 := by exact prefixLift 1884197
  have htrace : WordTrace (prefixWord ++ tailWord_1884197) baseStart_1884197 baseEnd_1884197 := by
    simpa [prefixWord, tailWord_1884197, baseEnd_1884197] using wordTrace_append hprefix tailTrace_1884197
  have hstable : (prefixWord ++ tailWord_1884197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884197).length < 2 ^ (prefixWord ++ tailWord_1884197).sum := by decide
  have hdescent : baseEnd_1884197 < baseStart_1884197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884229 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_1884229 : Nat := 118140960795 + 1884229 * 2 ^ 59
def prefixEnd_1884229 : Nat := 4983230072969 + 3 ^ 40 * 1884229 * 2
def baseEnd_1884229 : Nat := 645010093427075786048063

theorem tailTrace_1884229 : CollatzResearch.WordTrace tailWord_1884229 prefixEnd_1884229 645010093427075786048063 := by
  unfold tailWord_1884229
  simp only [CollatzResearch.WordTrace]
  refine ⟨68723477490767608538447741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45815651660511739025631827 68723477490767608538447741)
  ·
    refine ⟨25771304059037853201917903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68723477490767608538447741 25771304059037853201917903)
    ·
      refine ⟨38656956088556779802876855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25771304059037853201917903 38656956088556779802876855)
      ·
        refine ⟨57985434132835169704315283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38656956088556779802876855 57985434132835169704315283)
        ·
          refine ⟨86978151199252754556472925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57985434132835169704315283 86978151199252754556472925)
          ·
            refine ⟨32616806699719782958677347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86978151199252754556472925 32616806699719782958677347)
            ·
              refine ⟨48925210049579674438016021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32616806699719782958677347 48925210049579674438016021)
              ·
                refine ⟨2293369221074047239282001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48925210049579674438016021 2293369221074047239282001)
                ·
                  refine ⟨1720026915805535429461501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2293369221074047239282001 1720026915805535429461501)
                  ·
                    refine ⟨645010093427075786048063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1720026915805535429461501 645010093427075786048063)
                    ·
                      rfl

theorem cell22_1884229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_1884229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884229 prefixEnd_1884229 := by exact prefixLift 1884229
  have htrace : WordTrace (prefixWord ++ tailWord_1884229) baseStart_1884229 baseEnd_1884229 := by
    simpa [prefixWord, tailWord_1884229, baseEnd_1884229] using wordTrace_append hprefix tailTrace_1884229
  have hstable : (prefixWord ++ tailWord_1884229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884229).length < 2 ^ (prefixWord ++ tailWord_1884229).sum := by decide
  have hdescent : baseEnd_1884229 < baseStart_1884229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884231 : List Nat := [1, 1, 4, 1, 3, 1, 5, 2, 4]
def baseStart_1884231 : Nat := 118140960795 + 1884231 * 2 ^ 59
def prefixEnd_1884231 : Nat := 4983230072969 + 3 ^ 40 * 1884231 * 2
def baseEnd_1884231 : Nat := 215003592689316149166019

theorem tailTrace_1884231 : CollatzResearch.WordTrace tailWord_1884231 prefixEnd_1884231 215003592689316149166019 := by
  unfold tailWord_1884231
  simp only [CollatzResearch.WordTrace]
  refine ⟨68723550436760362880020547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45815700291173575253347031 68723550436760362880020547)
  ·
    refine ⟨103085325655140544320030821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68723550436760362880020547 103085325655140544320030821)
    ·
      refine ⟨19328498560338852060005779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103085325655140544320030821 19328498560338852060005779)
      ·
        refine ⟨28992747840508278090008669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19328498560338852060005779 28992747840508278090008669)
        ·
          refine ⟨10872280440190604283753251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28992747840508278090008669 10872280440190604283753251)
          ·
            refine ⟨16308420660285906425629877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872280440190604283753251 16308420660285906425629877)
            ·
              refine ⟨1528914436901803727402801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16308420660285906425629877 1528914436901803727402801)
              ·
                refine ⟨1146685827676352795552101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528914436901803727402801 1146685827676352795552101)
                ·
                  refine ⟨215003592689316149166019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1146685827676352795552101 215003592689316149166019)
                  ·
                    rfl

theorem cell22_1884231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 4].length) (baseStart_1884231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884231 prefixEnd_1884231 := by exact prefixLift 1884231
  have htrace : WordTrace (prefixWord ++ tailWord_1884231) baseStart_1884231 baseEnd_1884231 := by
    simpa [prefixWord, tailWord_1884231, baseEnd_1884231] using wordTrace_append hprefix tailTrace_1884231
  have hstable : (prefixWord ++ tailWord_1884231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884231).length < 2 ^ (prefixWord ++ tailWord_1884231).sum := by decide
  have hdescent : baseEnd_1884231 < baseStart_1884231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884426 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1884426 : Nat := 118140960795 + 1884426 * 2 ^ 59
def prefixEnd_1884426 : Nat := 4983230072969 + 3 ^ 40 * 1884426 * 2
def baseEnd_1884426 : Nat := 645077530553032938872459

theorem tailTrace_1884426 : CollatzResearch.WordTrace tailWord_1884426 prefixEnd_1884426 645077530553032938872459 := by
  unfold tailWord_1884426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182665667763477795842283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45820441780702607455579421 17182665667763477795842283)
  ·
    refine ⟨25773998501645216693763425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17182665667763477795842283 25773998501645216693763425)
    ·
      refine ⟨19330498876233912520322569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25773998501645216693763425 19330498876233912520322569)
      ·
        refine ⟨14497874157175434390241927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19330498876233912520322569 14497874157175434390241927)
        ·
          refine ⟨21746811235763151585362891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14497874157175434390241927 21746811235763151585362891)
          ·
            refine ⟨32620216853644727378044337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21746811235763151585362891 32620216853644727378044337)
            ·
              refine ⟨24465162640233545533533253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32620216853644727378044337 24465162640233545533533253)
              ·
                refine ⟨4587217995043789787537485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24465162640233545533533253 4587217995043789787537485)
                ·
                  refine ⟨1720206748141421170326557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4587217995043789787537485 1720206748141421170326557)
                  ·
                    refine ⟨645077530553032938872459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1720206748141421170326557 645077530553032938872459)
                    ·
                      rfl

theorem cell22_1884426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1884426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884426 prefixEnd_1884426 := by exact prefixLift 1884426
  have htrace : WordTrace (prefixWord ++ tailWord_1884426) baseStart_1884426 baseEnd_1884426 := by
    simpa [prefixWord, tailWord_1884426, baseEnd_1884426] using wordTrace_append hprefix tailTrace_1884426
  have hstable : (prefixWord ++ tailWord_1884426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884426).length < 2 ^ (prefixWord ++ tailWord_1884426).sum := by decide
  have hdescent : baseEnd_1884426 < baseStart_1884426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884460 : List Nat := [2, 2, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_1884460 : Nat := 118140960795 + 1884460 * 2 ^ 59
def prefixEnd_1884460 : Nat := 4983230072969 + 3 ^ 40 * 1884460 * 2
def baseEnd_1884460 : Nat := 645089169447868183522355

theorem tailTrace_1884460 : CollatzResearch.WordTrace tailWord_1884460 prefixEnd_1884460 645089169447868183522355 := by
  unfold tailWord_1884460
  simp only [CollatzResearch.WordTrace]
  refine ⟨34365951376465367495053417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45821268501953823326737889 34365951376465367495053417)
  ·
    refine ⟨25774463532349025621290063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34365951376465367495053417 25774463532349025621290063)
    ·
      refine ⟨38661695298523538431935095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25774463532349025621290063 38661695298523538431935095)
      ·
        refine ⟨57992542947785307647902643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38661695298523538431935095 57992542947785307647902643)
        ·
          refine ⟨86988814421677961471853965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57992542947785307647902643 86988814421677961471853965)
          ·
            refine ⟨32620805408129235551945237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86988814421677961471853965 32620805408129235551945237)
            ·
              refine ⟨1529100253506057916497433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32620805408129235551945237 1529100253506057916497433)
              ·
                refine ⟨1146825190129543437373075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529100253506057916497433 1146825190129543437373075)
                ·
                  refine ⟨1720237785194315156059613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146825190129543437373075 1720237785194315156059613)
                  ·
                    refine ⟨645089169447868183522355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1720237785194315156059613 645089169447868183522355)
                    ·
                      rfl

theorem cell22_1884460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_1884460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884460 prefixEnd_1884460 := by exact prefixLift 1884460
  have htrace : WordTrace (prefixWord ++ tailWord_1884460) baseStart_1884460 baseEnd_1884460 := by
    simpa [prefixWord, tailWord_1884460, baseEnd_1884460] using wordTrace_append hprefix tailTrace_1884460
  have hstable : (prefixWord ++ tailWord_1884460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884460).length < 2 ^ (prefixWord ++ tailWord_1884460).sum := by decide
  have hdescent : baseEnd_1884460 < baseStart_1884460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884499 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 3, 5]
def baseStart_1884499 : Nat := 118140960795 + 1884499 * 2 ^ 59
def prefixEnd_1884499 : Nat := 4983230072969 + 3 ^ 40 * 1884499 * 2
def baseEnd_1884499 : Nat := 645102519944885081797235

theorem tailTrace_1884499 : CollatzResearch.WordTrace tailWord_1884499 prefixEnd_1884499 645102519944885081797235 := by
  unfold tailWord_1884499
  simp only [CollatzResearch.WordTrace]
  refine ⟨68733325199789444650776551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45822216799859629767184367 68733325199789444650776551)
  ·
    refine ⟨103099987799684166976164827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68733325199789444650776551 103099987799684166976164827)
    ·
      refine ⟨154649981699526250464247241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103099987799684166976164827 154649981699526250464247241)
      ·
        refine ⟨115987486274644687848185431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154649981699526250464247241 115987486274644687848185431)
        ·
          refine ⟨173981229411967031772278147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115987486274644687848185431 173981229411967031772278147)
          ·
            refine ⟨260971844117950547658417221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173981229411967031772278147 260971844117950547658417221)
            ·
              refine ⟨48932220772115727685953229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260971844117950547658417221 48932220772115727685953229)
              ·
                refine ⟨18349582789543397882232461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48932220772115727685953229 18349582789543397882232461)
                ·
                  refine ⟨6881093546078774205837173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18349582789543397882232461 6881093546078774205837173)
                  ·
                    refine ⟨645102519944885081797235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6881093546078774205837173 645102519944885081797235)
                    ·
                      rfl

theorem cell22_1884499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_1884499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884499 prefixEnd_1884499 := by exact prefixLift 1884499
  have htrace : WordTrace (prefixWord ++ tailWord_1884499) baseStart_1884499 baseEnd_1884499 := by
    simpa [prefixWord, tailWord_1884499, baseEnd_1884499] using wordTrace_append hprefix tailTrace_1884499
  have hstable : (prefixWord ++ tailWord_1884499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884499).length < 2 ^ (prefixWord ++ tailWord_1884499).sum := by decide
  have hdescent : baseEnd_1884499 < baseStart_1884499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884529 : List Nat := [1, 2, 2, 2, 1, 2, 1, 11]
def baseStart_1884529 : Nat := 118140960795 + 1884529 * 2 ^ 59
def prefixEnd_1884529 : Nat := 4983230072969 + 3 ^ 40 * 1884529 * 2
def baseEnd_1884529 : Nat := 71679198839775000394127

theorem tailTrace_1884529 : CollatzResearch.WordTrace tailWord_1884529 prefixEnd_1884529 71679198839775000394127 := by
  unfold tailWord_1884529
  simp only [CollatzResearch.WordTrace]
  refine ⟨68734419389680759774368641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45822946259787173182912427 68734419389680759774368641)
  ·
    refine ⟨51550814542260569830776481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68734419389680759774368641 51550814542260569830776481)
    ·
      refine ⟨38663110906695427373082361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51550814542260569830776481 38663110906695427373082361)
      ·
        refine ⟨28997333180021570529811771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38663110906695427373082361 28997333180021570529811771)
        ·
          refine ⟨43495999770032355794717657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28997333180021570529811771 43495999770032355794717657)
          ·
            refine ⟨32621999827524266846038243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43495999770032355794717657 32621999827524266846038243)
            ·
              refine ⟨48932999741286400269057365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32621999827524266846038243 48932999741286400269057365)
              ·
                refine ⟨71679198839775000394127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 48932999741286400269057365 71679198839775000394127)
                ·
                  rfl

theorem cell22_1884529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 11].length) (baseStart_1884529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884529 prefixEnd_1884529 := by exact prefixLift 1884529
  have htrace : WordTrace (prefixWord ++ tailWord_1884529) baseStart_1884529 baseEnd_1884529 := by
    simpa [prefixWord, tailWord_1884529, baseEnd_1884529] using wordTrace_append hprefix tailTrace_1884529
  have hstable : (prefixWord ++ tailWord_1884529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884529).length < 2 ^ (prefixWord ++ tailWord_1884529).sum := by decide
  have hdescent : baseEnd_1884529 < baseStart_1884529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884533 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1884533 : Nat := 118140960795 + 1884533 * 2 ^ 59
def prefixEnd_1884533 : Nat := 4983230072969 + 3 ^ 40 * 1884533 * 2
def baseEnd_1884533 : Nat := 645114158839720326447131

theorem tailTrace_1884533 : CollatzResearch.WordTrace tailWord_1884533 prefixEnd_1884533 645114158839720326447131 := by
  unfold tailWord_1884533
  simp only [CollatzResearch.WordTrace]
  refine ⟨68734565281666268457514253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45823043521110845638342835 68734565281666268457514253)
  ·
    refine ⟨25775461980624850671567845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68734565281666268457514253 25775461980624850671567845)
    ·
      refine ⟨4832899121367159500918971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25775461980624850671567845 4832899121367159500918971)
      ·
        refine ⟨7249348682050739251378457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832899121367159500918971 7249348682050739251378457)
        ·
          refine ⟨5437011511538054438533843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7249348682050739251378457 5437011511538054438533843)
          ·
            refine ⟨8155517267307081657800765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5437011511538054438533843 8155517267307081657800765)
            ·
              refine ⟨3058318975240155621675287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8155517267307081657800765 3058318975240155621675287)
              ·
                refine ⟨4587478462860233432512931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058318975240155621675287 4587478462860233432512931)
                ·
                  refine ⟨6881217694290350148769397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587478462860233432512931 6881217694290350148769397)
                  ·
                    refine ⟨645114158839720326447131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6881217694290350148769397 645114158839720326447131)
                    ·
                      rfl

theorem cell22_1884533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1884533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884533 prefixEnd_1884533 := by exact prefixLift 1884533
  have htrace : WordTrace (prefixWord ++ tailWord_1884533) baseStart_1884533 baseEnd_1884533 := by
    simpa [prefixWord, tailWord_1884533, baseEnd_1884533] using wordTrace_append hprefix tailTrace_1884533
  have hstable : (prefixWord ++ tailWord_1884533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884533).length < 2 ^ (prefixWord ++ tailWord_1884533).sum := by decide
  have hdescent : baseEnd_1884533 < baseStart_1884533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884584 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1884584 : Nat := 118140960795 + 1884584 * 2 ^ 59
def prefixEnd_1884584 : Nat := 4983230072969 + 3 ^ 40 * 1884584 * 2
def baseEnd_1884584 : Nat := 645131617181973193421975

theorem tailTrace_1884584 : CollatzResearch.WordTrace tailWord_1884584 prefixEnd_1884584 645131617181973193421975 := by
  unfold tailWord_1884584
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368212702240752083810403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45824283602987669445080537 34368212702240752083810403)
  ·
    refine ⟨51552319053361128125715605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34368212702240752083810403 51552319053361128125715605)
    ·
      refine ⟨2416514955626302880892919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51552319053361128125715605 2416514955626302880892919)
      ·
        refine ⟨3624772433439454321339379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416514955626302880892919 3624772433439454321339379)
        ·
          refine ⟨5437158650159181482009069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624772433439454321339379 5437158650159181482009069)
          ·
            refine ⟨2038934493809693055753401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5437158650159181482009069 2038934493809693055753401)
            ·
              refine ⟨1529200870357269791815051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2038934493809693055753401 1529200870357269791815051)
              ·
                refine ⟨2293801305535904687722577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529200870357269791815051 2293801305535904687722577)
                ·
                  refine ⟨1720350979151928515791933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2293801305535904687722577 1720350979151928515791933)
                  ·
                    refine ⟨645131617181973193421975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1720350979151928515791933 645131617181973193421975)
                    ·
                      rfl

theorem cell22_1884584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1884584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884584 prefixEnd_1884584 := by exact prefixLift 1884584
  have htrace : WordTrace (prefixWord ++ tailWord_1884584) baseStart_1884584 baseEnd_1884584 := by
    simpa [prefixWord, tailWord_1884584, baseEnd_1884584] using wordTrace_append hprefix tailTrace_1884584
  have hstable : (prefixWord ++ tailWord_1884584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884584).length < 2 ^ (prefixWord ++ tailWord_1884584).sum := by decide
  have hdescent : baseEnd_1884584 < baseStart_1884584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884629 : List Nat := [1, 3, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_1884629 : Nat := 118140960795 + 1884629 * 2 ^ 59
def prefixEnd_1884629 : Nat := 4983230072969 + 3 ^ 40 * 1884629 * 2
def baseEnd_1884629 : Nat := 645147021601608076046837

theorem tailTrace_1884629 : CollatzResearch.WordTrace tailWord_1884629 prefixEnd_1884629 645147021601608076046837 := by
  unfold tailWord_1884629
  simp only [CollatzResearch.WordTrace]
  refine ⟨68738066689318476853008941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45825377792878984568672627 68738066689318476853008941)
  ·
    refine ⟨25776775008494428819878353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68738066689318476853008941 25776775008494428819878353)
    ·
      refine ⟨19332581256370821614908765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25776775008494428819878353 19332581256370821614908765)
      ·
        refine ⟨7249717971139058105590787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19332581256370821614908765 7249717971139058105590787)
        ·
          refine ⟨10874576956708587158386181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7249717971139058105590787 10874576956708587158386181)
          ·
            refine ⟨2038983179382860092197409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10874576956708587158386181 2038983179382860092197409)
            ·
              refine ⟨1529237384537145069148057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2038983179382860092197409 1529237384537145069148057)
              ·
                refine ⟨1146928038402858801861043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529237384537145069148057 1146928038402858801861043)
                ·
                  refine ⟨1720392057604288202791565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1146928038402858801861043 1720392057604288202791565)
                  ·
                    refine ⟨645147021601608076046837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1720392057604288202791565 645147021601608076046837)
                    ·
                      rfl

theorem cell22_1884629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_1884629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884629 prefixEnd_1884629 := by exact prefixLift 1884629
  have htrace : WordTrace (prefixWord ++ tailWord_1884629) baseStart_1884629 baseEnd_1884629 := by
    simpa [prefixWord, tailWord_1884629, baseEnd_1884629] using wordTrace_append hprefix tailTrace_1884629
  have hstable : (prefixWord ++ tailWord_1884629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884629).length < 2 ^ (prefixWord ++ tailWord_1884629).sum := by decide
  have hdescent : baseEnd_1884629 < baseStart_1884629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884653 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 8]
def baseStart_1884653 : Nat := 118140960795 + 1884653 * 2 ^ 59
def prefixEnd_1884653 : Nat := 4983230072969 + 3 ^ 40 * 1884653 * 2
def baseEnd_1884653 : Nat := 215051745764026671148921

theorem tailTrace_1884653 : CollatzResearch.WordTrace tailWord_1884653 prefixEnd_1884653 215051745764026671148921 := by
  unfold tailWord_1884653
  simp only [CollatzResearch.WordTrace]
  refine ⟨68738942041231528951882613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45825961360821019301255075 68738942041231528951882613)
  ·
    refine ⟨6444275816365455839238995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68738942041231528951882613 6444275816365455839238995)
    ·
      refine ⟨9666413724548183758858493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6444275816365455839238995 9666413724548183758858493)
      ·
        refine ⟨3624905146705568909571935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9666413724548183758858493 3624905146705568909571935)
        ·
          refine ⟨5437357720058353364357903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624905146705568909571935 5437357720058353364357903)
          ·
            refine ⟨8156036580087530046536855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5437357720058353364357903 8156036580087530046536855)
            ·
              refine ⟨12234054870131295069805283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156036580087530046536855 12234054870131295069805283)
              ·
                refine ⟨18351082305196942604707925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12234054870131295069805283 18351082305196942604707925)
                ·
                  refine ⟨215051745764026671148921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18351082305196942604707925 215051745764026671148921)
                  ·
                    rfl

theorem cell22_1884653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_1884653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884653 prefixEnd_1884653 := by exact prefixLift 1884653
  have htrace : WordTrace (prefixWord ++ tailWord_1884653) baseStart_1884653 baseEnd_1884653 := by
    simpa [prefixWord, tailWord_1884653, baseEnd_1884653] using wordTrace_append hprefix tailTrace_1884653
  have hstable : (prefixWord ++ tailWord_1884653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884653).length < 2 ^ (prefixWord ++ tailWord_1884653).sum := by decide
  have hdescent : baseEnd_1884653 < baseStart_1884653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884668 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_1884668 : Nat := 118140960795 + 1884668 * 2 ^ 59
def prefixEnd_1884668 : Nat := 4983230072969 + 3 ^ 40 * 1884668 * 2
def baseEnd_1884668 : Nat := 645160372098624974321717

theorem tailTrace_1884668 : CollatzResearch.WordTrace tailWord_1884668 prefixEnd_1884668 645160372098624974321717 := by
  unfold tailWord_1884668
  simp only [CollatzResearch.WordTrace]
  refine ⟨34369744568088593256839329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45826326090784791009119105 34369744568088593256839329)
  ·
    refine ⟨25777308426066444942629497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34369744568088593256839329 25777308426066444942629497)
    ·
      refine ⟨19332981319549833706972123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25777308426066444942629497 19332981319549833706972123)
      ·
        refine ⟨28999471979324750560458185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19332981319549833706972123 28999471979324750560458185)
        ·
          refine ⟨21749603984493562920343639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28999471979324750560458185 21749603984493562920343639)
          ·
            refine ⟨32624405976740344380515459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21749603984493562920343639 32624405976740344380515459)
            ·
              refine ⟨48936608965110516570773189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32624405976740344380515459 48936608965110516570773189)
              ·
                refine ⟨9175614180958221857019973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48936608965110516570773189 9175614180958221857019973)
                ·
                  refine ⟨1720427658929666598191245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9175614180958221857019973 1720427658929666598191245)
                  ·
                    refine ⟨645160372098624974321717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1720427658929666598191245 645160372098624974321717)
                    ·
                      rfl

theorem cell22_1884668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_1884668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884668 prefixEnd_1884668 := by exact prefixLift 1884668
  have htrace : WordTrace (prefixWord ++ tailWord_1884668) baseStart_1884668 baseEnd_1884668 := by
    simpa [prefixWord, tailWord_1884668, baseEnd_1884668] using wordTrace_append hprefix tailTrace_1884668
  have hstable : (prefixWord ++ tailWord_1884668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884668).length < 2 ^ (prefixWord ++ tailWord_1884668).sum := by decide
  have hdescent : baseEnd_1884668 < baseStart_1884668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884743 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 7]
def baseStart_1884743 : Nat := 118140960795 + 1884743 * 2 ^ 59
def prefixEnd_1884743 : Nat := 4983230072969 + 3 ^ 40 * 1884743 * 2
def baseEnd_1884743 : Nat := 215062015377116592898829

theorem tailTrace_1884743 : CollatzResearch.WordTrace tailWord_1884743 prefixEnd_1884743 215062015377116592898829 := by
  unfold tailWord_1884743
  simp only [CollatzResearch.WordTrace]
  refine ⟨68742224610905474322658883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45828149740603649548439255 68742224610905474322658883)
  ·
    refine ⟨103113336916358211483988325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68742224610905474322658883 103113336916358211483988325)
    ·
      refine ⟨19333750671817164653247811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103113336916358211483988325 19333750671817164653247811)
      ·
        refine ⟨29000626007725746979871717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19333750671817164653247811 29000626007725746979871717)
        ·
          refine ⟨5437617376448577558725947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29000626007725746979871717 5437617376448577558725947)
          ·
            refine ⟨8156426064672866338088921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5437617376448577558725947 8156426064672866338088921)
            ·
              refine ⟨6117319548504649753566691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8156426064672866338088921 6117319548504649753566691)
              ·
                refine ⟨9175979322756974630350037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117319548504649753566691 9175979322756974630350037)
                ·
                  refine ⟨215062015377116592898829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9175979322756974630350037 215062015377116592898829)
                  ·
                    rfl

theorem cell22_1884743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 7].length) (baseStart_1884743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884743 prefixEnd_1884743 := by exact prefixLift 1884743
  have htrace : WordTrace (prefixWord ++ tailWord_1884743) baseStart_1884743 baseEnd_1884743 := by
    simpa [prefixWord, tailWord_1884743, baseEnd_1884743] using wordTrace_append hprefix tailTrace_1884743
  have hstable : (prefixWord ++ tailWord_1884743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884743).length < 2 ^ (prefixWord ++ tailWord_1884743).sum := by decide
  have hdescent : baseEnd_1884743 < baseStart_1884743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884760 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 5]
def baseStart_1884760 : Nat := 118140960795 + 1884760 * 2 ^ 59
def prefixEnd_1884760 : Nat := 4983230072969 + 3 ^ 40 * 1884760 * 2
def baseEnd_1884760 : Nat := 215063955192922467007145

theorem tailTrace_1884760 : CollatzResearch.WordTrace tailWord_1884760 prefixEnd_1884760 215063955192922467007145 := by
  unfold tailWord_1884760
  simp only [CollatzResearch.WordTrace]
  refine ⟨34371422325921943113013867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45828563101229257484018489 34371422325921943113013867)
  ·
    refine ⟨51557133488882914669520801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34371422325921943113013867 51557133488882914669520801)
    ·
      refine ⟨38667850116662186002140601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51557133488882914669520801 38667850116662186002140601)
      ·
        refine ⟨29000887587496639501605451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38667850116662186002140601 29000887587496639501605451)
        ·
          refine ⟨43501331381244959252408177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29000887587496639501605451 43501331381244959252408177)
          ·
            refine ⟨32625998535933719439306133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43501331381244959252408177 32625998535933719439306133)
            ·
              refine ⟨1529343681371893098717475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32625998535933719439306133 1529343681371893098717475)
              ·
                refine ⟨2294015522057839648076213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529343681371893098717475 2294015522057839648076213)
                ·
                  refine ⟨215063955192922467007145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2294015522057839648076213 215063955192922467007145)
                  ·
                    rfl

theorem cell22_1884760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_1884760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884760 prefixEnd_1884760 := by exact prefixLift 1884760
  have htrace : WordTrace (prefixWord ++ tailWord_1884760) baseStart_1884760 baseEnd_1884760 := by
    simpa [prefixWord, tailWord_1884760, baseEnd_1884760] using wordTrace_append hprefix tailTrace_1884760
  have hstable : (prefixWord ++ tailWord_1884760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884760).length < 2 ^ (prefixWord ++ tailWord_1884760).sum := by decide
  have hdescent : baseEnd_1884760 < baseStart_1884760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884884 : List Nat := [2, 4, 1, 3, 2, 2, 2, 6]
def baseStart_1884884 : Nat := 118140960795 + 1884884 * 2 ^ 59
def prefixEnd_1884884 : Nat := 4983230072969 + 3 ^ 40 * 1884884 * 2
def baseEnd_1884884 : Nat := 71692701479208045657895

theorem tailTrace_1884884 : CollatzResearch.WordTrace tailWord_1884884 prefixEnd_1884884 71692701479208045657895 := by
  unfold tailWord_1884884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34373683651697327701770853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45831578202263103602361137 34373683651697327701770853)
  ·
    refine ⟨6445065684693248944082035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34373683651697327701770853 6445065684693248944082035)
    ·
      refine ⟨9667598527039873416123053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6445065684693248944082035 9667598527039873416123053)
      ·
        refine ⟨3625349447639952531046145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9667598527039873416123053 3625349447639952531046145)
        ·
          refine ⟨2719012085729964398284609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3625349447639952531046145 2719012085729964398284609)
          ·
            refine ⟨2039259064297473298713457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2719012085729964398284609 2039259064297473298713457)
            ·
              refine ⟨1529444298223104974035093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039259064297473298713457 1529444298223104974035093)
              ·
                refine ⟨71692701479208045657895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1529444298223104974035093 71692701479208045657895)
                ·
                  rfl

theorem cell22_1884884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 6].length) (baseStart_1884884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884884 prefixEnd_1884884 := by exact prefixLift 1884884
  have htrace : WordTrace (prefixWord ++ tailWord_1884884) baseStart_1884884 baseEnd_1884884 := by
    simpa [prefixWord, tailWord_1884884, baseEnd_1884884] using wordTrace_append hprefix tailTrace_1884884
  have hstable : (prefixWord ++ tailWord_1884884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884884).length < 2 ^ (prefixWord ++ tailWord_1884884).sum := by decide
  have hdescent : baseEnd_1884884 < baseStart_1884884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884925 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1884925 : Nat := 118140960795 + 1884925 * 2 ^ 59
def prefixEnd_1884925 : Nat := 4983230072969 + 3 ^ 40 * 1884925 * 2
def baseEnd_1884925 : Nat := 645248348450761970645929

theorem tailTrace_1884925 : CollatzResearch.WordTrace tailWord_1884925 prefixEnd_1884925 645248348450761970645929 := by
  unfold tailWord_1884925
  simp only [CollatzResearch.WordTrace]
  refine ⟨68748862696246119405784229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45832575130830746270522819 68748862696246119405784229)
  ·
    refine ⟨12890411755546147388584543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68748862696246119405784229 12890411755546147388584543)
    ·
      refine ⟨19335617633319221082876815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12890411755546147388584543 19335617633319221082876815)
      ·
        refine ⟨29003426449978831624315223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19335617633319221082876815 29003426449978831624315223)
        ·
          refine ⟨43505139674968247436472835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29003426449978831624315223 43505139674968247436472835)
          ·
            refine ⟨65257709512452371154709253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43505139674968247436472835 65257709512452371154709253)
            ·
              refine ⟨12235820533584819591507985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65257709512452371154709253 12235820533584819591507985)
              ·
                refine ⟨9176865400188614693630989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12235820533584819591507985 9176865400188614693630989)
                ·
                  refine ⟨3441324525070730510111621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9176865400188614693630989 3441324525070730510111621)
                  ·
                    refine ⟨645248348450761970645929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3441324525070730510111621 645248348450761970645929)
                    ·
                      rfl

theorem cell22_1884925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1884925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884925 prefixEnd_1884925 := by exact prefixLift 1884925
  have htrace : WordTrace (prefixWord ++ tailWord_1884925) baseStart_1884925 baseEnd_1884925 := by
    simpa [prefixWord, tailWord_1884925, baseEnd_1884925] using wordTrace_append hprefix tailTrace_1884925
  have hstable : (prefixWord ++ tailWord_1884925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884925).length < 2 ^ (prefixWord ++ tailWord_1884925).sum := by decide
  have hdescent : baseEnd_1884925 < baseStart_1884925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884959 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 1, 4]
def baseStart_1884959 : Nat := 118140960795 + 1884959 * 2 ^ 59
def prefixEnd_1884959 : Nat := 4983230072969 + 3 ^ 40 * 1884959 * 2
def baseEnd_1884959 : Nat := 645259987345597215295825

theorem tailTrace_1884959 : CollatzResearch.WordTrace tailWord_1884959 prefixEnd_1884959 645259987345597215295825 := by
  unfold tailWord_1884959
  simp only [CollatzResearch.WordTrace]
  refine ⟨68750102778122943212521931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45833401852081962141681287 68750102778122943212521931)
  ·
    refine ⟨103125154167184414818782897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68750102778122943212521931 103125154167184414818782897)
    ·
      refine ⟨77343865625388311114087173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103125154167184414818782897 77343865625388311114087173)
      ·
        refine ⟨14501974804760308333891345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77343865625388311114087173 14501974804760308333891345)
        ·
          refine ⟨10876481103570231250418509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14501974804760308333891345 10876481103570231250418509)
          ·
            refine ⟨4078680413838836718906941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10876481103570231250418509 4078680413838836718906941)
            ·
              refine ⟨1529505155189563769590103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4078680413838836718906941 1529505155189563769590103)
              ·
                refine ⟨2294257732784345654385155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1529505155189563769590103 2294257732784345654385155)
                ·
                  refine ⟨3441386599176518481577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2294257732784345654385155 3441386599176518481577733)
                  ·
                    refine ⟨645259987345597215295825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3441386599176518481577733 645259987345597215295825)
                    ·
                      rfl

theorem cell22_1884959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_1884959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884959 prefixEnd_1884959 := by exact prefixLift 1884959
  have htrace : WordTrace (prefixWord ++ tailWord_1884959) baseStart_1884959 baseEnd_1884959 := by
    simpa [prefixWord, tailWord_1884959, baseEnd_1884959] using wordTrace_append hprefix tailTrace_1884959
  have hstable : (prefixWord ++ tailWord_1884959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884959).length < 2 ^ (prefixWord ++ tailWord_1884959).sum := by decide
  have hdescent : baseEnd_1884959 < baseStart_1884959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1884989 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_1884989 : Nat := 118140960795 + 1884989 * 2 ^ 59
def prefixEnd_1884989 : Nat := 4983230072969 + 3 ^ 40 * 1884989 * 2
def baseEnd_1884989 : Nat := 645270256958687137045733

theorem tailTrace_1884989 : CollatzResearch.WordTrace tailWord_1884989 prefixEnd_1884989 645270256958687137045733 := by
  unfold tailWord_1884989
  simp only [CollatzResearch.WordTrace]
  refine ⟨68751196968014258336114021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45834131312009505557409347 68751196968014258336114021)
  ·
    refine ⟨12890849431502673438021379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68751196968014258336114021 12890849431502673438021379)
    ·
      refine ⟨19336274147254010157032069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12890849431502673438021379 19336274147254010157032069)
      ·
        refine ⟨3625551402610126904443513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19336274147254010157032069 3625551402610126904443513)
        ·
          refine ⟨2719163551957595178332635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3625551402610126904443513 2719163551957595178332635)
          ·
            refine ⟨4078745327936392767498953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719163551957595178332635 4078745327936392767498953)
            ·
              refine ⟨3059058995952294575624215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4078745327936392767498953 3059058995952294575624215)
              ·
                refine ⟨4588588493928441863436323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059058995952294575624215 4588588493928441863436323)
                ·
                  refine ⟨6882882740892662795154485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588588493928441863436323 6882882740892662795154485)
                  ·
                    refine ⟨645270256958687137045733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6882882740892662795154485 645270256958687137045733)
                    ·
                      rfl

theorem cell22_1884989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_1884989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1884989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1884989 prefixEnd_1884989 := by exact prefixLift 1884989
  have htrace : WordTrace (prefixWord ++ tailWord_1884989) baseStart_1884989 baseEnd_1884989 := by
    simpa [prefixWord, tailWord_1884989, baseEnd_1884989] using wordTrace_append hprefix tailTrace_1884989
  have hstable : (prefixWord ++ tailWord_1884989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1884989).length < 2 ^ (prefixWord ++ tailWord_1884989).sum := by decide
  have hdescent : baseEnd_1884989 < baseStart_1884989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1884989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885004 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_1885004 : Nat := 118140960795 + 1885004 * 2 ^ 59
def prefixEnd_1885004 : Nat := 4983230072969 + 3 ^ 40 * 1885004 * 2
def baseEnd_1885004 : Nat := 645275391765232097920687

theorem tailTrace_1885004 : CollatzResearch.WordTrace tailWord_1885004 prefixEnd_1885004 645275391765232097920687 := by
  unfold tailWord_1885004
  simp only [CollatzResearch.WordTrace]
  refine ⟨34375872031479957948955033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45834496041973277265273377 34375872031479957948955033)
  ·
    refine ⟨25781904023609968461716275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34375872031479957948955033 25781904023609968461716275)
    ·
      refine ⟨38672856035414952692574413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25781904023609968461716275 38672856035414952692574413)
      ·
        refine ⟨14502321013280607259715405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38672856035414952692574413 14502321013280607259715405)
        ·
          refine ⟨5438370379980227722393277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14502321013280607259715405 5438370379980227722393277)
          ·
            refine ⟨2039388892492585395897479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5438370379980227722393277 2039388892492585395897479)
            ·
              refine ⟨3059083338738878093846219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039388892492585395897479 3059083338738878093846219)
              ·
                refine ⟨4588625008108317140769329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059083338738878093846219 4588625008108317140769329)
                ·
                  refine ⟨3441468756081237855576997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4588625008108317140769329 3441468756081237855576997)
                  ·
                    refine ⟨645275391765232097920687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3441468756081237855576997 645275391765232097920687)
                    ·
                      rfl

theorem cell22_1885004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_1885004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885004 prefixEnd_1885004 := by exact prefixLift 1885004
  have htrace : WordTrace (prefixWord ++ tailWord_1885004) baseStart_1885004 baseEnd_1885004 := by
    simpa [prefixWord, tailWord_1885004, baseEnd_1885004] using wordTrace_append hprefix tailTrace_1885004
  have hstable : (prefixWord ++ tailWord_1885004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885004).length < 2 ^ (prefixWord ++ tailWord_1885004).sum := by decide
  have hdescent : baseEnd_1885004 < baseStart_1885004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885107 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 6, 3]
def baseStart_1885107 : Nat := 118140960795 + 1885107 * 2 ^ 59
def prefixEnd_1885107 : Nat := 4983230072969 + 3 ^ 40 * 1885107 * 2
def baseEnd_1885107 : Nat := 645310650770174162595371

theorem tailTrace_1885107 : CollatzResearch.WordTrace tailWord_1885107 prefixEnd_1885107 645310650770174162595371 := by
  unfold tailWord_1885107
  simp only [CollatzResearch.WordTrace]
  refine ⟨68755500781586764488909575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45837000521057842992606383 68755500781586764488909575)
  ·
    refine ⟨103133251172380146733364363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68755500781586764488909575 103133251172380146733364363)
    ·
      refine ⟨154699876758570220100046545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103133251172380146733364363 154699876758570220100046545)
      ·
        refine ⟨116024907568927665075034909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154699876758570220100046545 116024907568927665075034909)
        ·
          refine ⟨43509340338347874403138091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116024907568927665075034909 43509340338347874403138091)
          ·
            refine ⟨65264010507521811604707137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43509340338347874403138091 65264010507521811604707137)
            ·
              refine ⟨48948007880641358703530353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65264010507521811604707137 48948007880641358703530353)
              ·
                refine ⟨36711005910481019027647765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48948007880641358703530353 36711005910481019027647765)
                ·
                  refine ⟨1720828402053797766920989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36711005910481019027647765 1720828402053797766920989)
                  ·
                    refine ⟨645310650770174162595371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1720828402053797766920989 645310650770174162595371)
                    ·
                      rfl

theorem cell22_1885107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 3].length) (baseStart_1885107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885107 prefixEnd_1885107 := by exact prefixLift 1885107
  have htrace : WordTrace (prefixWord ++ tailWord_1885107) baseStart_1885107 baseEnd_1885107 := by
    simpa [prefixWord, tailWord_1885107, baseEnd_1885107] using wordTrace_append hprefix tailTrace_1885107
  have hstable : (prefixWord ++ tailWord_1885107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885107).length < 2 ^ (prefixWord ++ tailWord_1885107).sum := by decide
  have hdescent : baseEnd_1885107 < baseStart_1885107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885169 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 5, 3]
def baseStart_1885169 : Nat := 118140960795 + 1885169 * 2 ^ 59
def prefixEnd_1885169 : Nat := 4983230072969 + 3 ^ 40 * 1885169 * 2
def baseEnd_1885169 : Nat := 645331874637226667545181

theorem tailTrace_1885169 : CollatzResearch.WordTrace tailWord_1885169 prefixEnd_1885169 645331874637226667545181 := by
  unfold tailWord_1885169
  simp only [CollatzResearch.WordTrace]
  refine ⟨68757762107362149077666561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45838508071574766051777707 68757762107362149077666561)
  ·
    refine ⟨51568321580521611808249921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68757762107362149077666561 51568321580521611808249921)
    ·
      refine ⟨38676241185391208856187441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51568321580521611808249921 38676241185391208856187441)
      ·
        refine ⟨29007180889043406642140581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38676241185391208856187441 29007180889043406642140581)
        ·
          refine ⟨5438846416695638745401359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29007180889043406642140581 5438846416695638745401359)
          ·
            refine ⟨8158269625043458118102039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438846416695638745401359 8158269625043458118102039)
            ·
              refine ⟨12237404437565187177153059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8158269625043458118102039 12237404437565187177153059)
              ·
                refine ⟨18356106656347780765729589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12237404437565187177153059 18356106656347780765729589)
                ·
                  refine ⟨1720884999032604446787149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18356106656347780765729589 1720884999032604446787149)
                  ·
                    refine ⟨645331874637226667545181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1720884999032604446787149 645331874637226667545181)
                    ·
                      rfl

theorem cell22_1885169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_1885169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885169 prefixEnd_1885169 := by exact prefixLift 1885169
  have htrace : WordTrace (prefixWord ++ tailWord_1885169) baseStart_1885169 baseEnd_1885169 := by
    simpa [prefixWord, tailWord_1885169, baseEnd_1885169] using wordTrace_append hprefix tailTrace_1885169
  have hstable : (prefixWord ++ tailWord_1885169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885169).length < 2 ^ (prefixWord ++ tailWord_1885169).sum := by decide
  have hdescent : baseEnd_1885169 < baseStart_1885169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885227 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 6]
def baseStart_1885227 : Nat := 118140960795 + 1885227 * 2 ^ 59
def prefixEnd_1885227 : Nat := 4983230072969 + 3 ^ 40 * 1885227 * 2
def baseEnd_1885227 : Nat := 215117243074177949865001

theorem tailTrace_1885227 : CollatzResearch.WordTrace tailWord_1885227 prefixEnd_1885227 215117243074177949865001 := by
  unfold tailWord_1885227
  simp only [CollatzResearch.WordTrace]
  refine ⟨68759877541152024983277935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45839918360768016655518623 68759877541152024983277935)
  ·
    refine ⟨103139816311728037474916903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68759877541152024983277935 103139816311728037474916903)
    ·
      refine ⟨154709724467592056212375355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103139816311728037474916903 154709724467592056212375355)
      ·
        refine ⟨232064586701388084318563033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154709724467592056212375355 232064586701388084318563033)
        ·
          refine ⟨174048440026041063238922275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232064586701388084318563033 174048440026041063238922275)
          ·
            refine ⟨261072660039061594858383413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174048440026041063238922275 261072660039061594858383413)
            ·
              refine ⟨24475561878662024517973445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261072660039061594858383413 24475561878662024517973445)
              ·
                refine ⟨4589167852249129597120021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24475561878662024517973445 4589167852249129597120021)
                ·
                  refine ⟨215117243074177949865001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4589167852249129597120021 215117243074177949865001)
                  ·
                    rfl

theorem cell22_1885227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 6].length) (baseStart_1885227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885227 prefixEnd_1885227 := by exact prefixLift 1885227
  have htrace : WordTrace (prefixWord ++ tailWord_1885227) baseStart_1885227 baseEnd_1885227 := by
    simpa [prefixWord, tailWord_1885227, baseEnd_1885227] using wordTrace_append hprefix tailTrace_1885227
  have hstable : (prefixWord ++ tailWord_1885227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885227).length < 2 ^ (prefixWord ++ tailWord_1885227).sum := by decide
  have hdescent : baseEnd_1885227 < baseStart_1885227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885257 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_1885257 : Nat := 118140960795 + 1885257 * 2 ^ 59
def prefixEnd_1885257 : Nat := 4983230072969 + 3 ^ 40 * 1885257 * 2
def baseEnd_1885257 : Nat := 645361998835623771344911

theorem tailTrace_1885257 : CollatzResearch.WordTrace tailWord_1885257 prefixEnd_1885257 645361998835623771344911 := by
  unfold tailWord_1885257
  simp only [CollatzResearch.WordTrace]
  refine ⟨68760971731043340106870025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45840647820695560071246683 68760971731043340106870025)
  ·
    refine ⟨51570728798282505080152519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68760971731043340106870025 51570728798282505080152519)
    ·
      refine ⟨77356093197423757620228779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51570728798282505080152519 77356093197423757620228779)
      ·
        refine ⟨116034139796135636430343169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77356093197423757620228779 116034139796135636430343169)
        ·
          refine ⟨87025604847101727322757377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116034139796135636430343169 87025604847101727322757377)
          ·
            refine ⟨65269203635326295492068033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87025604847101727322757377 65269203635326295492068033)
            ·
              refine ⟨48951902726494721619051025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65269203635326295492068033 48951902726494721619051025)
              ·
                refine ⟨36713927044871041214288269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48951902726494721619051025 36713927044871041214288269)
                ·
                  refine ⟨13767722641826640455358101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36713927044871041214288269 13767722641826640455358101)
                  ·
                    refine ⟨645361998835623771344911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13767722641826640455358101 645361998835623771344911)
                    ·
                      rfl

theorem cell22_1885257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_1885257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885257 prefixEnd_1885257 := by exact prefixLift 1885257
  have htrace : WordTrace (prefixWord ++ tailWord_1885257) baseStart_1885257 baseEnd_1885257 := by
    simpa [prefixWord, tailWord_1885257, baseEnd_1885257] using wordTrace_append hprefix tailTrace_1885257
  have hstable : (prefixWord ++ tailWord_1885257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885257).length < 2 ^ (prefixWord ++ tailWord_1885257).sum := by decide
  have hdescent : baseEnd_1885257 < baseStart_1885257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885261 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1885261 : Nat := 118140960795 + 1885261 * 2 ^ 59
def prefixEnd_1885261 : Nat := 4983230072969 + 3 ^ 40 * 1885261 * 2
def baseEnd_1885261 : Nat := 215121122705789698081633

theorem tailTrace_1885261 : CollatzResearch.WordTrace tailWord_1885261 prefixEnd_1885261 215121122705789698081633 := by
  unfold tailWord_1885261
  simp only [CollatzResearch.WordTrace]
  refine ⟨68761117623028848790015637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45840745082019232526677091 68761117623028848790015637)
  ·
    refine ⟨3223177388579477287031983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68761117623028848790015637 3223177388579477287031983)
    ·
      refine ⟨4834766082869215930547975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3223177388579477287031983 4834766082869215930547975)
      ·
        refine ⟨7252149124303823895821963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834766082869215930547975 7252149124303823895821963)
        ·
          refine ⟨10878223686455735843732945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252149124303823895821963 10878223686455735843732945)
          ·
            refine ⟨8158667764841801882799709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878223686455735843732945 8158667764841801882799709)
            ·
              refine ⟨3059500411815675706049891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8158667764841801882799709 3059500411815675706049891)
              ·
                refine ⟨4589250617723513559074837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059500411815675706049891 4589250617723513559074837)
                ·
                  refine ⟨215121122705789698081633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4589250617723513559074837 215121122705789698081633)
                  ·
                    rfl

theorem cell22_1885261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1885261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885261 prefixEnd_1885261 := by exact prefixLift 1885261
  have htrace : WordTrace (prefixWord ++ tailWord_1885261) baseStart_1885261 baseEnd_1885261 := by
    simpa [prefixWord, tailWord_1885261, baseEnd_1885261] using wordTrace_append hprefix tailTrace_1885261
  have hstable : (prefixWord ++ tailWord_1885261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885261).length < 2 ^ (prefixWord ++ tailWord_1885261).sum := by decide
  have hdescent : baseEnd_1885261 < baseStart_1885261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885338 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1885338 : Nat := 118140960795 + 1885338 * 2 ^ 59
def prefixEnd_1885338 : Nat := 4983230072969 + 3 ^ 40 * 1885338 * 2
def baseEnd_1885338 : Nat := 645389726790966560069663

theorem tailTrace_1885338 : CollatzResearch.WordTrace tailWord_1885338 prefixEnd_1885338 645389726790966560069663 := by
  unfold tailWord_1885338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17190981510937472735142167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45842617362499927293712445 17190981510937472735142167)
  ·
    refine ⟨25786472266406209102713251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17190981510937472735142167 25786472266406209102713251)
    ·
      refine ⟨38679708399609313654069877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25786472266406209102713251 38679708399609313654069877)
      ·
        refine ⟨3626222662463373155069051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38679708399609313654069877 3626222662463373155069051)
        ·
          refine ⟨5439333993695059732603577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626222662463373155069051 5439333993695059732603577)
          ·
            refine ⟨4079500495271294799452683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5439333993695059732603577 4079500495271294799452683)
            ·
              refine ⟨6119250742906942199179025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079500495271294799452683 6119250742906942199179025)
              ·
                refine ⟨4589438057180206649384269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6119250742906942199179025 4589438057180206649384269)
                ·
                  refine ⟨1721039271442577493519101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4589438057180206649384269 1721039271442577493519101)
                  ·
                    refine ⟨645389726790966560069663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721039271442577493519101 645389726790966560069663)
                    ·
                      rfl

theorem cell22_1885338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1885338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885338 prefixEnd_1885338 := by exact prefixLift 1885338
  have htrace : WordTrace (prefixWord ++ tailWord_1885338) baseStart_1885338 baseEnd_1885338 := by
    simpa [prefixWord, tailWord_1885338, baseEnd_1885338] using wordTrace_append hprefix tailTrace_1885338
  have hstable : (prefixWord ++ tailWord_1885338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885338).length < 2 ^ (prefixWord ++ tailWord_1885338).sum := by decide
  have hdescent : baseEnd_1885338 < baseStart_1885338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885441 : List Nat := [1, 2, 4, 1, 1, 4, 2, 7]
def baseStart_1885441 : Nat := 118140960795 + 1885441 * 2 ^ 59
def prefixEnd_1885441 : Nat := 4983230072969 + 3 ^ 40 * 1885441 * 2
def baseEnd_1885441 : Nat := 71713887310656513860483

theorem tailTrace_1885441 : CollatzResearch.WordTrace tailWord_1885441 prefixEnd_1885441 71713887310656513860483 := by
  unfold tailWord_1885441
  simp only [CollatzResearch.WordTrace]
  refine ⟨68767682762376739531568177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45845121841584493021045451 68767682762376739531568177)
  ·
    refine ⟨51575762071782554648676133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68767682762376739531568177 51575762071782554648676133)
    ·
      refine ⟨9670455388459228996626775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51575762071782554648676133 9670455388459228996626775)
      ·
        refine ⟨14505683082688843494940163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670455388459228996626775 14505683082688843494940163)
        ·
          refine ⟨21758524624033265242410245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14505683082688843494940163 21758524624033265242410245)
          ·
            refine ⟨4079723367006237232951921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21758524624033265242410245 4079723367006237232951921)
            ·
              refine ⟨3059792525254677924713941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079723367006237232951921 3059792525254677924713941)
              ·
                refine ⟨71713887310656513860483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3059792525254677924713941 71713887310656513860483)
                ·
                  rfl

theorem cell22_1885441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 7].length) (baseStart_1885441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885441 prefixEnd_1885441 := by exact prefixLift 1885441
  have htrace : WordTrace (prefixWord ++ tailWord_1885441) baseStart_1885441 baseEnd_1885441 := by
    simpa [prefixWord, tailWord_1885441, baseEnd_1885441] using wordTrace_append hprefix tailTrace_1885441
  have hstable : (prefixWord ++ tailWord_1885441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885441).length < 2 ^ (prefixWord ++ tailWord_1885441).sum := by decide
  have hdescent : baseEnd_1885441 < baseStart_1885441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885548 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 6]
def baseStart_1885548 : Nat := 118140960795 + 1885548 * 2 ^ 59
def prefixEnd_1885548 : Nat := 4983230072969 + 3 ^ 40 * 1885548 * 2
def baseEnd_1885548 : Nat := 215153871360865337439673

theorem tailTrace_1885548 : CollatzResearch.WordTrace tailWord_1885548 prefixEnd_1885548 215153871360865337439673 := by
  unfold tailWord_1885548
  simp only [CollatzResearch.WordTrace]
  refine ⟨34385792686494548402856649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45847723581992731203808865 34385792686494548402856649)
  ·
    refine ⟨25789344514870911302142487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34385792686494548402856649 25789344514870911302142487)
    ·
      refine ⟨38684016772306366953213731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25789344514870911302142487 38684016772306366953213731)
      ·
        refine ⟨58026025158459550429820597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38684016772306366953213731 58026025158459550429820597)
        ·
          refine ⟨5439939858605582852795681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58026025158459550429820597 5439939858605582852795681)
          ·
            refine ⟨4079954893954187139596761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5439939858605582852795681 4079954893954187139596761)
            ·
              refine ⟨3059966170465640354697571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079954893954187139596761 3059966170465640354697571)
              ·
                refine ⟨4589949255698460532046357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3059966170465640354697571 4589949255698460532046357)
                ·
                  refine ⟨215153871360865337439673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4589949255698460532046357 215153871360865337439673)
                  ·
                    rfl

theorem cell22_1885548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_1885548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885548 prefixEnd_1885548 := by exact prefixLift 1885548
  have htrace : WordTrace (prefixWord ++ tailWord_1885548) baseStart_1885548 baseEnd_1885548 := by
    simpa [prefixWord, tailWord_1885548, baseEnd_1885548] using wordTrace_append hprefix tailTrace_1885548
  have hstable : (prefixWord ++ tailWord_1885548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885548).length < 2 ^ (prefixWord ++ tailWord_1885548).sum := by decide
  have hdescent : baseEnd_1885548 < baseStart_1885548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885561 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_1885561 : Nat := 118140960795 + 1885561 * 2 ^ 59
def prefixEnd_1885561 : Nat := 4983230072969 + 3 ^ 40 * 1885561 * 2
def baseEnd_1885561 : Nat := 645466064248268311743979

theorem tailTrace_1885561 : CollatzResearch.WordTrace tailWord_1885561 prefixEnd_1885561 645466064248268311743979 := by
  unfold tailWord_1885561
  simp only [CollatzResearch.WordTrace]
  refine ⟨68772059521942000025936537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45848039681294666683957691 68772059521942000025936537)
  ·
    refine ⟨51579044641456500019452403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68772059521942000025936537 51579044641456500019452403)
    ·
      refine ⟨77368566962184750029178605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51579044641456500019452403 77368566962184750029178605)
      ·
        refine ⟨29013212610819281260941977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77368566962184750029178605 29013212610819281260941977)
        ·
          refine ⟨21759909458114460945706483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29013212610819281260941977 21759909458114460945706483)
          ·
            refine ⟨32639864187171691418559725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21759909458114460945706483 32639864187171691418559725)
            ·
              refine ⟨12239949070189384281959897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32639864187171691418559725 12239949070189384281959897)
              ·
                refine ⟨9179961802642038211469923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12239949070189384281959897 9179961802642038211469923)
                ·
                  refine ⟨13769942703963057317204885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9179961802642038211469923 13769942703963057317204885)
                  ·
                    refine ⟨645466064248268311743979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13769942703963057317204885 645466064248268311743979)
                    ·
                      rfl

theorem cell22_1885561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_1885561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885561 prefixEnd_1885561 := by exact prefixLift 1885561
  have htrace : WordTrace (prefixWord ++ tailWord_1885561) baseStart_1885561 baseEnd_1885561 := by
    simpa [prefixWord, tailWord_1885561, baseEnd_1885561] using wordTrace_append hprefix tailTrace_1885561
  have hstable : (prefixWord ++ tailWord_1885561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885561).length < 2 ^ (prefixWord ++ tailWord_1885561).sum := by decide
  have hdescent : baseEnd_1885561 < baseStart_1885561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885653 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1885653 : Nat := 118140960795 + 1885653 * 2 ^ 59
def prefixEnd_1885653 : Nat := 4983230072969 + 3 ^ 40 * 1885653 * 2
def baseEnd_1885653 : Nat := 645497557728410738443697

theorem tailTrace_1885653 : CollatzResearch.WordTrace tailWord_1885653 prefixEnd_1885653 645497557728410738443697 := by
  unfold tailWord_1885653
  simp only [CollatzResearch.WordTrace]
  refine ⟨68775415037608699738285613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45850276691739133158857075 68775415037608699738285613)
  ·
    refine ⟨25790780639103262401857105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68775415037608699738285613 25790780639103262401857105)
    ·
      refine ⟨19343085479327446801392829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25790780639103262401857105 19343085479327446801392829)
      ·
        refine ⟨7253657054747792550522311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19343085479327446801392829 7253657054747792550522311)
        ·
          refine ⟨10880485582121688825783467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7253657054747792550522311 10880485582121688825783467)
          ·
            refine ⟨16320728373182533238675201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10880485582121688825783467 16320728373182533238675201)
            ·
              refine ⟨12240546279886899929006401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16320728373182533238675201 12240546279886899929006401)
              ·
                refine ⟨9180409709915174946754801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12240546279886899929006401 9180409709915174946754801)
                ·
                  refine ⟨6885307282436381210066101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9180409709915174946754801 6885307282436381210066101)
                  ·
                    refine ⟨645497557728410738443697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6885307282436381210066101 645497557728410738443697)
                    ·
                      rfl

theorem cell22_1885653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1885653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885653 prefixEnd_1885653 := by exact prefixLift 1885653
  have htrace : WordTrace (prefixWord ++ tailWord_1885653) baseStart_1885653 baseEnd_1885653 := by
    simpa [prefixWord, tailWord_1885653, baseEnd_1885653] using wordTrace_append hprefix tailTrace_1885653
  have hstable : (prefixWord ++ tailWord_1885653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885653).length < 2 ^ (prefixWord ++ tailWord_1885653).sum := by decide
  have hdescent : baseEnd_1885653 < baseStart_1885653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885713 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1885713 : Nat := 118140960795 + 1885713 * 2 ^ 59
def prefixEnd_1885713 : Nat := 4983230072969 + 3 ^ 40 * 1885713 * 2
def baseEnd_1885713 : Nat := 645518096954590581943513

theorem tailTrace_1885713 : CollatzResearch.WordTrace tailWord_1885713 prefixEnd_1885713 645518096954590581943513 := by
  unfold tailWord_1885713
  simp only [CollatzResearch.WordTrace]
  refine ⟨68777603417391329985469793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45851735611594219990313195 68777603417391329985469793)
  ·
    refine ⟨51583202563043497489102345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68777603417391329985469793 51583202563043497489102345)
    ·
      refine ⟨38687401922282623116826759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51583202563043497489102345 38687401922282623116826759)
      ·
        refine ⟨58031102883423934675240139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38687401922282623116826759 58031102883423934675240139)
        ·
          refine ⟨87046654325135902012860209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58031102883423934675240139 87046654325135902012860209)
          ·
            refine ⟨65284990743851926509645157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87046654325135902012860209 65284990743851926509645157)
            ·
              refine ⟨12240935764472236220558467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65284990743851926509645157 12240935764472236220558467)
              ·
                refine ⟨18361403646708354330837701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12240935764472236220558467 18361403646708354330837701)
                ·
                  refine ⟨3442763183757816437032069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18361403646708354330837701 3442763183757816437032069)
                  ·
                    refine ⟨645518096954590581943513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3442763183757816437032069 645518096954590581943513)
                    ·
                      rfl

theorem cell22_1885713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1885713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885713 prefixEnd_1885713 := by exact prefixLift 1885713
  have htrace : WordTrace (prefixWord ++ tailWord_1885713) baseStart_1885713 baseEnd_1885713 := by
    simpa [prefixWord, tailWord_1885713, baseEnd_1885713] using wordTrace_append hprefix tailTrace_1885713
  have hstable : (prefixWord ++ tailWord_1885713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885713).length < 2 ^ (prefixWord ++ tailWord_1885713).sum := by decide
  have hdescent : baseEnd_1885713 < baseStart_1885713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885715 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 4, 3]
def baseStart_1885715 : Nat := 118140960795 + 1885715 * 2 ^ 59
def prefixEnd_1885715 : Nat := 4983230072969 + 3 ^ 40 * 1885715 * 2
def baseEnd_1885715 : Nat := 645518781595463243393507

theorem tailTrace_1885715 : CollatzResearch.WordTrace tailWord_1885715 prefixEnd_1885715 645518781595463243393507 := by
  unfold tailWord_1885715
  simp only [CollatzResearch.WordTrace]
  refine ⟨68777676363384084327042599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45851784242256056218028399 68777676363384084327042599)
  ·
    refine ⟨103166514545076126490563899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68777676363384084327042599 103166514545076126490563899)
    ·
      refine ⟨154749771817614189735845849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103166514545076126490563899 154749771817614189735845849)
      ·
        refine ⟨116062328863210642301884387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154749771817614189735845849 116062328863210642301884387)
        ·
          refine ⟨174093493294815963452826581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116062328863210642301884387 174093493294815963452826581)
          ·
            refine ⟨4080316249097249143425623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 174093493294815963452826581 4080316249097249143425623)
            ·
              refine ⟨6120474373645873715138435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080316249097249143425623 6120474373645873715138435)
              ·
                refine ⟨9180711560468810572707653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6120474373645873715138435 9180711560468810572707653)
                ·
                  refine ⟨1721383417587901982382685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9180711560468810572707653 1721383417587901982382685)
                  ·
                    refine ⟨645518781595463243393507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721383417587901982382685 645518781595463243393507)
                    ·
                      rfl

theorem cell22_1885715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 3].length) (baseStart_1885715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885715 prefixEnd_1885715 := by exact prefixLift 1885715
  have htrace : WordTrace (prefixWord ++ tailWord_1885715) baseStart_1885715 baseEnd_1885715 := by
    simpa [prefixWord, tailWord_1885715, baseEnd_1885715] using wordTrace_append hprefix tailTrace_1885715
  have hstable : (prefixWord ++ tailWord_1885715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885715).length < 2 ^ (prefixWord ++ tailWord_1885715).sum := by decide
  have hdescent : baseEnd_1885715 < baseStart_1885715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885818 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_1885818 : Nat := 118140960795 + 1885818 * 2 ^ 59
def prefixEnd_1885818 : Nat := 4983230072969 + 3 ^ 40 * 1885818 * 2
def baseEnd_1885818 : Nat := 215184680200135102689397

theorem tailTrace_1885818 : CollatzResearch.WordTrace tailWord_1885818 prefixEnd_1885818 215184680200135102689397 := by
  unfold tailWord_1885818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17195358270502733229510527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45854288721340621945361405 17195358270502733229510527)
  ·
    refine ⟨25793037405754099844265791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17195358270502733229510527 25793037405754099844265791)
    ·
      refine ⟨38689556108631149766398687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25793037405754099844265791 38689556108631149766398687)
      ·
        refine ⟨58034334162946724649598031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38689556108631149766398687 58034334162946724649598031)
        ·
          refine ⟨87051501244420086974397047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58034334162946724649598031 87051501244420086974397047)
          ·
            refine ⟨130577251866630130461595571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87051501244420086974397047 130577251866630130461595571)
            ·
              refine ⟨195865877799945195692393357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130577251866630130461595571 195865877799945195692393357)
              ·
                refine ⟨73449704174979448384647509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195865877799945195692393357 73449704174979448384647509)
                ·
                  refine ⟨215184680200135102689397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 73449704174979448384647509 215184680200135102689397)
                  ·
                    rfl

theorem cell22_1885818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_1885818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885818 prefixEnd_1885818 := by exact prefixLift 1885818
  have htrace : WordTrace (prefixWord ++ tailWord_1885818) baseStart_1885818 baseEnd_1885818 := by
    simpa [prefixWord, tailWord_1885818, baseEnd_1885818] using wordTrace_append hprefix tailTrace_1885818
  have hstable : (prefixWord ++ tailWord_1885818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885818).length < 2 ^ (prefixWord ++ tailWord_1885818).sum := by decide
  have hdescent : baseEnd_1885818 < baseStart_1885818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885828 : List Nat := [2, 3, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1885828 : Nat := 118140960795 + 1885828 * 2 ^ 59
def prefixEnd_1885828 : Nat := 4983230072969 + 3 ^ 40 * 1885828 * 2
def baseEnd_1885828 : Nat := 645557463804768615318161

theorem tailTrace_1885828 : CollatzResearch.WordTrace tailWord_1885828 prefixEnd_1885828 645557463804768615318161 := by
  unfold tailWord_1885828
  simp only [CollatzResearch.WordTrace]
  refine ⟨34390898905987352312953069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45854531874649803083937425 34390898905987352312953069)
  ·
    refine ⟨12896587089745257117357401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34390898905987352312953069 12896587089745257117357401)
    ·
      refine ⟨9672440317308942838018051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12896587089745257117357401 9672440317308942838018051)
      ·
        refine ⟨14508660475963414257027077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9672440317308942838018051 14508660475963414257027077)
        ·
          refine ⟨2720373839243140173192577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14508660475963414257027077 2720373839243140173192577)
          ·
            refine ⟨2040280379432355129894433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720373839243140173192577 2040280379432355129894433)
            ·
              refine ⟨1530210284574266347420825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2040280379432355129894433 1530210284574266347420825)
              ·
                refine ⟨1147657713430699760565619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530210284574266347420825 1147657713430699760565619)
                ·
                  refine ⟨1721486570146049640848429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1147657713430699760565619 1721486570146049640848429)
                  ·
                    refine ⟨645557463804768615318161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721486570146049640848429 645557463804768615318161)
                    ·
                      rfl

theorem cell22_1885828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1885828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885828 prefixEnd_1885828 := by exact prefixLift 1885828
  have htrace : WordTrace (prefixWord ++ tailWord_1885828) baseStart_1885828 baseEnd_1885828 := by
    simpa [prefixWord, tailWord_1885828, baseEnd_1885828] using wordTrace_append hprefix tailTrace_1885828
  have hstable : (prefixWord ++ tailWord_1885828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885828).length < 2 ^ (prefixWord ++ tailWord_1885828).sum := by decide
  have hdescent : baseEnd_1885828 < baseStart_1885828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885852 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 6]
def baseStart_1885852 : Nat := 118140960795 + 1885852 * 2 ^ 59
def prefixEnd_1885852 : Nat := 4983230072969 + 3 ^ 40 * 1885852 * 2
def baseEnd_1885852 : Nat := 215188559831746850906029

theorem tailTrace_1885852 : CollatzResearch.WordTrace tailWord_1885852 prefixEnd_1885852 215188559831746850906029 := by
  unfold tailWord_1885852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34391336581943878362389905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45855115442591837816519873 34391336581943878362389905)
  ·
    refine ⟨25793502436457908771792429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34391336581943878362389905 25793502436457908771792429)
    ·
      refine ⟨9672563413671715789422161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25793502436457908771792429 9672563413671715789422161)
      ·
        refine ⟨7254422560253786842066621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9672563413671715789422161 7254422560253786842066621)
        ·
          refine ⟨2720408460095170065774983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7254422560253786842066621 2720408460095170065774983)
          ·
            refine ⟨4080612690142755098662475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720408460095170065774983 4080612690142755098662475)
            ·
              refine ⟨6120919035214132647993713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080612690142755098662475 6120919035214132647993713)
              ·
                refine ⟨4590689276410599485995285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6120919035214132647993713 4590689276410599485995285)
                ·
                  refine ⟨215188559831746850906029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4590689276410599485995285 215188559831746850906029)
                  ·
                    rfl

theorem cell22_1885852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_1885852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885852 prefixEnd_1885852 := by exact prefixLift 1885852
  have htrace : WordTrace (prefixWord ++ tailWord_1885852) baseStart_1885852 baseEnd_1885852 := by
    simpa [prefixWord, tailWord_1885852, baseEnd_1885852] using wordTrace_append hprefix tailTrace_1885852
  have hstable : (prefixWord ++ tailWord_1885852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885852).length < 2 ^ (prefixWord ++ tailWord_1885852).sum := by decide
  have hdescent : baseEnd_1885852 < baseStart_1885852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885869 : List Nat := [1, 5, 2, 1, 1, 1, 4, 3, 4]
def baseStart_1885869 : Nat := 118140960795 + 1885869 * 2 ^ 59
def prefixEnd_1885869 : Nat := 4983230072969 + 3 ^ 40 * 1885869 * 2
def baseEnd_1885869 : Nat := 215190499647552725014345

theorem tailTrace_1885869 : CollatzResearch.WordTrace tailWord_1885869 prefixEnd_1885869 215190499647552725014345 := by
  unfold tailWord_1885869
  simp only [CollatzResearch.WordTrace]
  refine ⟨68783293204826168628148661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45855528803217445752099107 68783293204826168628148661)
  ·
    refine ⟨6448433737952453308888937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68783293204826168628148661 6448433737952453308888937)
    ·
      refine ⟨4836325303464339981666703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6448433737952453308888937 4836325303464339981666703)
      ·
        refine ⟨7254487955196509972500055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836325303464339981666703 7254487955196509972500055)
        ·
          refine ⟨10881731932794764958750083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254487955196509972500055 10881731932794764958750083)
          ·
            refine ⟨16322597899192147438125125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10881731932794764958750083 16322597899192147438125125)
            ·
              refine ⟨3060487106098527644648461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16322597899192147438125125 3060487106098527644648461)
              ·
                refine ⟨1147682664786947866743173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060487106098527644648461 1147682664786947866743173)
                ·
                  refine ⟨215190499647552725014345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1147682664786947866743173 215190499647552725014345)
                  ·
                    rfl

theorem cell22_1885869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_1885869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885869 prefixEnd_1885869 := by exact prefixLift 1885869
  have htrace : WordTrace (prefixWord ++ tailWord_1885869) baseStart_1885869 baseEnd_1885869 := by
    simpa [prefixWord, tailWord_1885869, baseEnd_1885869] using wordTrace_append hprefix tailTrace_1885869
  have hstable : (prefixWord ++ tailWord_1885869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885869).length < 2 ^ (prefixWord ++ tailWord_1885869).sum := by decide
  have hdescent : baseEnd_1885869 < baseStart_1885869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885884 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_1885884 : Nat := 118140960795 + 1885884 * 2 ^ 59
def prefixEnd_1885884 : Nat := 4983230072969 + 3 ^ 40 * 1885884 * 2
def baseEnd_1885884 : Nat := 645576633749203135917989

theorem tailTrace_1885884 : CollatzResearch.WordTrace tailWord_1885884 prefixEnd_1885884 645576633749203135917989 := by
  unfold tailWord_1885884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34391920149885913094972353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45855893533181217459963137 34391920149885913094972353)
  ·
    refine ⟨25793940112414434821229265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34391920149885913094972353 25793940112414434821229265)
    ·
      refine ⟨19345455084310826115921949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25793940112414434821229265 19345455084310826115921949)
      ·
        refine ⟨7254545656616559793470731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19345455084310826115921949 7254545656616559793470731)
        ·
          refine ⟨10881818484924839690206097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254545656616559793470731 10881818484924839690206097)
          ·
            refine ⟨8161363863693629767654573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10881818484924839690206097 8161363863693629767654573)
            ·
              refine ⟨3060511448885111162870465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8161363863693629767654573 3060511448885111162870465)
              ·
                refine ⟨2295383586663833372152849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060511448885111162870465 2295383586663833372152849)
                ·
                  refine ⟨1721537689997875029114637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2295383586663833372152849 1721537689997875029114637)
                  ·
                    refine ⟨645576633749203135917989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721537689997875029114637 645576633749203135917989)
                    ·
                      rfl

theorem cell22_1885884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_1885884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885884 prefixEnd_1885884 := by exact prefixLift 1885884
  have htrace : WordTrace (prefixWord ++ tailWord_1885884) baseStart_1885884 baseEnd_1885884 := by
    simpa [prefixWord, tailWord_1885884, baseEnd_1885884] using wordTrace_append hprefix tailTrace_1885884
  have hstable : (prefixWord ++ tailWord_1885884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885884).length < 2 ^ (prefixWord ++ tailWord_1885884).sum := by decide
  have hdescent : baseEnd_1885884 < baseStart_1885884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885901 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1885901 : Nat := 118140960795 + 1885901 * 2 ^ 59
def prefixEnd_1885901 : Nat := 4983230072969 + 3 ^ 40 * 1885901 * 2
def baseEnd_1885901 : Nat := 645582453196620758242937

theorem tailTrace_1885901 : CollatzResearch.WordTrace tailWord_1885901 prefixEnd_1885901 645582453196620758242937 := by
  unfold tailWord_1885901
  simp only [CollatzResearch.WordTrace]
  refine ⟨68784460340710238093313557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45856306893806825395542371 68784460340710238093313557)
  ·
    refine ⟨3224271578470792410624073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68784460340710238093313557 3224271578470792410624073)
    ·
      refine ⟨2418203683853094307968055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3224271578470792410624073 2418203683853094307968055)
      ·
        refine ⟨3627305525779641461952083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418203683853094307968055 3627305525779641461952083)
        ·
          refine ⟨5440958288669462192928125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627305525779641461952083 5440958288669462192928125)
          ·
            refine ⟨2040359358251048322348047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5440958288669462192928125 2040359358251048322348047)
            ·
              refine ⟨3060539037376572483522071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040359358251048322348047 3060539037376572483522071)
              ·
                refine ⟨4590808556064858725283107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060539037376572483522071 4590808556064858725283107)
                ·
                  refine ⟨6886212834097288087924661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4590808556064858725283107 6886212834097288087924661)
                  ·
                    refine ⟨645582453196620758242937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6886212834097288087924661 645582453196620758242937)
                    ·
                      rfl

theorem cell22_1885901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1885901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885901 prefixEnd_1885901 := by exact prefixLift 1885901
  have htrace : WordTrace (prefixWord ++ tailWord_1885901) baseStart_1885901 baseEnd_1885901 := by
    simpa [prefixWord, tailWord_1885901, baseEnd_1885901] using wordTrace_append hprefix tailTrace_1885901
  have hstable : (prefixWord ++ tailWord_1885901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885901).length < 2 ^ (prefixWord ++ tailWord_1885901).sum := by decide
  have hdescent : baseEnd_1885901 < baseStart_1885901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885912 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 3, 3]
def baseStart_1885912 : Nat := 118140960795 + 1885912 * 2 ^ 59
def prefixEnd_1885912 : Nat := 4983230072969 + 3 ^ 40 * 1885912 * 2
def baseEnd_1885912 : Nat := 645586218721420396217903

theorem tailTrace_1885912 : CollatzResearch.WordTrace tailWord_1885912 prefixEnd_1885912 645586218721420396217903 := by
  unfold tailWord_1885912
  simp only [CollatzResearch.WordTrace]
  refine ⟨34392430771835193485981995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45856574362446924647975993 34392430771835193485981995)
  ·
    refine ⟨51588646157752790228972993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34392430771835193485981995 51588646157752790228972993)
    ·
      refine ⟨38691484618314592671729745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51588646157752790228972993 38691484618314592671729745)
      ·
        refine ⟨29018613463735944503797309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38691484618314592671729745 29018613463735944503797309)
        ·
          refine ⟨10881980048900979188923991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29018613463735944503797309 10881980048900979188923991)
          ·
            refine ⟨16322970073351468783385987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10881980048900979188923991 16322970073351468783385987)
            ·
              refine ⟨24484455110027203175078981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16322970073351468783385987 24484455110027203175078981)
              ·
                refine ⟨4590835333130100595327309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24484455110027203175078981 4590835333130100595327309)
                ·
                  refine ⟨1721563249923787723247741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4590835333130100595327309 1721563249923787723247741)
                  ·
                    refine ⟨645586218721420396217903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721563249923787723247741 645586218721420396217903)
                    ·
                      rfl

theorem cell22_1885912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_1885912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885912 prefixEnd_1885912 := by exact prefixLift 1885912
  have htrace : WordTrace (prefixWord ++ tailWord_1885912) baseStart_1885912 baseEnd_1885912 := by
    simpa [prefixWord, tailWord_1885912, baseEnd_1885912] using wordTrace_append hprefix tailTrace_1885912
  have hstable : (prefixWord ++ tailWord_1885912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885912).length < 2 ^ (prefixWord ++ tailWord_1885912).sum := by decide
  have hdescent : baseEnd_1885912 < baseStart_1885912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885925 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 9]
def baseStart_1885925 : Nat := 118140960795 + 1885925 * 2 ^ 59
def prefixEnd_1885925 : Nat := 4983230072969 + 3 ^ 40 * 1885925 * 2
def baseEnd_1885925 : Nat := 215196889629030898547621

theorem tailTrace_1885925 : CollatzResearch.WordTrace tailWord_1885925 prefixEnd_1885925 215196889629030898547621 := by
  unfold tailWord_1885925
  simp only [CollatzResearch.WordTrace]
  refine ⟨68785335692623290192187229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45856890461748860128124819 68785335692623290192187229)
  ·
    refine ⟨25794500884733733822070211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68785335692623290192187229 25794500884733733822070211)
    ·
      refine ⟨38691751327100600733105317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25794500884733733822070211 38691751327100600733105317)
      ·
        refine ⟨7254703373831362637457247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38691751327100600733105317 7254703373831362637457247)
        ·
          refine ⟨10882055060747043956185871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254703373831362637457247 10882055060747043956185871)
          ·
            refine ⟨16323082591120565934278807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10882055060747043956185871 16323082591120565934278807)
            ·
              refine ⟨24484623886680848901418211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16323082591120565934278807 24484623886680848901418211)
              ·
                refine ⟨36726935830021273352127317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24484623886680848901418211 36726935830021273352127317)
                ·
                  refine ⟨215196889629030898547621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36726935830021273352127317 215196889629030898547621)
                  ·
                    rfl

theorem cell22_1885925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_1885925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885925 prefixEnd_1885925 := by exact prefixLift 1885925
  have htrace : WordTrace (prefixWord ++ tailWord_1885925) baseStart_1885925 baseEnd_1885925 := by
    simpa [prefixWord, tailWord_1885925, baseEnd_1885925] using wordTrace_append hprefix tailTrace_1885925
  have hstable : (prefixWord ++ tailWord_1885925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885925).length < 2 ^ (prefixWord ++ tailWord_1885925).sum := by decide
  have hdescent : baseEnd_1885925 < baseStart_1885925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885942 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1885942 : Nat := 118140960795 + 1885942 * 2 ^ 59
def prefixEnd_1885942 : Nat := 4983230072969 + 3 ^ 40 * 1885942 * 2
def baseEnd_1885942 : Nat := 215198829444836772655937

theorem tailTrace_1885942 : CollatzResearch.WordTrace tailWord_1885942 prefixEnd_1885942 215198829444836772655937 := by
  unfold tailWord_1885942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299122233347606380972255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45857303822374468063704053 4299122233347606380972255)
  ·
    refine ⟨6448683350021409571458383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4299122233347606380972255 6448683350021409571458383)
    ·
      refine ⟨9673025025032114357187575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6448683350021409571458383 9673025025032114357187575)
      ·
        refine ⟨14509537537548171535781363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9673025025032114357187575 14509537537548171535781363)
        ·
          refine ⟨21764306306322257303672045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14509537537548171535781363 21764306306322257303672045)
          ·
            refine ⟨8161614864870846488877017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21764306306322257303672045 8161614864870846488877017)
            ·
              refine ⟨6121211148653134866657763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8161614864870846488877017 6121211148653134866657763)
              ·
                refine ⟨9181816722979702299986645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6121211148653134866657763 9181816722979702299986645)
                ·
                  refine ⟨215198829444836772655937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9181816722979702299986645 215198829444836772655937)
                  ·
                    rfl

theorem cell22_1885942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1885942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885942 prefixEnd_1885942 := by exact prefixLift 1885942
  have htrace : WordTrace (prefixWord ++ tailWord_1885942) baseStart_1885942 baseEnd_1885942 := by
    simpa [prefixWord, tailWord_1885942, baseEnd_1885942] using wordTrace_append hprefix tailTrace_1885942
  have hstable : (prefixWord ++ tailWord_1885942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885942).length < 2 ^ (prefixWord ++ tailWord_1885942).sum := by decide
  have hdescent : baseEnd_1885942 < baseStart_1885942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1885959 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 5]
def baseStart_1885959 : Nat := 118140960795 + 1885959 * 2 ^ 59
def prefixEnd_1885959 : Nat := 4983230072969 + 3 ^ 40 * 1885959 * 2
def baseEnd_1885959 : Nat := 215200769260642646764253

theorem tailTrace_1885959 : CollatzResearch.WordTrace tailWord_1885959 prefixEnd_1885959 215200769260642646764253 := by
  unfold tailWord_1885959
  simp only [CollatzResearch.WordTrace]
  refine ⟨68786575774500113998924931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45857717183000075999283287 68786575774500113998924931)
  ·
    refine ⟨103179863661750170998387397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68786575774500113998924931 103179863661750170998387397)
    ·
      refine ⟨19346224436578157062197637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103179863661750170998387397 19346224436578157062197637)
      ·
        refine ⟨3627417081858404449162057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19346224436578157062197637 3627417081858404449162057)
        ·
          refine ⟨2720562811393803336871543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3627417081858404449162057 2720562811393803336871543)
          ·
            refine ⟨4080844217090705005307315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720562811393803336871543 4080844217090705005307315)
            ·
              refine ⟨6121266325636057507960973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080844217090705005307315 6121266325636057507960973)
              ·
                refine ⟨2295474872113521565485365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6121266325636057507960973 2295474872113521565485365)
                ·
                  refine ⟨215200769260642646764253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2295474872113521565485365 215200769260642646764253)
                  ·
                    rfl

theorem cell22_1885959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 5].length) (baseStart_1885959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1885959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1885959 prefixEnd_1885959 := by exact prefixLift 1885959
  have htrace : WordTrace (prefixWord ++ tailWord_1885959) baseStart_1885959 baseEnd_1885959 := by
    simpa [prefixWord, tailWord_1885959, baseEnd_1885959] using wordTrace_append hprefix tailTrace_1885959
  have hstable : (prefixWord ++ tailWord_1885959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1885959).length < 2 ^ (prefixWord ++ tailWord_1885959).sum := by decide
  have hdescent : baseEnd_1885959 < baseStart_1885959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1885959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886000 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_1886000 : Nat := 118140960795 + 1886000 * 2 ^ 59
def prefixEnd_1886000 : Nat := 4983230072969 + 3 ^ 40 * 1886000 * 2
def baseEnd_1886000 : Nat := 645616342919817500017633

theorem tailTrace_1886000 : CollatzResearch.WordTrace tailWord_1886000 prefixEnd_1886000 645616342919817500017633 := by
  unfold tailWord_1886000
  simp only [CollatzResearch.WordTrace]
  refine ⟨34394035583675789000583727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45858714111567718667444969 34394035583675789000583727)
  ·
    refine ⟨51591053375513683500875591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34394035583675789000583727 51591053375513683500875591)
    ·
      refine ⟨77386580063270525251313387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51591053375513683500875591 77386580063270525251313387)
      ·
        refine ⟨116079870094905787876970081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77386580063270525251313387 116079870094905787876970081)
        ·
          refine ⟨87059902571179340907727561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116079870094905787876970081 87059902571179340907727561)
          ·
            refine ⟨65294926928384505680795671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87059902571179340907727561 65294926928384505680795671)
            ·
              refine ⟨97942390392576758521193507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65294926928384505680795671 97942390392576758521193507)
              ·
                refine ⟨146913585588865137781790261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97942390392576758521193507 146913585588865137781790261)
                ·
                  refine ⟨13773148648956106667042837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146913585588865137781790261 13773148648956106667042837)
                  ·
                    refine ⟨645616342919817500017633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13773148648956106667042837 645616342919817500017633)
                    ·
                      rfl

theorem cell22_1886000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_1886000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886000 prefixEnd_1886000 := by exact prefixLift 1886000
  have htrace : WordTrace (prefixWord ++ tailWord_1886000) baseStart_1886000 baseEnd_1886000 := by
    simpa [prefixWord, tailWord_1886000, baseEnd_1886000] using wordTrace_append hprefix tailTrace_1886000
  have hstable : (prefixWord ++ tailWord_1886000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886000).length < 2 ^ (prefixWord ++ tailWord_1886000).sum := by decide
  have hdescent : baseEnd_1886000 < baseStart_1886000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886019 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 2, 3]
def baseStart_1886019 : Nat := 118140960795 + 1886019 * 2 ^ 59
def prefixEnd_1886019 : Nat := 4983230072969 + 3 ^ 40 * 1886019 * 2
def baseEnd_1886019 : Nat := 645622847008107783792575

theorem tailTrace_1886019 : CollatzResearch.WordTrace tailWord_1886019 prefixEnd_1886019 645622847008107783792575 := by
  unfold tailWord_1886019
  simp only [CollatzResearch.WordTrace]
  refine ⟨68788764154282744246109111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45859176102855162830739407 68788764154282744246109111)
  ·
    refine ⟨103183146231424116369163667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68788764154282744246109111 103183146231424116369163667)
    ·
      refine ⟨154774719347136174553745501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103183146231424116369163667 154774719347136174553745501)
      ·
        refine ⟨58040519755176065457654563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154774719347136174553745501 58040519755176065457654563)
        ·
          refine ⟨87060779632764098186481845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58040519755176065457654563 87060779632764098186481845)
          ·
            refine ⟨8161948090571634204982673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87060779632764098186481845 8161948090571634204982673)
            ·
              refine ⟨6121461067928725653737005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8161948090571634204982673 6121461067928725653737005)
              ·
                refine ⟨2295547900473272120151377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6121461067928725653737005 2295547900473272120151377)
                ·
                  refine ⟨1721660925354954090113533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2295547900473272120151377 1721660925354954090113533)
                  ·
                    refine ⟨645622847008107783792575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721660925354954090113533 645622847008107783792575)
                    ·
                      rfl

theorem cell22_1886019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 3].length) (baseStart_1886019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886019 prefixEnd_1886019 := by exact prefixLift 1886019
  have htrace : WordTrace (prefixWord ++ tailWord_1886019) baseStart_1886019 baseEnd_1886019 := by
    simpa [prefixWord, tailWord_1886019, baseEnd_1886019] using wordTrace_append hprefix tailTrace_1886019
  have hstable : (prefixWord ++ tailWord_1886019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886019).length < 2 ^ (prefixWord ++ tailWord_1886019).sum := by decide
  have hdescent : baseEnd_1886019 < baseStart_1886019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886034 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1886034 : Nat := 118140960795 + 1886034 * 2 ^ 59
def prefixEnd_1886034 : Nat := 4983230072969 + 3 ^ 40 * 1886034 * 2
def baseEnd_1886034 : Nat := 645627981814652744667529

theorem tailTrace_1886034 : CollatzResearch.WordTrace tailWord_1886034 prefixEnd_1886034 645627981814652744667529 := by
  unfold tailWord_1886034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17197327812307100451976289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45859540832818934538603437 17197327812307100451976289)
  ·
    refine ⟨12897995859230325338982217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17197327812307100451976289 12897995859230325338982217)
    ·
      refine ⟨9673496894422744004236663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12897995859230325338982217 9673496894422744004236663)
      ·
        refine ⟨14510245341634116006354995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9673496894422744004236663 14510245341634116006354995)
        ·
          refine ⟨21765368012451174009532493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14510245341634116006354995 21765368012451174009532493)
          ·
            refine ⟨8162013004669190253574685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21765368012451174009532493 8162013004669190253574685)
            ·
              refine ⟨3060754876750946345090507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8162013004669190253574685 3060754876750946345090507)
              ·
                refine ⟨4591132315126419517635761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060754876750946345090507 4591132315126419517635761)
                ·
                  refine ⟨3443349236344814638226821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591132315126419517635761 3443349236344814638226821)
                  ·
                    refine ⟨645627981814652744667529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3443349236344814638226821 645627981814652744667529)
                    ·
                      rfl

theorem cell22_1886034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1886034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886034 prefixEnd_1886034 := by exact prefixLift 1886034
  have htrace : WordTrace (prefixWord ++ tailWord_1886034) baseStart_1886034 baseEnd_1886034 := by
    simpa [prefixWord, tailWord_1886034, baseEnd_1886034] using wordTrace_append hprefix tailTrace_1886034
  have hstable : (prefixWord ++ tailWord_1886034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886034).length < 2 ^ (prefixWord ++ tailWord_1886034).sum := by decide
  have hdescent : baseEnd_1886034 < baseStart_1886034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886070 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_1886070 : Nat := 118140960795 + 1886070 * 2 ^ 59
def prefixEnd_1886070 : Nat := 4983230072969 + 3 ^ 40 * 1886070 * 2
def baseEnd_1886070 : Nat := 645640305350360650767419

theorem tailTrace_1886070 : CollatzResearch.WordTrace tailWord_1886070 prefixEnd_1886070 645640305350360650767419 := by
  unfold tailWord_1886070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299414017318623747263479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45860416184731986637477109 4299414017318623747263479)
  ·
    refine ⟨6449121025977935620895219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4299414017318623747263479 6449121025977935620895219)
    ·
      refine ⟨9673681538966903431342829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6449121025977935620895219 9673681538966903431342829)
      ·
        refine ⟨3627630577112588786753561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9673681538966903431342829 3627630577112588786753561)
        ·
          refine ⟨2720722932834441590065171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3627630577112588786753561 2720722932834441590065171)
          ·
            refine ⟨4081084399251662385097757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720722932834441590065171 4081084399251662385097757)
            ·
              refine ⟨1530406649719373394411659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4081084399251662385097757 1530406649719373394411659)
              ·
                refine ⟨2295609974579060091617489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530406649719373394411659 2295609974579060091617489)
                ·
                  refine ⟨1721707480934295068713117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2295609974579060091617489 1721707480934295068713117)
                  ·
                    refine ⟨645640305350360650767419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721707480934295068713117 645640305350360650767419)
                    ·
                      rfl

theorem cell22_1886070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_1886070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886070 prefixEnd_1886070 := by exact prefixLift 1886070
  have htrace : WordTrace (prefixWord ++ tailWord_1886070) baseStart_1886070 baseEnd_1886070 := by
    simpa [prefixWord, tailWord_1886070, baseEnd_1886070] using wordTrace_append hprefix tailTrace_1886070
  have hstable : (prefixWord ++ tailWord_1886070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886070).length < 2 ^ (prefixWord ++ tailWord_1886070).sum := by decide
  have hdescent : baseEnd_1886070 < baseStart_1886070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886141 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_1886141 : Nat := 118140960795 + 1886141 * 2 ^ 59
def prefixEnd_1886141 : Nat := 4983230072969 + 3 ^ 40 * 1886141 * 2
def baseEnd_1886141 : Nat := 645664610101340132242201

theorem tailTrace_1886141 : CollatzResearch.WordTrace tailWord_1886141 prefixEnd_1886141 645664610101340132242201 := by
  unfold tailWord_1886141
  simp only [CollatzResearch.WordTrace]
  refine ⟨68793213859840759082050277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45862142573227172721366851 68793213859840759082050277)
  ·
    refine ⟨12898727598720142327884427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68793213859840759082050277 12898727598720142327884427)
    ·
      refine ⟨19348091398080213491826641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12898727598720142327884427 19348091398080213491826641)
      ·
        refine ⟨14511068548560160118869981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19348091398080213491826641 14511068548560160118869981)
        ·
          refine ⟨5441650705710060044576243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14511068548560160118869981 5441650705710060044576243)
          ·
            refine ⟨8162476058565090066864365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5441650705710060044576243 8162476058565090066864365)
            ·
              refine ⟨3060928521961908775074137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8162476058565090066864365 3060928521961908775074137)
              ·
                refine ⟨2295696391471431581305603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3060928521961908775074137 2295696391471431581305603)
                ·
                  refine ⟨3443544587207147371958405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2295696391471431581305603 3443544587207147371958405)
                  ·
                    refine ⟨645664610101340132242201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3443544587207147371958405 645664610101340132242201)
                    ·
                      rfl

theorem cell22_1886141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_1886141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886141 prefixEnd_1886141 := by exact prefixLift 1886141
  have htrace : WordTrace (prefixWord ++ tailWord_1886141) baseStart_1886141 baseEnd_1886141 := by
    simpa [prefixWord, tailWord_1886141, baseEnd_1886141] using wordTrace_append hprefix tailTrace_1886141
  have hstable : (prefixWord ++ tailWord_1886141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886141).length < 2 ^ (prefixWord ++ tailWord_1886141).sum := by decide
  have hdescent : baseEnd_1886141 < baseStart_1886141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886154 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1886154 : Nat := 118140960795 + 1886154 * 2 ^ 59
def prefixEnd_1886154 : Nat := 4983230072969 + 3 ^ 40 * 1886154 * 2
def baseEnd_1886154 : Nat := 645669060267012431667161

theorem tailTrace_1886154 : CollatzResearch.WordTrace tailWord_1886154 prefixEnd_1886154 645669060267012431667161 := by
  unfold tailWord_1886154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17198422002198415575568379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45862458672529108201515677 17198422002198415575568379)
  ·
    refine ⟨25797633003297623363352569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17198422002198415575568379 25797633003297623363352569)
    ·
      refine ⟨19348224752473217522514427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25797633003297623363352569 19348224752473217522514427)
      ·
        refine ⟨29022337128709826283771641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19348224752473217522514427 29022337128709826283771641)
        ·
          refine ⟨21766752846532369712828731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29022337128709826283771641 21766752846532369712828731)
          ·
            refine ⟨32650129269798554569243097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21766752846532369712828731 32650129269798554569243097)
            ·
              refine ⟨24487596952348915926932323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32650129269798554569243097 24487596952348915926932323)
              ·
                refine ⟨36731395428523373890398485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24487596952348915926932323 36731395428523373890398485)
                ·
                  refine ⟨1721784160712033151112429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36731395428523373890398485 1721784160712033151112429)
                  ·
                    refine ⟨645669060267012431667161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721784160712033151112429 645669060267012431667161)
                    ·
                      rfl

theorem cell22_1886154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1886154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886154 prefixEnd_1886154 := by exact prefixLift 1886154
  have htrace : WordTrace (prefixWord ++ tailWord_1886154) baseStart_1886154 baseEnd_1886154 := by
    simpa [prefixWord, tailWord_1886154, baseEnd_1886154] using wordTrace_append hprefix tailTrace_1886154
  have hstable : (prefixWord ++ tailWord_1886154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886154).length < 2 ^ (prefixWord ++ tailWord_1886154).sum := by decide
  have hdescent : baseEnd_1886154 < baseStart_1886154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886173 : List Nat := [1, 4, 3, 1, 3, 1, 1, 4, 4]
def baseStart_1886173 : Nat := 118140960795 + 1886173 * 2 ^ 59
def prefixEnd_1886173 : Nat := 4983230072969 + 3 ^ 40 * 1886173 * 2
def baseEnd_1886173 : Nat := 215225188118434238480701

theorem tailTrace_1886173 : CollatzResearch.WordTrace tailWord_1886173 prefixEnd_1886173 215225188118434238480701 := by
  unfold tailWord_1886173
  simp only [CollatzResearch.WordTrace]
  refine ⟨68794380995724828547215173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45862920663816552364810115 68794380995724828547215173)
  ·
    refine ⟨12898946436698405352602845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68794380995724828547215173 12898946436698405352602845)
    ·
      refine ⟨4837104913761902007226067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12898946436698405352602845 4837104913761902007226067)
      ·
        refine ⟨7255657370642853010839101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837104913761902007226067 7255657370642853010839101)
        ·
          refine ⟨2720871513991069879064663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7255657370642853010839101 2720871513991069879064663)
          ·
            refine ⟨4081307270986604818596995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2720871513991069879064663 4081307270986604818596995)
            ·
              refine ⟨6121960906479907227895493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081307270986604818596995 6121960906479907227895493)
              ·
                refine ⟨1147867669964982605230405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6121960906479907227895493 1147867669964982605230405)
                ·
                  refine ⟨215225188118434238480701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1147867669964982605230405 215225188118434238480701)
                  ·
                    rfl

theorem cell22_1886173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_1886173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886173 prefixEnd_1886173 := by exact prefixLift 1886173
  have htrace : WordTrace (prefixWord ++ tailWord_1886173) baseStart_1886173 baseEnd_1886173 := by
    simpa [prefixWord, tailWord_1886173, baseEnd_1886173] using wordTrace_append hprefix tailTrace_1886173
  have hstable : (prefixWord ++ tailWord_1886173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886173).length < 2 ^ (prefixWord ++ tailWord_1886173).sum := by decide
  have hdescent : baseEnd_1886173 < baseStart_1886173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886259 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 3, 4]
def baseStart_1886259 : Nat := 118140960795 + 1886259 * 2 ^ 59
def prefixEnd_1886259 : Nat := 4983230072969 + 3 ^ 40 * 1886259 * 2
def baseEnd_1886259 : Nat := 645705003912827157791839

theorem tailTrace_1886259 : CollatzResearch.WordTrace tailWord_1886259 prefixEnd_1886259 645705003912827157791839 := by
  unfold tailWord_1886259
  simp only [CollatzResearch.WordTrace]
  refine ⟨68797517673413265234845831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45865011782275510156563887 68797517673413265234845831)
  ·
    refine ⟨103196276510119897852268747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68797517673413265234845831 103196276510119897852268747)
    ·
      refine ⟨154794414765179846778403121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103196276510119897852268747 154794414765179846778403121)
      ·
        refine ⟨116095811073884885083802341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154794414765179846778403121 116095811073884885083802341)
        ·
          refine ⟨21767964576353415953212939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116095811073884885083802341 21767964576353415953212939)
          ·
            refine ⟨32651946864530123929819409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21767964576353415953212939 32651946864530123929819409)
            ·
              refine ⟨24488960148397592947364557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32651946864530123929819409 24488960148397592947364557)
              ·
                refine ⟨9183360055649097355261709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24488960148397592947364557 9183360055649097355261709)
                ·
                  refine ⟨3443760020868411508223141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9183360055649097355261709 3443760020868411508223141)
                  ·
                    refine ⟨645705003912827157791839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3443760020868411508223141 645705003912827157791839)
                    ·
                      rfl

theorem cell22_1886259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_1886259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886259 prefixEnd_1886259 := by exact prefixLift 1886259
  have htrace : WordTrace (prefixWord ++ tailWord_1886259) baseStart_1886259 baseEnd_1886259 := by
    simpa [prefixWord, tailWord_1886259, baseEnd_1886259] using wordTrace_append hprefix tailTrace_1886259
  have hstable : (prefixWord ++ tailWord_1886259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886259).length < 2 ^ (prefixWord ++ tailWord_1886259).sum := by decide
  have hdescent : baseEnd_1886259 < baseStart_1886259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886319 : List Nat := [1, 1, 2, 1, 3, 4, 2, 8]
def baseStart_1886319 : Nat := 118140960795 + 1886319 * 2 ^ 59
def prefixEnd_1886319 : Nat := 4983230072969 + 3 ^ 40 * 1886319 * 2
def baseEnd_1886319 : Nat := 71747282571000777921295

theorem tailTrace_1886319 : CollatzResearch.WordTrace tailWord_1886319 prefixEnd_1886319 71747282571000777921295 := by
  unfold tailWord_1886319
  simp only [CollatzResearch.WordTrace]
  refine ⟨68799706053195895482030011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45866470702130596988020007 68799706053195895482030011)
  ·
    refine ⟨103199559079793843223045017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68799706053195895482030011 103199559079793843223045017)
    ·
      refine ⟨77399669309845382417283763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103199559079793843223045017 77399669309845382417283763)
      ·
        refine ⟨116099503964768073625925645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77399669309845382417283763 116099503964768073625925645)
        ·
          refine ⟨43537313986788027609722117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116099503964768073625925645 43537313986788027609722117)
          ·
            refine ⟨8163246372522755176822897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43537313986788027609722117 8163246372522755176822897)
            ·
              refine ⟨6122434779392066382617173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8163246372522755176822897 6122434779392066382617173)
              ·
                refine ⟨71747282571000777921295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6122434779392066382617173 71747282571000777921295)
                ·
                  rfl

theorem cell22_1886319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 8].length) (baseStart_1886319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886319 prefixEnd_1886319 := by exact prefixLift 1886319
  have htrace : WordTrace (prefixWord ++ tailWord_1886319) baseStart_1886319 baseEnd_1886319 := by
    simpa [prefixWord, tailWord_1886319, baseEnd_1886319] using wordTrace_append hprefix tailTrace_1886319
  have hstable : (prefixWord ++ tailWord_1886319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886319).length < 2 ^ (prefixWord ++ tailWord_1886319).sum := by decide
  have hdescent : baseEnd_1886319 < baseStart_1886319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886321 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1886321 : Nat := 118140960795 + 1886321 * 2 ^ 59
def prefixEnd_1886321 : Nat := 4983230072969 + 3 ^ 40 * 1886321 * 2
def baseEnd_1886321 : Nat := 645726227779879662741649

theorem tailTrace_1886321 : CollatzResearch.WordTrace tailWord_1886321 prefixEnd_1886321 645726227779879662741649 := by
  unfold tailWord_1886321
  simp only [CollatzResearch.WordTrace]
  refine ⟨68799778999188649823602817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45866519332792433215735211 68799778999188649823602817)
  ·
    refine ⟨51599834249391487367702113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68799778999188649823602817 51599834249391487367702113)
    ·
      refine ⟨38699875687043615525776585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51599834249391487367702113 38699875687043615525776585)
      ·
        refine ⟨29024906765282711644332439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38699875687043615525776585 29024906765282711644332439)
        ·
          refine ⟨43537360147924067466498659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29024906765282711644332439 43537360147924067466498659)
          ·
            refine ⟨65306040221886101199747989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43537360147924067466498659 65306040221886101199747989)
            ·
              refine ⟨3061220635400910993738187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65306040221886101199747989 3061220635400910993738187)
              ·
                refine ⟨4591830953101366490607281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061220635400910993738187 4591830953101366490607281)
                ·
                  refine ⟨3443873214826024867955461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4591830953101366490607281 3443873214826024867955461)
                  ·
                    refine ⟨645726227779879662741649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3443873214826024867955461 645726227779879662741649)
                    ·
                      rfl

theorem cell22_1886321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1886321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886321 prefixEnd_1886321 := by exact prefixLift 1886321
  have htrace : WordTrace (prefixWord ++ tailWord_1886321) baseStart_1886321 baseEnd_1886321 := by
    simpa [prefixWord, tailWord_1886321, baseEnd_1886321] using wordTrace_append hprefix tailTrace_1886321
  have hstable : (prefixWord ++ tailWord_1886321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886321).length < 2 ^ (prefixWord ++ tailWord_1886321).sum := by decide
  have hdescent : baseEnd_1886321 < baseStart_1886321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886368 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 3, 3]
def baseStart_1886368 : Nat := 118140960795 + 1886368 * 2 ^ 59
def prefixEnd_1886368 : Nat := 4983230072969 + 3 ^ 40 * 1886368 * 2
def baseEnd_1886368 : Nat := 645742316840387206816505

theorem tailTrace_1886368 : CollatzResearch.WordTrace tailWord_1886368 prefixEnd_1886368 645742316840387206816505 := by
  unfold tailWord_1886368
  simp only [CollatzResearch.WordTrace]
  refine ⟨34400746615009188425281879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45867662153345584567042505 34400746615009188425281879)
  ·
    refine ⟨51601119922513782637922819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34400746615009188425281879 51601119922513782637922819)
    ·
      refine ⟨77401679883770673956884229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51601119922513782637922819 77401679883770673956884229)
      ·
        refine ⟨14512814978207001366915793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77401679883770673956884229 14512814978207001366915793)
        ·
          refine ⟨10884611233655251025186845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14512814978207001366915793 10884611233655251025186845)
          ·
            refine ⟨4081729212620719134445067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10884611233655251025186845 4081729212620719134445067)
            ·
              refine ⟨6122593818931078701667601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081729212620719134445067 6122593818931078701667601)
              ·
                refine ⟨4591945364198309026250701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6122593818931078701667601 4591945364198309026250701)
                ·
                  refine ⟨1721979511574365884844013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4591945364198309026250701 1721979511574365884844013)
                  ·
                    refine ⟨645742316840387206816505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1721979511574365884844013 645742316840387206816505)
                    ·
                      rfl

theorem cell22_1886368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_1886368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886368 prefixEnd_1886368 := by exact prefixLift 1886368
  have htrace : WordTrace (prefixWord ++ tailWord_1886368) baseStart_1886368 baseEnd_1886368 := by
    simpa [prefixWord, tailWord_1886368, baseEnd_1886368] using wordTrace_append hprefix tailTrace_1886368
  have hstable : (prefixWord ++ tailWord_1886368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886368).length < 2 ^ (prefixWord ++ tailWord_1886368).sum := by decide
  have hdescent : baseEnd_1886368 < baseStart_1886368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886398 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1886398 : Nat := 118140960795 + 1886398 * 2 ^ 59
def prefixEnd_1886398 : Nat := 4983230072969 + 3 ^ 40 * 1886398 * 2
def baseEnd_1886398 : Nat := 215250862151159042855471

theorem tailTrace_1886398 : CollatzResearch.WordTrace tailWord_1886398 prefixEnd_1886398 215250862151159042855471 := by
  unfold tailWord_1886398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600323427488711496769481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45868391613273127982770565 8600323427488711496769481)
  ·
    refine ⟨6450242570616533622577111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8600323427488711496769481 6450242570616533622577111)
    ·
      refine ⟨9675363855924800433865667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450242570616533622577111 9675363855924800433865667)
      ·
        refine ⟨14513045783887200650798501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675363855924800433865667 14513045783887200650798501)
        ·
          refine ⟨2721196084478850122024719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14513045783887200650798501 2721196084478850122024719)
          ·
            refine ⟨4081794126718275183037079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721196084478850122024719 4081794126718275183037079)
            ·
              refine ⟨6122691190077412774555619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4081794126718275183037079 6122691190077412774555619)
              ·
                refine ⟨9184036785116119161833429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122691190077412774555619 9184036785116119161833429)
                ·
                  refine ⟨215250862151159042855471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9184036785116119161833429 215250862151159042855471)
                  ·
                    rfl

theorem cell22_1886398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1886398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886398 prefixEnd_1886398 := by exact prefixLift 1886398
  have htrace : WordTrace (prefixWord ++ tailWord_1886398) baseStart_1886398 baseEnd_1886398 := by
    simpa [prefixWord, tailWord_1886398, baseEnd_1886398] using wordTrace_append hprefix tailTrace_1886398
  have hstable : (prefixWord ++ tailWord_1886398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886398).length < 2 ^ (prefixWord ++ tailWord_1886398).sum := by decide
  have hdescent : baseEnd_1886398 < baseStart_1886398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886402 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1886402 : Nat := 118140960795 + 1886402 * 2 ^ 59
def prefixEnd_1886402 : Nat := 4983230072969 + 3 ^ 40 * 1886402 * 2
def baseEnd_1886402 : Nat := 645753955735222451466401

theorem tailTrace_1886402 : CollatzResearch.WordTrace tailWord_1886402 prefixEnd_1886402 645753955735222451466401 := by
  unfold tailWord_1886402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200683327973800164325365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45868488874596800438200973 17200683327973800164325365)
  ·
    refine ⟨1612564061997543765405503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17200683327973800164325365 1612564061997543765405503)
    ·
      refine ⟨2418846092996315648108255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612564061997543765405503 2418846092996315648108255)
      ·
        refine ⟨3628269139494473472162383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418846092996315648108255 3628269139494473472162383)
        ·
          refine ⟨5442403709241710208243575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628269139494473472162383 5442403709241710208243575)
          ·
            refine ⟨8163605563862565312365363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5442403709241710208243575 8163605563862565312365363)
            ·
              refine ⟨12245408345793847968548045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8163605563862565312365363 12245408345793847968548045)
              ·
                refine ⟨4592028129672692988205517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12245408345793847968548045 4592028129672692988205517)
                ·
                  refine ⟨1722010548627259870577069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4592028129672692988205517 1722010548627259870577069)
                  ·
                    refine ⟨645753955735222451466401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1722010548627259870577069 645753955735222451466401)
                    ·
                      rfl

theorem cell22_1886402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1886402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886402 prefixEnd_1886402 := by exact prefixLift 1886402
  have htrace : WordTrace (prefixWord ++ tailWord_1886402) baseStart_1886402 baseEnd_1886402 := by
    simpa [prefixWord, tailWord_1886402, baseEnd_1886402] using wordTrace_append hprefix tailTrace_1886402
  have hstable : (prefixWord ++ tailWord_1886402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886402).length < 2 ^ (prefixWord ++ tailWord_1886402).sum := by decide
  have hdescent : baseEnd_1886402 < baseStart_1886402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886426 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_1886426 : Nat := 118140960795 + 1886426 * 2 ^ 59
def prefixEnd_1886426 : Nat := 4983230072969 + 3 ^ 40 * 1886426 * 2
def baseEnd_1886426 : Nat := 215254057141898129622109

theorem tailTrace_1886426 : CollatzResearch.WordTrace tailWord_1886426 prefixEnd_1886426 215254057141898129622109 := by
  unfold tailWord_1886426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200902165952063189043783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45869072442538835170783421 17200902165952063189043783)
  ·
    refine ⟨25801353248928094783565675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17200902165952063189043783 25801353248928094783565675)
    ·
      refine ⟨38702029873392142175348513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25801353248928094783565675 38702029873392142175348513)
      ·
        refine ⟨29026522405044106631511385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38702029873392142175348513 29026522405044106631511385)
        ·
          refine ⟨21769891803783079973633539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29026522405044106631511385 21769891803783079973633539)
          ·
            refine ⟨32654837705674619960450309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21769891803783079973633539 32654837705674619960450309)
            ·
              refine ⟨6122782069813991242584433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32654837705674619960450309 6122782069813991242584433)
              ·
                refine ⟨4592086552360493431938325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6122782069813991242584433 4592086552360493431938325)
                ·
                  refine ⟨215254057141898129622109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4592086552360493431938325 215254057141898129622109)
                  ·
                    rfl

theorem cell22_1886426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_1886426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886426 prefixEnd_1886426 := by exact prefixLift 1886426
  have htrace : WordTrace (prefixWord ++ tailWord_1886426) baseStart_1886426 baseEnd_1886426 := by
    simpa [prefixWord, tailWord_1886426, baseEnd_1886426] using wordTrace_append hprefix tailTrace_1886426
  have hstable : (prefixWord ++ tailWord_1886426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886426).length < 2 ^ (prefixWord ++ tailWord_1886426).sum := by decide
  have hdescent : baseEnd_1886426 < baseStart_1886426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886458 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_1886458 : Nat := 118140960795 + 1886458 * 2 ^ 59
def prefixEnd_1886458 : Nat := 4983230072969 + 3 ^ 40 * 1886458 * 2
def baseEnd_1886458 : Nat := 645773125679656972066229

theorem tailTrace_1886458 : CollatzResearch.WordTrace tailWord_1886458 prefixEnd_1886458 645773125679656972066229 := by
  unfold tailWord_1886458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201193949923080555335007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45869850533128214814226685 17201193949923080555335007)
  ·
    refine ⟨25801790924884620833002511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17201193949923080555335007 25801790924884620833002511)
    ·
      refine ⟨38702686387326931249503767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25801790924884620833002511 38702686387326931249503767)
      ·
        refine ⟨58054029580990396874255651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38702686387326931249503767 58054029580990396874255651)
        ·
          refine ⟨87081044371485595311383477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58054029580990396874255651 87081044371485595311383477)
          ·
            refine ⟨8163847909826774560442201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87081044371485595311383477 8163847909826774560442201)
            ·
              refine ⟨6122885932370080920331651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8163847909826774560442201 6122885932370080920331651)
              ·
                refine ⟨9184328898555121380497477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6122885932370080920331651 9184328898555121380497477)
                ·
                  refine ⟨1722061668479085258843277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9184328898555121380497477 1722061668479085258843277)
                  ·
                    refine ⟨645773125679656972066229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1722061668479085258843277 645773125679656972066229)
                    ·
                      rfl

theorem cell22_1886458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_1886458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886458 prefixEnd_1886458 := by exact prefixLift 1886458
  have htrace : WordTrace (prefixWord ++ tailWord_1886458) baseStart_1886458 baseEnd_1886458 := by
    simpa [prefixWord, tailWord_1886458, baseEnd_1886458] using wordTrace_append hprefix tailTrace_1886458
  have hstable : (prefixWord ++ tailWord_1886458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886458).length < 2 ^ (prefixWord ++ tailWord_1886458).sum := by decide
  have hdescent : baseEnd_1886458 < baseStart_1886458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886490 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1886490 : Nat := 118140960795 + 1886490 * 2 ^ 59
def prefixEnd_1886490 : Nat := 4983230072969 + 3 ^ 40 * 1886490 * 2
def baseEnd_1886490 : Nat := 645784079933619555266131

theorem tailTrace_1886490 : CollatzResearch.WordTrace tailWord_1886490 prefixEnd_1886490 645784079933619555266131 := by
  unfold tailWord_1886490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201485733894097921626231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45870628623717594457669949 17201485733894097921626231)
  ·
    refine ⟨25802228600841146882439347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17201485733894097921626231 25802228600841146882439347)
    ·
      refine ⟨38703342901261720323659021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25802228600841146882439347 38703342901261720323659021)
      ·
        refine ⟨14513753587973145121372133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38703342901261720323659021 14513753587973145121372133)
        ·
          refine ⟨2721328797744964710257275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14513753587973145121372133 2721328797744964710257275)
          ·
            refine ⟨4081993196617447065385913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721328797744964710257275 4081993196617447065385913)
            ·
              refine ⟨3061494897463085299039435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081993196617447065385913 3061494897463085299039435)
              ·
                refine ⟨4592242346194627948559153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061494897463085299039435 4592242346194627948559153)
                ·
                  refine ⟨3444181759645970961419365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592242346194627948559153 3444181759645970961419365)
                  ·
                    refine ⟨645784079933619555266131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3444181759645970961419365 645784079933619555266131)
                    ·
                      rfl

theorem cell22_1886490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1886490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886490 prefixEnd_1886490 := by exact prefixLift 1886490
  have htrace : WordTrace (prefixWord ++ tailWord_1886490) baseStart_1886490 baseEnd_1886490 := by
    simpa [prefixWord, tailWord_1886490, baseEnd_1886490] using wordTrace_append hprefix tailTrace_1886490
  have hstable : (prefixWord ++ tailWord_1886490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886490).length < 2 ^ (prefixWord ++ tailWord_1886490).sum := by decide
  have hdescent : baseEnd_1886490 < baseStart_1886490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886509 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1886509 : Nat := 118140960795 + 1886509 * 2 ^ 59
def prefixEnd_1886509 : Nat := 4983230072969 + 3 ^ 40 * 1886509 * 2
def baseEnd_1886509 : Nat := 645790584021909839041073

theorem tailTrace_1886509 : CollatzResearch.WordTrace tailWord_1886509 prefixEnd_1886509 645790584021909839041073 := by
  unfold tailWord_1886509
  simp only [CollatzResearch.WordTrace]
  refine ⟨68806635922507557931446581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45871090615005038620964387 68806635922507557931446581)
  ·
    refine ⟨6450622117735083556073117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68806635922507557931446581 6450622117735083556073117)
    ·
      refine ⟨2418983294150656333527419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6450622117735083556073117 2418983294150656333527419)
      ·
        refine ⟨3628474941225984500291129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2418983294150656333527419 3628474941225984500291129)
        ·
          refine ⟨2721356205919488375218347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3628474941225984500291129 2721356205919488375218347)
          ·
            refine ⟨4082034308879232562827521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721356205919488375218347 4082034308879232562827521)
            ·
              refine ⟨3061525731659424422120641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082034308879232562827521 3061525731659424422120641)
              ·
                refine ⟨2296144298744568316590481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3061525731659424422120641 2296144298744568316590481)
                ·
                  refine ⟨1722108224058426237442861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2296144298744568316590481 1722108224058426237442861)
                  ·
                    refine ⟨645790584021909839041073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1722108224058426237442861 645790584021909839041073)
                    ·
                      rfl

theorem cell22_1886509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1886509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886509 prefixEnd_1886509 := by exact prefixLift 1886509
  have htrace : WordTrace (prefixWord ++ tailWord_1886509) baseStart_1886509 baseEnd_1886509 := by
    simpa [prefixWord, tailWord_1886509, baseEnd_1886509] using wordTrace_append hprefix tailTrace_1886509
  have hstable : (prefixWord ++ tailWord_1886509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886509).length < 2 ^ (prefixWord ++ tailWord_1886509).sum := by decide
  have hdescent : baseEnd_1886509 < baseStart_1886509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886531 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 1, 7]
def baseStart_1886531 : Nat := 118140960795 + 1886531 * 2 ^ 59
def prefixEnd_1886531 : Nat := 4983230072969 + 3 ^ 40 * 1886531 * 2
def baseEnd_1886531 : Nat := 645798115071509114991005

theorem tailTrace_1886531 : CollatzResearch.WordTrace tailWord_1886531 prefixEnd_1886531 645798115071509114991005 := by
  unfold tailWord_1886531
  simp only [CollatzResearch.WordTrace]
  refine ⟨68807438328427855688747447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45871625552285237125831631 68807438328427855688747447)
  ·
    refine ⟨103211157492641783533121171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68807438328427855688747447 103211157492641783533121171)
    ·
      refine ⟨154816736238962675299681757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103211157492641783533121171 154816736238962675299681757)
      ·
        refine ⟨58056276089611003237380659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154816736238962675299681757 58056276089611003237380659)
        ·
          refine ⟨87084414134416504856070989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58056276089611003237380659 87084414134416504856070989)
          ·
            refine ⟨32656655300406189321026621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87084414134416504856070989 32656655300406189321026621)
            ·
              refine ⟨12246245737652320995384983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32656655300406189321026621 12246245737652320995384983)
              ·
                refine ⟨18369368606478481493077475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12246245737652320995384983 18369368606478481493077475)
                ·
                  refine ⟨27554052909717722239616213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18369368606478481493077475 27554052909717722239616213)
                  ·
                    refine ⟨645798115071509114991005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27554052909717722239616213 645798115071509114991005)
                    ·
                      rfl

theorem cell22_1886531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_1886531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886531 prefixEnd_1886531 := by exact prefixLift 1886531
  have htrace : WordTrace (prefixWord ++ tailWord_1886531) baseStart_1886531 baseEnd_1886531 := by
    simpa [prefixWord, tailWord_1886531, baseEnd_1886531] using wordTrace_append hprefix tailTrace_1886531
  have hstable : (prefixWord ++ tailWord_1886531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886531).length < 2 ^ (prefixWord ++ tailWord_1886531).sum := by decide
  have hdescent : baseEnd_1886531 < baseStart_1886531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886578 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1886578 : Nat := 118140960795 + 1886578 * 2 ^ 59
def prefixEnd_1886578 : Nat := 4983230072969 + 3 ^ 40 * 1886578 * 2
def baseEnd_1886578 : Nat := 215271401377338886355287

theorem tailTrace_1886578 : CollatzResearch.WordTrace tailWord_1886578 prefixEnd_1886578 215271401377338886355287 := by
  unfold tailWord_1886578
  simp only [CollatzResearch.WordTrace]
  refine ⟨17202288139814395678927097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45872768372838388477138925 17202288139814395678927097)
  ·
    refine ⟨12901716104860796759195323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17202288139814395678927097 12901716104860796759195323)
    ·
      refine ⟨19352574157291195138792985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12901716104860796759195323 19352574157291195138792985)
      ·
        refine ⟨14514430617968396354094739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19352574157291195138792985 14514430617968396354094739)
        ·
          refine ⟨21771645926952594531142109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14514430617968396354094739 21771645926952594531142109)
          ·
            refine ⟨8164367222607222949178291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21771645926952594531142109 8164367222607222949178291)
            ·
              refine ⟨12246550833910834423767437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8164367222607222949178291 12246550833910834423767437)
              ·
                refine ⟨4592456562716562908912789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12246550833910834423767437 4592456562716562908912789)
                ·
                  refine ⟨215271401377338886355287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4592456562716562908912789 215271401377338886355287)
                  ·
                    rfl

theorem cell22_1886578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1886578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886578 prefixEnd_1886578 := by exact prefixLift 1886578
  have htrace : WordTrace (prefixWord ++ tailWord_1886578) baseStart_1886578 baseEnd_1886578 := by
    simpa [prefixWord, tailWord_1886578, baseEnd_1886578] using wordTrace_append hprefix tailTrace_1886578
  have hstable : (prefixWord ++ tailWord_1886578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886578).length < 2 ^ (prefixWord ++ tailWord_1886578).sum := by decide
  have hdescent : baseEnd_1886578 < baseStart_1886578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886713 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 8]
def baseStart_1886713 : Nat := 118140960795 + 1886713 * 2 ^ 59
def prefixEnd_1886713 : Nat := 4983230072969 + 3 ^ 40 * 1886713 * 2
def baseEnd_1886713 : Nat := 215286805796973768980149

theorem tailTrace_1886713 : CollatzResearch.WordTrace tailWord_1886713 prefixEnd_1886713 215286805796973768980149 := by
  unfold tailWord_1886713
  simp only [CollatzResearch.WordTrace]
  refine ⟨68814076413768500771872793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45876050942512333847915195 68814076413768500771872793)
  ·
    refine ⟨51610557310326375578904595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68814076413768500771872793 51610557310326375578904595)
    ·
      refine ⟨77415835965489563368356893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51610557310326375578904595 77415835965489563368356893)
      ·
        refine ⟨29030938487058586263133835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77415835965489563368356893 29030938487058586263133835)
        ·
          refine ⟨43546407730587879394700753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29030938487058586263133835 43546407730587879394700753)
          ·
            refine ⟨32659805797940909546025565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43546407730587879394700753 32659805797940909546025565)
            ·
              refine ⟨12247427174227841079759587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32659805797940909546025565 12247427174227841079759587)
              ·
                refine ⟨18371140761341761619639381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12247427174227841079759587 18371140761341761619639381)
                ·
                  refine ⟨215286805796973768980149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18371140761341761619639381 215286805796973768980149)
                  ·
                    rfl

theorem cell22_1886713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_1886713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886713 prefixEnd_1886713 := by exact prefixLift 1886713
  have htrace : WordTrace (prefixWord ++ tailWord_1886713) baseStart_1886713 baseEnd_1886713 := by
    simpa [prefixWord, tailWord_1886713, baseEnd_1886713] using wordTrace_append hprefix tailTrace_1886713
  have hstable : (prefixWord ++ tailWord_1886713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886713).length < 2 ^ (prefixWord ++ tailWord_1886713).sum := by decide
  have hdescent : baseEnd_1886713 < baseStart_1886713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886732 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_1886732 : Nat := 118140960795 + 1886732 * 2 ^ 59
def prefixEnd_1886732 : Nat := 4983230072969 + 3 ^ 40 * 1886732 * 2
def baseEnd_1886732 : Nat := 645866921479211590715389

theorem tailTrace_1886732 : CollatzResearch.WordTrace tailWord_1886732 prefixEnd_1886732 645866921479211590715389 := by
  unfold tailWord_1886732
  simp only [CollatzResearch.WordTrace]
  refine ⟨34407384700349833508407225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45876512933799778011209633 34407384700349833508407225)
  ·
    refine ⟨25805538525262375131305419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34407384700349833508407225 25805538525262375131305419)
    ·
      refine ⟨38708307787893562696958129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25805538525262375131305419 38708307787893562696958129)
      ·
        refine ⟨29031230840920172022718597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38708307787893562696958129 29031230840920172022718597)
        ·
          refine ⟨5443355782672532254259737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29031230840920172022718597 5443355782672532254259737)
          ·
            refine ⟨4082516837004399190694803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5443355782672532254259737 4082516837004399190694803)
            ·
              refine ⟨6123775255506598786042205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082516837004399190694803 6123775255506598786042205)
              ·
                refine ⟨2296415720814974544765827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6123775255506598786042205 2296415720814974544765827)
                ·
                  refine ⟨3444623581222461817148741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296415720814974544765827 3444623581222461817148741)
                  ·
                    refine ⟨645866921479211590715389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3444623581222461817148741 645866921479211590715389)
                    ·
                      rfl

theorem cell22_1886732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_1886732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886732 prefixEnd_1886732 := by exact prefixLift 1886732
  have htrace : WordTrace (prefixWord ++ tailWord_1886732) baseStart_1886732 baseEnd_1886732 := by
    simpa [prefixWord, tailWord_1886732, baseEnd_1886732] using wordTrace_append hprefix tailTrace_1886732
  have hstable : (prefixWord ++ tailWord_1886732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886732).length < 2 ^ (prefixWord ++ tailWord_1886732).sum := by decide
  have hdescent : baseEnd_1886732 < baseStart_1886732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886745 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 4, 3]
def baseStart_1886745 : Nat := 118140960795 + 1886745 * 2 ^ 59
def prefixEnd_1886745 : Nat := 4983230072969 + 3 ^ 40 * 1886745 * 2
def baseEnd_1886745 : Nat := 645871371644883890140349

theorem tailTrace_1886745 : CollatzResearch.WordTrace tailWord_1886745 prefixEnd_1886745 645871371644883890140349 := by
  unfold tailWord_1886745
  simp only [CollatzResearch.WordTrace]
  refine ⟨68815243549652570237037689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45876829033101713491358459 68815243549652570237037689)
  ·
    refine ⟨51611432662239427677778267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68815243549652570237037689 51611432662239427677778267)
    ·
      refine ⟨77417148993359141516667401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51611432662239427677778267 77417148993359141516667401)
      ·
        refine ⟨58062861745019356137500551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77417148993359141516667401 58062861745019356137500551)
        ·
          refine ⟨87094292617529034206250827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58062861745019356137500551 87094292617529034206250827)
          ·
            refine ⟨130641438926293551309376241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87094292617529034206250827 130641438926293551309376241)
            ·
              refine ⟨97981079194720163482032181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130641438926293551309376241 97981079194720163482032181)
              ·
                refine ⟨9185726174505015326440517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97981079194720163482032181 9185726174505015326440517)
                ·
                  refine ⟨1722323657719690373707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9185726174505015326440517 1722323657719690373707597)
                  ·
                    refine ⟨645871371644883890140349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1722323657719690373707597 645871371644883890140349)
                    ·
                      rfl

theorem cell22_1886745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_1886745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886745 prefixEnd_1886745 := by exact prefixLift 1886745
  have htrace : WordTrace (prefixWord ++ tailWord_1886745) baseStart_1886745 baseEnd_1886745 := by
    simpa [prefixWord, tailWord_1886745, baseEnd_1886745] using wordTrace_append hprefix tailTrace_1886745
  have hstable : (prefixWord ++ tailWord_1886745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886745).length < 2 ^ (prefixWord ++ tailWord_1886745).sum := by decide
  have hdescent : baseEnd_1886745 < baseStart_1886745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886762 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1886762 : Nat := 118140960795 + 1886762 * 2 ^ 59
def prefixEnd_1886762 : Nat := 4983230072969 + 3 ^ 40 * 1886762 * 2
def baseEnd_1886762 : Nat := 645877191092301512465297

theorem tailTrace_1886762 : CollatzResearch.WordTrace tailWord_1886762 prefixEnd_1886762 645877191092301512465297 := by
  unfold tailWord_1886762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17203965897647745535101635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45877242393727321426937693 17203965897647745535101635)
  ·
    refine ⟨25805948846471618302652453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17203965897647745535101635 25805948846471618302652453)
    ·
      refine ⟨4838615408713428431747335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25805948846471618302652453 4838615408713428431747335)
      ·
        refine ⟨7257923113070142647621003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4838615408713428431747335 7257923113070142647621003)
        ·
          refine ⟨10886884669605213971431505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7257923113070142647621003 10886884669605213971431505)
          ·
            refine ⟨8165163502203910478573629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10886884669605213971431505 8165163502203910478573629)
            ·
              refine ⟨3061936313326466429465111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8165163502203910478573629 3061936313326466429465111)
              ·
                refine ⟨4592904469989699644197667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061936313326466429465111 4592904469989699644197667)
                ·
                  refine ⟨6889356704984549466296501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592904469989699644197667 6889356704984549466296501)
                  ·
                    refine ⟨645877191092301512465297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6889356704984549466296501 645877191092301512465297)
                    ·
                      rfl

theorem cell22_1886762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1886762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886762 prefixEnd_1886762 := by exact prefixLift 1886762
  have htrace : WordTrace (prefixWord ++ tailWord_1886762) baseStart_1886762 baseEnd_1886762 := by
    simpa [prefixWord, tailWord_1886762, baseEnd_1886762] using wordTrace_append hprefix tailTrace_1886762
  have hstable : (prefixWord ++ tailWord_1886762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886762).length < 2 ^ (prefixWord ++ tailWord_1886762).sum := by decide
  have hdescent : baseEnd_1886762 < baseStart_1886762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886899 : List Nat := [1, 1, 1, 2, 3, 5, 2, 3, 4]
def baseStart_1886899 : Nat := 118140960795 + 1886899 * 2 ^ 59
def prefixEnd_1886899 : Nat := 4983230072969 + 3 ^ 40 * 1886899 * 2
def baseEnd_1886899 : Nat := 215308029664026273929959

theorem tailTrace_1886899 : CollatzResearch.WordTrace tailWord_1886899 prefixEnd_1886899 215308029664026273929959 := by
  unfold tailWord_1886899
  simp only [CollatzResearch.WordTrace]
  refine ⟨68820860391094654538143751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45880573594063103025429167 68820860391094654538143751)
  ·
    refine ⟨103231290586641981807215627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68820860391094654538143751 103231290586641981807215627)
    ·
      refine ⟨154846935879962972710823441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103231290586641981807215627 154846935879962972710823441)
      ·
        refine ⟨116135201909972229533117581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154846935879962972710823441 116135201909972229533117581)
        ·
          refine ⟨43550700716239586074919093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116135201909972229533117581 43550700716239586074919093)
          ·
            refine ⟨4082878192147461194523665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43550700716239586074919093 4082878192147461194523665)
            ·
              refine ⟨3062158644110595895892749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082878192147461194523665 3062158644110595895892749)
              ·
                refine ⟨1148309491541473460959781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3062158644110595895892749 1148309491541473460959781)
                ·
                  refine ⟨215308029664026273929959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1148309491541473460959781 215308029664026273929959)
                  ·
                    rfl

theorem cell22_1886899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 4].length) (baseStart_1886899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886899 prefixEnd_1886899 := by exact prefixLift 1886899
  have htrace : WordTrace (prefixWord ++ tailWord_1886899) baseStart_1886899 baseEnd_1886899 := by
    simpa [prefixWord, tailWord_1886899, baseEnd_1886899] using wordTrace_append hprefix tailTrace_1886899
  have hstable : (prefixWord ++ tailWord_1886899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886899).length < 2 ^ (prefixWord ++ tailWord_1886899).sum := by decide
  have hdescent : baseEnd_1886899 < baseStart_1886899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886901 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_1886901 : Nat := 118140960795 + 1886901 * 2 ^ 59
def prefixEnd_1886901 : Nat := 4983230072969 + 3 ^ 40 * 1886901 * 2
def baseEnd_1886901 : Nat := 645924773632951483239871

theorem tailTrace_1886901 : CollatzResearch.WordTrace tailWord_1886901 prefixEnd_1886901 645924773632951483239871 := by
  unfold tailWord_1886901
  simp only [CollatzResearch.WordTrace]
  refine ⟨68820933337087408879716557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45880622224724939253144371 68820933337087408879716557)
  ·
    refine ⟨25807850001407778329893709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68820933337087408879716557 25807850001407778329893709)
    ·
      refine ⟨9677943750527916873710141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25807850001407778329893709 9677943750527916873710141)
      ·
        refine ⟨3629228906447968827641303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9677943750527916873710141 3629228906447968827641303)
        ·
          refine ⟨5443843359671953241461955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3629228906447968827641303 5443843359671953241461955)
          ·
            refine ⟨8165765039507929862192933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443843359671953241461955 8165765039507929862192933)
            ·
              refine ⟨1531080944907736849161175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8165765039507929862192933 1531080944907736849161175)
              ·
                refine ⟨2296621417361605273741763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531080944907736849161175 2296621417361605273741763)
                ·
                  refine ⟨3444932126042407910612645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296621417361605273741763 3444932126042407910612645)
                  ·
                    refine ⟨645924773632951483239871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3444932126042407910612645 645924773632951483239871)
                    ·
                      rfl

theorem cell22_1886901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_1886901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886901 prefixEnd_1886901 := by exact prefixLift 1886901
  have htrace : WordTrace (prefixWord ++ tailWord_1886901) baseStart_1886901 baseEnd_1886901 := by
    simpa [prefixWord, tailWord_1886901, baseEnd_1886901] using wordTrace_append hprefix tailTrace_1886901
  have hstable : (prefixWord ++ tailWord_1886901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886901).length < 2 ^ (prefixWord ++ tailWord_1886901).sum := by decide
  have hdescent : baseEnd_1886901 < baseStart_1886901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1886972 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 7]
def baseStart_1886972 : Nat := 118140960795 + 1886972 * 2 ^ 59
def prefixEnd_1886972 : Nat := 4983230072969 + 3 ^ 40 * 1886972 * 2
def baseEnd_1886972 : Nat := 215316359461310321571551

theorem tailTrace_1886972 : CollatzResearch.WordTrace tailWord_1886972 prefixEnd_1886972 215316359461310321571551 := by
  unfold tailWord_1886972
  simp only [CollatzResearch.WordTrace]
  refine ⟨34411761459915094002775585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45882348613220125337034113 34411761459915094002775585)
  ·
    refine ⟨25808821094936320502081689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34411761459915094002775585 25808821094936320502081689)
    ·
      refine ⟨19356615821202240376561267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25808821094936320502081689 19356615821202240376561267)
      ·
        refine ⟨29034923731803360564841901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19356615821202240376561267 29034923731803360564841901)
        ·
          refine ⟨10888096399426260211815713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29034923731803360564841901 10888096399426260211815713)
          ·
            refine ⟨8166072299569695158861785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10888096399426260211815713 8166072299569695158861785)
            ·
              refine ⟨6124554224677271369146339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8166072299569695158861785 6124554224677271369146339)
              ·
                refine ⟨9186831337015907053719509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6124554224677271369146339 9186831337015907053719509)
                ·
                  refine ⟨215316359461310321571551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9186831337015907053719509 215316359461310321571551)
                  ·
                    rfl

theorem cell22_1886972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_1886972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1886972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1886972 prefixEnd_1886972 := by exact prefixLift 1886972
  have htrace : WordTrace (prefixWord ++ tailWord_1886972) baseStart_1886972 baseEnd_1886972 := by
    simpa [prefixWord, tailWord_1886972, baseEnd_1886972] using wordTrace_append hprefix tailTrace_1886972
  have hstable : (prefixWord ++ tailWord_1886972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1886972).length < 2 ^ (prefixWord ++ tailWord_1886972).sum := by decide
  have hdescent : baseEnd_1886972 < baseStart_1886972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1886972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887032 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_1887032 : Nat := 118140960795 + 1887032 * 2 ^ 59
def prefixEnd_1887032 : Nat := 4983230072969 + 3 ^ 40 * 1887032 * 2
def baseEnd_1887032 : Nat := 645969617610110808214469

theorem tailTrace_1887032 : CollatzResearch.WordTrace tailWord_1887032 prefixEnd_1887032 645969617610110808214469 := by
  unfold tailWord_1887032
  simp only [CollatzResearch.WordTrace]
  refine ⟨34412855649806409126367675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45883807533075212168490233 34412855649806409126367675)
  ·
    refine ⟨51619283474709613689551513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34412855649806409126367675 51619283474709613689551513)
    ·
      refine ⟨38714462606032210267163635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51619283474709613689551513 38714462606032210267163635)
      ·
        refine ⟨58071693909048315400745453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38714462606032210267163635 58071693909048315400745453)
        ·
          refine ⟨21776885215893118275279545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58071693909048315400745453 21776885215893118275279545)
          ·
            refine ⟨16332663911919838706459659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21776885215893118275279545 16332663911919838706459659)
            ·
              refine ⟨24498995867879758059689489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16332663911919838706459659 24498995867879758059689489)
              ·
                refine ⟨18374246900909818544767117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24498995867879758059689489 18374246900909818544767117)
                ·
                  refine ⟨6890342587841181954287669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18374246900909818544767117 6890342587841181954287669)
                  ·
                    refine ⟨645969617610110808214469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6890342587841181954287669 645969617610110808214469)
                    ·
                      rfl

theorem cell22_1887032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_1887032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887032 prefixEnd_1887032 := by exact prefixLift 1887032
  have htrace : WordTrace (prefixWord ++ tailWord_1887032) baseStart_1887032 baseEnd_1887032 := by
    simpa [prefixWord, tailWord_1887032, baseEnd_1887032] using wordTrace_append hprefix tailTrace_1887032
  have hstable : (prefixWord ++ tailWord_1887032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887032).length < 2 ^ (prefixWord ++ tailWord_1887032).sum := by decide
  have hdescent : baseEnd_1887032 < baseStart_1887032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887047 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1887047 : Nat := 118140960795 + 1887047 * 2 ^ 59
def prefixEnd_1887047 : Nat := 4983230072969 + 3 ^ 40 * 1887047 * 2
def baseEnd_1887047 : Nat := 645974752416655769089423

theorem tailTrace_1887047 : CollatzResearch.WordTrace tailWord_1887047 prefixEnd_1887047 645974752416655769089423 := by
  unfold tailWord_1887047
  simp only [CollatzResearch.WordTrace]
  refine ⟨68826258394558475814531395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45884172263038983876354263 68826258394558475814531395)
  ·
    refine ⟨103239387591837713721797093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68826258394558475814531395 103239387591837713721797093)
    ·
      refine ⟨19357385173469571322836955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103239387591837713721797093 19357385173469571322836955)
      ·
        refine ⟨29036077760204356984255433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19357385173469571322836955 29036077760204356984255433)
        ·
          refine ⟨21777058320153267738191575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29036077760204356984255433 21777058320153267738191575)
          ·
            refine ⟨32665587480229901607287363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21777058320153267738191575 32665587480229901607287363)
            ·
              refine ⟨48998381220344852410931045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32665587480229901607287363 48998381220344852410931045)
              ·
                refine ⟨9187196478814659827049571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48998381220344852410931045 9187196478814659827049571)
                ·
                  refine ⟨13780794718221989740574357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9187196478814659827049571 13780794718221989740574357)
                  ·
                    refine ⟨645974752416655769089423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13780794718221989740574357 645974752416655769089423)
                    ·
                      rfl

theorem cell22_1887047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1887047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887047 prefixEnd_1887047 := by exact prefixLift 1887047
  have htrace : WordTrace (prefixWord ++ tailWord_1887047) baseStart_1887047 baseEnd_1887047 := by
    simpa [prefixWord, tailWord_1887047, baseEnd_1887047] using wordTrace_append hprefix tailTrace_1887047
  have hstable : (prefixWord ++ tailWord_1887047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887047).length < 2 ^ (prefixWord ++ tailWord_1887047).sum := by decide
  have hdescent : baseEnd_1887047 < baseStart_1887047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887049 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_1887049 : Nat := 118140960795 + 1887049 * 2 ^ 59
def prefixEnd_1887049 : Nat := 4983230072969 + 3 ^ 40 * 1887049 * 2
def baseEnd_1887049 : Nat := 645975437057528430539417

theorem tailTrace_1887049 : CollatzResearch.WordTrace tailWord_1887049 prefixEnd_1887049 645975437057528430539417 := by
  unfold tailWord_1887049
  simp only [CollatzResearch.WordTrace]
  refine ⟨68826331340551230156104201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45884220893700820104069467 68826331340551230156104201)
  ·
    refine ⟨51619748505413422617078151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68826331340551230156104201 51619748505413422617078151)
    ·
      refine ⟨77429622758120133925617227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51619748505413422617078151 77429622758120133925617227)
      ·
        refine ⟨116144434137180200888425841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77429622758120133925617227 116144434137180200888425841)
        ·
          refine ⟨87108325602885150666319381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116144434137180200888425841 87108325602885150666319381)
          ·
            refine ⟨4083202762635241437483721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87108325602885150666319381 4083202762635241437483721)
            ·
              refine ⟨3062402071976431078112791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083202762635241437483721 3062402071976431078112791)
              ·
                refine ⟨4593603107964646617169187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062402071976431078112791 4593603107964646617169187)
                ·
                  refine ⟨6890404661946969925753781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593603107964646617169187 6890404661946969925753781)
                  ·
                    refine ⟨645975437057528430539417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6890404661946969925753781 645975437057528430539417)
                    ·
                      rfl

theorem cell22_1887049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_1887049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887049 prefixEnd_1887049 := by exact prefixLift 1887049
  have htrace : WordTrace (prefixWord ++ tailWord_1887049) baseStart_1887049 baseEnd_1887049 := by
    simpa [prefixWord, tailWord_1887049, baseEnd_1887049] using wordTrace_append hprefix tailTrace_1887049
  have hstable : (prefixWord ++ tailWord_1887049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887049).length < 2 ^ (prefixWord ++ tailWord_1887049).sum := by decide
  have hdescent : baseEnd_1887049 < baseStart_1887049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887068 : List Nat := [2, 2, 4, 2, 1, 2, 2, 3, 4]
def baseStart_1887068 : Nat := 118140960795 + 1887068 * 2 ^ 59
def prefixEnd_1887068 : Nat := 4983230072969 + 3 ^ 40 * 1887068 * 2
def baseEnd_1887068 : Nat := 215327313715272904771453

theorem tailTrace_1887068 : CollatzResearch.WordTrace tailWord_1887068 prefixEnd_1887068 215327313715272904771453 := by
  unfold tailWord_1887068
  simp only [CollatzResearch.WordTrace]
  refine ⟨34413512163741198200522929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45884682884988264267363905 34413512163741198200522929)
  ·
    refine ⟨25810134122805898650392197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34413512163741198200522929 25810134122805898650392197)
    ·
      refine ⟨4839400148026105996948537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25810134122805898650392197 4839400148026105996948537)
      ·
        refine ⟨3629550111019579497711403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4839400148026105996948537 3629550111019579497711403)
        ·
          refine ⟨5444325166529369246567105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3629550111019579497711403 5444325166529369246567105)
          ·
            refine ⟨4083243874897026934925329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5444325166529369246567105 4083243874897026934925329)
            ·
              refine ⟨3062432906172770201193997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083243874897026934925329 3062432906172770201193997)
              ·
                refine ⟨1148412339814788825447749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3062432906172770201193997 1148412339814788825447749)
                ·
                  refine ⟨215327313715272904771453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1148412339814788825447749 215327313715272904771453)
                  ·
                    rfl

theorem cell22_1887068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_1887068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887068 prefixEnd_1887068 := by exact prefixLift 1887068
  have htrace : WordTrace (prefixWord ++ tailWord_1887068) baseStart_1887068 baseEnd_1887068 := by
    simpa [prefixWord, tailWord_1887068, baseEnd_1887068] using wordTrace_append hprefix tailTrace_1887068
  have hstable : (prefixWord ++ tailWord_1887068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887068).length < 2 ^ (prefixWord ++ tailWord_1887068).sum := by decide
  have hdescent : baseEnd_1887068 < baseStart_1887068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887111 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1887111 : Nat := 118140960795 + 1887111 * 2 ^ 59
def prefixEnd_1887111 : Nat := 4983230072969 + 3 ^ 40 * 1887111 * 2
def baseEnd_1887111 : Nat := 645996660924580935489227

theorem tailTrace_1887111 : CollatzResearch.WordTrace tailWord_1887111 prefixEnd_1887111 645996660924580935489227 := by
  unfold tailWord_1887111
  simp only [CollatzResearch.WordTrace]
  refine ⟨68828592666326614744861187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45885728444217743163240791 68828592666326614744861187)
  ·
    refine ⟨103242888999489922117291781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68828592666326614744861187 103242888999489922117291781)
    ·
      refine ⟨19358041687404360396992209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103242888999489922117291781 19358041687404360396992209)
      ·
        refine ⟨14518531265553270297744157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19358041687404360396992209 14518531265553270297744157)
        ·
          refine ⟨5444449224582476361654059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14518531265553270297744157 5444449224582476361654059)
          ·
            refine ⟨8166673836873714542481089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5444449224582476361654059 8166673836873714542481089)
            ·
              refine ⟨6125005377655285906860817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8166673836873714542481089 6125005377655285906860817)
              ·
                refine ⟨4593754033241464430145613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125005377655285906860817 4593754033241464430145613)
                ·
                  refine ⟨1722657762465549161304605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4593754033241464430145613 1722657762465549161304605)
                  ·
                    refine ⟨645996660924580935489227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1722657762465549161304605 645996660924580935489227)
                    ·
                      rfl

theorem cell22_1887111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1887111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887111 prefixEnd_1887111 := by exact prefixLift 1887111
  have htrace : WordTrace (prefixWord ++ tailWord_1887111) baseStart_1887111 baseEnd_1887111 := by
    simpa [prefixWord, tailWord_1887111, baseEnd_1887111] using wordTrace_append hprefix tailTrace_1887111
  have hstable : (prefixWord ++ tailWord_1887111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887111).length < 2 ^ (prefixWord ++ tailWord_1887111).sum := by decide
  have hdescent : baseEnd_1887111 < baseStart_1887111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887124 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 9]
def baseStart_1887124 : Nat := 118140960795 + 1887124 * 2 ^ 59
def prefixEnd_1887124 : Nat := 4983230072969 + 3 ^ 40 * 1887124 * 2
def baseEnd_1887124 : Nat := 215333703696751078304729

theorem tailTrace_1887124 : CollatzResearch.WordTrace tailWord_1887124 prefixEnd_1887124 215333703696751078304729 := by
  unfold tailWord_1887124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34414533407639758982542213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45886044543519678643389617 34414533407639758982542213)
  ·
    refine ⟨6452725013932454809226665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34414533407639758982542213 6452725013932454809226665)
    ·
      refine ⟨4839543760449341106919999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6452725013932454809226665 4839543760449341106919999)
      ·
        refine ⟨7259315640674011660379999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839543760449341106919999 7259315640674011660379999)
        ·
          refine ⟨10888973461011017490569999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259315640674011660379999 10888973461011017490569999)
          ·
            refine ⟨16333460191516526235854999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10888973461011017490569999 16333460191516526235854999)
            ·
              refine ⟨24500190287274789353782499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16333460191516526235854999 24500190287274789353782499)
              ·
                refine ⟨36750285430912184030673749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24500190287274789353782499 36750285430912184030673749)
                ·
                  refine ⟨215333703696751078304729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36750285430912184030673749 215333703696751078304729)
                  ·
                    rfl

theorem cell22_1887124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1887124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887124 prefixEnd_1887124 := by exact prefixLift 1887124
  have htrace : WordTrace (prefixWord ++ tailWord_1887124) baseStart_1887124 baseEnd_1887124 := by
    simpa [prefixWord, tailWord_1887124, baseEnd_1887124] using wordTrace_append hprefix tailTrace_1887124
  have hstable : (prefixWord ++ tailWord_1887124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887124).length < 2 ^ (prefixWord ++ tailWord_1887124).sum := by decide
  have hdescent : baseEnd_1887124 < baseStart_1887124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887233 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1887233 : Nat := 118140960795 + 1887233 * 2 ^ 59
def prefixEnd_1887233 : Nat := 4983230072969 + 3 ^ 40 * 1887233 * 2
def baseEnd_1887233 : Nat := 646038424017813283938853

theorem tailTrace_1887233 : CollatzResearch.WordTrace tailWord_1887233 prefixEnd_1887233 646038424017813283938853 := by
  unfold tailWord_1887233
  simp only [CollatzResearch.WordTrace]
  refine ⟨68833042371884629580802353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45888694914589753053868235 68833042371884629580802353)
  ·
    refine ⟨51624781778913472185601765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68833042371884629580802353 51624781778913472185601765)
    ·
      refine ⟨9679646583546276034800331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51624781778913472185601765 9679646583546276034800331)
      ·
        refine ⟨14519469875319414052200497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679646583546276034800331 14519469875319414052200497)
        ·
          refine ⟨10889602406489560539150373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14519469875319414052200497 10889602406489560539150373)
          ·
            refine ⟨2041800451216792601090695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10889602406489560539150373 2041800451216792601090695)
            ·
              refine ⟨3062700676825188901636043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041800451216792601090695 3062700676825188901636043)
              ·
                refine ⟨4594051015237783352454065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062700676825188901636043 4594051015237783352454065)
                ·
                  refine ⟨3445538261428337514340549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594051015237783352454065 3445538261428337514340549)
                  ·
                    refine ⟨646038424017813283938853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3445538261428337514340549 646038424017813283938853)
                    ·
                      rfl

theorem cell22_1887233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1887233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887233 prefixEnd_1887233 := by exact prefixLift 1887233
  have htrace : WordTrace (prefixWord ++ tailWord_1887233) baseStart_1887233 baseEnd_1887233 := by
    simpa [prefixWord, tailWord_1887233, baseEnd_1887233] using wordTrace_append hprefix tailTrace_1887233
  have hstable : (prefixWord ++ tailWord_1887233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887233).length < 2 ^ (prefixWord ++ tailWord_1887233).sum := by decide
  have hdescent : baseEnd_1887233 < baseStart_1887233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887263 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 3, 3]
def baseStart_1887263 : Nat := 118140960795 + 1887263 * 2 ^ 59
def prefixEnd_1887263 : Nat := 4983230072969 + 3 ^ 40 * 1887263 * 2
def baseEnd_1887263 : Nat := 646048693630903205688761

theorem tailTrace_1887263 : CollatzResearch.WordTrace tailWord_1887263 prefixEnd_1887263 646048693630903205688761 := by
  unfold tailWord_1887263
  simp only [CollatzResearch.WordTrace]
  refine ⟨68834136561775944704394443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45889424374517296469596295 68834136561775944704394443)
  ·
    refine ⟨103251204842663917056591665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68834136561775944704394443 103251204842663917056591665)
    ·
      refine ⟨77438403631997937792443749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103251204842663917056591665 77438403631997937792443749)
      ·
        refine ⟨14519700680999613336083203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77438403631997937792443749 14519700680999613336083203)
        ·
          refine ⟨21779551021499420004124805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519700680999613336083203 21779551021499420004124805)
          ·
            refine ⟨4083665816531141250773401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21779551021499420004124805 4083665816531141250773401)
            ·
              refine ⟨3062749362398355938080051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083665816531141250773401 3062749362398355938080051)
              ·
                refine ⟨4594124043597533907120077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062749362398355938080051 4594124043597533907120077)
                ·
                  refine ⟨1722796516349075215170029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4594124043597533907120077 1722796516349075215170029)
                  ·
                    refine ⟨646048693630903205688761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1722796516349075215170029 646048693630903205688761)
                    ·
                      rfl

theorem cell22_1887263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_1887263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887263 prefixEnd_1887263 := by exact prefixLift 1887263
  have htrace : WordTrace (prefixWord ++ tailWord_1887263) baseStart_1887263 baseEnd_1887263 := by
    simpa [prefixWord, tailWord_1887263, baseEnd_1887263] using wordTrace_append hprefix tailTrace_1887263
  have hstable : (prefixWord ++ tailWord_1887263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887263).length < 2 ^ (prefixWord ++ tailWord_1887263).sum := by decide
  have hdescent : baseEnd_1887263 < baseStart_1887263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887353 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_1887353 : Nat := 118140960795 + 1887353 * 2 ^ 59
def prefixEnd_1887353 : Nat := 4983230072969 + 3 ^ 40 * 1887353 * 2
def baseEnd_1887353 : Nat := 646079502470172970938485

theorem tailTrace_1887353 : CollatzResearch.WordTrace tailWord_1887353 prefixEnd_1887353 646079502470172970938485 := by
  unfold tailWord_1887353
  simp only [CollatzResearch.WordTrace]
  refine ⟨68837419131449890075170713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45891612754299926716780475 68837419131449890075170713)
  ·
    refine ⟨51628064348587417556378035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68837419131449890075170713 51628064348587417556378035)
    ·
      refine ⟨77442096522881126334567053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51628064348587417556378035 77442096522881126334567053)
      ·
        refine ⟨29040786196080422375462645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77442096522881126334567053 29040786196080422375462645)
        ·
          refine ⟨2722573705882539597699623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29040786196080422375462645 2722573705882539597699623)
          ·
            refine ⟨4083860558823809396549435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722573705882539597699623 4083860558823809396549435)
            ·
              refine ⟨6125790838235714094824153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083860558823809396549435 6125790838235714094824153)
              ·
                refine ⟨4594343128676785571118115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125790838235714094824153 4594343128676785571118115)
                ·
                  refine ⟨6891514693015178356677173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594343128676785571118115 6891514693015178356677173)
                  ·
                    refine ⟨646079502470172970938485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6891514693015178356677173 646079502470172970938485)
                    ·
                      rfl

theorem cell22_1887353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_1887353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887353 prefixEnd_1887353 := by exact prefixLift 1887353
  have htrace : WordTrace (prefixWord ++ tailWord_1887353) baseStart_1887353 baseEnd_1887353 := by
    simpa [prefixWord, tailWord_1887353, baseEnd_1887353] using wordTrace_append hprefix tailTrace_1887353
  have hstable : (prefixWord ++ tailWord_1887353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887353).length < 2 ^ (prefixWord ++ tailWord_1887353).sum := by decide
  have hdescent : baseEnd_1887353 < baseStart_1887353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887370 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1887370 : Nat := 118140960795 + 1887370 * 2 ^ 59
def prefixEnd_1887370 : Nat := 4983230072969 + 3 ^ 40 * 1887370 * 2
def baseEnd_1887370 : Nat := 646085321917590593263433

theorem tailTrace_1887370 : CollatzResearch.WordTrace tailWord_1887370 prefixEnd_1887370 646085321917590593263433 := by
  unfold tailWord_1887370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209509793097075494634891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45892026114925534652359709 17209509793097075494634891)
  ·
    refine ⟨25814264689645613241952337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17209509793097075494634891 25814264689645613241952337)
    ·
      refine ⟨19360698517234209931464253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25814264689645613241952337 19360698517234209931464253)
      ·
        refine ⟨7260261943962828724299095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19360698517234209931464253 7260261943962828724299095)
        ·
          refine ⟨10890392915944243086448643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7260261943962828724299095 10890392915944243086448643)
          ·
            refine ⟨16335589373916364629672965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10890392915944243086448643 16335589373916364629672965)
            ·
              refine ⟨3062923007609318368063681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16335589373916364629672965 3062923007609318368063681)
              ·
                refine ⟨2297192255706988776047761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3062923007609318368063681 2297192255706988776047761)
                ·
                  refine ⟨1722894191780241582035821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2297192255706988776047761 1722894191780241582035821)
                  ·
                    refine ⟨646085321917590593263433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1722894191780241582035821 646085321917590593263433)
                    ·
                      rfl

theorem cell22_1887370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1887370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887370 prefixEnd_1887370 := by exact prefixLift 1887370
  have htrace : WordTrace (prefixWord ++ tailWord_1887370) baseStart_1887370 baseEnd_1887370 := by
    simpa [prefixWord, tailWord_1887370, baseEnd_1887370] using wordTrace_append hprefix tailTrace_1887370
  have hstable : (prefixWord ++ tailWord_1887370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887370).length < 2 ^ (prefixWord ++ tailWord_1887370).sum := by decide
  have hdescent : baseEnd_1887370 < baseStart_1887370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887383 : List Nat := [1, 1, 3, 3, 3, 3, 1, 7]
def baseStart_1887383 : Nat := 118140960795 + 1887383 * 2 ^ 59
def prefixEnd_1887383 : Nat := 4983230072969 + 3 ^ 40 * 1887383 * 2
def baseEnd_1887383 : Nat := 71787752453695876965377

theorem tailTrace_1887383 : CollatzResearch.WordTrace tailWord_1887383 prefixEnd_1887383 71787752453695876965377 := by
  unfold tailWord_1887383
  simp only [CollatzResearch.WordTrace]
  refine ⟨68838513321341205198762803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45892342214227470132508535 68838513321341205198762803)
  ·
    refine ⟨103257769982011807798144205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68838513321341205198762803 103257769982011807798144205)
    ·
      refine ⟨38721663743254427924304077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103257769982011807798144205 38721663743254427924304077)
      ·
        refine ⟨14520623903720410471614029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38721663743254427924304077 14520623903720410471614029)
        ·
          refine ⟨5445233963895153926855261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14520623903720410471614029 5445233963895153926855261)
          ·
            refine ⟨2041962736460682722570723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5445233963895153926855261 2041962736460682722570723)
            ·
              refine ⟨3062944104691024083856085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041962736460682722570723 3062944104691024083856085)
              ·
                refine ⟨71787752453695876965377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3062944104691024083856085 71787752453695876965377)
                ·
                  rfl

theorem cell22_1887383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 7].length) (baseStart_1887383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887383 prefixEnd_1887383 := by exact prefixLift 1887383
  have htrace : WordTrace (prefixWord ++ tailWord_1887383) baseStart_1887383 baseEnd_1887383 := by
    simpa [prefixWord, tailWord_1887383, baseEnd_1887383] using wordTrace_append hprefix tailTrace_1887383
  have hstable : (prefixWord ++ tailWord_1887383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887383).length < 2 ^ (prefixWord ++ tailWord_1887383).sum := by decide
  have hdescent : baseEnd_1887383 < baseStart_1887383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887402 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1887402 : Nat := 118140960795 + 1887402 * 2 ^ 59
def prefixEnd_1887402 : Nat := 4983230072969 + 3 ^ 40 * 1887402 * 2
def baseEnd_1887402 : Nat := 646096276171553176463335

theorem tailTrace_1887402 : CollatzResearch.WordTrace tailWord_1887402 prefixEnd_1887402 646096276171553176463335 := by
  unfold tailWord_1887402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209801577068092860926115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45892804205514914295802973 17209801577068092860926115)
  ·
    refine ⟨25814702365602139291389173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17209801577068092860926115 25814702365602139291389173)
    ·
      refine ⟨2420128346775200558567735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25814702365602139291389173 2420128346775200558567735)
      ·
        refine ⟨3630192520162800837851603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420128346775200558567735 3630192520162800837851603)
        ·
          refine ⟨5445288780244201256777405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630192520162800837851603 5445288780244201256777405)
          ·
            refine ⟨2041983292591575471291527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5445288780244201256777405 2041983292591575471291527)
            ·
              refine ⟨3062974938887363206937291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041983292591575471291527 3062974938887363206937291)
              ·
                refine ⟨4594462408331044810405937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062974938887363206937291 4594462408331044810405937)
                ·
                  refine ⟨3445846806248283607804453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594462408331044810405937 3445846806248283607804453)
                  ·
                    refine ⟨646096276171553176463335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3445846806248283607804453 646096276171553176463335)
                    ·
                      rfl

theorem cell22_1887402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1887402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887402 prefixEnd_1887402 := by exact prefixLift 1887402
  have htrace : WordTrace (prefixWord ++ tailWord_1887402) baseStart_1887402 baseEnd_1887402 := by
    simpa [prefixWord, tailWord_1887402, baseEnd_1887402] using wordTrace_append hprefix tailTrace_1887402
  have hstable : (prefixWord ++ tailWord_1887402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887402).length < 2 ^ (prefixWord ++ tailWord_1887402).sum := by decide
  have hdescent : baseEnd_1887402 < baseStart_1887402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887505 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 2, 3]
def baseStart_1887505 : Nat := 118140960795 + 1887505 * 2 ^ 59
def prefixEnd_1887505 : Nat := 4983230072969 + 3 ^ 40 * 1887505 * 2
def baseEnd_1887505 : Nat := 646131535176495241138019

theorem tailTrace_1887505 : CollatzResearch.WordTrace tailWord_1887505 prefixEnd_1887505 646131535176495241138019 := by
  unfold tailWord_1887505
  simp only [CollatzResearch.WordTrace]
  refine ⟨68842963026899220034703969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45895308684599480023135979 68842963026899220034703969)
  ·
    refine ⟨51632222270174415026027977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68842963026899220034703969 51632222270174415026027977)
    ·
      refine ⟨38724166702630811269520983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51632222270174415026027977 38724166702630811269520983)
      ·
        refine ⟨58086250053946216904281475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38724166702630811269520983 58086250053946216904281475)
        ·
          refine ⟨87129375080919325356422213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58086250053946216904281475 87129375080919325356422213)
          ·
            refine ⟨16336757827672373504329165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87129375080919325356422213 16336757827672373504329165)
            ·
              refine ⟨6126284185377140064123437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16336757827672373504329165 6126284185377140064123437)
              ·
                refine ⟨2297356569516427524046289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6126284185377140064123437 2297356569516427524046289)
                ·
                  refine ⟨1723017427137320643034717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2297356569516427524046289 1723017427137320643034717)
                  ·
                    refine ⟨646131535176495241138019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723017427137320643034717 646131535176495241138019)
                    ·
                      rfl

theorem cell22_1887505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_1887505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887505 prefixEnd_1887505 := by exact prefixLift 1887505
  have htrace : WordTrace (prefixWord ++ tailWord_1887505) baseStart_1887505 baseEnd_1887505 := by
    simpa [prefixWord, tailWord_1887505, baseEnd_1887505] using wordTrace_append hprefix tailTrace_1887505
  have hstable : (prefixWord ++ tailWord_1887505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887505).length < 2 ^ (prefixWord ++ tailWord_1887505).sum := by decide
  have hdescent : baseEnd_1887505 < baseStart_1887505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887548 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1887548 : Nat := 118140960795 + 1887548 * 2 ^ 59
def prefixEnd_1887548 : Nat := 4983230072969 + 3 ^ 40 * 1887548 * 2
def baseEnd_1887548 : Nat := 646146254955257462312887

theorem tailTrace_1887548 : CollatzResearch.WordTrace tailWord_1887548 prefixEnd_1887548 646146254955257462312887 := by
  unfold tailWord_1887548
  simp only [CollatzResearch.WordTrace]
  refine ⟨34422265682871719189259649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45896354243828958919012865 34422265682871719189259649)
  ·
    refine ⟨25816699262153789391944737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34422265682871719189259649 25816699262153789391944737)
    ·
      refine ⟨19362524446615342043958553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25816699262153789391944737 19362524446615342043958553)
      ·
        refine ⟨14521893334961506532968915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19362524446615342043958553 14521893334961506532968915)
        ·
          refine ⟨21782840002442259799453373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14521893334961506532968915 21782840002442259799453373)
          ·
            refine ⟨8168565000915847424795015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21782840002442259799453373 8168565000915847424795015)
            ·
              refine ⟨12252847501373771137192523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8168565000915847424795015 12252847501373771137192523)
              ·
                refine ⟨18379271252060656705788785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12252847501373771137192523 18379271252060656705788785)
                ·
                  refine ⟨13784453439045492529341589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18379271252060656705788785 13784453439045492529341589)
                  ·
                    refine ⟨646146254955257462312887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13784453439045492529341589 646146254955257462312887)
                    ·
                      rfl

theorem cell22_1887548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1887548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887548 prefixEnd_1887548 := by exact prefixLift 1887548
  have htrace : WordTrace (prefixWord ++ tailWord_1887548) baseStart_1887548 baseEnd_1887548 := by
    simpa [prefixWord, tailWord_1887548, baseEnd_1887548] using wordTrace_append hprefix tailTrace_1887548
  have hstable : (prefixWord ++ tailWord_1887548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887548).length < 2 ^ (prefixWord ++ tailWord_1887548).sum := by decide
  have hdescent : baseEnd_1887548 < baseStart_1887548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887584 : List Nat := [2, 1, 1, 3, 4, 2, 2, 3, 1, 3]
def baseStart_1887584 : Nat := 118140960795 + 1887584 * 2 ^ 59
def prefixEnd_1887584 : Nat := 4983230072969 + 3 ^ 40 * 1887584 * 2
def baseEnd_1887584 : Nat := 646158578490965368412777

theorem tailTrace_1887584 : CollatzResearch.WordTrace tailWord_1887584 prefixEnd_1887584 646158578490965368412777 := by
  unfold tailWord_1887584
  simp only [CollatzResearch.WordTrace]
  refine ⟨34422922196806508263414903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45897229595742011017886537 34422922196806508263414903)
  ·
    refine ⟨51634383295209762395122355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34422922196806508263414903 51634383295209762395122355)
    ·
      refine ⟨77451574942814643592683533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51634383295209762395122355 77451574942814643592683533)
      ·
        refine ⟨29044340603555491347256325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77451574942814643592683533 29044340603555491347256325)
        ·
          refine ⟨5445813863166654627610561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29044340603555491347256325 5445813863166654627610561)
          ·
            refine ⟨4084360397374990970707921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5445813863166654627610561 4084360397374990970707921)
            ·
              refine ⟨3063270298031243228030941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4084360397374990970707921 3063270298031243228030941)
              ·
                refine ⟨1148726361761716210511603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3063270298031243228030941 1148726361761716210511603)
                ·
                  refine ⟨1723089542642574315767405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148726361761716210511603 1723089542642574315767405)
                  ·
                    refine ⟨646158578490965368412777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723089542642574315767405 646158578490965368412777)
                    ·
                      rfl

theorem cell22_1887584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 3].length) (baseStart_1887584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887584 prefixEnd_1887584 := by exact prefixLift 1887584
  have htrace : WordTrace (prefixWord ++ tailWord_1887584) baseStart_1887584 baseEnd_1887584 := by
    simpa [prefixWord, tailWord_1887584, baseEnd_1887584] using wordTrace_append hprefix tailTrace_1887584
  have hstable : (prefixWord ++ tailWord_1887584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887584).length < 2 ^ (prefixWord ++ tailWord_1887584).sum := by decide
  have hdescent : baseEnd_1887584 < baseStart_1887584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887593 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_1887593 : Nat := 118140960795 + 1887593 * 2 ^ 59
def prefixEnd_1887593 : Nat := 4983230072969 + 3 ^ 40 * 1887593 * 2
def baseEnd_1887593 : Nat := 646161659374892344937749

theorem tailTrace_1887593 : CollatzResearch.WordTrace tailWord_1887593 prefixEnd_1887593 646161659374892344937749 := by
  unfold tailWord_1887593
  simp only [CollatzResearch.WordTrace]
  refine ⟨68846172650580411063907433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45897448433720274042604955 68846172650580411063907433)
  ·
    refine ⟨51634629487935308297930575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68846172650580411063907433 51634629487935308297930575)
    ·
      refine ⟨77451944231902962446895863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51634629487935308297930575 77451944231902962446895863)
      ·
        refine ⟨116177916347854443670343795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77451944231902962446895863 116177916347854443670343795)
        ·
          refine ⟨174266874521781665505515693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116177916347854443670343795 174266874521781665505515693)
          ·
            refine ⟨65350077945668124564568385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174266874521781665505515693 65350077945668124564568385)
            ·
              refine ⟨49012558459251093423426289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65350077945668124564568385 49012558459251093423426289)
              ·
                refine ⟨36759418844438320067569717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49012558459251093423426289 36759418844438320067569717)
                ·
                  refine ⟨3446195516666092506334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36759418844438320067569717 3446195516666092506334661)
                  ·
                    refine ⟨646161659374892344937749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3446195516666092506334661 646161659374892344937749)
                    ·
                      rfl

theorem cell22_1887593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_1887593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887593 prefixEnd_1887593 := by exact prefixLift 1887593
  have htrace : WordTrace (prefixWord ++ tailWord_1887593) baseStart_1887593 baseEnd_1887593 := by
    simpa [prefixWord, tailWord_1887593, baseEnd_1887593] using wordTrace_append hprefix tailTrace_1887593
  have hstable : (prefixWord ++ tailWord_1887593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887593).length < 2 ^ (prefixWord ++ tailWord_1887593).sum := by decide
  have hdescent : baseEnd_1887593 < baseStart_1887593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887597 : List Nat := [1, 5, 1, 1, 1, 5, 1, 2, 5]
def baseStart_1887597 : Nat := 118140960795 + 1887597 * 2 ^ 59
def prefixEnd_1887597 : Nat := 4983230072969 + 3 ^ 40 * 1887597 * 2
def baseEnd_1887597 : Nat := 215387676218879222612579

theorem tailTrace_1887597 : CollatzResearch.WordTrace tailWord_1887597 prefixEnd_1887597 215387676218879222612579 := by
  unfold tailWord_1887597
  simp only [CollatzResearch.WordTrace]
  refine ⟨68846318542565919747053045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45897545695043946498035363 68846318542565919747053045)
  ·
    refine ⟨6454342363365554976286223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68846318542565919747053045 6454342363365554976286223)
    ·
      refine ⟨9681513545048332464429335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6454342363365554976286223 9681513545048332464429335)
      ·
        refine ⟨14522270317572498696644003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9681513545048332464429335 14522270317572498696644003)
        ·
          refine ⟨21783405476358748044966005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14522270317572498696644003 21783405476358748044966005)
          ·
            refine ⟨2042194263408632629215563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21783405476358748044966005 2042194263408632629215563)
            ·
              refine ⟨3063291395112948943823345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2042194263408632629215563 3063291395112948943823345)
              ·
                refine ⟨2297468546334711707867509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063291395112948943823345 2297468546334711707867509)
                ·
                  refine ⟨215387676218879222612579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2297468546334711707867509 215387676218879222612579)
                  ·
                    rfl

theorem cell22_1887597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_1887597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887597 prefixEnd_1887597 := by exact prefixLift 1887597
  have htrace : WordTrace (prefixWord ++ tailWord_1887597) baseStart_1887597 baseEnd_1887597 := by
    simpa [prefixWord, tailWord_1887597, baseEnd_1887597] using wordTrace_append hprefix tailTrace_1887597
  have hstable : (prefixWord ++ tailWord_1887597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887597).length < 2 ^ (prefixWord ++ tailWord_1887597).sum := by decide
  have hdescent : baseEnd_1887597 < baseStart_1887597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887775 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 3, 5]
def baseStart_1887775 : Nat := 118140960795 + 1887775 * 2 ^ 59
def prefixEnd_1887775 : Nat := 4983230072969 + 3 ^ 40 * 1887775 * 2
def baseEnd_1887775 : Nat := 646223961694304536887191

theorem tailTrace_1887775 : CollatzResearch.WordTrace tailWord_1887775 prefixEnd_1887775 646223961694304536887191 := by
  unfold tailWord_1887775
  simp only [CollatzResearch.WordTrace]
  refine ⟨68852810735921056147032779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45901873823947370764688519 68852810735921056147032779)
  ·
    refine ⟨103279216103881584220549169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68852810735921056147032779 103279216103881584220549169)
    ·
      refine ⟨77459412077911188165411877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103279216103881584220549169 77459412077911188165411877)
      ·
        refine ⟨14523639764608347781014727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77459412077911188165411877 14523639764608347781014727)
        ·
          refine ⟨21785459646912521671522091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14523639764608347781014727 21785459646912521671522091)
          ·
            refine ⟨32678189470368782507283137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21785459646912521671522091 32678189470368782507283137)
            ·
              refine ⟨24508642102776586880462353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32678189470368782507283137 24508642102776586880462353)
              ·
                refine ⟨18381481577082440160346765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24508642102776586880462353 18381481577082440160346765)
                ·
                  refine ⟨6893055591405915060130037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18381481577082440160346765 6893055591405915060130037)
                  ·
                    refine ⟨646223961694304536887191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6893055591405915060130037 646223961694304536887191)
                    ·
                      rfl

theorem cell22_1887775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_1887775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887775 prefixEnd_1887775 := by exact prefixLift 1887775
  have htrace : WordTrace (prefixWord ++ tailWord_1887775) baseStart_1887775 baseEnd_1887775 := by
    simpa [prefixWord, tailWord_1887775, baseEnd_1887775] using wordTrace_append hprefix tailTrace_1887775
  have hstable : (prefixWord ++ tailWord_1887775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887775).length < 2 ^ (prefixWord ++ tailWord_1887775).sum := by decide
  have hdescent : baseEnd_1887775 < baseStart_1887775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887777 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 6]
def baseStart_1887777 : Nat := 118140960795 + 1887777 * 2 ^ 59
def prefixEnd_1887777 : Nat := 4983230072969 + 3 ^ 40 * 1887777 * 2
def baseEnd_1887777 : Nat := 215408215445059066112395

theorem tailTrace_1887777 : CollatzResearch.WordTrace tailWord_1887777 prefixEnd_1887777 215408215445059066112395 := by
  unfold tailWord_1887777
  simp only [CollatzResearch.WordTrace]
  refine ⟨68852883681913810488605585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45901922454609206992403723 68852883681913810488605585)
  ·
    refine ⟨51639662761435357866454189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68852883681913810488605585 51639662761435357866454189)
    ·
      refine ⟨19364873535538259199920321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51639662761435357866454189 19364873535538259199920321)
      ·
        refine ⟨14523655151653694399940241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19364873535538259199920321 14523655151653694399940241)
        ·
          refine ⟨10892741363740270799955181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14523655151653694399940241 10892741363740270799955181)
          ·
            refine ⟨4084778011402601549983193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10892741363740270799955181 4084778011402601549983193)
            ·
              refine ⟨3063583508551951162487395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4084778011402601549983193 3063583508551951162487395)
              ·
                refine ⟨4595375262827926743731093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063583508551951162487395 4595375262827926743731093)
                ·
                  refine ⟨215408215445059066112395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4595375262827926743731093 215408215445059066112395)
                  ·
                    rfl

theorem cell22_1887777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_1887777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887777 prefixEnd_1887777 := by exact prefixLift 1887777
  have htrace : WordTrace (prefixWord ++ tailWord_1887777) baseStart_1887777 baseEnd_1887777 := by
    simpa [prefixWord, tailWord_1887777, baseEnd_1887777] using wordTrace_append hprefix tailTrace_1887777
  have hstable : (prefixWord ++ tailWord_1887777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887777).length < 2 ^ (prefixWord ++ tailWord_1887777).sum := by decide
  have hdescent : baseEnd_1887777 < baseStart_1887777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887929 : List Nat := [1, 2, 1, 4, 1, 1, 3, 5, 4]
def baseStart_1887929 : Nat := 118140960795 + 1887929 * 2 ^ 59
def prefixEnd_1887929 : Nat := 4983230072969 + 3 ^ 40 * 1887929 * 2
def baseEnd_1887929 : Nat := 215425559680499822845573

theorem tailTrace_1887929 : CollatzResearch.WordTrace tailWord_1887929 prefixEnd_1887929 215425559680499822845573 := by
  unfold tailWord_1887929
  simp only [CollatzResearch.WordTrace]
  refine ⟨68858427577363140448138841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45905618384908760298759227 68858427577363140448138841)
  ·
    refine ⟨51643820683022355336104131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68858427577363140448138841 51643820683022355336104131)
    ·
      refine ⟨77465731024533533004156197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51643820683022355336104131 77465731024533533004156197)
      ·
        refine ⟨14524824567100037438279287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77465731024533533004156197 14524824567100037438279287)
        ·
          refine ⟨21787236850650056157418931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524824567100037438279287 21787236850650056157418931)
          ·
            refine ⟨32680855275975084236128397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21787236850650056157418931 32680855275975084236128397)
            ·
              refine ⟨12255320728490656588548149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32680855275975084236128397 12255320728490656588548149)
              ·
                refine ⟨1148936318295999055176389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12255320728490656588548149 1148936318295999055176389)
                ·
                  refine ⟨215425559680499822845573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1148936318295999055176389 215425559680499822845573)
                  ·
                    rfl

theorem cell22_1887929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_1887929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887929 prefixEnd_1887929 := by exact prefixLift 1887929
  have htrace : WordTrace (prefixWord ++ tailWord_1887929) baseStart_1887929 baseEnd_1887929 := by
    simpa [prefixWord, tailWord_1887929, baseEnd_1887929] using wordTrace_append hprefix tailTrace_1887929
  have hstable : (prefixWord ++ tailWord_1887929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887929).length < 2 ^ (prefixWord ++ tailWord_1887929).sum := by decide
  have hdescent : baseEnd_1887929 < baseStart_1887929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887944 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 4, 3]
def baseStart_1887944 : Nat := 118140960795 + 1887944 * 2 ^ 59
def prefixEnd_1887944 : Nat := 4983230072969 + 3 ^ 40 * 1887944 * 2
def baseEnd_1887944 : Nat := 646281813848044429411673

theorem tailTrace_1887944 : CollatzResearch.WordTrace tailWord_1887944 prefixEnd_1887944 646281813848044429411673 := by
  unfold tailWord_1887944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34429487336154399004967443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45905983114872532006623257 34429487336154399004967443)
  ·
    refine ⟨51644231004231598507451165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34429487336154399004967443 51644231004231598507451165)
    ·
      refine ⟨19366586626586849440294187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51644231004231598507451165 19366586626586849440294187)
      ·
        refine ⟨29049879939880274160441281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19366586626586849440294187 29049879939880274160441281)
        ·
          refine ⟨21787409954910205620330961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29049879939880274160441281 21787409954910205620330961)
          ·
            refine ⟨16340557466182654215248221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21787409954910205620330961 16340557466182654215248221)
            ·
              refine ⟨6127709049818495330718083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16340557466182654215248221 6127709049818495330718083)
              ·
                refine ⟨9191563574727742996077125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127709049818495330718083 9191563574727742996077125)
                ·
                  refine ⟨1723418170261451811764461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9191563574727742996077125 1723418170261451811764461)
                  ·
                    refine ⟨646281813848044429411673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723418170261451811764461 646281813848044429411673)
                    ·
                      rfl

theorem cell22_1887944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_1887944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887944 prefixEnd_1887944 := by exact prefixLift 1887944
  have htrace : WordTrace (prefixWord ++ tailWord_1887944) baseStart_1887944 baseEnd_1887944 := by
    simpa [prefixWord, tailWord_1887944, baseEnd_1887944] using wordTrace_append hprefix tailTrace_1887944
  have hstable : (prefixWord ++ tailWord_1887944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887944).length < 2 ^ (prefixWord ++ tailWord_1887944).sum := by decide
  have hdescent : baseEnd_1887944 < baseStart_1887944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1887972 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1887972 : Nat := 118140960795 + 1887972 * 2 ^ 59
def prefixEnd_1887972 : Nat := 4983230072969 + 3 ^ 40 * 1887972 * 2
def baseEnd_1887972 : Nat := 646291398820261689711587

theorem tailTrace_1887972 : CollatzResearch.WordTrace tailWord_1887972 prefixEnd_1887972 646291398820261689711587 := by
  unfold tailWord_1887972
  simp only [CollatzResearch.WordTrace]
  refine ⟨34429997958103679395977085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45906663944138239194636113 34429997958103679395977085)
  ·
    refine ⟨12911249234288879773491407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34429997958103679395977085 12911249234288879773491407)
    ·
      refine ⟨19366873851433319660237111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12911249234288879773491407 19366873851433319660237111)
      ·
        refine ⟨29050310777149979490355667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19366873851433319660237111 29050310777149979490355667)
        ·
          refine ⟨43575466165724969235533501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29050310777149979490355667 43575466165724969235533501)
          ·
            refine ⟨16340799812146863463325063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43575466165724969235533501 16340799812146863463325063)
            ·
              refine ⟨24511199718220295194987595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16340799812146863463325063 24511199718220295194987595)
              ·
                refine ⟨36766799577330442792481393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24511199718220295194987595 36766799577330442792481393)
                ·
                  refine ⟨27575099682997832094361045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36766799577330442792481393 27575099682997832094361045)
                  ·
                    refine ⟨646291398820261689711587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27575099682997832094361045 646291398820261689711587)
                    ·
                      rfl

theorem cell22_1887972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1887972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1887972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1887972 prefixEnd_1887972 := by exact prefixLift 1887972
  have htrace : WordTrace (prefixWord ++ tailWord_1887972) baseStart_1887972 baseEnd_1887972 := by
    simpa [prefixWord, tailWord_1887972, baseEnd_1887972] using wordTrace_append hprefix tailTrace_1887972
  have hstable : (prefixWord ++ tailWord_1887972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1887972).length < 2 ^ (prefixWord ++ tailWord_1887972).sum := by decide
  have hdescent : baseEnd_1887972 < baseStart_1887972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1887972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888017 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1888017 : Nat := 118140960795 + 1888017 * 2 ^ 59
def prefixEnd_1888017 : Nat := 4983230072969 + 3 ^ 40 * 1888017 * 2
def baseEnd_1888017 : Nat := 646306803239896572336449

theorem tailTrace_1888017 : CollatzResearch.WordTrace tailWord_1888017 prefixEnd_1888017 646306803239896572336449 := by
  unfold tailWord_1888017
  simp only [CollatzResearch.WordTrace]
  refine ⟨68861637201044331477342305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45907758134029554318228203 68861637201044331477342305)
  ·
    refine ⟨51646227900783248608006729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68861637201044331477342305 51646227900783248608006729)
    ·
      refine ⟨38734670925587436456005047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51646227900783248608006729 38734670925587436456005047)
      ·
        refine ⟨58102006388381154684007571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38734670925587436456005047 58102006388381154684007571)
        ·
          refine ⟨87153009582571732026011357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58102006388381154684007571 87153009582571732026011357)
          ·
            refine ⟨32682378593464399509754259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87153009582571732026011357 32682378593464399509754259)
            ·
              refine ⟨49023567890196599264631389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32682378593464399509754259 49023567890196599264631389)
              ·
                refine ⟨18383837958823724724236771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49023567890196599264631389 18383837958823724724236771)
                ·
                  refine ⟨27575756938235587086355157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18383837958823724724236771 27575756938235587086355157)
                  ·
                    refine ⟨646306803239896572336449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27575756938235587086355157 646306803239896572336449)
                    ·
                      rfl

theorem cell22_1888017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1888017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888017 prefixEnd_1888017 := by exact prefixLift 1888017
  have htrace : WordTrace (prefixWord ++ tailWord_1888017) baseStart_1888017 baseEnd_1888017 := by
    simpa [prefixWord, tailWord_1888017, baseEnd_1888017] using wordTrace_append hprefix tailTrace_1888017
  have hstable : (prefixWord ++ tailWord_1888017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888017).length < 2 ^ (prefixWord ++ tailWord_1888017).sum := by decide
  have hdescent : baseEnd_1888017 < baseStart_1888017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888047 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 8]
def baseStart_1888047 : Nat := 118140960795 + 1888047 * 2 ^ 59
def prefixEnd_1888047 : Nat := 4983230072969 + 3 ^ 40 * 1888047 * 2
def baseEnd_1888047 : Nat := 215439024284328831362119

theorem tailTrace_1888047 : CollatzResearch.WordTrace tailWord_1888047 prefixEnd_1888047 215439024284328831362119 := by
  unfold tailWord_1888047
  simp only [CollatzResearch.WordTrace]
  refine ⟨68862731390935646600934395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45908487593957097733956263 68862731390935646600934395)
  ·
    refine ⟨103294097086403469901401593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68862731390935646600934395 103294097086403469901401593)
    ·
      refine ⟨77470572814802602426051195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103294097086403469901401593 77470572814802602426051195)
      ·
        refine ⟨116205859222203903639076793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77470572814802602426051195 116205859222203903639076793)
        ·
          refine ⟨87154394416652927729307595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116205859222203903639076793 87154394416652927729307595)
          ·
            refine ⟨130731591624979391593961393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87154394416652927729307595 130731591624979391593961393)
            ·
              refine ⟨98048693718734543695471045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130731591624979391593961393 98048693718734543695471045)
              ·
                refine ⟨18384130072262726942900821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98048693718734543695471045 18384130072262726942900821)
                ·
                  refine ⟨215439024284328831362119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18384130072262726942900821 215439024284328831362119)
                  ·
                    rfl

theorem cell22_1888047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 8].length) (baseStart_1888047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888047 prefixEnd_1888047 := by exact prefixLift 1888047
  have htrace : WordTrace (prefixWord ++ tailWord_1888047) baseStart_1888047 baseEnd_1888047 := by
    simpa [prefixWord, tailWord_1888047, baseEnd_1888047] using wordTrace_append hprefix tailTrace_1888047
  have hstable : (prefixWord ++ tailWord_1888047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888047).length < 2 ^ (prefixWord ++ tailWord_1888047).sum := by decide
  have hdescent : baseEnd_1888047 < baseStart_1888047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888098 : List Nat := [3, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1888098 : Nat := 118140960795 + 1888098 * 2 ^ 59
def prefixEnd_1888098 : Nat := 4983230072969 + 3 ^ 40 * 1888098 * 2
def baseEnd_1888098 : Nat := 215444843731746453687067

theorem tailTrace_1888098 : CollatzResearch.WordTrace tailWord_1888098 prefixEnd_1888098 215444843731746453687067 := by
  unfold tailWord_1888098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216147878437720577760237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45909727675833921540693965 17216147878437720577760237)
  ·
    refine ⟨6456055454414145216660089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17216147878437720577760237 6456055454414145216660089)
    ·
      refine ⟨4842041590810608912495067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6456055454414145216660089 4842041590810608912495067)
      ·
        refine ⟨7263062386215913368742601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4842041590810608912495067 7263062386215913368742601)
        ·
          refine ⟨5447296789661935026556951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7263062386215913368742601 5447296789661935026556951)
          ·
            refine ⟨8170945184492902539835427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447296789661935026556951 8170945184492902539835427)
            ·
              refine ⟨12256417776739353809753141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8170945184492902539835427 12256417776739353809753141)
              ·
                refine ⟨1149039166569314419664357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12256417776739353809753141 1149039166569314419664357)
                ·
                  refine ⟨215444843731746453687067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149039166569314419664357 215444843731746453687067)
                  ·
                    rfl

theorem cell22_1888098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1888098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888098 prefixEnd_1888098 := by exact prefixLift 1888098
  have htrace : WordTrace (prefixWord ++ tailWord_1888098) baseStart_1888098 baseEnd_1888098 := by
    simpa [prefixWord, tailWord_1888098, baseEnd_1888098] using wordTrace_append hprefix tailTrace_1888098
  have hstable : (prefixWord ++ tailWord_1888098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888098).length < 2 ^ (prefixWord ++ tailWord_1888098).sum := by decide
  have hdescent : baseEnd_1888098 < baseStart_1888098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888100 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_1888100 : Nat := 118140960795 + 1888100 * 2 ^ 59
def prefixEnd_1888100 : Nat := 4983230072969 + 3 ^ 40 * 1888100 * 2
def baseEnd_1888100 : Nat := 646335215836112022511195

theorem tailTrace_1888100 : CollatzResearch.WordTrace tailWord_1888100 prefixEnd_1888100 646335215836112022511195 := by
  unfold tailWord_1888100
  simp only [CollatzResearch.WordTrace]
  refine ⟨34432332229871818326306877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45909776306495757768409169 34432332229871818326306877)
  ·
    refine ⟨12912124586201931872365079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34432332229871818326306877 12912124586201931872365079)
    ·
      refine ⟨19368186879302897808547619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12912124586201931872365079 19368186879302897808547619)
      ·
        refine ⟨29052280318954346712821429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19368186879302897808547619 29052280318954346712821429)
        ·
          refine ⟨2723651279901970004327009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29052280318954346712821429 2723651279901970004327009)
          ·
            refine ⟨2042738459926477503245257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2723651279901970004327009 2042738459926477503245257)
            ·
              refine ⟨1532053844944858127433943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042738459926477503245257 1532053844944858127433943)
              ·
                refine ⟨2298080767417287191150915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532053844944858127433943 2298080767417287191150915)
                ·
                  refine ⟨3447121151125930786726373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298080767417287191150915 3447121151125930786726373)
                  ·
                    refine ⟨646335215836112022511195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447121151125930786726373 646335215836112022511195)
                    ·
                      rfl

theorem cell22_1888100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_1888100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888100 prefixEnd_1888100 := by exact prefixLift 1888100
  have htrace : WordTrace (prefixWord ++ tailWord_1888100) baseStart_1888100 baseEnd_1888100 := by
    simpa [prefixWord, tailWord_1888100, baseEnd_1888100] using wordTrace_append hprefix tailTrace_1888100
  have hstable : (prefixWord ++ tailWord_1888100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888100).length < 2 ^ (prefixWord ++ tailWord_1888100).sum := by decide
  have hdescent : baseEnd_1888100 < baseStart_1888100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888169 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_1888169 : Nat := 118140960795 + 1888169 * 2 ^ 59
def prefixEnd_1888169 : Nat := 4983230072969 + 3 ^ 40 * 1888169 * 2
def baseEnd_1888169 : Nat := 646358835946218842535983

theorem tailTrace_1888169 : CollatzResearch.WordTrace tailWord_1888169 prefixEnd_1888169 646358835946218842535983 := by
  unfold tailWord_1888169
  simp only [CollatzResearch.WordTrace]
  refine ⟨68867181096493661436875561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45911454064329107624583707 68867181096493661436875561)
  ·
    refine ⟨51650385822370246077656671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68867181096493661436875561 51650385822370246077656671)
    ·
      refine ⟨77475578733555369116485007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51650385822370246077656671 77475578733555369116485007)
      ·
        refine ⟨116213368100333053674727511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77475578733555369116485007 116213368100333053674727511)
        ·
          refine ⟨174320052150499580512091267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116213368100333053674727511 174320052150499580512091267)
          ·
            refine ⟨261480078225749370768136901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174320052150499580512091267 261480078225749370768136901)
            ·
              refine ⟨49027514667328007019025669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261480078225749370768136901 49027514667328007019025669)
              ·
                refine ⟨9192659000124001316067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49027514667328007019025669 9192659000124001316067313)
                ·
                  refine ⟨6894494250093000987050485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192659000124001316067313 6894494250093000987050485)
                  ·
                    refine ⟨646358835946218842535983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6894494250093000987050485 646358835946218842535983)
                    ·
                      rfl

theorem cell22_1888169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_1888169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888169 prefixEnd_1888169 := by exact prefixLift 1888169
  have htrace : WordTrace (prefixWord ++ tailWord_1888169) baseStart_1888169 baseEnd_1888169 := by
    simpa [prefixWord, tailWord_1888169, baseEnd_1888169] using wordTrace_append hprefix tailTrace_1888169
  have hstable : (prefixWord ++ tailWord_1888169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888169).length < 2 ^ (prefixWord ++ tailWord_1888169).sum := by decide
  have hdescent : baseEnd_1888169 < baseStart_1888169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888175 : List Nat := [1, 1, 2, 1, 2, 2, 7, 2, 1, 3]
def baseStart_1888175 : Nat := 118140960795 + 1888175 * 2 ^ 59
def prefixEnd_1888175 : Nat := 4983230072969 + 3 ^ 40 * 1888175 * 2
def baseEnd_1888175 : Nat := 646360889868836826885965

theorem tailTrace_1888175 : CollatzResearch.WordTrace tailWord_1888175 prefixEnd_1888175 646360889868836826885965 := by
  unfold tailWord_1888175
  simp only [CollatzResearch.WordTrace]
  refine ⟨68867399934471924461593979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45911599956314616307729319 68867399934471924461593979)
  ·
    refine ⟨103301099901707886692390969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68867399934471924461593979 103301099901707886692390969)
    ·
      refine ⟨77475824926280915019293227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103301099901707886692390969 77475824926280915019293227)
      ·
        refine ⟨116213737389421372528939841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77475824926280915019293227 116213737389421372528939841)
        ·
          refine ⟨87160303042066029396704881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116213737389421372528939841 87160303042066029396704881)
          ·
            refine ⟨65370227281549522047528661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87160303042066029396704881 65370227281549522047528661)
            ·
              refine ⟨1532114701911316922988953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65370227281549522047528661 1532114701911316922988953)
              ·
                refine ⟨1149086026433487692241715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532114701911316922988953 1149086026433487692241715)
                ·
                  refine ⟨1723629039650231538362573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149086026433487692241715 1723629039650231538362573)
                  ·
                    refine ⟨646360889868836826885965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723629039650231538362573 646360889868836826885965)
                    ·
                      rfl

theorem cell22_1888175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 3].length) (baseStart_1888175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888175 prefixEnd_1888175 := by exact prefixLift 1888175
  have htrace : WordTrace (prefixWord ++ tailWord_1888175) baseStart_1888175 baseEnd_1888175 := by
    simpa [prefixWord, tailWord_1888175, baseEnd_1888175] using wordTrace_append hprefix tailTrace_1888175
  have hstable : (prefixWord ++ tailWord_1888175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888175).length < 2 ^ (prefixWord ++ tailWord_1888175).sum := by decide
  have hdescent : baseEnd_1888175 < baseStart_1888175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888199 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 8]
def baseStart_1888199 : Nat := 118140960795 + 1888199 * 2 ^ 59
def prefixEnd_1888199 : Nat := 4983230072969 + 3 ^ 40 * 1888199 * 2
def baseEnd_1888199 : Nat := 215456368519769588095297

theorem tailTrace_1888199 : CollatzResearch.WordTrace tailWord_1888199 prefixEnd_1888199 215456368519769588095297 := by
  unfold tailWord_1888199
  simp only [CollatzResearch.WordTrace]
  refine ⟨68868275286384976560467651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45912183524256651040311767 68868275286384976560467651)
  ·
    refine ⟨103302412929577464840701477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68868275286384976560467651 103302412929577464840701477)
    ·
      refine ⟨19369202424295774657631527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103302412929577464840701477 19369202424295774657631527)
      ·
        refine ⟨29053803636443661986447291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19369202424295774657631527 29053803636443661986447291)
        ·
          refine ⟨43580705454665492979670937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29053803636443661986447291 43580705454665492979670937)
          ·
            refine ⟨32685529090999119734753203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43580705454665492979670937 32685529090999119734753203)
            ·
              refine ⟨49028293636498679602129805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32685529090999119734753203 49028293636498679602129805)
              ·
                refine ⟨18385610113687004850798677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49028293636498679602129805 18385610113687004850798677)
                ·
                  refine ⟨215456368519769588095297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18385610113687004850798677 215456368519769588095297)
                  ·
                    rfl

theorem cell22_1888199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 8].length) (baseStart_1888199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888199 prefixEnd_1888199 := by exact prefixLift 1888199
  have htrace : WordTrace (prefixWord ++ tailWord_1888199) baseStart_1888199 baseEnd_1888199 := by
    simpa [prefixWord, tailWord_1888199, baseEnd_1888199] using wordTrace_append hprefix tailTrace_1888199
  have hstable : (prefixWord ++ tailWord_1888199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888199).length < 2 ^ (prefixWord ++ tailWord_1888199).sum := by decide
  have hdescent : baseEnd_1888199 < baseStart_1888199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888226 : List Nat := [3, 3, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1888226 : Nat := 118140960795 + 1888226 * 2 ^ 59
def prefixEnd_1888226 : Nat := 4983230072969 + 3 ^ 40 * 1888226 * 2
def baseEnd_1888226 : Nat := 646378348211089693860809

theorem tailTrace_1888226 : CollatzResearch.WordTrace tailWord_1888226 prefixEnd_1888226 646378348211089693860809 := by
  unfold tailWord_1888226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217315014321790042925133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45912840038191440114467021 17217315014321790042925133)
  ·
    refine ⟨6456493130370671266096925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17217315014321790042925133 6456493130370671266096925)
    ·
      refine ⟨2421184923889001724786347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6456493130370671266096925 2421184923889001724786347)
      ·
        refine ⟨3631777385833502587179521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421184923889001724786347 3631777385833502587179521)
        ·
          refine ⟨2723833039375126940384641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631777385833502587179521 2723833039375126940384641)
          ·
            refine ⟨2042874779531345205288481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2723833039375126940384641 2042874779531345205288481)
            ·
              refine ⟨1532156084648508903966361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042874779531345205288481 1532156084648508903966361)
              ·
                refine ⟨1149117063486381677974771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532156084648508903966361 1149117063486381677974771)
                ·
                  refine ⟨1723675595229572516962157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149117063486381677974771 1723675595229572516962157)
                  ·
                    refine ⟨646378348211089693860809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723675595229572516962157 646378348211089693860809)
                    ·
                      rfl

theorem cell22_1888226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1888226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888226 prefixEnd_1888226 := by exact prefixLift 1888226
  have htrace : WordTrace (prefixWord ++ tailWord_1888226) baseStart_1888226 baseEnd_1888226 := by
    simpa [prefixWord, tailWord_1888226, baseEnd_1888226] using wordTrace_append hprefix tailTrace_1888226
  have hstable : (prefixWord ++ tailWord_1888226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888226).length < 2 ^ (prefixWord ++ tailWord_1888226).sum := by decide
  have hdescent : baseEnd_1888226 < baseStart_1888226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888248 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 2, 3]
def baseStart_1888248 : Nat := 118140960795 + 1888248 * 2 ^ 59
def prefixEnd_1888248 : Nat := 4983230072969 + 3 ^ 40 * 1888248 * 2
def baseEnd_1888248 : Nat := 646385879260688969810741

theorem tailTrace_1888248 : CollatzResearch.WordTrace tailWord_1888248 prefixEnd_1888248 646385879260688969810741 := by
  unfold tailWord_1888248
  simp only [CollatzResearch.WordTrace]
  refine ⟨34435031231603728964500699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45913374975471638619334265 34435031231603728964500699)
  ·
    refine ⟨51652546847405593446751049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34435031231603728964500699 51652546847405593446751049)
    ·
      refine ⟨38739410135554195085063287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51652546847405593446751049 38739410135554195085063287)
      ·
        refine ⟨58109115203331292627594931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38739410135554195085063287 58109115203331292627594931)
        ·
          refine ⟨87163672804996938941392397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58109115203331292627594931 87163672804996938941392397)
          ·
            refine ⟨32686377301873852103022149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87163672804996938941392397 32686377301873852103022149)
            ·
              refine ⟨6128695744101347269316653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32686377301873852103022149 6128695744101347269316653)
              ·
                refine ⟨2298260904038005225993745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6128695744101347269316653 2298260904038005225993745)
                ·
                  refine ⟨1723695678028503919495309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298260904038005225993745 1723695678028503919495309)
                  ·
                    refine ⟨646385879260688969810741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723695678028503919495309 646385879260688969810741)
                    ·
                      rfl

theorem cell22_1888248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_1888248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888248 prefixEnd_1888248 := by exact prefixLift 1888248
  have htrace : WordTrace (prefixWord ++ tailWord_1888248) baseStart_1888248 baseEnd_1888248 := by
    simpa [prefixWord, tailWord_1888248, baseEnd_1888248] using wordTrace_append hprefix tailTrace_1888248
  have hstable : (prefixWord ++ tailWord_1888248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888248).length < 2 ^ (prefixWord ++ tailWord_1888248).sum := by decide
  have hdescent : baseEnd_1888248 < baseStart_1888248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888263 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1888263 : Nat := 118140960795 + 1888263 * 2 ^ 59
def prefixEnd_1888263 : Nat := 4983230072969 + 3 ^ 40 * 1888263 * 2
def baseEnd_1888263 : Nat := 646391014067233930685695

theorem tailTrace_1888263 : CollatzResearch.WordTrace tailWord_1888263 prefixEnd_1888263 646391014067233930685695 := by
  unfold tailWord_1888263
  simp only [CollatzResearch.WordTrace]
  refine ⟨68870609558153115490797443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45913739705435410327198295 68870609558153115490797443)
  ·
    refine ⟨103305914337229673236196165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68870609558153115490797443 103305914337229673236196165)
    ·
      refine ⟨19369858938230563731786781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103305914337229673236196165 19369858938230563731786781)
      ·
        refine ⟨7263697101836461399420043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19369858938230563731786781 7263697101836461399420043)
        ·
          refine ⟨10895545652754692099130065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7263697101836461399420043 10895545652754692099130065)
          ·
            refine ⟨8171659239566019074347549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10895545652754692099130065 8171659239566019074347549)
            ·
              refine ⟨3064372214837257152880331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8171659239566019074347549 3064372214837257152880331)
              ·
                refine ⟨4596558322255885729320497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064372214837257152880331 4596558322255885729320497)
                ·
                  refine ⟨3447418741691914296990373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596558322255885729320497 3447418741691914296990373)
                  ·
                    refine ⟨646391014067233930685695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447418741691914296990373 646391014067233930685695)
                    ·
                      rfl

theorem cell22_1888263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1888263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888263 prefixEnd_1888263 := by exact prefixLift 1888263
  have htrace : WordTrace (prefixWord ++ tailWord_1888263) baseStart_1888263 baseEnd_1888263 := by
    simpa [prefixWord, tailWord_1888263, baseEnd_1888263] using wordTrace_append hprefix tailTrace_1888263
  have hstable : (prefixWord ++ tailWord_1888263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888263).length < 2 ^ (prefixWord ++ tailWord_1888263).sum := by decide
  have hdescent : baseEnd_1888263 < baseStart_1888263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888269 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1888269 : Nat := 118140960795 + 1888269 * 2 ^ 59
def prefixEnd_1888269 : Nat := 4983230072969 + 3 ^ 40 * 1888269 * 2
def baseEnd_1888269 : Nat := 646393067989851915035677

theorem tailTrace_1888269 : CollatzResearch.WordTrace tailWord_1888269 prefixEnd_1888269 646393067989851915035677 := by
  unfold tailWord_1888269
  simp only [CollatzResearch.WordTrace]
  refine ⟨68870828396131378515515861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45913885597420919010343907 68870828396131378515515861)
  ·
    refine ⟨1614160040534329183957403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 68870828396131378515515861 1614160040534329183957403)
    ·
      refine ⟨2421240060801493775936105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614160040534329183957403 2421240060801493775936105)
      ·
        refine ⟨1815930045601120331952079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2421240060801493775936105 1815930045601120331952079)
        ·
          refine ⟨2723895068401680497928119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815930045601120331952079 2723895068401680497928119)
          ·
            refine ⟨4085842602602520746892179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723895068401680497928119 4085842602602520746892179)
            ·
              refine ⟨6128763903903781120338269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085842602602520746892179 6128763903903781120338269)
              ·
                refine ⟨2298286463963917920126851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6128763903903781120338269 2298286463963917920126851)
                ·
                  refine ⟨3447429695945876880190277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298286463963917920126851 3447429695945876880190277)
                  ·
                    refine ⟨646393067989851915035677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447429695945876880190277 646393067989851915035677)
                    ·
                      rfl

theorem cell22_1888269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1888269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888269 prefixEnd_1888269 := by exact prefixLift 1888269
  have htrace : WordTrace (prefixWord ++ tailWord_1888269) baseStart_1888269 baseEnd_1888269 := by
    simpa [prefixWord, tailWord_1888269, baseEnd_1888269] using wordTrace_append hprefix tailTrace_1888269
  have hstable : (prefixWord ++ tailWord_1888269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888269).length < 2 ^ (prefixWord ++ tailWord_1888269).sum := by decide
  have hdescent : baseEnd_1888269 < baseStart_1888269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888293 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_1888293 : Nat := 118140960795 + 1888293 * 2 ^ 59
def prefixEnd_1888293 : Nat := 4983230072969 + 3 ^ 40 * 1888293 * 2
def baseEnd_1888293 : Nat := 646401283680323852435603

theorem tailTrace_1888293 : CollatzResearch.WordTrace tailWord_1888293 prefixEnd_1888293 646401283680323852435603 := by
  unfold tailWord_1888293
  simp only [CollatzResearch.WordTrace]
  refine ⟨68871703748044430614389533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45914469165362953742926355 68871703748044430614389533)
  ·
    refine ⟨25826888905516661480396075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68871703748044430614389533 25826888905516661480396075)
    ·
      refine ⟨38740333358274992220594113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25826888905516661480396075 38740333358274992220594113)
      ·
        refine ⟨29055250018706244165445585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38740333358274992220594113 29055250018706244165445585)
        ·
          refine ⟨21791437514029683124084189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29055250018706244165445585 21791437514029683124084189)
          ·
            refine ⟨8171789067761131171531571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21791437514029683124084189 8171789067761131171531571)
            ·
              refine ⟨12257683601641696757297357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171789067761131171531571 12257683601641696757297357)
              ·
                refine ⟨4596631350615636283986509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12257683601641696757297357 4596631350615636283986509)
                ·
                  refine ⟨1723736756480863606494941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4596631350615636283986509 1723736756480863606494941)
                  ·
                    refine ⟨646401283680323852435603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723736756480863606494941 646401283680323852435603)
                    ·
                      rfl

theorem cell22_1888293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_1888293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888293 prefixEnd_1888293 := by exact prefixLift 1888293
  have htrace : WordTrace (prefixWord ++ tailWord_1888293) baseStart_1888293 baseEnd_1888293 := by
    simpa [prefixWord, tailWord_1888293, baseEnd_1888293] using wordTrace_append hprefix tailTrace_1888293
  have hstable : (prefixWord ++ tailWord_1888293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888293).length < 2 ^ (prefixWord ++ tailWord_1888293).sum := by decide
  have hdescent : baseEnd_1888293 < baseStart_1888293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888310 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1888310 : Nat := 118140960795 + 1888310 * 2 ^ 59
def prefixEnd_1888310 : Nat := 4983230072969 + 3 ^ 40 * 1888310 * 2
def baseEnd_1888310 : Nat := 646407103127741474760551

theorem tailTrace_1888310 : CollatzResearch.WordTrace tailWord_1888310 prefixEnd_1888310 646407103127741474760551 := by
  unfold tailWord_1888310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304520236811427657359899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45914882525988561678505589 4304520236811427657359899)
  ·
    refine ⟨6456780355217141486039849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4304520236811427657359899 6456780355217141486039849)
    ·
      refine ⟨4842585266412856114529887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6456780355217141486039849 4842585266412856114529887)
      ·
        refine ⟨7263877899619284171794831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4842585266412856114529887 7263877899619284171794831)
        ·
          refine ⟨10895816849428926257692247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7263877899619284171794831 10895816849428926257692247)
          ·
            refine ⟨16343725274143389386538371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895816849428926257692247 16343725274143389386538371)
            ·
              refine ⟨24515587911215084079807557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16343725274143389386538371 24515587911215084079807557)
              ·
                refine ⟨4596672733352828264963917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24515587911215084079807557 4596672733352828264963917)
                ·
                  refine ⟨1723752275007310599361469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4596672733352828264963917 1723752275007310599361469)
                  ·
                    refine ⟨646407103127741474760551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723752275007310599361469 646407103127741474760551)
                    ·
                      rfl

theorem cell22_1888310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1888310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888310 prefixEnd_1888310 := by exact prefixLift 1888310
  have htrace : WordTrace (prefixWord ++ tailWord_1888310) baseStart_1888310 baseEnd_1888310 := by
    simpa [prefixWord, tailWord_1888310, baseEnd_1888310] using wordTrace_append hprefix tailTrace_1888310
  have hstable : (prefixWord ++ tailWord_1888310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888310).length < 2 ^ (prefixWord ++ tailWord_1888310).sum := by decide
  have hdescent : baseEnd_1888310 < baseStart_1888310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888336 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_1888336 : Nat := 118140960795 + 1888336 * 2 ^ 59
def prefixEnd_1888336 : Nat := 4983230072969 + 3 ^ 40 * 1888336 * 2
def baseEnd_1888336 : Nat := 646416003459086073610471

theorem tailTrace_1888336 : CollatzResearch.WordTrace tailWord_1888336 prefixEnd_1888336 646416003459086073610471 := by
  unfold tailWord_1888336
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436636043444324479102431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45915514724592432638803241 34436636043444324479102431)
  ·
    refine ⟨51654954065166486718653647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34436636043444324479102431 51654954065166486718653647)
    ·
      refine ⟨77482431097749730077980471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51654954065166486718653647 77482431097749730077980471)
      ·
        refine ⟨116223646646624595116970707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77482431097749730077980471 116223646646624595116970707)
        ·
          refine ⟨174335469969936892675456061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116223646646624595116970707 174335469969936892675456061)
          ·
            refine ⟨65375801238726334753296023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174335469969936892675456061 65375801238726334753296023)
            ·
              refine ⟨98063701858089502129944035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65375801238726334753296023 98063701858089502129944035)
              ·
                refine ⟨147095552787134253194916053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98063701858089502129944035 147095552787134253194916053)
                ·
                  refine ⟨3447552018448459059255845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 147095552787134253194916053 3447552018448459059255845)
                  ·
                    refine ⟨646416003459086073610471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447552018448459059255845 646416003459086073610471)
                    ·
                      rfl

theorem cell22_1888336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_1888336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888336 prefixEnd_1888336 := by exact prefixLift 1888336
  have htrace : WordTrace (prefixWord ++ tailWord_1888336) baseStart_1888336 baseEnd_1888336 := by
    simpa [prefixWord, tailWord_1888336, baseEnd_1888336] using wordTrace_append hprefix tailTrace_1888336
  have hstable : (prefixWord ++ tailWord_1888336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888336).length < 2 ^ (prefixWord ++ tailWord_1888336).sum := by decide
  have hdescent : baseEnd_1888336 < baseStart_1888336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888351 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 6]
def baseStart_1888351 : Nat := 118140960795 + 1888351 * 2 ^ 59
def prefixEnd_1888351 : Nat := 4983230072969 + 3 ^ 40 * 1888351 * 2
def baseEnd_1888351 : Nat := 215473712755210344828475

theorem tailTrace_1888351 : CollatzResearch.WordTrace tailWord_1888351 prefixEnd_1888351 215473712755210344828475 := by
  unfold tailWord_1888351
  simp only [CollatzResearch.WordTrace]
  refine ⟨68873819181834306520000907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45915879454556204346667271 68873819181834306520000907)
  ·
    refine ⟨103310728772751459780001361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68873819181834306520000907 103310728772751459780001361)
    ·
      refine ⟨77483046579563594835001021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103310728772751459780001361 77483046579563594835001021)
      ·
        refine ⟨29056142467336348063125383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77483046579563594835001021 29056142467336348063125383)
        ·
          refine ⟨43584213701004522094688075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29056142467336348063125383 43584213701004522094688075)
          ·
            refine ⟨65376320551506783142032113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43584213701004522094688075 65376320551506783142032113)
            ·
              refine ⟨49032240413630087356524085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65376320551506783142032113 49032240413630087356524085)
              ·
                refine ⟨4596772538777820689674133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49032240413630087356524085 4596772538777820689674133)
                ·
                  refine ⟨215473712755210344828475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4596772538777820689674133 215473712755210344828475)
                  ·
                    rfl

theorem cell22_1888351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 6].length) (baseStart_1888351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888351 prefixEnd_1888351 := by exact prefixLift 1888351
  have htrace : WordTrace (prefixWord ++ tailWord_1888351) baseStart_1888351 baseEnd_1888351 := by
    simpa [prefixWord, tailWord_1888351, baseEnd_1888351] using wordTrace_append hprefix tailTrace_1888351
  have hstable : (prefixWord ++ tailWord_1888351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888351).length < 2 ^ (prefixWord ++ tailWord_1888351).sum := by decide
  have hdescent : baseEnd_1888351 < baseStart_1888351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888370 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1888370 : Nat := 118140960795 + 1888370 * 2 ^ 59
def prefixEnd_1888370 : Nat := 4983230072969 + 3 ^ 40 * 1888370 * 2
def baseEnd_1888370 : Nat := 646427642353921318260367

theorem tailTrace_1888370 : CollatzResearch.WordTrace tailWord_1888370 prefixEnd_1888370 646427642353921318260367 := by
  unfold tailWord_1888370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218628042191368191235641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45916341445843648509961709 17218628042191368191235641)
  ·
    refine ⟨12913971031643526143426731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17218628042191368191235641 12913971031643526143426731)
    ·
      refine ⟨19370956547465289215140097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12913971031643526143426731 19370956547465289215140097)
      ·
        refine ⟨14528217410598966911355073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19370956547465289215140097 14528217410598966911355073)
        ·
          refine ⟨10896163057949225183516305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14528217410598966911355073 10896163057949225183516305)
          ·
            refine ⟨8172122293461918887637229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10896163057949225183516305 8172122293461918887637229)
            ·
              refine ⟨3064545860048219582863961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8172122293461918887637229 3064545860048219582863961)
              ·
                refine ⟨2298409395036164687147971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064545860048219582863961 2298409395036164687147971)
                ·
                  refine ⟨3447614092554247030721957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298409395036164687147971 3447614092554247030721957)
                  ·
                    refine ⟨646427642353921318260367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447614092554247030721957 646427642353921318260367)
                    ·
                      rfl

theorem cell22_1888370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1888370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888370 prefixEnd_1888370 := by exact prefixLift 1888370
  have htrace : WordTrace (prefixWord ++ tailWord_1888370) baseStart_1888370 baseEnd_1888370 := by
    simpa [prefixWord, tailWord_1888370, baseEnd_1888370] using wordTrace_append hprefix tailTrace_1888370
  have hstable : (prefixWord ++ tailWord_1888370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888370).length < 2 ^ (prefixWord ++ tailWord_1888370).sum := by decide
  have hdescent : baseEnd_1888370 < baseStart_1888370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888400 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 2, 3]
def baseStart_1888400 : Nat := 118140960795 + 1888400 * 2 ^ 59
def prefixEnd_1888400 : Nat := 4983230072969 + 3 ^ 40 * 1888400 * 2
def baseEnd_1888400 : Nat := 646437911967011240010275

theorem tailTrace_1888400 : CollatzResearch.WordTrace tailWord_1888400 prefixEnd_1888400 646437911967011240010275 := by
  unfold tailWord_1888400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34437803179328393944267327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45917070905771191925689769 34437803179328393944267327)
  ·
    refine ⟨51656704768992590916400991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34437803179328393944267327 51656704768992590916400991)
    ·
      refine ⟨77485057153488886374601487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51656704768992590916400991 77485057153488886374601487)
      ·
        refine ⟨116227585730233329561902231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77485057153488886374601487 116227585730233329561902231)
        ·
          refine ⟨174341378595349994342853347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116227585730233329561902231 174341378595349994342853347)
          ·
            refine ⟨261512067893024991514280021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174341378595349994342853347 261512067893024991514280021)
            ·
              refine ⟨3064594545621386619307969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 261512067893024991514280021 3064594545621386619307969)
              ·
                refine ⟨2298445909216039964480977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064594545621386619307969 2298445909216039964480977)
                ·
                  refine ⟨1723834431912029973360733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298445909216039964480977 1723834431912029973360733)
                  ·
                    refine ⟨646437911967011240010275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723834431912029973360733 646437911967011240010275)
                    ·
                      rfl

theorem cell22_1888400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_1888400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888400 prefixEnd_1888400 := by exact prefixLift 1888400
  have htrace : WordTrace (prefixWord ++ tailWord_1888400) baseStart_1888400 baseEnd_1888400 := by
    simpa [prefixWord, tailWord_1888400, baseEnd_1888400] using wordTrace_append hprefix tailTrace_1888400
  have hstable : (prefixWord ++ tailWord_1888400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888400).length < 2 ^ (prefixWord ++ tailWord_1888400).sum := by decide
  have hdescent : baseEnd_1888400 < baseStart_1888400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888406 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1888406 : Nat := 118140960795 + 1888406 * 2 ^ 59
def prefixEnd_1888406 : Nat := 4983230072969 + 3 ^ 40 * 1888406 * 2
def baseEnd_1888406 : Nat := 646439965889629224360257

theorem tailTrace_1888406 : CollatzResearch.WordTrace tailWord_1888406 prefixEnd_1888406 646439965889629224360257 := by
  unfold tailWord_1888406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304739074789690682078317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45917216797756700608835381 4304739074789690682078317)
  ·
    refine ⟨1614277153046134005779369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4304739074789690682078317 1614277153046134005779369)
    ·
      refine ⟨1210707864784600504334527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1614277153046134005779369 1210707864784600504334527)
      ·
        refine ⟨1816061797176900756501791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210707864784600504334527 1816061797176900756501791)
        ·
          refine ⟨2724092695765351134752687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816061797176900756501791 2724092695765351134752687)
          ·
            refine ⟨4086139043648026702129031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724092695765351134752687 4086139043648026702129031)
            ·
              refine ⟨6129208565472040053193547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086139043648026702129031 6129208565472040053193547)
              ·
                refine ⟨9193812848208060079790321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129208565472040053193547 9193812848208060079790321)
                ·
                  refine ⟨6895359636156045059842741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9193812848208060079790321 6895359636156045059842741)
                  ·
                    refine ⟨646439965889629224360257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6895359636156045059842741 646439965889629224360257)
                    ·
                      rfl

theorem cell22_1888406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1888406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888406 prefixEnd_1888406 := by exact prefixLift 1888406
  have htrace : WordTrace (prefixWord ++ tailWord_1888406) baseStart_1888406 baseEnd_1888406 := by
    simpa [prefixWord, tailWord_1888406, baseEnd_1888406] using wordTrace_append hprefix tailTrace_1888406
  have hstable : (prefixWord ++ tailWord_1888406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888406).length < 2 ^ (prefixWord ++ tailWord_1888406).sum := by decide
  have hdescent : baseEnd_1888406 < baseStart_1888406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888413 : List Nat := [1, 4, 2, 1, 1, 3, 3, 7]
def baseStart_1888413 : Nat := 118140960795 + 1888413 * 2 ^ 59
def prefixEnd_1888413 : Nat := 4983230072969 + 3 ^ 40 * 1888413 * 2
def baseEnd_1888413 : Nat := 71826929125853726603915

theorem tailTrace_1888413 : CollatzResearch.WordTrace tailWord_1888413 prefixEnd_1888413 71826929125853726603915 := by
  unfold tailWord_1888413
  simp only [CollatzResearch.WordTrace]
  refine ⟨68876080507609691108757893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45917387005073127405838595 68876080507609691108757893)
  ·
    refine ⟨12914265095176817082892105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68876080507609691108757893 12914265095176817082892105)
    ·
      refine ⟨9685698821382612812169079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12914265095176817082892105 9685698821382612812169079)
      ·
        refine ⟨14528548232073919218253619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685698821382612812169079 14528548232073919218253619)
        ·
          refine ⟨21792822348110878827380429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14528548232073919218253619 21792822348110878827380429)
          ·
            refine ⟨8172308380541579560267661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21792822348110878827380429 8172308380541579560267661)
            ·
              refine ⟨3064615642703092335100373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8172308380541579560267661 3064615642703092335100373)
              ·
                refine ⟨71826929125853726603915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3064615642703092335100373 71826929125853726603915)
                ·
                  rfl

theorem cell22_1888413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 7].length) (baseStart_1888413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888413 prefixEnd_1888413 := by exact prefixLift 1888413
  have htrace : WordTrace (prefixWord ++ tailWord_1888413) baseStart_1888413 baseEnd_1888413 := by
    simpa [prefixWord, tailWord_1888413, baseEnd_1888413] using wordTrace_append hprefix tailTrace_1888413
  have hstable : (prefixWord ++ tailWord_1888413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888413).length < 2 ^ (prefixWord ++ tailWord_1888413).sum := by decide
  have hdescent : baseEnd_1888413 < baseStart_1888413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888458 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_1888458 : Nat := 118140960795 + 1888458 * 2 ^ 59
def prefixEnd_1888458 : Nat := 4983230072969 + 3 ^ 40 * 1888458 * 2
def baseEnd_1888458 : Nat := 215485922184106140686699

theorem tailTrace_1888458 : CollatzResearch.WordTrace tailWord_1888458 prefixEnd_1888458 215485922184106140686699 := by
  unfold tailWord_1888458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219430448111665948536507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45918481194964442529430685 17219430448111665948536507)
  ·
    refine ⟨25829145672167498922804761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17219430448111665948536507 25829145672167498922804761)
    ·
      refine ⟨19371859254125624192103571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25829145672167498922804761 19371859254125624192103571)
      ·
        refine ⟨29057788881188436288155357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19371859254125624192103571 29057788881188436288155357)
        ·
          refine ⟨10896670830445663608058259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29057788881188436288155357 10896670830445663608058259)
          ·
            refine ⟨16345006245668495412087389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896670830445663608058259 16345006245668495412087389)
            ·
              refine ⟨6129377342125685779532771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16345006245668495412087389 6129377342125685779532771)
              ·
                refine ⟨9194066013188528669299157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129377342125685779532771 9194066013188528669299157)
                ·
                  refine ⟨215485922184106140686699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9194066013188528669299157 215485922184106140686699)
                  ·
                    rfl

theorem cell22_1888458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_1888458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888458 prefixEnd_1888458 := by exact prefixLift 1888458
  have htrace : WordTrace (prefixWord ++ tailWord_1888458) baseStart_1888458 baseEnd_1888458 := by
    simpa [prefixWord, tailWord_1888458, baseEnd_1888458] using wordTrace_append hprefix tailTrace_1888458
  have hstable : (prefixWord ++ tailWord_1888458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888458).length < 2 ^ (prefixWord ++ tailWord_1888458).sum := by decide
  have hdescent : baseEnd_1888458 < baseStart_1888458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888462 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_1888462 : Nat := 118140960795 + 1888462 * 2 ^ 59
def prefixEnd_1888462 : Nat := 4983230072969 + 3 ^ 40 * 1888462 * 2
def baseEnd_1888462 : Nat := 646459135834063744960085

theorem tailTrace_1888462 : CollatzResearch.WordTrace tailWord_1888462 prefixEnd_1888462 646459135834063744960085 := by
  unfold tailWord_1888462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8609733460554021559661455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45918578456288114984861093 8609733460554021559661455)
  ·
    refine ⟨12914600190831032339492183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8609733460554021559661455 12914600190831032339492183)
    ·
      refine ⟨19371900286246548509238275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12914600190831032339492183 19371900286246548509238275)
      ·
        refine ⟨29057850429369822763857413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19371900286246548509238275 29057850429369822763857413)
        ·
          refine ⟨5448346955506841768223265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29057850429369822763857413 5448346955506841768223265)
          ·
            refine ⟨4086260216630131326167449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5448346955506841768223265 4086260216630131326167449)
            ·
              refine ⟨3064695162472598494625587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086260216630131326167449 3064695162472598494625587)
              ·
                refine ⟨4597042743708897741938381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064695162472598494625587 4597042743708897741938381)
                ·
                  refine ⟨1723891028890836653226893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4597042743708897741938381 1723891028890836653226893)
                  ·
                    refine ⟨646459135834063744960085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723891028890836653226893 646459135834063744960085)
                    ·
                      rfl

theorem cell22_1888462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_1888462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888462 prefixEnd_1888462 := by exact prefixLift 1888462
  have htrace : WordTrace (prefixWord ++ tailWord_1888462) baseStart_1888462 baseEnd_1888462 := by
    simpa [prefixWord, tailWord_1888462, baseEnd_1888462] using wordTrace_append hprefix tailTrace_1888462
  have hstable : (prefixWord ++ tailWord_1888462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888462).length < 2 ^ (prefixWord ++ tailWord_1888462).sum := by decide
  have hdescent : baseEnd_1888462 < baseStart_1888462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888473 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_1888473 : Nat := 118140960795 + 1888473 * 2 ^ 59
def prefixEnd_1888473 : Nat := 4983230072969 + 3 ^ 40 * 1888473 * 2
def baseEnd_1888473 : Nat := 646462901358863382935051

theorem tailTrace_1888473 : CollatzResearch.WordTrace tailWord_1888473 prefixEnd_1888473 646462901358863382935051 := by
  unfold tailWord_1888473
  simp only [CollatzResearch.WordTrace]
  refine ⟨68878268887392321355942073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45918845924928214237294715 68878268887392321355942073)
  ·
    refine ⟨51658701665544241016956555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68878268887392321355942073 51658701665544241016956555)
    ·
      refine ⟨77488052498316361525434833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51658701665544241016956555 77488052498316361525434833)
      ·
        refine ⟨58116039373737271144076125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77488052498316361525434833 58116039373737271144076125)
        ·
          refine ⟨21793514765151476679028547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58116039373737271144076125 21793514765151476679028547)
          ·
            refine ⟨32690272147727215018542821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21793514765151476679028547 32690272147727215018542821)
            ·
              refine ⟨6129426027698852815976779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32690272147727215018542821 6129426027698852815976779)
              ·
                refine ⟨9194139041548279223965169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129426027698852815976779 9194139041548279223965169)
                ·
                  refine ⟨6895604281161209417973877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9194139041548279223965169 6895604281161209417973877)
                  ·
                    refine ⟨646462901358863382935051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6895604281161209417973877 646462901358863382935051)
                    ·
                      rfl

theorem cell22_1888473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_1888473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888473 prefixEnd_1888473 := by exact prefixLift 1888473
  have htrace : WordTrace (prefixWord ++ tailWord_1888473) baseStart_1888473 baseEnd_1888473 := by
    simpa [prefixWord, tailWord_1888473, baseEnd_1888473] using wordTrace_append hprefix tailTrace_1888473
  have hstable : (prefixWord ++ tailWord_1888473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888473).length < 2 ^ (prefixWord ++ tailWord_1888473).sum := by decide
  have hdescent : baseEnd_1888473 < baseStart_1888473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888520 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 6]
def baseStart_1888520 : Nat := 118140960795 + 1888520 * 2 ^ 59
def prefixEnd_1888520 : Nat := 4983230072969 + 3 ^ 40 * 1888520 * 2
def baseEnd_1888520 : Nat := 215492996806456975669969

theorem tailTrace_1888520 : CollatzResearch.WordTrace tailWord_1888520 prefixEnd_1888520 215492996806456975669969 := by
  unfold tailWord_1888520
  simp only [CollatzResearch.WordTrace]
  refine ⟨34439991559111024191451507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45919988745481365588602009 34439991559111024191451507)
  ·
    refine ⟨51659987338666536287177261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34439991559111024191451507 51659987338666536287177261)
    ·
      refine ⟨19372495251999951107691473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51659987338666536287177261 19372495251999951107691473)
      ·
        refine ⟨14529371438999963330768605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19372495251999951107691473 14529371438999963330768605)
        ·
          refine ⟨5448514289624986249038227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14529371438999963330768605 5448514289624986249038227)
          ·
            refine ⟨8172771434437479373557341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448514289624986249038227 8172771434437479373557341)
            ·
              refine ⟨3064789287914054765084003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8172771434437479373557341 3064789287914054765084003)
              ·
                refine ⟨4597183931871082147626005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064789287914054765084003 4597183931871082147626005)
                ·
                  refine ⟨215492996806456975669969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4597183931871082147626005 215492996806456975669969)
                  ·
                    rfl

theorem cell22_1888520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_1888520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888520 prefixEnd_1888520 := by exact prefixLift 1888520
  have htrace : WordTrace (prefixWord ++ tailWord_1888520) baseStart_1888520 baseEnd_1888520 := by
    simpa [prefixWord, tailWord_1888520, baseEnd_1888520] using wordTrace_append hprefix tailTrace_1888520
  have hstable : (prefixWord ++ tailWord_1888520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888520).length < 2 ^ (prefixWord ++ tailWord_1888520).sum := by decide
  have hdescent : baseEnd_1888520 < baseStart_1888520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888533 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1888533 : Nat := 118140960795 + 1888533 * 2 ^ 59
def prefixEnd_1888533 : Nat := 4983230072969 + 3 ^ 40 * 1888533 * 2
def baseEnd_1888533 : Nat := 646483440585043226434867

theorem tailTrace_1888533 : CollatzResearch.WordTrace tailWord_1888533 prefixEnd_1888533 646483440585043226434867 := by
  unfold tailWord_1888533
  simp only [CollatzResearch.WordTrace]
  refine ⟨68880457267174951603126253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45920304844783301068750835 68880457267174951603126253)
  ·
    refine ⟨25830171475190606851172345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68880457267174951603126253 25830171475190606851172345)
    ·
      refine ⟨19372628606392955138379259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25830171475190606851172345 19372628606392955138379259)
      ·
        refine ⟨29058942909589432707568889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19372628606392955138379259 29058942909589432707568889)
        ·
          refine ⟨21794207182192074530676667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29058942909589432707568889 21794207182192074530676667)
          ·
            refine ⟨32691310773288111796015001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21794207182192074530676667 32691310773288111796015001)
            ·
              refine ⟨24518483079966083847011251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32691310773288111796015001 24518483079966083847011251)
              ·
                refine ⟨36777724619949125770516877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24518483079966083847011251 36777724619949125770516877)
                ·
                  refine ⟨13791646732480922163943829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36777724619949125770516877 13791646732480922163943829)
                  ·
                    refine ⟨646483440585043226434867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13791646732480922163943829 646483440585043226434867)
                    ·
                      rfl

theorem cell22_1888533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1888533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888533 prefixEnd_1888533 := by exact prefixLift 1888533
  have htrace : WordTrace (prefixWord ++ tailWord_1888533) baseStart_1888533 baseEnd_1888533 := by
    simpa [prefixWord, tailWord_1888533, baseEnd_1888533] using wordTrace_append hprefix tailTrace_1888533
  have hstable : (prefixWord ++ tailWord_1888533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888533).length < 2 ^ (prefixWord ++ tailWord_1888533).sum := by decide
  have hdescent : baseEnd_1888533 < baseStart_1888533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888552 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1888552 : Nat := 118140960795 + 1888552 * 2 ^ 59
def prefixEnd_1888552 : Nat := 4983230072969 + 3 ^ 40 * 1888552 * 2
def baseEnd_1888552 : Nat := 646489944673333510209809

theorem tailTrace_1888552 : CollatzResearch.WordTrace tailWord_1888552 prefixEnd_1888552 646489944673333510209809 := by
  unfold tailWord_1888552
  simp only [CollatzResearch.WordTrace]
  refine ⟨34440575127053058924033955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45920766836070745232045273 34440575127053058924033955)
  ·
    refine ⟨51660862690579588386050933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34440575127053058924033955 51660862690579588386050933)
    ·
      refine ⟨4843205877241836411192275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51660862690579588386050933 4843205877241836411192275)
      ·
        refine ⟨7264808815862754616788413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843205877241836411192275 7264808815862754616788413)
        ·
          refine ⟨2724303305948532981295655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7264808815862754616788413 2724303305948532981295655)
          ·
            refine ⟨4086454958922799471943483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724303305948532981295655 4086454958922799471943483)
            ·
              refine ⟨6129682438384199207915225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086454958922799471943483 6129682438384199207915225)
              ·
                refine ⟨4597261828788149405936419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129682438384199207915225 4597261828788149405936419)
                ·
                  refine ⟨6895892743182224108904629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597261828788149405936419 6895892743182224108904629)
                  ·
                    refine ⟨646489944673333510209809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6895892743182224108904629 646489944673333510209809)
                    ·
                      rfl

theorem cell22_1888552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1888552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888552 prefixEnd_1888552 := by exact prefixLift 1888552
  have htrace : WordTrace (prefixWord ++ tailWord_1888552) baseStart_1888552 baseEnd_1888552 := by
    simpa [prefixWord, tailWord_1888552, baseEnd_1888552] using wordTrace_append hprefix tailTrace_1888552
  have hstable : (prefixWord ++ tailWord_1888552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888552).length < 2 ^ (prefixWord ++ tailWord_1888552).sum := by decide
  have hdescent : baseEnd_1888552 < baseStart_1888552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888569 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 2, 3]
def baseStart_1888569 : Nat := 118140960795 + 1888569 * 2 ^ 59
def prefixEnd_1888569 : Nat := 4983230072969 + 3 ^ 40 * 1888569 * 2
def baseEnd_1888569 : Nat := 646495764120751132534757

theorem tailTrace_1888569 : CollatzResearch.WordTrace tailWord_1888569 prefixEnd_1888569 646495764120751132534757 := by
  unfold tailWord_1888569
  simp only [CollatzResearch.WordTrace]
  refine ⟨68881770295044529751436761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45921180196696353167624507 68881770295044529751436761)
  ·
    refine ⟨51661327721283397313577571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68881770295044529751436761 51661327721283397313577571)
    ·
      refine ⟨77491991581925095970366357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51661327721283397313577571 77491991581925095970366357)
      ·
        refine ⟨3632437105402738873610923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77491991581925095970366357 3632437105402738873610923)
        ·
          refine ⟨5448655658104108310416385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632437105402738873610923 5448655658104108310416385)
          ·
            refine ⟨4086491743578081232812289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5448655658104108310416385 4086491743578081232812289)
            ·
              refine ⟨3064868807683560924609217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086491743578081232812289 3064868807683560924609217)
              ·
                refine ⟨2298651605762670693456913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064868807683560924609217 2298651605762670693456913)
                ·
                  refine ⟨1723988704322003020092685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298651605762670693456913 1723988704322003020092685)
                  ·
                    refine ⟨646495764120751132534757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1723988704322003020092685 646495764120751132534757)
                    ·
                      rfl

theorem cell22_1888569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_1888569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888569 prefixEnd_1888569 := by exact prefixLift 1888569
  have htrace : WordTrace (prefixWord ++ tailWord_1888569) baseStart_1888569 baseEnd_1888569 := by
    simpa [prefixWord, tailWord_1888569, baseEnd_1888569] using wordTrace_append hprefix tailTrace_1888569
  have hstable : (prefixWord ++ tailWord_1888569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888569).length < 2 ^ (prefixWord ++ tailWord_1888569).sum := by decide
  have hdescent : baseEnd_1888569 < baseStart_1888569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888682 : List Nat := [3, 1, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1888682 : Nat := 118140960795 + 1888682 * 2 ^ 59
def prefixEnd_1888682 : Nat := 4983230072969 + 3 ^ 40 * 1888682 * 2
def baseEnd_1888682 : Nat := 646534446330056504459411

theorem tailTrace_1888682 : CollatzResearch.WordTrace tailWord_1888682 prefixEnd_1888682 646534446330056504459411 := by
  unfold tailWord_1888682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221472935908787512575075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45923927829090100033533533 17221472935908787512575075)
  ·
    refine ⟨25832209403863181268862613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17221472935908787512575075 25832209403863181268862613)
    ·
      refine ⟨1210884815806086621977935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25832209403863181268862613 1210884815806086621977935)
      ·
        refine ⟨1816327223709129932966903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210884815806086621977935 1816327223709129932966903)
        ·
          refine ⟨2724490835563694899450355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816327223709129932966903 2724490835563694899450355)
          ·
            refine ⟨4086736253345542349175533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724490835563694899450355 4086736253345542349175533)
            ·
              refine ⟨1532526095004578380940825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4086736253345542349175533 1532526095004578380940825)
              ·
                refine ⟨1149394571253433785705619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532526095004578380940825 1149394571253433785705619)
                ·
                  refine ⟨1724091856880150678558429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149394571253433785705619 1724091856880150678558429)
                  ·
                    refine ⟨646534446330056504459411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724091856880150678558429 646534446330056504459411)
                    ·
                      rfl

theorem cell22_1888682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1888682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888682 prefixEnd_1888682 := by exact prefixLift 1888682
  have htrace : WordTrace (prefixWord ++ tailWord_1888682) baseStart_1888682 baseEnd_1888682 := by
    simpa [prefixWord, tailWord_1888682, baseEnd_1888682] using wordTrace_append hprefix tailTrace_1888682
  have hstable : (prefixWord ++ tailWord_1888682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888682).length < 2 ^ (prefixWord ++ tailWord_1888682).sum := by decide
  have hdescent : baseEnd_1888682 < baseStart_1888682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888708 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1888708 : Nat := 118140960795 + 1888708 * 2 ^ 59
def prefixEnd_1888708 : Nat := 4983230072969 + 3 ^ 40 * 1888708 * 2
def baseEnd_1888708 : Nat := 646543346661401103309331

theorem tailTrace_1888708 : CollatzResearch.WordTrace tailWord_1888708 prefixEnd_1888708 646543346661401103309331 := by
  unfold tailWord_1888708
  simp only [CollatzResearch.WordTrace]
  refine ⟨34443420020770478245373389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45924560027693970993831185 34443420020770478245373389)
  ·
    refine ⟨12916282507788929342015021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34443420020770478245373389 12916282507788929342015021)
    ·
      refine ⟨4843605940420848503255633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12916282507788929342015021 4843605940420848503255633)
      ·
        refine ⟨3632704455315636377441725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4843605940420848503255633 3632704455315636377441725)
        ·
          refine ⟨1362264170743363641540647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3632704455315636377441725 1362264170743363641540647)
          ·
            refine ⟨2043396256115045462310971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362264170743363641540647 2043396256115045462310971)
            ·
              refine ⟨3065094384172568193466457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043396256115045462310971 3065094384172568193466457)
              ·
                refine ⟨2298820788129426145099843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065094384172568193466457 2298820788129426145099843)
                ·
                  refine ⟨3448231182194139217649765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298820788129426145099843 3448231182194139217649765)
                  ·
                    refine ⟨646543346661401103309331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3448231182194139217649765 646543346661401103309331)
                    ·
                      rfl

theorem cell22_1888708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1888708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888708 prefixEnd_1888708 := by exact prefixLift 1888708
  have htrace : WordTrace (prefixWord ++ tailWord_1888708) baseStart_1888708 baseEnd_1888708 := by
    simpa [prefixWord, tailWord_1888708, baseEnd_1888708] using wordTrace_append hprefix tailTrace_1888708
  have hstable : (prefixWord ++ tailWord_1888708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888708).length < 2 ^ (prefixWord ++ tailWord_1888708).sum := by decide
  have hdescent : baseEnd_1888708 < baseStart_1888708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888837 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1888837 : Nat := 118140960795 + 1888837 * 2 ^ 59
def prefixEnd_1888837 : Nat := 4983230072969 + 3 ^ 40 * 1888837 * 2
def baseEnd_1888837 : Nat := 646587505997687766833935

theorem tailTrace_1888837 : CollatzResearch.WordTrace tailWord_1888837 prefixEnd_1888837 646587505997687766833935 := by
  unfold tailWord_1888837
  simp only [CollatzResearch.WordTrace]
  refine ⟨68891545058073611522192765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45927696705382407681461843 68891545058073611522192765)
  ·
    refine ⟨25834329396777604320822287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68891545058073611522192765 25834329396777604320822287)
    ·
      refine ⟨38751494095166406481233431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25834329396777604320822287 38751494095166406481233431)
      ·
        refine ⟨58127241142749609721850147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38751494095166406481233431 58127241142749609721850147)
        ·
          refine ⟨87190861714124414582775221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58127241142749609721850147 87190861714124414582775221)
          ·
            refine ⟨8174143285699163867135177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87190861714124414582775221 8174143285699163867135177)
            ·
              refine ⟨6130607464274372900351383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8174143285699163867135177 6130607464274372900351383)
              ·
                refine ⟨9195911196411559350527075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130607464274372900351383 9195911196411559350527075)
                ·
                  refine ⟨13793866794617339025790613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9195911196411559350527075 13793866794617339025790613)
                  ·
                    refine ⟨646587505997687766833935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13793866794617339025790613 646587505997687766833935)
                    ·
                      rfl

theorem cell22_1888837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1888837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888837 prefixEnd_1888837 := by exact prefixLift 1888837
  have htrace : WordTrace (prefixWord ++ tailWord_1888837) baseStart_1888837 baseEnd_1888837 := by
    simpa [prefixWord, tailWord_1888837, baseEnd_1888837] using wordTrace_append hprefix tailTrace_1888837
  have hstable : (prefixWord ++ tailWord_1888837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888837).length < 2 ^ (prefixWord ++ tailWord_1888837).sum := by decide
  have hdescent : baseEnd_1888837 < baseStart_1888837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888839 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1888839 : Nat := 118140960795 + 1888839 * 2 ^ 59
def prefixEnd_1888839 : Nat := 4983230072969 + 3 ^ 40 * 1888839 * 2
def baseEnd_1888839 : Nat := 646588190638560428283929

theorem tailTrace_1888839 : CollatzResearch.WordTrace tailWord_1888839 prefixEnd_1888839 646588190638560428283929 := by
  unfold tailWord_1888839
  simp only [CollatzResearch.WordTrace]
  refine ⟨68891618004066365863765571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45927745336044243909177047 68891618004066365863765571)
  ·
    refine ⟨103337427006099548795648357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68891618004066365863765571 103337427006099548795648357)
    ·
      refine ⟨19375767563643665399184067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103337427006099548795648357 19375767563643665399184067)
      ·
        refine ⟨29063651345465498098776101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19375767563643665399184067 29063651345465498098776101)
        ·
          refine ⟨5449434627274780893520519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29063651345465498098776101 5449434627274780893520519)
          ·
            refine ⟨8174151940912171340280779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449434627274780893520519 8174151940912171340280779)
            ·
              refine ⟨12261227911368257010421169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174151940912171340280779 12261227911368257010421169)
              ·
                refine ⟨9195920933526192757815877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12261227911368257010421169 9195920933526192757815877)
                ·
                  refine ⟨1724235175036161142090477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9195920933526192757815877 1724235175036161142090477)
                  ·
                    refine ⟨646588190638560428283929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724235175036161142090477 646588190638560428283929)
                    ·
                      rfl

theorem cell22_1888839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1888839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888839 prefixEnd_1888839 := by exact prefixLift 1888839
  have htrace : WordTrace (prefixWord ++ tailWord_1888839) baseStart_1888839 baseEnd_1888839 := by
    simpa [prefixWord, tailWord_1888839, baseEnd_1888839] using wordTrace_append hprefix tailTrace_1888839
  have hstable : (prefixWord ++ tailWord_1888839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888839).length < 2 ^ (prefixWord ++ tailWord_1888839).sum := by decide
  have hdescent : baseEnd_1888839 < baseStart_1888839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888852 : List Nat := [2, 4, 1, 1, 1, 3, 10]
def baseStart_1888852 : Nat := 118140960795 + 1888852 * 2 ^ 59
def prefixEnd_1888852 : Nat := 4983230072969 + 3 ^ 40 * 1888852 * 2
def baseEnd_1888852 : Nat := 23947875585341952878107

theorem tailTrace_1888852 : CollatzResearch.WordTrace tailWord_1888852 prefixEnd_1888852 23947875585341952878107 := by
  unfold tailWord_1888852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34446046076509634541994405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45928061435346179389325873 34446046076509634541994405)
  ·
    refine ⟨6458633639345556476623951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34446046076509634541994405 6458633639345556476623951)
    ·
      refine ⟨9687950459018334714935927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6458633639345556476623951 9687950459018334714935927)
      ·
        refine ⟨14531925688527502072403891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687950459018334714935927 14531925688527502072403891)
        ·
          refine ⟨21797888532791253108605837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14531925688527502072403891 21797888532791253108605837)
          ·
            refine ⟨8174208199796719915727189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21797888532791253108605837 8174208199796719915727189)
            ·
              refine ⟨23947875585341952878107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8174208199796719915727189 23947875585341952878107)
              ·
                rfl

theorem cell22_1888852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 10].length) (baseStart_1888852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888852 prefixEnd_1888852 := by exact prefixLift 1888852
  have htrace : WordTrace (prefixWord ++ tailWord_1888852) baseStart_1888852 baseEnd_1888852 := by
    simpa [prefixWord, tailWord_1888852, baseEnd_1888852] using wordTrace_append hprefix tailTrace_1888852
  have hstable : (prefixWord ++ tailWord_1888852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888852).length < 2 ^ (prefixWord ++ tailWord_1888852).sum := by decide
  have hdescent : baseEnd_1888852 < baseStart_1888852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888869 : List Nat := [1, 3, 1, 3, 4, 1, 2, 7]
def baseStart_1888869 : Nat := 118140960795 + 1888869 * 2 ^ 59
def prefixEnd_1888869 : Nat := 4983230072969 + 3 ^ 40 * 1888869 * 2
def baseEnd_1888869 : Nat := 71844273361294483337093

theorem tailTrace_1888869 : CollatzResearch.WordTrace tailWord_1888869 prefixEnd_1888869 71844273361294483337093 := by
  unfold tailWord_1888869
  simp only [CollatzResearch.WordTrace]
  refine ⟨68892712193957680987357661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45928474795971787324905107 68892712193957680987357661)
  ·
    refine ⟨25834767072734130370259123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68892712193957680987357661 25834767072734130370259123)
    ·
      refine ⟨38752150609101195555388685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25834767072734130370259123 38752150609101195555388685)
      ·
        refine ⟨14532056478412948333270757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38752150609101195555388685 14532056478412948333270757)
        ·
          refine ⟨2724760589702427812488267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14532056478412948333270757 2724760589702427812488267)
          ·
            refine ⟨4087140884553641718732401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724760589702427812488267 4087140884553641718732401)
            ·
              refine ⟨3065355663415231289049301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087140884553641718732401 3065355663415231289049301)
              ·
                refine ⟨71844273361294483337093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3065355663415231289049301 71844273361294483337093)
                ·
                  rfl

theorem cell22_1888869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 7].length) (baseStart_1888869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888869 prefixEnd_1888869 := by exact prefixLift 1888869
  have htrace : WordTrace (prefixWord ++ tailWord_1888869) baseStart_1888869 baseEnd_1888869 := by
    simpa [prefixWord, tailWord_1888869, baseEnd_1888869] using wordTrace_append hprefix tailTrace_1888869
  have hstable : (prefixWord ++ tailWord_1888869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888869).length < 2 ^ (prefixWord ++ tailWord_1888869).sum := by decide
  have hdescent : baseEnd_1888869 < baseStart_1888869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888944 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_1888944 : Nat := 118140960795 + 1888944 * 2 ^ 59
def prefixEnd_1888944 : Nat := 4983230072969 + 3 ^ 40 * 1888944 * 2
def baseEnd_1888944 : Nat := 646624134284375154408607

theorem tailTrace_1888944 : CollatzResearch.WordTrace tailWord_1888944 prefixEnd_1888944 646624134284375154408607 := by
  unfold tailWord_1888944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447723834342984398168943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45930298445790645864225257 34447723834342984398168943)
  ·
    refine ⟨51671585751514476597253415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34447723834342984398168943 51671585751514476597253415)
    ·
      refine ⟨77507378627271714895880123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51671585751514476597253415 77507378627271714895880123)
      ·
        refine ⟨116261067940907572343820185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77507378627271714895880123 116261067940907572343820185)
        ·
          refine ⟨87195800955680679257865139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116261067940907572343820185 87195800955680679257865139)
          ·
            refine ⟨130793701433521018886797709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87195800955680679257865139 130793701433521018886797709)
            ·
              refine ⟨49047638037570382082549141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130793701433521018886797709 49047638037570382082549141)
              ·
                refine ⟨2299108033011111660119491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49047638037570382082549141 2299108033011111660119491)
                ·
                  refine ⟨3448662049516667490179237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299108033011111660119491 3448662049516667490179237)
                  ·
                    refine ⟨646624134284375154408607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3448662049516667490179237 646624134284375154408607)
                    ·
                      rfl

theorem cell22_1888944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_1888944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888944 prefixEnd_1888944 := by exact prefixLift 1888944
  have htrace : WordTrace (prefixWord ++ tailWord_1888944) baseStart_1888944 baseEnd_1888944 := by
    simpa [prefixWord, tailWord_1888944, baseEnd_1888944] using wordTrace_append hprefix tailTrace_1888944
  have hstable : (prefixWord ++ tailWord_1888944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888944).length < 2 ^ (prefixWord ++ tailWord_1888944).sum := by decide
  have hdescent : baseEnd_1888944 < baseStart_1888944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1888991 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 1, 5]
def baseStart_1888991 : Nat := 118140960795 + 1888991 * 2 ^ 59
def prefixEnd_1888991 : Nat := 4983230072969 + 3 ^ 40 * 1888991 * 2
def baseEnd_1888991 : Nat := 646640223344882698483463

theorem tailTrace_1888991 : CollatzResearch.WordTrace tailWord_1888991 prefixEnd_1888991 646640223344882698483463 := by
  unfold tailWord_1888991
  simp only [CollatzResearch.WordTrace]
  refine ⟨68897161899515695823298827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45931441266343797215532551 68897161899515695823298827)
  ·
    refine ⟨103345742849273543734948241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68897161899515695823298827 103345742849273543734948241)
    ·
      refine ⟨77509307136955157801211181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103345742849273543734948241 77509307136955157801211181)
      ·
        refine ⟨29065990176358184175454193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77509307136955157801211181 29065990176358184175454193)
        ·
          refine ⟨21799492632268638131590645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29065990176358184175454193 21799492632268638131590645)
          ·
            refine ⟨2043702434275184824836623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21799492632268638131590645 2043702434275184824836623)
            ·
              refine ⟨3065553651412777237254935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043702434275184824836623 3065553651412777237254935)
              ·
                refine ⟨4598330477119165855882403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065553651412777237254935 4598330477119165855882403)
                ·
                  refine ⟨6897495715678748783823605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598330477119165855882403 6897495715678748783823605)
                  ·
                    refine ⟨646640223344882698483463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6897495715678748783823605 646640223344882698483463)
                    ·
                      rfl

theorem cell22_1888991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_1888991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1888991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1888991 prefixEnd_1888991 := by exact prefixLift 1888991
  have htrace : WordTrace (prefixWord ++ tailWord_1888991) baseStart_1888991 baseEnd_1888991 := by
    simpa [prefixWord, tailWord_1888991, baseEnd_1888991] using wordTrace_append hprefix tailTrace_1888991
  have hstable : (prefixWord ++ tailWord_1888991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1888991).length < 2 ^ (prefixWord ++ tailWord_1888991).sum := by decide
  have hdescent : baseEnd_1888991 < baseStart_1888991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1888991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889034 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1889034 : Nat := 118140960795 + 1889034 * 2 ^ 59
def prefixEnd_1889034 : Nat := 4983230072969 + 3 ^ 40 * 1889034 * 2
def baseEnd_1889034 : Nat := 646654943123644919658331

theorem tailTrace_1889034 : CollatzResearch.WordTrace tailWord_1889034 prefixEnd_1889034 646654943123644919658331 := by
  unfold tailWord_1889034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17224682559589978541778539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45932486825573276111409437 17224682559589978541778539)
  ·
    refine ⟨25837023839384967812667809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17224682559589978541778539 25837023839384967812667809)
    ·
      refine ⟨19377767879538725859500857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25837023839384967812667809 19377767879538725859500857)
      ·
        refine ⟨14533325909654044394625643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19377767879538725859500857 14533325909654044394625643)
        ·
          refine ⟨21799988864481066591938465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14533325909654044394625643 21799988864481066591938465)
          ·
            refine ⟨16349991648360799943953849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21799988864481066591938465 16349991648360799943953849)
            ·
              refine ⟨12262493736270599957965387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16349991648360799943953849 12262493736270599957965387)
              ·
                refine ⟨18393740604405899936948081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12262493736270599957965387 18393740604405899936948081)
                ·
                  refine ⟨13795305453304424952711061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18393740604405899936948081 13795305453304424952711061)
                  ·
                    refine ⟨646654943123644919658331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13795305453304424952711061 646654943123644919658331)
                    ·
                      rfl

theorem cell22_1889034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1889034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889034 prefixEnd_1889034 := by exact prefixLift 1889034
  have htrace : WordTrace (prefixWord ++ tailWord_1889034) baseStart_1889034 baseEnd_1889034 := by
    simpa [prefixWord, tailWord_1889034, baseEnd_1889034] using wordTrace_append hprefix tailTrace_1889034
  have hstable : (prefixWord ++ tailWord_1889034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889034).length < 2 ^ (prefixWord ++ tailWord_1889034).sum := by decide
  have hdescent : baseEnd_1889034 < baseStart_1889034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889087 : List Nat := [1, 1, 2, 2, 5, 3, 2, 2, 1, 3]
def baseStart_1889087 : Nat := 118140960795 + 1889087 * 2 ^ 59
def prefixEnd_1889087 : Nat := 4983230072969 + 3 ^ 40 * 1889087 * 2
def baseEnd_1889087 : Nat := 646673086106770448083169

theorem tailTrace_1889087 : CollatzResearch.WordTrace tailWord_1889087 prefixEnd_1889087 646673086106770448083169 := by
  unfold tailWord_1889087
  simp only [CollatzResearch.WordTrace]
  refine ⟨68900663307167904218793515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45933775538111936145862343 68900663307167904218793515)
  ·
    refine ⟨103350994960751856328190273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68900663307167904218793515 103350994960751856328190273)
    ·
      refine ⟨77513246220563892246142705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103350994960751856328190273 77513246220563892246142705)
      ·
        refine ⟨58134934665422919184607029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77513246220563892246142705 58134934665422919184607029)
        ·
          refine ⟨5450150124883398673556909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58134934665422919184607029 5450150124883398673556909)
          ·
            refine ⟨2043806296831274502583841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5450150124883398673556909 2043806296831274502583841)
            ·
              refine ⟨1532854722623455876937881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043806296831274502583841 1532854722623455876937881)
              ·
                refine ⟨1149641041967591907703411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532854722623455876937881 1149641041967591907703411)
                ·
                  refine ⟨1724461562951387861555117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149641041967591907703411 1724461562951387861555117)
                  ·
                    refine ⟨646673086106770448083169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724461562951387861555117 646673086106770448083169)
                    ·
                      rfl

theorem cell22_1889087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 3].length) (baseStart_1889087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889087 prefixEnd_1889087 := by exact prefixLift 1889087
  have htrace : WordTrace (prefixWord ++ tailWord_1889087) baseStart_1889087 baseEnd_1889087 := by
    simpa [prefixWord, tailWord_1889087, baseEnd_1889087] using wordTrace_append hprefix tailTrace_1889087
  have hstable : (prefixWord ++ tailWord_1889087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889087).length < 2 ^ (prefixWord ++ tailWord_1889087).sum := by decide
  have hdescent : baseEnd_1889087 < baseStart_1889087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889111 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 6]
def baseStart_1889111 : Nat := 118140960795 + 1889111 * 2 ^ 59
def prefixEnd_1889111 : Nat := 4983230072969 + 3 ^ 40 * 1889111 * 2
def baseEnd_1889111 : Nat := 215560433932414128494365

theorem tailTrace_1889111 : CollatzResearch.WordTrace tailWord_1889111 prefixEnd_1889111 215560433932414128494365 := by
  unfold tailWord_1889111
  simp only [CollatzResearch.WordTrace]
  refine ⟨68901538659080956317667187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45934359106053970878444791 68901538659080956317667187)
  ·
    refine ⟨103352307988621434476500781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68901538659080956317667187 103352307988621434476500781)
    ·
      refine ⟨38757115495733037928687793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103352307988621434476500781 38757115495733037928687793)
      ·
        refine ⟨29067836621799778446515845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38757115495733037928687793 29067836621799778446515845)
        ·
          refine ⟨5450219366587458458721721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29067836621799778446515845 5450219366587458458721721)
          ·
            refine ⟨4087664524940593844041291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5450219366587458458721721 4087664524940593844041291)
            ·
              refine ⟨6131496787410890766061937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087664524940593844041291 6131496787410890766061937)
              ·
                refine ⟨4598622590558168074546453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6131496787410890766061937 4598622590558168074546453)
                ·
                  refine ⟨215560433932414128494365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4598622590558168074546453 215560433932414128494365)
                  ·
                    rfl

theorem cell22_1889111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 6].length) (baseStart_1889111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889111 prefixEnd_1889111 := by exact prefixLift 1889111
  have htrace : WordTrace (prefixWord ++ tailWord_1889111) baseStart_1889111 baseEnd_1889111 := by
    simpa [prefixWord, tailWord_1889111, baseEnd_1889111] using wordTrace_append hprefix tailTrace_1889111
  have hstable : (prefixWord ++ tailWord_1889111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889111).length < 2 ^ (prefixWord ++ tailWord_1889111).sum := by decide
  have hdescent : baseEnd_1889111 < baseStart_1889111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889128 : List Nat := [2, 1, 4, 2, 1, 2, 1, 5, 4]
def baseStart_1889128 : Nat := 118140960795 + 1889128 * 2 ^ 59
def prefixEnd_1889128 : Nat := 4983230072969 + 3 ^ 40 * 1889128 * 2
def baseEnd_1889128 : Nat := 215562373748220002602681

theorem tailTrace_1889128 : CollatzResearch.WordTrace tailWord_1889128 prefixEnd_1889128 215562373748220002602681 := by
  unfold tailWord_1889128
  simp only [CollatzResearch.WordTrace]
  refine ⟨34451079350009684110518019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45934772466679578814024025 34451079350009684110518019)
  ·
    refine ⟨51676619025014526165777029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34451079350009684110518019 51676619025014526165777029)
    ·
      refine ⟨9689366067190223656083193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51676619025014526165777029 9689366067190223656083193)
      ·
        refine ⟨7267024550392667742062395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9689366067190223656083193 7267024550392667742062395)
        ·
          refine ⟨10900536825589001613093593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7267024550392667742062395 10900536825589001613093593)
          ·
            refine ⟨8175402619191751209820195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10900536825589001613093593 8175402619191751209820195)
            ·
              refine ⟨12263103928787626814730293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8175402619191751209820195 12263103928787626814730293)
              ·
                refine ⟨1149665993323840013880965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12263103928787626814730293 1149665993323840013880965)
                ·
                  refine ⟨215562373748220002602681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149665993323840013880965 215562373748220002602681)
                  ·
                    rfl

theorem cell22_1889128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_1889128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889128 prefixEnd_1889128 := by exact prefixLift 1889128
  have htrace : WordTrace (prefixWord ++ tailWord_1889128) baseStart_1889128 baseEnd_1889128 := by
    simpa [prefixWord, tailWord_1889128, baseEnd_1889128] using wordTrace_append hprefix tailTrace_1889128
  have hstable : (prefixWord ++ tailWord_1889128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889128).length < 2 ^ (prefixWord ++ tailWord_1889128).sum := by decide
  have hdescent : baseEnd_1889128 < baseStart_1889128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889171 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 5, 3]
def baseStart_1889171 : Nat := 118140960795 + 1889171 * 2 ^ 59
def prefixEnd_1889171 : Nat := 4983230072969 + 3 ^ 40 * 1889171 * 2
def baseEnd_1889171 : Nat := 646701841023422228982911

theorem tailTrace_1889171 : CollatzResearch.WordTrace tailWord_1889171 prefixEnd_1889171 646701841023422228982911 := by
  unfold tailWord_1889171
  simp only [CollatzResearch.WordTrace]
  refine ⟨68903727038863586564851367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45935818025909057709900911 68903727038863586564851367)
  ·
    refine ⟨103355590558295379847277051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68903727038863586564851367 103355590558295379847277051)
    ·
      refine ⟨155033385837443069770915577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103355590558295379847277051 155033385837443069770915577)
      ·
        refine ⟨116275039378082302328186683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155033385837443069770915577 116275039378082302328186683)
        ·
          refine ⟨174412559067123453492280025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116275039378082302328186683 174412559067123453492280025)
          ·
            refine ⟨130809419300342590119210019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174412559067123453492280025 130809419300342590119210019)
            ·
              refine ⟨196214128950513885178815029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130809419300342590119210019 196214128950513885178815029)
              ·
                refine ⟨18395074589110676735513909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196214128950513885178815029 18395074589110676735513909)
                ·
                  refine ⟨1724538242729125943954429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18395074589110676735513909 1724538242729125943954429)
                  ·
                    refine ⟨646701841023422228982911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724538242729125943954429 646701841023422228982911)
                    ·
                      rfl

theorem cell22_1889171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 3].length) (baseStart_1889171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889171 prefixEnd_1889171 := by exact prefixLift 1889171
  have htrace : WordTrace (prefixWord ++ tailWord_1889171) baseStart_1889171 baseEnd_1889171 := by
    simpa [prefixWord, tailWord_1889171, baseEnd_1889171] using wordTrace_append hprefix tailTrace_1889171
  have hstable : (prefixWord ++ tailWord_1889171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889171).length < 2 ^ (prefixWord ++ tailWord_1889171).sum := by decide
  have hdescent : baseEnd_1889171 < baseStart_1889171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889173 : List Nat := [1, 3, 2, 1, 1, 6, 2, 6]
def baseStart_1889173 : Nat := 118140960795 + 1889173 * 2 ^ 59
def prefixEnd_1889173 : Nat := 4983230072969 + 3 ^ 40 * 1889173 * 2
def baseEnd_1889173 : Nat := 71855836184921654492545

theorem tailTrace_1889173 : CollatzResearch.WordTrace tailWord_1889173 prefixEnd_1889173 71855836184921654492545 := by
  unfold tailWord_1889173
  simp only [CollatzResearch.WordTrace]
  refine ⟨68903799984856340906424173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45935866656570893937616115 68903799984856340906424173)
  ·
    refine ⟨25838924994321127839909065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68903799984856340906424173 25838924994321127839909065)
    ·
      refine ⟨19379193745740845879931799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25838924994321127839909065 19379193745740845879931799)
      ·
        refine ⟨29068790618611268819897699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19379193745740845879931799 29068790618611268819897699)
        ·
          refine ⟨43603185927916903229846549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29068790618611268819897699 43603185927916903229846549)
          ·
            refine ⟨2043899340371104838899057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43603185927916903229846549 2043899340371104838899057)
            ·
              refine ⟨1532924505278328629174293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2043899340371104838899057 1532924505278328629174293)
              ·
                refine ⟨71855836184921654492545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1532924505278328629174293 71855836184921654492545)
                ·
                  rfl

theorem cell22_1889173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 6].length) (baseStart_1889173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889173 prefixEnd_1889173 := by exact prefixLift 1889173
  have htrace : WordTrace (prefixWord ++ tailWord_1889173) baseStart_1889173 baseEnd_1889173 := by
    simpa [prefixWord, tailWord_1889173, baseEnd_1889173] using wordTrace_append hprefix tailTrace_1889173
  have hstable : (prefixWord ++ tailWord_1889173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889173).length < 2 ^ (prefixWord ++ tailWord_1889173).sum := by decide
  have hdescent : baseEnd_1889173 < baseStart_1889173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889308 : List Nat := [2, 2, 3, 1, 4, 1, 9]
def baseStart_1889308 : Nat := 118140960795 + 1889308 * 2 ^ 59
def prefixEnd_1889308 : Nat := 4983230072969 + 3 ^ 40 * 1889308 * 2
def baseEnd_1889308 : Nat := 23953656997155538455833

theorem tailTrace_1889308 : CollatzResearch.WordTrace tailWord_1889308 prefixEnd_1889308 23953656997155538455833 := by
  unfold tailWord_1889308
  simp only [CollatzResearch.WordTrace]
  refine ⟨34454361919683629481294289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45939149226244839308392385 34454361919683629481294289)
  ·
    refine ⟨25840771439762722110970717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34454361919683629481294289 25840771439762722110970717)
    ·
      refine ⟨9690289289911020791614019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25840771439762722110970717 9690289289911020791614019)
      ·
        refine ⟨14535433934866531187421029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9690289289911020791614019 14535433934866531187421029)
        ·
          refine ⟨2725393862787474597641443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14535433934866531187421029 2725393862787474597641443)
          ·
            refine ⟨4088090794181211896462165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725393862787474597641443 4088090794181211896462165)
            ·
              refine ⟨23953656997155538455833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4088090794181211896462165 23953656997155538455833)
              ·
                rfl

theorem cell22_1889308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 9].length) (baseStart_1889308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889308 prefixEnd_1889308 := by exact prefixLift 1889308
  have htrace : WordTrace (prefixWord ++ tailWord_1889308) baseStart_1889308 baseEnd_1889308 := by
    simpa [prefixWord, tailWord_1889308, baseEnd_1889308] using wordTrace_append hprefix tailTrace_1889308
  have hstable : (prefixWord ++ tailWord_1889308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889308).length < 2 ^ (prefixWord ++ tailWord_1889308).sum := by decide
  have hdescent : baseEnd_1889308 < baseStart_1889308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889312 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 4, 3]
def baseStart_1889312 : Nat := 118140960795 + 1889312 * 2 ^ 59
def prefixEnd_1889312 : Nat := 4983230072969 + 3 ^ 40 * 1889312 * 2
def baseEnd_1889312 : Nat := 646750108204944861207479

theorem tailTrace_1889312 : CollatzResearch.WordTrace tailWord_1889312 prefixEnd_1889312 646750108204944861207479 := by
  unfold tailWord_1889312
  simp only [CollatzResearch.WordTrace]
  refine ⟨34454434865676383822867095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45939246487568511763822793 34454434865676383822867095)
  ·
    refine ⟨51681652298514575734300643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34454434865676383822867095 51681652298514575734300643)
    ·
      refine ⟨77522478447771863601450965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51681652298514575734300643 77522478447771863601450965)
      ·
        refine ⟨1816933088619653053159007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 77522478447771863601450965 1816933088619653053159007)
        ·
          refine ⟨2725399632929479579738511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816933088619653053159007 2725399632929479579738511)
          ·
            refine ⟨4088099449394219369607767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725399632929479579738511 4088099449394219369607767)
            ·
              refine ⟨6132149174091329054411651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088099449394219369607767 6132149174091329054411651)
              ·
                refine ⟨9198223761136993581617477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132149174091329054411651 9198223761136993581617477)
                ·
                  refine ⟨1724666955213186296553277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9198223761136993581617477 1724666955213186296553277)
                  ·
                    refine ⟨646750108204944861207479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724666955213186296553277 646750108204944861207479)
                    ·
                      rfl

theorem cell22_1889312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_1889312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889312 prefixEnd_1889312 := by exact prefixLift 1889312
  have htrace : WordTrace (prefixWord ++ tailWord_1889312) baseStart_1889312 baseEnd_1889312 := by
    simpa [prefixWord, tailWord_1889312, baseEnd_1889312] using wordTrace_append hprefix tailTrace_1889312
  have hstable : (prefixWord ++ tailWord_1889312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889312).length < 2 ^ (prefixWord ++ tailWord_1889312).sum := by decide
  have hdescent : baseEnd_1889312 < baseStart_1889312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889340 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_1889340 : Nat := 118140960795 + 1889340 * 2 ^ 59
def prefixEnd_1889340 : Nat := 4983230072969 + 3 ^ 40 * 1889340 * 2
def baseEnd_1889340 : Nat := 646759693177162121507393

theorem tailTrace_1889340 : CollatzResearch.WordTrace tailWord_1889340 prefixEnd_1889340 646759693177162121507393 := by
  unfold tailWord_1889340
  simp only [CollatzResearch.WordTrace]
  refine ⟨34454945487625664213876737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45939927316834218951835649 34454945487625664213876737)
  ·
    refine ⟨25841209115719248160407553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34454945487625664213876737 25841209115719248160407553)
    ·
      refine ⟨19380906836789436120305665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25841209115719248160407553 19380906836789436120305665)
      ·
        refine ⟨14535680127592077090229249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19380906836789436120305665 14535680127592077090229249)
        ·
          refine ⟨10901760095694057817671937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14535680127592077090229249 10901760095694057817671937)
          ·
            refine ⟨8176320071770543363253953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10901760095694057817671937 8176320071770543363253953)
            ·
              refine ⟨6132240053827907522440465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8176320071770543363253953 6132240053827907522440465)
              ·
                refine ⟨4599180040370930641830349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6132240053827907522440465 4599180040370930641830349)
                ·
                  refine ⟨1724692515139098990686381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4599180040370930641830349 1724692515139098990686381)
                  ·
                    refine ⟨646759693177162121507393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724692515139098990686381 646759693177162121507393)
                    ·
                      rfl

theorem cell22_1889340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_1889340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889340 prefixEnd_1889340 := by exact prefixLift 1889340
  have htrace : WordTrace (prefixWord ++ tailWord_1889340) baseStart_1889340 baseEnd_1889340 := by
    simpa [prefixWord, tailWord_1889340, baseEnd_1889340] using wordTrace_append hprefix tailTrace_1889340
  have hstable : (prefixWord ++ tailWord_1889340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889340).length < 2 ^ (prefixWord ++ tailWord_1889340).sum := by decide
  have hdescent : baseEnd_1889340 < baseStart_1889340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889342 : List Nat := [4, 2, 1, 3, 1, 3, 2, 6]
def baseStart_1889342 : Nat := 118140960795 + 1889342 * 2 ^ 59
def prefixEnd_1889342 : Nat := 4983230072969 + 3 ^ 40 * 1889342 * 2
def baseEnd_1889342 : Nat := 71862264202003864773043

theorem tailTrace_1889342 : CollatzResearch.WordTrace tailWord_1889342 prefixEnd_1889342 71862264202003864773043 := by
  unfold tailWord_1889342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8613745490155510346165785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45939975947496055179550853 8613745490155510346165785)
  ·
    refine ⟨6460309117616632759624339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8613745490155510346165785 6460309117616632759624339)
    ·
      refine ⟨9690463676424949139436509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6460309117616632759624339 9690463676424949139436509)
      ·
        refine ⟨3633923878659355927288691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9690463676424949139436509 3633923878659355927288691)
        ·
          refine ⟨5450885817989033890933037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633923878659355927288691 5450885817989033890933037)
          ·
            refine ⟨2044082181745887709099889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5450885817989033890933037 2044082181745887709099889)
            ·
              refine ⟨1533061636309415781824917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044082181745887709099889 1533061636309415781824917)
              ·
                refine ⟨71862264202003864773043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1533061636309415781824917 71862264202003864773043)
                ·
                  rfl

theorem cell22_1889342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_1889342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889342 prefixEnd_1889342 := by exact prefixLift 1889342
  have htrace : WordTrace (prefixWord ++ tailWord_1889342) baseStart_1889342 baseEnd_1889342 := by
    simpa [prefixWord, tailWord_1889342, baseEnd_1889342] using wordTrace_append hprefix tailTrace_1889342
  have hstable : (prefixWord ++ tailWord_1889342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889342).length < 2 ^ (prefixWord ++ tailWord_1889342).sum := by decide
  have hdescent : baseEnd_1889342 < baseStart_1889342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889400 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_1889400 : Nat := 118140960795 + 1889400 * 2 ^ 59
def prefixEnd_1889400 : Nat := 4983230072969 + 3 ^ 40 * 1889400 * 2
def baseEnd_1889400 : Nat := 646780232403341965007209

theorem tailTrace_1889400 : CollatzResearch.WordTrace tailWord_1889400 prefixEnd_1889400 646780232403341965007209 := by
  unfold tailWord_1889400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34456039677516979337468827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45941386236689305783291769 34456039677516979337468827)
  ·
    refine ⟨51684059516275469006203241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34456039677516979337468827 51684059516275469006203241)
    ·
      refine ⟨38763044637206601754652431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51684059516275469006203241 38763044637206601754652431)
      ·
        refine ⟨58144566955809902631978647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38763044637206601754652431 58144566955809902631978647)
        ·
          refine ⟨87216850433714853947967971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58144566955809902631978647 87216850433714853947967971)
          ·
            refine ⟨130825275650572280921951957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87216850433714853947967971 130825275650572280921951957)
            ·
              refine ⟨3066217398060287834108249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130825275650572280921951957 3066217398060287834108249)
              ·
                refine ⟨2299663048545215875581187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066217398060287834108249 2299663048545215875581187)
                ·
                  refine ⟨3449494572817823813371781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299663048545215875581187 3449494572817823813371781)
                  ·
                    refine ⟨646780232403341965007209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3449494572817823813371781 646780232403341965007209)
                    ·
                      rfl

theorem cell22_1889400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_1889400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889400 prefixEnd_1889400 := by exact prefixLift 1889400
  have htrace : WordTrace (prefixWord ++ tailWord_1889400) baseStart_1889400 baseEnd_1889400 := by
    simpa [prefixWord, tailWord_1889400, baseEnd_1889400] using wordTrace_append hprefix tailTrace_1889400
  have hstable : (prefixWord ++ tailWord_1889400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889400).length < 2 ^ (prefixWord ++ tailWord_1889400).sum := by decide
  have hdescent : baseEnd_1889400 < baseStart_1889400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889415 : List Nat := [1, 1, 4, 2, 1, 1, 1, 7, 4]
def baseStart_1889415 : Nat := 118140960795 + 1889415 * 2 ^ 59
def prefixEnd_1889415 : Nat := 4983230072969 + 3 ^ 40 * 1889415 * 2
def baseEnd_1889415 : Nat := 215595122403295641960721

theorem tailTrace_1889415 : CollatzResearch.WordTrace tailWord_1889415 prefixEnd_1889415 215595122403295641960721 := by
  unfold tailWord_1889415
  simp only [CollatzResearch.WordTrace]
  refine ⟨68912626449979616236733699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45941750966653077491155799 68912626449979616236733699)
  ·
    refine ⟨103368939674969424355100549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68912626449979616236733699 103368939674969424355100549)
    ·
      refine ⟨19381676189056767066581353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103368939674969424355100549 19381676189056767066581353)
      ·
        refine ⟨14536257141792575299936015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19381676189056767066581353 14536257141792575299936015)
        ·
          refine ⟨21804385712688862949904023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14536257141792575299936015 21804385712688862949904023)
          ·
            refine ⟨32706578569033294424856035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21804385712688862949904023 32706578569033294424856035)
            ·
              refine ⟨49059867853549941637284053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32706578569033294424856035 49059867853549941637284053)
              ·
                refine ⟨1149840652817576757123845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49059867853549941637284053 1149840652817576757123845)
                ·
                  refine ⟨215595122403295641960721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149840652817576757123845 215595122403295641960721)
                  ·
                    rfl

theorem cell22_1889415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 4].length) (baseStart_1889415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889415 prefixEnd_1889415 := by exact prefixLift 1889415
  have htrace : WordTrace (prefixWord ++ tailWord_1889415) baseStart_1889415 baseEnd_1889415 := by
    simpa [prefixWord, tailWord_1889415, baseEnd_1889415] using wordTrace_append hprefix tailTrace_1889415
  have hstable : (prefixWord ++ tailWord_1889415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889415).length < 2 ^ (prefixWord ++ tailWord_1889415).sum := by decide
  have hdescent : baseEnd_1889415 < baseStart_1889415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889417 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 1, 4]
def baseStart_1889417 : Nat := 118140960795 + 1889417 * 2 ^ 59
def prefixEnd_1889417 : Nat := 4983230072969 + 3 ^ 40 * 1889417 * 2
def baseEnd_1889417 : Nat := 646786051850759587332157

theorem tailTrace_1889417 : CollatzResearch.WordTrace tailWord_1889417 prefixEnd_1889417 646786051850759587332157 := by
  unfold tailWord_1889417
  simp only [CollatzResearch.WordTrace]
  refine ⟨68912699395972370578306505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45941799597314913718871003 68912699395972370578306505)
  ·
    refine ⟨51684524546979277933729879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68912699395972370578306505 51684524546979277933729879)
    ·
      refine ⟨77526786820468916900594819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51684524546979277933729879 77526786820468916900594819)
      ·
        refine ⟨116290180230703375350892229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77526786820468916900594819 116290180230703375350892229)
        ·
          refine ⟨21804408793256882878292293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116290180230703375350892229 21804408793256882878292293)
          ·
            refine ⟨4088326648735665539679805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21804408793256882878292293 4088326648735665539679805)
            ·
              refine ⟨1533122493275874577379927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4088326648735665539679805 1533122493275874577379927)
              ·
                refine ⟨2299683739913811866069891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533122493275874577379927 2299683739913811866069891)
                ·
                  refine ⟨3449525609870717799104837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299683739913811866069891 3449525609870717799104837)
                  ·
                    refine ⟨646786051850759587332157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3449525609870717799104837 646786051850759587332157)
                    ·
                      rfl

theorem cell22_1889417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_1889417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889417 prefixEnd_1889417 := by exact prefixLift 1889417
  have htrace : WordTrace (prefixWord ++ tailWord_1889417) baseStart_1889417 baseEnd_1889417 := by
    simpa [prefixWord, tailWord_1889417, baseEnd_1889417] using wordTrace_append hprefix tailTrace_1889417
  have hstable : (prefixWord ++ tailWord_1889417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889417).length < 2 ^ (prefixWord ++ tailWord_1889417).sum := by decide
  have hdescent : baseEnd_1889417 < baseStart_1889417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889432 : List Nat := [2, 1, 2, 4, 2, 2, 1, 4, 4]
def baseStart_1889432 : Nat := 118140960795 + 1889432 * 2 ^ 59
def prefixEnd_1889432 : Nat := 4983230072969 + 3 ^ 40 * 1889432 * 2
def baseEnd_1889432 : Nat := 215597062219101516069037

theorem tailTrace_1889432 : CollatzResearch.WordTrace tailWord_1889432 prefixEnd_1889432 215597062219101516069037 := by
  unfold tailWord_1889432
  simp only [CollatzResearch.WordTrace]
  refine ⟨34456623245459014070051275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45942164327278685426735033 34456623245459014070051275)
  ·
    refine ⟨51684934868188521105076913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34456623245459014070051275 51684934868188521105076913)
    ·
      refine ⟨38763701151141390828807685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51684934868188521105076913 38763701151141390828807685)
      ·
        refine ⟨7268193965839010780401441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38763701151141390828807685 7268193965839010780401441)
        ·
          refine ⟨5451145474379258085301081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7268193965839010780401441 5451145474379258085301081)
          ·
            refine ⟨4088359105784443563975811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5451145474379258085301081 4088359105784443563975811)
            ·
              refine ⟨6132538658676665345963717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088359105784443563975811 6132538658676665345963717)
              ·
                refine ⟨1149850998501874752368197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6132538658676665345963717 1149850998501874752368197)
                ·
                  refine ⟨215597062219101516069037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149850998501874752368197 215597062219101516069037)
                  ·
                    rfl

theorem cell22_1889432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_1889432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889432 prefixEnd_1889432 := by exact prefixLift 1889432
  have htrace : WordTrace (prefixWord ++ tailWord_1889432) baseStart_1889432 baseEnd_1889432 := by
    simpa [prefixWord, tailWord_1889432, baseEnd_1889432] using wordTrace_append hprefix tailTrace_1889432
  have hstable : (prefixWord ++ tailWord_1889432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889432).length < 2 ^ (prefixWord ++ tailWord_1889432).sum := by decide
  have hdescent : baseEnd_1889432 < baseStart_1889432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889447 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1889447 : Nat := 118140960795 + 1889447 * 2 ^ 59
def prefixEnd_1889447 : Nat := 4983230072969 + 3 ^ 40 * 1889447 * 2
def baseEnd_1889447 : Nat := 646796321463849509082065

theorem tailTrace_1889447 : CollatzResearch.WordTrace tailWord_1889447 prefixEnd_1889447 646796321463849509082065 := by
  unfold tailWord_1889447
  simp only [CollatzResearch.WordTrace]
  refine ⟨68913793585863685701898595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45942529057242457134599063 68913793585863685701898595)
  ·
    refine ⟨103370690378795528552847893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68913793585863685701898595 103370690378795528552847893)
    ·
      refine ⟨4845501111506040400914745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103370690378795528552847893 4845501111506040400914745)
      ·
        refine ⟨3634125833629530300686059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4845501111506040400914745 3634125833629530300686059)
        ·
          refine ⟨5451188750444295451029089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634125833629530300686059 5451188750444295451029089)
          ·
            refine ⟨4088391562833221588271817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5451188750444295451029089 4088391562833221588271817)
            ·
              refine ⟨3066293672124916191203863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088391562833221588271817 3066293672124916191203863)
              ·
                refine ⟨4599440508187374286805795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066293672124916191203863 4599440508187374286805795)
                ·
                  refine ⟨6899160762281061430208693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599440508187374286805795 6899160762281061430208693)
                  ·
                    refine ⟨646796321463849509082065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6899160762281061430208693 646796321463849509082065)
                    ·
                      rfl

theorem cell22_1889447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1889447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889447 prefixEnd_1889447 := by exact prefixLift 1889447
  have htrace : WordTrace (prefixWord ++ tailWord_1889447) baseStart_1889447 baseEnd_1889447 := by
    simpa [prefixWord, tailWord_1889447, baseEnd_1889447] using wordTrace_append hprefix tailTrace_1889447
  have hstable : (prefixWord ++ tailWord_1889447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889447).length < 2 ^ (prefixWord ++ tailWord_1889447).sum := by decide
  have hdescent : baseEnd_1889447 < baseStart_1889447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889599 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 2, 3]
def baseStart_1889599 : Nat := 118140960795 + 1889599 * 2 ^ 59
def prefixEnd_1889599 : Nat := 4983230072969 + 3 ^ 40 * 1889599 * 2
def baseEnd_1889599 : Nat := 646848354170171779281599

theorem tailTrace_1889599 : CollatzResearch.WordTrace tailWord_1889599 prefixEnd_1889599 646848354170171779281599 := by
  unfold tailWord_1889599
  simp only [CollatzResearch.WordTrace]
  refine ⟨68919337481313015661431851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45946224987542010440954567 68919337481313015661431851)
  ·
    refine ⟨103379006221969523492147777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68919337481313015661431851 103379006221969523492147777)
    ·
      refine ⟨77534254666477142619110833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103379006221969523492147777 77534254666477142619110833)
      ·
        refine ⟨58150690999857856964333125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77534254666477142619110833 58150690999857856964333125)
        ·
          refine ⟨10903254562473348180812461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58150690999857856964333125 10903254562473348180812461)
          ·
            refine ⟨4088720460927505567804673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10903254562473348180812461 4088720460927505567804673)
            ·
              refine ⟨3066540345695629175853505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088720460927505567804673 3066540345695629175853505)
              ·
                refine ⟨2299905259271721881890129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066540345695629175853505 2299905259271721881890129)
                ·
                  refine ⟨1724928944453791411417597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2299905259271721881890129 1724928944453791411417597)
                  ·
                    refine ⟨646848354170171779281599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1724928944453791411417597 646848354170171779281599)
                    ·
                      rfl

theorem cell22_1889599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_1889599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889599 prefixEnd_1889599 := by exact prefixLift 1889599
  have htrace : WordTrace (prefixWord ++ tailWord_1889599) baseStart_1889599 baseEnd_1889599 := by
    simpa [prefixWord, tailWord_1889599, baseEnd_1889599] using wordTrace_append hprefix tailTrace_1889599
  have hstable : (prefixWord ++ tailWord_1889599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889599).length < 2 ^ (prefixWord ++ tailWord_1889599).sum := by decide
  have hdescent : baseEnd_1889599 < baseStart_1889599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889601 : List Nat := [1, 2, 5, 2, 1, 1, 4, 2, 4]
def baseStart_1889601 : Nat := 118140960795 + 1889601 * 2 ^ 59
def prefixEnd_1889601 : Nat := 4983230072969 + 3 ^ 40 * 1889601 * 2
def baseEnd_1889601 : Nat := 215616346270348146910531

theorem tailTrace_1889601 : CollatzResearch.WordTrace tailWord_1889601 prefixEnd_1889601 215616346270348146910531 := by
  unfold tailWord_1889601
  simp only [CollatzResearch.WordTrace]
  refine ⟨68919410427305770003004657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45946273618203846668669771 68919410427305770003004657)
  ·
    refine ⟨51689557820479327502253493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68919410427305770003004657 51689557820479327502253493)
    ·
      refine ⟨4845896045669936953336265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51689557820479327502253493 4845896045669936953336265)
      ·
        refine ⟨3634422034252452715002199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4845896045669936953336265 3634422034252452715002199)
        ·
          refine ⟨5451633051378679072503299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634422034252452715002199 5451633051378679072503299)
          ·
            refine ⟨8177449577068018608754949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451633051378679072503299 8177449577068018608754949)
            ·
              refine ⟨1533271795700253489141553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8177449577068018608754949 1533271795700253489141553)
              ·
                refine ⟨1149953846775190116856165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533271795700253489141553 1149953846775190116856165)
                ·
                  refine ⟨215616346270348146910531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1149953846775190116856165 215616346270348146910531)
                  ·
                    rfl

theorem cell22_1889601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_1889601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889601 prefixEnd_1889601 := by exact prefixLift 1889601
  have htrace : WordTrace (prefixWord ++ tailWord_1889601) baseStart_1889601 baseEnd_1889601 := by
    simpa [prefixWord, tailWord_1889601, baseEnd_1889601] using wordTrace_append hprefix tailTrace_1889601
  have hstable : (prefixWord ++ tailWord_1889601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889601).length < 2 ^ (prefixWord ++ tailWord_1889601).sum := by decide
  have hdescent : baseEnd_1889601 < baseStart_1889601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889612 : List Nat := [2, 2, 1, 3, 2, 4, 1, 7]
def baseStart_1889612 : Nat := 118140960795 + 1889612 * 2 ^ 59
def prefixEnd_1889612 : Nat := 4983230072969 + 3 ^ 40 * 1889612 * 2
def baseEnd_1889612 : Nat := 71872533815093786522951

theorem tailTrace_1889612 : CollatzResearch.WordTrace tailWord_1889612 prefixEnd_1889612 71872533815093786522951 := by
  unfold tailWord_1889612
  simp only [CollatzResearch.WordTrace]
  refine ⟨34459905815132959440827545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45946541086843945921103393 34459905815132959440827545)
  ·
    refine ⟨25844929361349719580620659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34459905815132959440827545 25844929361349719580620659)
    ·
      refine ⟨38767394042024579370930989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25844929361349719580620659 38767394042024579370930989)
      ·
        refine ⟨14537772765759217264099121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38767394042024579370930989 14537772765759217264099121)
        ·
          refine ⟨10903329574319412948074341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14537772765759217264099121 10903329574319412948074341)
          ·
            refine ⟨2044374295184889927763939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10903329574319412948074341 2044374295184889927763939)
            ·
              refine ⟨3066561442777334891645909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044374295184889927763939 3066561442777334891645909)
              ·
                refine ⟨71872533815093786522951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3066561442777334891645909 71872533815093786522951)
                ·
                  rfl

theorem cell22_1889612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 7].length) (baseStart_1889612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889612 prefixEnd_1889612 := by exact prefixLift 1889612
  have htrace : WordTrace (prefixWord ++ tailWord_1889612) baseStart_1889612 baseEnd_1889612 := by
    simpa [prefixWord, tailWord_1889612, baseEnd_1889612] using wordTrace_append hprefix tailTrace_1889612
  have hstable : (prefixWord ++ tailWord_1889612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889612).length < 2 ^ (prefixWord ++ tailWord_1889612).sum := by decide
  have hdescent : baseEnd_1889612 < baseStart_1889612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889655 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1889655 : Nat := 118140960795 + 1889655 * 2 ^ 59
def prefixEnd_1889655 : Nat := 4983230072969 + 3 ^ 40 * 1889655 * 2
def baseEnd_1889655 : Nat := 646867524114606299881427

theorem tailTrace_1889655 : CollatzResearch.WordTrace tailWord_1889655 prefixEnd_1889655 646867524114606299881427 := by
  unfold tailWord_1889655
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921379969110137225470419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45947586646073424816980279 68921379969110137225470419)
  ·
    refine ⟨103382069953665205838205629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68921379969110137225470419 103382069953665205838205629)
    ·
      refine ⟨38768276232624452189327111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103382069953665205838205629 38768276232624452189327111)
      ·
        refine ⟨58152414348936678283990667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38768276232624452189327111 58152414348936678283990667)
        ·
          refine ⟨87228621523405017425986001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58152414348936678283990667 87228621523405017425986001)
          ·
            refine ⟨65421466142553763069489501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87228621523405017425986001 65421466142553763069489501)
            ·
              refine ⟨24533049803457661151058563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65421466142553763069489501 24533049803457661151058563)
              ·
                refine ⟨36799574705186491726587845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24533049803457661151058563 36799574705186491726587845)
                ·
                  refine ⟨6899920257222467198735221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36799574705186491726587845 6899920257222467198735221)
                  ·
                    refine ⟨646867524114606299881427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6899920257222467198735221 646867524114606299881427)
                    ·
                      rfl

theorem cell22_1889655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1889655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889655 prefixEnd_1889655 := by exact prefixLift 1889655
  have htrace : WordTrace (prefixWord ++ tailWord_1889655) baseStart_1889655 baseEnd_1889655 := by
    simpa [prefixWord, tailWord_1889655, baseEnd_1889655] using wordTrace_append hprefix tailTrace_1889655
  have hstable : (prefixWord ++ tailWord_1889655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889655).length < 2 ^ (prefixWord ++ tailWord_1889655).sum := by decide
  have hdescent : baseEnd_1889655 < baseStart_1889655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889657 : List Nat := [1, 2, 1, 3, 2, 1, 5, 2, 5]
def baseStart_1889657 : Nat := 118140960795 + 1889657 * 2 ^ 59
def prefixEnd_1889657 : Nat := 4983230072969 + 3 ^ 40 * 1889657 * 2
def baseEnd_1889657 : Nat := 215622736251826320443807

theorem tailTrace_1889657 : CollatzResearch.WordTrace tailWord_1889657 prefixEnd_1889657 215622736251826320443807 := by
  unfold tailWord_1889657
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921452915102891567043225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45947635276735261044695483 68921452915102891567043225)
  ·
    refine ⟨51691089686327168675282419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68921452915102891567043225 51691089686327168675282419)
    ·
      refine ⟨77536634529490753012923629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51691089686327168675282419 77536634529490753012923629)
      ·
        refine ⟨29076237948559032379846361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77536634529490753012923629 29076237948559032379846361)
        ·
          refine ⟨21807178461419274284884771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29076237948559032379846361 21807178461419274284884771)
          ·
            refine ⟨32710767692128911427327157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21807178461419274284884771 32710767692128911427327157)
            ·
              refine ⟨3066634471137085446311921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32710767692128911427327157 3066634471137085446311921)
              ·
                refine ⟨2299975853352814084733941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066634471137085446311921 2299975853352814084733941)
                ·
                  refine ⟨215622736251826320443807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2299975853352814084733941 215622736251826320443807)
                  ·
                    rfl

theorem cell22_1889657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_1889657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889657 prefixEnd_1889657 := by exact prefixLift 1889657
  have htrace : WordTrace (prefixWord ++ tailWord_1889657) baseStart_1889657 baseEnd_1889657 := by
    simpa [prefixWord, tailWord_1889657, baseEnd_1889657] using wordTrace_append hprefix tailTrace_1889657
  have hstable : (prefixWord ++ tailWord_1889657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889657).length < 2 ^ (prefixWord ++ tailWord_1889657).sum := by decide
  have hdescent : baseEnd_1889657 < baseStart_1889657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889672 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_1889672 : Nat := 118140960795 + 1889672 * 2 ^ 59
def prefixEnd_1889672 : Nat := 4983230072969 + 3 ^ 40 * 1889672 * 2
def baseEnd_1889672 : Nat := 646873343562023922206375

theorem tailTrace_1889672 : CollatzResearch.WordTrace tailWord_1889672 prefixEnd_1889672 646873343562023922206375 := by
  unfold tailWord_1889672
  simp only [CollatzResearch.WordTrace]
  refine ⟨34461000005024274564419635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45948000006699032752559513 34461000005024274564419635)
  ·
    refine ⟨51691500007536411846629453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34461000005024274564419635 51691500007536411846629453)
    ·
      refine ⟨19384312502826154442486045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51691500007536411846629453 19384312502826154442486045)
      ·
        refine ⟨7269117188559807915932267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19384312502826154442486045 7269117188559807915932267)
        ·
          refine ⟨10903675782839711873898401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7269117188559807915932267 10903675782839711873898401)
          ·
            refine ⟨8177756837129783905423801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10903675782839711873898401 8177756837129783905423801)
            ·
              refine ⟨6133317627847337929067851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8177756837129783905423801 6133317627847337929067851)
              ·
                refine ⟨9199976441771006893601777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6133317627847337929067851 9199976441771006893601777)
                ·
                  refine ⟨6899982331328255170201333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9199976441771006893601777 6899982331328255170201333)
                  ·
                    refine ⟨646873343562023922206375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6899982331328255170201333 646873343562023922206375)
                    ·
                      rfl

theorem cell22_1889672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_1889672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889672 prefixEnd_1889672 := by exact prefixLift 1889672
  have htrace : WordTrace (prefixWord ++ tailWord_1889672) baseStart_1889672 baseEnd_1889672 := by
    simpa [prefixWord, tailWord_1889672, baseEnd_1889672] using wordTrace_append hprefix tailTrace_1889672
  have hstable : (prefixWord ++ tailWord_1889672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889672).length < 2 ^ (prefixWord ++ tailWord_1889672).sum := by decide
  have hdescent : baseEnd_1889672 < baseStart_1889672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889749 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1889749 : Nat := 118140960795 + 1889749 * 2 ^ 59
def prefixEnd_1889749 : Nat := 4983230072969 + 3 ^ 40 * 1889749 * 2
def baseEnd_1889749 : Nat := 646899702235621388031139

theorem tailTrace_1889749 : CollatzResearch.WordTrace tailWord_1889749 prefixEnd_1889749 646899702235621388031139 := by
  unfold tailWord_1889749
  simp only [CollatzResearch.WordTrace]
  refine ⟨68924808430769591279392301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45949872287179727519594867 68924808430769591279392301)
  ·
    refine ⟨25846803161538596729772113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68924808430769591279392301 25846803161538596729772113)
    ·
      refine ⟨19385102371153947547329085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25846803161538596729772113 19385102371153947547329085)
      ·
        refine ⟨7269413389182730330248407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19385102371153947547329085 7269413389182730330248407)
        ·
          refine ⟨10904120083774095495372611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7269413389182730330248407 10904120083774095495372611)
          ·
            refine ⟨16356180125661143243058917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10904120083774095495372611 16356180125661143243058917)
            ·
              refine ⟨3066783773561464358073547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16356180125661143243058917 3066783773561464358073547)
              ·
                refine ⟨4600175660342196537110321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066783773561464358073547 4600175660342196537110321)
                ·
                  refine ⟨3450131745256647402832741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4600175660342196537110321 3450131745256647402832741)
                  ·
                    refine ⟨646899702235621388031139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450131745256647402832741 646899702235621388031139)
                    ·
                      rfl

theorem cell22_1889749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1889749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889749 prefixEnd_1889749 := by exact prefixLift 1889749
  have htrace : WordTrace (prefixWord ++ tailWord_1889749) baseStart_1889749 baseEnd_1889749 := by
    simpa [prefixWord, tailWord_1889749, baseEnd_1889749] using wordTrace_append hprefix tailTrace_1889749
  have hstable : (prefixWord ++ tailWord_1889749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889749).length < 2 ^ (prefixWord ++ tailWord_1889749).sum := by decide
  have hdescent : baseEnd_1889749 < baseStart_1889749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889770 : List Nat := [3, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_1889770 : Nat := 118140960795 + 1889770 * 2 ^ 59
def prefixEnd_1889770 : Nat := 4983230072969 + 3 ^ 40 * 1889770 * 2
def baseEnd_1889770 : Nat := 215635630321594777752025

theorem tailTrace_1889770 : CollatzResearch.WordTrace tailWord_1889770 prefixEnd_1889770 215635630321594777752025 := by
  unfold tailWord_1889770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231393590923377966476691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45950382909129007910604509 17231393590923377966476691)
  ·
    refine ⟨25847090386385066949715037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17231393590923377966476691 25847090386385066949715037)
    ·
      refine ⟨9692658894894400106143139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25847090386385066949715037 9692658894894400106143139)
      ·
        refine ⟨14538988342341600159214709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9692658894894400106143139 14538988342341600159214709)
        ·
          refine ⟨1363030157094525014926379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14538988342341600159214709 1363030157094525014926379)
          ·
            refine ⟨2044545235641787522389569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363030157094525014926379 2044545235641787522389569)
            ·
              refine ⟨1533408926731340641792177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044545235641787522389569 1533408926731340641792177)
              ·
                refine ⟨1150056695048505481344133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533408926731340641792177 1150056695048505481344133)
                ·
                  refine ⟨215635630321594777752025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1150056695048505481344133 215635630321594777752025)
                  ·
                    rfl

theorem cell22_1889770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_1889770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889770 prefixEnd_1889770 := by exact prefixLift 1889770
  have htrace : WordTrace (prefixWord ++ tailWord_1889770) baseStart_1889770 baseEnd_1889770 := by
    simpa [prefixWord, tailWord_1889770, baseEnd_1889770] using wordTrace_append hprefix tailTrace_1889770
  have hstable : (prefixWord ++ tailWord_1889770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889770).length < 2 ^ (prefixWord ++ tailWord_1889770).sum := by decide
  have hdescent : baseEnd_1889770 < baseStart_1889770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889777 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1889777 : Nat := 118140960795 + 1889777 * 2 ^ 59
def prefixEnd_1889777 : Nat := 4983230072969 + 3 ^ 40 * 1889777 * 2
def baseEnd_1889777 : Nat := 646909287207838648331053

theorem tailTrace_1889777 : CollatzResearch.WordTrace tailWord_1889777 prefixEnd_1889777 646909287207838648331053 := by
  unfold tailWord_1889777
  simp only [CollatzResearch.WordTrace]
  refine ⟨68925829674668152061411585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45950553116445434707607723 68925829674668152061411585)
  ·
    refine ⟨51694372256001114046058689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68925829674668152061411585 51694372256001114046058689)
    ·
      refine ⟨38770779192000835534544017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51694372256001114046058689 38770779192000835534544017)
      ·
        refine ⟨29078084394000626650908013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38770779192000835534544017 29078084394000626650908013)
        ·
          refine ⟨10904281647750234994090505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29078084394000626650908013 10904281647750234994090505)
          ·
            refine ⟨8178211235812676245567879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10904281647750234994090505 8178211235812676245567879)
            ·
              refine ⟨12267316853719014368351819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178211235812676245567879 12267316853719014368351819)
              ·
                refine ⟨18400975280578521552527729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267316853719014368351819 18400975280578521552527729)
                ·
                  refine ⟨13800731460433891164395797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18400975280578521552527729 13800731460433891164395797)
                  ·
                    refine ⟨646909287207838648331053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13800731460433891164395797 646909287207838648331053)
                    ·
                      rfl

theorem cell22_1889777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1889777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889777 prefixEnd_1889777 := by exact prefixLift 1889777
  have htrace : WordTrace (prefixWord ++ tailWord_1889777) baseStart_1889777 baseEnd_1889777 := by
    simpa [prefixWord, tailWord_1889777, baseEnd_1889777] using wordTrace_append hprefix tailTrace_1889777
  have hstable : (prefixWord ++ tailWord_1889777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889777).length < 2 ^ (prefixWord ++ tailWord_1889777).sum := by decide
  have hdescent : baseEnd_1889777 < baseStart_1889777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889781 : List Nat := [1, 3, 5, 1, 1, 3, 1, 7]
def baseStart_1889781 : Nat := 118140960795 + 1889781 * 2 ^ 59
def prefixEnd_1889781 : Nat := 4983230072969 + 3 ^ 40 * 1889781 * 2
def baseEnd_1889781 : Nat := 71878961832175996803449

theorem tailTrace_1889781 : CollatzResearch.WordTrace tailWord_1889781 prefixEnd_1889781 71878961832175996803449 := by
  unfold tailWord_1889781
  simp only [CollatzResearch.WordTrace]
  refine ⟨68925975566653660744557197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45950650377769107163038131 68925975566653660744557197)
  ·
    refine ⟨25847240837495122779208949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68925975566653660744557197 25847240837495122779208949)
    ·
      refine ⟨2423178828515167760550839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25847240837495122779208949 2423178828515167760550839)
      ·
        refine ⟨3634768242772751640826259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423178828515167760550839 3634768242772751640826259)
        ·
          refine ⟨5452152364159127461239389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634768242772751640826259 5452152364159127461239389)
          ·
            refine ⟨2044557136559672797964771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5452152364159127461239389 2044557136559672797964771)
            ·
              refine ⟨3066835704839509196947157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044557136559672797964771 3066835704839509196947157)
              ·
                refine ⟨71878961832175996803449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3066835704839509196947157 71878961832175996803449)
                ·
                  rfl

theorem cell22_1889781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 7].length) (baseStart_1889781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889781 prefixEnd_1889781 := by exact prefixLift 1889781
  have htrace : WordTrace (prefixWord ++ tailWord_1889781) baseStart_1889781 baseEnd_1889781 := by
    simpa [prefixWord, tailWord_1889781, baseEnd_1889781] using wordTrace_append hprefix tailTrace_1889781
  have hstable : (prefixWord ++ tailWord_1889781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889781).length < 2 ^ (prefixWord ++ tailWord_1889781).sum := by decide
  have hdescent : baseEnd_1889781 < baseStart_1889781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889813 : List Nat := [1, 3, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_1889813 : Nat := 118140960795 + 1889813 * 2 ^ 59
def prefixEnd_1889813 : Nat := 4983230072969 + 3 ^ 40 * 1889813 * 2
def baseEnd_1889813 : Nat := 646921610743546554430943

theorem tailTrace_1889813 : CollatzResearch.WordTrace tailWord_1889813 prefixEnd_1889813 646921610743546554430943 := by
  unfold tailWord_1889813
  simp only [CollatzResearch.WordTrace]
  refine ⟨68927142702537730209722093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45951428468358486806481395 68927142702537730209722093)
  ·
    refine ⟨25847678513451648828645785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68927142702537730209722093 25847678513451648828645785)
    ·
      refine ⟨19385758885088736621484339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25847678513451648828645785 19385758885088736621484339)
      ·
        refine ⟨29078638327633104932226509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19385758885088736621484339 29078638327633104932226509)
        ·
          refine ⟨10904489372862414349584941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29078638327633104932226509 10904489372862414349584941)
          ·
            refine ⟨4089183514823405381094353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10904489372862414349584941 4089183514823405381094353)
            ·
              refine ⟨3066887636117554035820765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089183514823405381094353 3066887636117554035820765)
              ·
                refine ⟨1150082863544082763432787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3066887636117554035820765 1150082863544082763432787)
                ·
                  refine ⟨1725124295316124145149181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150082863544082763432787 1725124295316124145149181)
                  ·
                    refine ⟨646921610743546554430943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1725124295316124145149181 646921610743546554430943)
                    ·
                      rfl

theorem cell22_1889813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_1889813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889813 prefixEnd_1889813 := by exact prefixLift 1889813
  have htrace : WordTrace (prefixWord ++ tailWord_1889813) baseStart_1889813 baseEnd_1889813 := by
    simpa [prefixWord, tailWord_1889813, baseEnd_1889813] using wordTrace_append hprefix tailTrace_1889813
  have hstable : (prefixWord ++ tailWord_1889813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889813).length < 2 ^ (prefixWord ++ tailWord_1889813).sum := by decide
  have hdescent : baseEnd_1889813 < baseStart_1889813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889824 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_1889824 : Nat := 118140960795 + 1889824 * 2 ^ 59
def prefixEnd_1889824 : Nat := 4983230072969 + 3 ^ 40 * 1889824 * 2
def baseEnd_1889824 : Nat := 646925376268346192405909

theorem tailTrace_1889824 : CollatzResearch.WordTrace tailWord_1889824 prefixEnd_1889824 646925376268346192405909 := by
  unfold tailWord_1889824
  simp only [CollatzResearch.WordTrace]
  refine ⟨34463771952748939544186263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45951695936998586058915017 34463771952748939544186263)
  ·
    refine ⟨51695657929123409316279395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34463771952748939544186263 51695657929123409316279395)
    ·
      refine ⟨77543486893685113974419093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51695657929123409316279395 77543486893685113974419093)
      ·
        refine ⟨3634850948141489717550895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77543486893685113974419093 3634850948141489717550895)
        ·
          refine ⟨5452276422212234576326343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634850948141489717550895 5452276422212234576326343)
          ·
            refine ⟨8178414633318351864489515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5452276422212234576326343 8178414633318351864489515)
            ·
              refine ⟨12267621949977527796734273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178414633318351864489515 12267621949977527796734273)
              ·
                refine ⟨9200716462483145847550705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12267621949977527796734273 9200716462483145847550705)
                ·
                  refine ⟨6900537346862359385663029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200716462483145847550705 6900537346862359385663029)
                  ·
                    refine ⟨646925376268346192405909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6900537346862359385663029 646925376268346192405909)
                    ·
                      rfl

theorem cell22_1889824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_1889824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889824 prefixEnd_1889824 := by exact prefixLift 1889824
  have htrace : WordTrace (prefixWord ++ tailWord_1889824) baseStart_1889824 baseEnd_1889824 := by
    simpa [prefixWord, tailWord_1889824, baseEnd_1889824] using wordTrace_append hprefix tailTrace_1889824
  have hstable : (prefixWord ++ tailWord_1889824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889824).length < 2 ^ (prefixWord ++ tailWord_1889824).sum := by decide
  have hdescent : baseEnd_1889824 < baseStart_1889824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889991 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1889991 : Nat := 118140960795 + 1889991 * 2 ^ 59
def prefixEnd_1889991 : Nat := 4983230072969 + 3 ^ 40 * 1889991 * 2
def baseEnd_1889991 : Nat := 646982543781213423480397

theorem tailTrace_1889991 : CollatzResearch.WordTrace tailWord_1889991 prefixEnd_1889991 646982543781213423480397 := by
  unfold tailWord_1889991
  simp only [CollatzResearch.WordTrace]
  refine ⟨68933634895892866609701827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45955756597261911073134551 68933634895892866609701827)
  ·
    refine ⟨103400452343839299914552741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68933634895892866609701827 103400452343839299914552741)
    ·
      refine ⟨19387584814469868733978639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103400452343839299914552741 19387584814469868733978639)
      ·
        refine ⟨29081377221704803100967959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19387584814469868733978639 29081377221704803100967959)
        ·
          refine ⟨43622065832557204651451939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29081377221704803100967959 43622065832557204651451939)
          ·
            refine ⟨65433098748835806977177909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43622065832557204651451939 65433098748835806977177909)
            ·
              refine ⟨6134353007703356904110429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65433098748835806977177909 6134353007703356904110429)
              ·
                refine ⟨2300382377888758839041411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6134353007703356904110429 2300382377888758839041411)
                ·
                  refine ⟨3450573566833138258562117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300382377888758839041411 3450573566833138258562117)
                  ·
                    refine ⟨646982543781213423480397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450573566833138258562117 646982543781213423480397)
                    ·
                      rfl

theorem cell22_1889991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1889991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1889991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1889991 prefixEnd_1889991 := by exact prefixLift 1889991
  have htrace : WordTrace (prefixWord ++ tailWord_1889991) baseStart_1889991 baseEnd_1889991 := by
    simpa [prefixWord, tailWord_1889991, baseEnd_1889991] using wordTrace_append hprefix tailTrace_1889991
  have hstable : (prefixWord ++ tailWord_1889991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889991).length < 2 ^ (prefixWord ++ tailWord_1889991).sum := by decide
  have hdescent : baseEnd_1889991 < baseStart_1889991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890038 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1890038 : Nat := 118140960795 + 1890038 * 2 ^ 59
def prefixEnd_1890038 : Nat := 4983230072969 + 3 ^ 40 * 1890038 * 2
def baseEnd_1890038 : Nat := 646998632841720967555253

theorem tailTrace_1890038 : CollatzResearch.WordTrace tailWord_1890038 prefixEnd_1890038 646998632841720967555253 := by
  unfold tailWord_1890038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308459320420162102291423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45956899417815062424441845 4308459320420162102291423)
  ·
    refine ⟨6462688980630243153437135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4308459320420162102291423 6462688980630243153437135)
    ·
      refine ⟨9694033470945364730155703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6462688980630243153437135 9694033470945364730155703)
      ·
        refine ⟨14541050206418047095233555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694033470945364730155703 14541050206418047095233555)
        ·
          refine ⟨21811575309627070642850333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14541050206418047095233555 21811575309627070642850333)
          ·
            refine ⟨8179340741110151491068875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21811575309627070642850333 8179340741110151491068875)
            ·
              refine ⟨12269011111665227236603313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8179340741110151491068875 12269011111665227236603313)
              ·
                refine ⟨9201758333748920427452485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12269011111665227236603313 9201758333748920427452485)
                ·
                  refine ⟨1725329687577922580147341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9201758333748920427452485 1725329687577922580147341)
                  ·
                    refine ⟨646998632841720967555253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1725329687577922580147341 646998632841720967555253)
                    ·
                      rfl

theorem cell22_1890038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1890038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890038 prefixEnd_1890038 := by exact prefixLift 1890038
  have htrace : WordTrace (prefixWord ++ tailWord_1890038) baseStart_1890038 baseEnd_1890038 := by
    simpa [prefixWord, tailWord_1890038, baseEnd_1890038] using wordTrace_append hprefix tailTrace_1890038
  have hstable : (prefixWord ++ tailWord_1890038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890038).length < 2 ^ (prefixWord ++ tailWord_1890038).sum := by decide
  have hdescent : baseEnd_1890038 < baseStart_1890038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890171 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 4, 4]
def baseStart_1890171 : Nat := 118140960795 + 1890171 * 2 ^ 59
def prefixEnd_1890171 : Nat := 4983230072969 + 3 ^ 40 * 1890171 * 2
def baseEnd_1890171 : Nat := 647044161459752953979845

theorem tailTrace_1890171 : CollatzResearch.WordTrace tailWord_1890171 prefixEnd_1890171 647044161459752953979845 := by
  unfold tailWord_1890171
  simp only [CollatzResearch.WordTrace]
  refine ⟨68940200035240757351254367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45960133356827171567502911 68940200035240757351254367)
  ·
    refine ⟨103410300052861136026881551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68940200035240757351254367 103410300052861136026881551)
    ·
      refine ⟨155115450079291704040322327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103410300052861136026881551 155115450079291704040322327)
      ·
        refine ⟨232673175118937556060483491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155115450079291704040322327 232673175118937556060483491)
        ·
          refine ⟨349009762678406334090725237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232673175118937556060483491 349009762678406334090725237)
          ·
            refine ⟨32719665251100593821005491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349009762678406334090725237 32719665251100593821005491)
            ·
              refine ⟨49079497876650890731508237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32719665251100593821005491 49079497876650890731508237)
              ·
                refine ⟨18404811703744084024315589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49079497876650890731508237 18404811703744084024315589)
                ·
                  refine ⟨3450902194452015754559173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18404811703744084024315589 3450902194452015754559173)
                  ·
                    refine ⟨647044161459752953979845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3450902194452015754559173 647044161459752953979845)
                    ·
                      rfl

theorem cell22_1890171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_1890171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890171 prefixEnd_1890171 := by exact prefixLift 1890171
  have htrace : WordTrace (prefixWord ++ tailWord_1890171) baseStart_1890171 baseEnd_1890171 := by
    simpa [prefixWord, tailWord_1890171, baseEnd_1890171] using wordTrace_append hprefix tailTrace_1890171
  have hstable : (prefixWord ++ tailWord_1890171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890171).length < 2 ^ (prefixWord ++ tailWord_1890171).sum := by decide
  have hdescent : baseEnd_1890171 < baseStart_1890171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890209 : List Nat := [1, 2, 3, 4, 3, 1, 1, 3, 4]
def baseStart_1890209 : Nat := 118140960795 + 1890209 * 2 ^ 59
def prefixEnd_1890209 : Nat := 4983230072969 + 3 ^ 40 * 1890209 * 2
def baseEnd_1890209 : Nat := 215685723212111173843243

theorem tailTrace_1890209 : CollatzResearch.WordTrace tailWord_1890209 prefixEnd_1890209 215685723212111173843243 := by
  unfold tailWord_1890209
  simp only [CollatzResearch.WordTrace]
  refine ⟨68941586009103089841137681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45961057339402059894091787 68941586009103089841137681)
  ·
    refine ⟨51706189506827317380853261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68941586009103089841137681 51706189506827317380853261)
    ·
      refine ⟨19389821065060244017819973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51706189506827317380853261 19389821065060244017819973)
      ·
        refine ⟨3635591449698795753341245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19389821065060244017819973 3635591449698795753341245)
        ·
          refine ⟨1363346793637048407502967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3635591449698795753341245 1363346793637048407502967)
          ·
            refine ⟨2045020190455572611254451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363346793637048407502967 2045020190455572611254451)
            ·
              refine ⟨3067530285683358916881677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045020190455572611254451 3067530285683358916881677)
              ·
                refine ⟨1150323857131259593830629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3067530285683358916881677 1150323857131259593830629)
                ·
                  refine ⟨215685723212111173843243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1150323857131259593830629 215685723212111173843243)
                  ·
                    rfl

theorem cell22_1890209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_1890209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890209 prefixEnd_1890209 := by exact prefixLift 1890209
  have htrace : WordTrace (prefixWord ++ tailWord_1890209) baseStart_1890209 baseEnd_1890209 := by
    simpa [prefixWord, tailWord_1890209, baseEnd_1890209] using wordTrace_append hprefix tailTrace_1890209
  have hstable : (prefixWord ++ tailWord_1890209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890209).length < 2 ^ (prefixWord ++ tailWord_1890209).sum := by decide
  have hdescent : baseEnd_1890209 < baseStart_1890209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890286 : List Nat := [4, 1, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_1890286 : Nat := 118140960795 + 1890286 * 2 ^ 59
def prefixEnd_1890286 : Nat := 4983230072969 + 3 ^ 40 * 1890286 * 2
def baseEnd_1890286 : Nat := 647083528309930987354493

theorem tailTrace_1890286 : CollatzResearch.WordTrace tailWord_1890286 prefixEnd_1890286 647083528309930987354493 := by
  unfold tailWord_1890286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8618049303728016498961339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45962929619882754661127141 8618049303728016498961339)
  ·
    refine ⟨12927073955592024748442009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8618049303728016498961339 12927073955592024748442009)
    ·
      refine ⟨9695305466694018561331507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12927073955592024748442009 9695305466694018561331507)
      ·
        refine ⟨14542958200041027841997261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9695305466694018561331507 14542958200041027841997261)
        ·
          refine ⟨5453609325015385440748973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14542958200041027841997261 5453609325015385440748973)
          ·
            refine ⟨2045103496880769540280865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5453609325015385440748973 2045103496880769540280865)
            ·
              refine ⟨1533827622660577155210649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045103496880769540280865 1533827622660577155210649)
              ·
                refine ⟨1150370716995432866407987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533827622660577155210649 1150370716995432866407987)
                ·
                  refine ⟨1725556075493149299611981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150370716995432866407987 1725556075493149299611981)
                  ·
                    refine ⟨647083528309930987354493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1725556075493149299611981 647083528309930987354493)
                    ·
                      rfl

theorem cell22_1890286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_1890286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890286 prefixEnd_1890286 := by exact prefixLift 1890286
  have htrace : WordTrace (prefixWord ++ tailWord_1890286) baseStart_1890286 baseEnd_1890286 := by
    simpa [prefixWord, tailWord_1890286, baseEnd_1890286] using wordTrace_append hprefix tailTrace_1890286
  have hstable : (prefixWord ++ tailWord_1890286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890286).length < 2 ^ (prefixWord ++ tailWord_1890286).sum := by decide
  have hdescent : baseEnd_1890286 < baseStart_1890286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890338 : List Nat := [3, 3, 1, 1, 1, 2, 11]
def baseStart_1890338 : Nat := 118140960795 + 1890338 * 2 ^ 59
def prefixEnd_1890338 : Nat := 4983230072969 + 3 ^ 40 * 1890338 * 2
def baseEnd_1890338 : Nat := 23966715887874821668679

theorem tailTrace_1890338 : CollatzResearch.WordTrace tailWord_1890338 prefixEnd_1890338 23966715887874821668679 := by
  unfold tailWord_1890338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236572756408936218145917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45964194017090496581722445 17236572756408936218145917)
  ·
    refine ⟨6463714783653351081804719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17236572756408936218145917 6463714783653351081804719)
    ·
      refine ⟨9695572175480026622707079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6463714783653351081804719 9695572175480026622707079)
      ·
        refine ⟨14543358263220039934060619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9695572175480026622707079 14543358263220039934060619)
        ·
          refine ⟨21815037394830059901090929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14543358263220039934060619 21815037394830059901090929)
          ·
            refine ⟨16361278046122544925818197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21815037394830059901090929 16361278046122544925818197)
            ·
              refine ⟨23966715887874821668679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16361278046122544925818197 23966715887874821668679)
              ·
                rfl

theorem cell22_1890338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 11].length) (baseStart_1890338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890338 prefixEnd_1890338 := by exact prefixLift 1890338
  have htrace : WordTrace (prefixWord ++ tailWord_1890338) baseStart_1890338 baseEnd_1890338 := by
    simpa [prefixWord, tailWord_1890338, baseEnd_1890338] using wordTrace_append hprefix tailTrace_1890338
  have hstable : (prefixWord ++ tailWord_1890338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890338).length < 2 ^ (prefixWord ++ tailWord_1890338).sum := by decide
  have hdescent : baseEnd_1890338 < baseStart_1890338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890460 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1890460 : Nat := 118140960795 + 1890460 * 2 ^ 59
def prefixEnd_1890460 : Nat := 4983230072969 + 3 ^ 40 * 1890460 * 2
def baseEnd_1890460 : Nat := 647143092065852533503959

theorem tailTrace_1890460 : CollatzResearch.WordTrace tailWord_1890460 prefixEnd_1890460 647143092065852533503959 := by
  unfold tailWord_1890460
  simp only [CollatzResearch.WordTrace]
  refine ⟨34475370365596879854262417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45967160487462506472349889 34475370365596879854262417)
  ·
    refine ⟨25856527774197659890696813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34475370365596879854262417 25856527774197659890696813)
    ·
      refine ⟨9696197915324122459011305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25856527774197659890696813 9696197915324122459011305)
      ·
        refine ⟨7272148436493091844258479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9696197915324122459011305 7272148436493091844258479)
        ·
          refine ⟨10908222654739637766387719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7272148436493091844258479 10908222654739637766387719)
          ·
            refine ⟨16362333982109456649581579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10908222654739637766387719 16362333982109456649581579)
            ·
              refine ⟨24543500973164184974372369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16362333982109456649581579 24543500973164184974372369)
              ·
                refine ⟨18407625729873138730779277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24543500973164184974372369 18407625729873138730779277)
                ·
                  refine ⟨6902859648702427024042229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18407625729873138730779277 6902859648702427024042229)
                  ·
                    refine ⟨647143092065852533503959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6902859648702427024042229 647143092065852533503959)
                    ·
                      rfl

theorem cell22_1890460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1890460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890460 prefixEnd_1890460 := by exact prefixLift 1890460
  have htrace : WordTrace (prefixWord ++ tailWord_1890460) baseStart_1890460 baseEnd_1890460 := by
    simpa [prefixWord, tailWord_1890460, baseEnd_1890460] using wordTrace_append hprefix tailTrace_1890460
  have hstable : (prefixWord ++ tailWord_1890460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890460).length < 2 ^ (prefixWord ++ tailWord_1890460).sum := by decide
  have hdescent : baseEnd_1890460 < baseStart_1890460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890477 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1890477 : Nat := 118140960795 + 1890477 * 2 ^ 59
def prefixEnd_1890477 : Nat := 4983230072969 + 3 ^ 40 * 1890477 * 2
def baseEnd_1890477 : Nat := 647148911513270155828907

theorem tailTrace_1890477 : CollatzResearch.WordTrace tailWord_1890477 prefixEnd_1890477 647148911513270155828907 := by
  unfold tailWord_1890477
  simp only [CollatzResearch.WordTrace]
  refine ⟨68951360772132171611893685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45967573848088114407929123 68951360772132171611893685)
  ·
    refine ⟨6464190072387391088615033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68951360772132171611893685 6464190072387391088615033)
    ·
      refine ⟨4848142554290543316461275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6464190072387391088615033 4848142554290543316461275)
      ·
        refine ⟨7272213831435814974691913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4848142554290543316461275 7272213831435814974691913)
        ·
          refine ⟨5454160373576861231018935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7272213831435814974691913 5454160373576861231018935)
          ·
            refine ⟨8181240560365291846528403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454160373576861231018935 8181240560365291846528403)
            ·
              refine ⟨12271860840547937769792605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181240560365291846528403 12271860840547937769792605)
              ·
                refine ⟨4601947815205476663672227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12271860840547937769792605 4601947815205476663672227)
                ·
                  refine ⟨6902921722808214995508341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4601947815205476663672227 6902921722808214995508341)
                  ·
                    refine ⟨647148911513270155828907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6902921722808214995508341 647148911513270155828907)
                    ·
                      rfl

theorem cell22_1890477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1890477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890477 prefixEnd_1890477 := by exact prefixLift 1890477
  have htrace : WordTrace (prefixWord ++ tailWord_1890477) baseStart_1890477 baseEnd_1890477 := by
    simpa [prefixWord, tailWord_1890477, baseEnd_1890477] using wordTrace_append hprefix tailTrace_1890477
  have hstable : (prefixWord ++ tailWord_1890477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890477).length < 2 ^ (prefixWord ++ tailWord_1890477).sum := by decide
  have hdescent : baseEnd_1890477 < baseStart_1890477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890492 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_1890492 : Nat := 118140960795 + 1890492 * 2 ^ 59
def prefixEnd_1890492 : Nat := 4983230072969 + 3 ^ 40 * 1890492 * 2
def baseEnd_1890492 : Nat := 647154046319815116703861

theorem tailTrace_1890492 : CollatzResearch.WordTrace tailWord_1890492 prefixEnd_1890492 647154046319815116703861 := by
  unfold tailWord_1890492
  simp only [CollatzResearch.WordTrace]
  refine ⟨34475953933538914586844865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45967938578051886115793153 34475953933538914586844865)
  ·
    refine ⟨25856965450154185940133649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34475953933538914586844865 25856965450154185940133649)
    ·
      refine ⟨19392724087615639455100237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25856965450154185940133649 19392724087615639455100237)
      ·
        refine ⟨7272271532855864795662589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19392724087615639455100237 7272271532855864795662589)
        ·
          refine ⟨2727101824820949298373471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7272271532855864795662589 2727101824820949298373471)
          ·
            refine ⟨4090652737231423947560207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727101824820949298373471 4090652737231423947560207)
            ·
              refine ⟨6135979105847135921340311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090652737231423947560207 6135979105847135921340311)
              ·
                refine ⟨9203968658770703882010467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135979105847135921340311 9203968658770703882010467)
                ·
                  refine ⟨13805952988156055823015701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9203968658770703882010467 13805952988156055823015701)
                  ·
                    refine ⟨647154046319815116703861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13805952988156055823015701 647154046319815116703861)
                    ·
                      rfl

theorem cell22_1890492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_1890492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890492 prefixEnd_1890492 := by exact prefixLift 1890492
  have htrace : WordTrace (prefixWord ++ tailWord_1890492) baseStart_1890492 baseEnd_1890492 := by
    simpa [prefixWord, tailWord_1890492, baseEnd_1890492] using wordTrace_append hprefix tailTrace_1890492
  have hstable : (prefixWord ++ tailWord_1890492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890492).length < 2 ^ (prefixWord ++ tailWord_1890492).sum := by decide
  have hdescent : baseEnd_1890492 < baseStart_1890492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890498 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1890498 : Nat := 118140960795 + 1890498 * 2 ^ 59
def prefixEnd_1890498 : Nat := 4983230072969 + 3 ^ 40 * 1890498 * 2
def baseEnd_1890498 : Nat := 647156100242433101053843

theorem tailTrace_1890498 : CollatzResearch.WordTrace tailWord_1890498 prefixEnd_1890498 647156100242433101053843 := by
  unfold tailWord_1890498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17238031676264023049602037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45968084470037394798938765 17238031676264023049602037)
  ·
    refine ⟨1616065469649752160900191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17238031676264023049602037 1616065469649752160900191)
    ·
      refine ⟨2424098204474628241350287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616065469649752160900191 2424098204474628241350287)
      ·
        refine ⟨3636147306711942362025431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424098204474628241350287 3636147306711942362025431)
        ·
          refine ⟨5454220960067913543038147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636147306711942362025431 5454220960067913543038147)
          ·
            refine ⟨8181331440101870314557221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454220960067913543038147 8181331440101870314557221)
            ·
              refine ⟨1533999645019100683979479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8181331440101870314557221 1533999645019100683979479)
              ·
                refine ⟨2300999467528651025969219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533999645019100683979479 2300999467528651025969219)
                ·
                  refine ⟨3451499201292976538953829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300999467528651025969219 3451499201292976538953829)
                  ·
                    refine ⟨647156100242433101053843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3451499201292976538953829 647156100242433101053843)
                    ·
                      rfl

theorem cell22_1890498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1890498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890498 prefixEnd_1890498 := by exact prefixLift 1890498
  have htrace : WordTrace (prefixWord ++ tailWord_1890498) baseStart_1890498 baseEnd_1890498 := by
    simpa [prefixWord, tailWord_1890498, baseEnd_1890498] using wordTrace_append hprefix tailTrace_1890498
  have hstable : (prefixWord ++ tailWord_1890498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890498).length < 2 ^ (prefixWord ++ tailWord_1890498).sum := by decide
  have hdescent : baseEnd_1890498 < baseStart_1890498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890522 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1890522 : Nat := 118140960795 + 1890522 * 2 ^ 59
def prefixEnd_1890522 : Nat := 4983230072969 + 3 ^ 40 * 1890522 * 2
def baseEnd_1890522 : Nat := 647164315932905038453769

theorem tailTrace_1890522 : CollatzResearch.WordTrace tailWord_1890522 prefixEnd_1890522 647164315932905038453769 := by
  unfold tailWord_1890522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17238250514242286074320455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45968668037979429531521213 17238250514242286074320455)
  ·
    refine ⟨25857375771363429111480683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17238250514242286074320455 25857375771363429111480683)
    ·
      refine ⟨38786063657045143667221025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25857375771363429111480683 38786063657045143667221025)
      ·
        refine ⟨29089547742783857750415769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38786063657045143667221025 29089547742783857750415769)
        ·
          refine ⟨21817160807087893312811827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29089547742783857750415769 21817160807087893312811827)
          ·
            refine ⟨32725741210631839969217741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21817160807087893312811827 32725741210631839969217741)
            ·
              refine ⟨12272152953986939988456653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32725741210631839969217741 12272152953986939988456653)
              ·
                refine ⟨4602057357745102495671245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12272152953986939988456653 4602057357745102495671245)
                ·
                  refine ⟨1725771509154413435876717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4602057357745102495671245 1725771509154413435876717)
                  ·
                    refine ⟨647164315932905038453769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1725771509154413435876717 647164315932905038453769)
                    ·
                      rfl

theorem cell22_1890522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1890522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890522 prefixEnd_1890522 := by exact prefixLift 1890522
  have htrace : WordTrace (prefixWord ++ tailWord_1890522) baseStart_1890522 baseEnd_1890522 := by
    simpa [prefixWord, tailWord_1890522, baseEnd_1890522] using wordTrace_append hprefix tailTrace_1890522
  have hstable : (prefixWord ++ tailWord_1890522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890522).length < 2 ^ (prefixWord ++ tailWord_1890522).sum := by decide
  have hdescent : baseEnd_1890522 < baseStart_1890522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890541 : List Nat := [1, 5, 1, 2, 4, 1, 2, 6]
def baseStart_1890541 : Nat := 118140960795 + 1890541 * 2 ^ 59
def prefixEnd_1890541 : Nat := 4983230072969 + 3 ^ 40 * 1890541 * 2
def baseEnd_1890541 : Nat := 71907868891243924692079

theorem tailTrace_1890541 : CollatzResearch.WordTrace tailWord_1890541 prefixEnd_1890541 71907868891243924692079 := by
  unfold tailWord_1890541
  simp only [CollatzResearch.WordTrace]
  refine ⟨68953695043900310542223477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45969130029266873694815651 68953695043900310542223477)
  ·
    refine ⟨6464408910365654113333451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68953695043900310542223477 6464408910365654113333451)
    ·
      refine ⟨9696613365548481170000177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6464408910365654113333451 9696613365548481170000177)
      ·
        refine ⟨7272460024161360877500133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9696613365548481170000177 7272460024161360877500133)
        ·
          refine ⟨1363586254530255164531275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7272460024161360877500133 1363586254530255164531275)
          ·
            refine ⟨2045379381795382746796913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363586254530255164531275 2045379381795382746796913)
            ·
              refine ⟨1534034536346537060097685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045379381795382746796913 1534034536346537060097685)
              ·
                refine ⟨71907868891243924692079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1534034536346537060097685 71907868891243924692079)
                ·
                  rfl

theorem cell22_1890541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 6].length) (baseStart_1890541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890541 prefixEnd_1890541 := by exact prefixLift 1890541
  have htrace : WordTrace (prefixWord ++ tailWord_1890541) baseStart_1890541 baseEnd_1890541 := by
    simpa [prefixWord, tailWord_1890541, baseEnd_1890541] using wordTrace_append hprefix tailTrace_1890541
  have hstable : (prefixWord ++ tailWord_1890541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890541).length < 2 ^ (prefixWord ++ tailWord_1890541).sum := by decide
  have hdescent : baseEnd_1890541 < baseStart_1890541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890556 : List Nat := [2, 2, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_1890556 : Nat := 118140960795 + 1890556 * 2 ^ 59
def prefixEnd_1890556 : Nat := 4983230072969 + 3 ^ 40 * 1890556 * 2
def baseEnd_1890556 : Nat := 647175954827740283103665

theorem tailTrace_1890556 : CollatzResearch.WordTrace tailWord_1890556 prefixEnd_1890556 647175954827740283103665 := by
  unfold tailWord_1890556
  simp only [CollatzResearch.WordTrace]
  refine ⟨34477121069422984052009761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45969494759230645402679681 34477121069422984052009761)
  ·
    refine ⟨25857840802067238039007321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34477121069422984052009761 25857840802067238039007321)
    ·
      refine ⟨19393380601550428529255491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25857840802067238039007321 19393380601550428529255491)
      ·
        refine ⟨29090070902325642793883237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19393380601550428529255491 29090070902325642793883237)
        ·
          refine ⟨5454388294186058023853107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29090070902325642793883237 5454388294186058023853107)
          ·
            refine ⟨8181582441279087035779661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454388294186058023853107 8181582441279087035779661)
            ·
              refine ⟨3068093415479657638417373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8181582441279087035779661 3068093415479657638417373)
              ·
                refine ⟨1150535030804871614406515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3068093415479657638417373 1150535030804871614406515)
                ·
                  refine ⟨1725802546207307421609773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150535030804871614406515 1725802546207307421609773)
                  ·
                    refine ⟨647175954827740283103665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1725802546207307421609773 647175954827740283103665)
                    ·
                      rfl

theorem cell22_1890556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_1890556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890556 prefixEnd_1890556 := by exact prefixLift 1890556
  have htrace : WordTrace (prefixWord ++ tailWord_1890556) baseStart_1890556 baseEnd_1890556 := by
    simpa [prefixWord, tailWord_1890556, baseEnd_1890556] using wordTrace_append hprefix tailTrace_1890556
  have hstable : (prefixWord ++ tailWord_1890556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890556).length < 2 ^ (prefixWord ++ tailWord_1890556).sum := by decide
  have hdescent : baseEnd_1890556 < baseStart_1890556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890586 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_1890586 : Nat := 118140960795 + 1890586 * 2 ^ 59
def prefixEnd_1890586 : Nat := 4983230072969 + 3 ^ 40 * 1890586 * 2
def baseEnd_1890586 : Nat := 215728741480276734951191

theorem tailTrace_1890586 : CollatzResearch.WordTrace tailWord_1890586 prefixEnd_1890586 215728741480276734951191 := by
  unfold tailWord_1890586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17238834082184320806902903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45970224219158188818407741 17238834082184320806902903)
  ·
    refine ⟨25858251123276481210354355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17238834082184320806902903 25858251123276481210354355)
    ·
      refine ⟨38787376684914721815531533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25858251123276481210354355 38787376684914721815531533)
      ·
        refine ⟨14545266256843020680824325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38787376684914721815531533 14545266256843020680824325)
        ·
          refine ⟨2727237423158066377654561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14545266256843020680824325 2727237423158066377654561)
          ·
            refine ⟨2045428067368549783240921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727237423158066377654561 2045428067368549783240921)
            ·
              refine ⟨1534071050526412337430691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045428067368549783240921 1534071050526412337430691)
              ·
                refine ⟨2301106575789618506146037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534071050526412337430691 2301106575789618506146037)
                ·
                  refine ⟨215728741480276734951191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2301106575789618506146037 215728741480276734951191)
                  ·
                    rfl

theorem cell22_1890586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_1890586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890586 prefixEnd_1890586 := by exact prefixLift 1890586
  have htrace : WordTrace (prefixWord ++ tailWord_1890586) baseStart_1890586 baseEnd_1890586 := by
    simpa [prefixWord, tailWord_1890586, baseEnd_1890586] using wordTrace_append hprefix tailTrace_1890586
  have hstable : (prefixWord ++ tailWord_1890586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890586).length < 2 ^ (prefixWord ++ tailWord_1890586).sum := by decide
  have hdescent : baseEnd_1890586 < baseStart_1890586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890627 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 2, 4]
def baseStart_1890627 : Nat := 118140960795 + 1890627 * 2 ^ 59
def prefixEnd_1890627 : Nat := 4983230072969 + 3 ^ 40 * 1890627 * 2
def baseEnd_1890627 : Nat := 647200259578719764578447

theorem tailTrace_1890627 : CollatzResearch.WordTrace tailWord_1890627 prefixEnd_1890627 647200259578719764578447 := by
  unfold tailWord_1890627
  simp only [CollatzResearch.WordTrace]
  refine ⟨68956831721588747229854135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45971221147725831486569423 68956831721588747229854135)
  ·
    refine ⟨103435247582383120844781203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68956831721588747229854135 103435247582383120844781203)
    ·
      refine ⟨155152871373574681267171805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103435247582383120844781203 155152871373574681267171805)
      ·
        refine ⟨58182326765090505475189427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155152871373574681267171805 58182326765090505475189427)
        ·
          refine ⟨87273490147635758212784141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58182326765090505475189427 87273490147635758212784141)
          ·
            refine ⟨32727558805363409329794053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87273490147635758212784141 32727558805363409329794053)
            ·
              refine ⟨6136417276005639249336385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32727558805363409329794053 6136417276005639249336385)
              ·
                refine ⟨4602312957004229437002289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6136417276005639249336385 4602312957004229437002289)
                ·
                  refine ⟨3451734717753172077751717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4602312957004229437002289 3451734717753172077751717)
                  ·
                    refine ⟨647200259578719764578447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3451734717753172077751717 647200259578719764578447)
                    ·
                      rfl

theorem cell22_1890627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_1890627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890627 prefixEnd_1890627 := by exact prefixLift 1890627
  have htrace : WordTrace (prefixWord ++ tailWord_1890627) baseStart_1890627 baseEnd_1890627 := by
    simpa [prefixWord, tailWord_1890627, baseEnd_1890627] using wordTrace_append hprefix tailTrace_1890627
  have hstable : (prefixWord ++ tailWord_1890627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890627).length < 2 ^ (prefixWord ++ tailWord_1890627).sum := by decide
  have hdescent : baseEnd_1890627 < baseStart_1890627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890642 : List Nat := [3, 2, 2, 1, 1, 1, 5, 7]
def baseStart_1890642 : Nat := 118140960795 + 1890642 * 2 ^ 59
def prefixEnd_1890642 : Nat := 4983230072969 + 3 ^ 40 * 1890642 * 2
def baseEnd_1890642 : Nat := 71911710487251636161489

theorem tailTrace_1890642 : CollatzResearch.WordTrace tailWord_1890642 prefixEnd_1890642 71911710487251636161489 := by
  unfold tailWord_1890642
  simp only [CollatzResearch.WordTrace]
  refine ⟨17239344704133601197912545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45971585877689603194433453 17239344704133601197912545)
  ·
    refine ⟨12929508528100200898434409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17239344704133601197912545 12929508528100200898434409)
    ·
      refine ⟨9697131396075150673825807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12929508528100200898434409 9697131396075150673825807)
      ·
        refine ⟨14545697094112726010738711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697131396075150673825807 14545697094112726010738711)
        ·
          refine ⟨21818545641169089016108067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14545697094112726010738711 21818545641169089016108067)
          ·
            refine ⟨32727818461753633524162101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21818545641169089016108067 32727818461753633524162101)
            ·
              refine ⟨3068232980789403142890197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32727818461753633524162101 3068232980789403142890197)
              ·
                refine ⟨71911710487251636161489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3068232980789403142890197 71911710487251636161489)
                ·
                  rfl

theorem cell22_1890642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_1890642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890642 prefixEnd_1890642 := by exact prefixLift 1890642
  have htrace : WordTrace (prefixWord ++ tailWord_1890642) baseStart_1890642 baseEnd_1890642 := by
    simpa [prefixWord, tailWord_1890642, baseEnd_1890642] using wordTrace_append hprefix tailTrace_1890642
  have hstable : (prefixWord ++ tailWord_1890642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890642).length < 2 ^ (prefixWord ++ tailWord_1890642).sum := by decide
  have hdescent : baseEnd_1890642 < baseStart_1890642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890691 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 3, 3]
def baseStart_1890691 : Nat := 118140960795 + 1890691 * 2 ^ 59
def prefixEnd_1890691 : Nat := 4983230072969 + 3 ^ 40 * 1890691 * 2
def baseEnd_1890691 : Nat := 647222168086644930978251

theorem tailTrace_1890691 : CollatzResearch.WordTrace tailWord_1890691 prefixEnd_1890691 647222168086644930978251 := by
  unfold tailWord_1890691
  simp only [CollatzResearch.WordTrace]
  refine ⟨68959165993356886160183927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45972777328904590773455951 68959165993356886160183927)
  ·
    refine ⟨103438748990035329240275891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68959165993356886160183927 103438748990035329240275891)
    ·
      refine ⟨155158123485052993860413837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103438748990035329240275891 155158123485052993860413837)
      ·
        refine ⟨58184296306894872697655189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155158123485052993860413837 58184296306894872697655189)
        ·
          refine ⟨2727388889385697157702587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58184296306894872697655189 2727388889385697157702587)
          ·
            refine ⟨4091083334078545736553881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727388889385697157702587 4091083334078545736553881)
            ·
              refine ⟨3068312500558909302415411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091083334078545736553881 3068312500558909302415411)
              ·
                refine ⟨4602468750838363953623117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068312500558909302415411 4602468750838363953623117)
                ·
                  refine ⟨1725925781564386482608669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4602468750838363953623117 1725925781564386482608669)
                  ·
                    refine ⟨647222168086644930978251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1725925781564386482608669 647222168086644930978251)
                    ·
                      rfl

theorem cell22_1890691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 3].length) (baseStart_1890691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890691 prefixEnd_1890691 := by exact prefixLift 1890691
  have htrace : WordTrace (prefixWord ++ tailWord_1890691) baseStart_1890691 baseEnd_1890691 := by
    simpa [prefixWord, tailWord_1890691, baseEnd_1890691] using wordTrace_append hprefix tailTrace_1890691
  have hstable : (prefixWord ++ tailWord_1890691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890691).length < 2 ^ (prefixWord ++ tailWord_1890691).sum := by decide
  have hdescent : baseEnd_1890691 < baseStart_1890691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890749 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 6]
def baseStart_1890749 : Nat := 118140960795 + 1890749 * 2 ^ 59
def prefixEnd_1890749 : Nat := 4983230072969 + 3 ^ 40 * 1890749 * 2
def baseEnd_1890749 : Nat := 215747340890650704342691

theorem tailTrace_1890749 : CollatzResearch.WordTrace tailWord_1890749 prefixEnd_1890749 215747340890650704342691 := by
  unfold tailWord_1890749
  simp only [CollatzResearch.WordTrace]
  refine ⟨68961281427146762065795301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45974187618097841377196867 68961281427146762065795301)
  ·
    refine ⟨12930240267590017887336619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68961281427146762065795301 12930240267590017887336619)
    ·
      refine ⟨19395360401385026831004929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12930240267590017887336619 19395360401385026831004929)
      ·
        refine ⟨14546520301038770123253697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19395360401385026831004929 14546520301038770123253697)
        ·
          refine ⟨10909890225779077592440273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14546520301038770123253697 10909890225779077592440273)
          ·
            refine ⟨8182417669334308194330205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10909890225779077592440273 8182417669334308194330205)
            ·
              refine ⟨3068406626000365572873827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8182417669334308194330205 3068406626000365572873827)
              ·
                refine ⟨4602609939000548359310741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068406626000365572873827 4602609939000548359310741)
                ·
                  refine ⟨215747340890650704342691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4602609939000548359310741 215747340890650704342691)
                  ·
                    rfl

theorem cell22_1890749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_1890749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890749 prefixEnd_1890749 := by exact prefixLift 1890749
  have htrace : WordTrace (prefixWord ++ tailWord_1890749) baseStart_1890749 baseEnd_1890749 := by
    simpa [prefixWord, tailWord_1890749, baseEnd_1890749] using wordTrace_append hprefix tailTrace_1890749
  have hstable : (prefixWord ++ tailWord_1890749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890749).length < 2 ^ (prefixWord ++ tailWord_1890749).sum := by decide
  have hdescent : baseEnd_1890749 < baseStart_1890749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890777 : List Nat := [1, 2, 1, 2, 4, 1, 1, 10]
def baseStart_1890777 : Nat := 118140960795 + 1890777 * 2 ^ 59
def prefixEnd_1890777 : Nat := 4983230072969 + 3 ^ 40 * 1890777 * 2
def baseEnd_1890777 : Nat := 71916845293796597036443

theorem tailTrace_1890777 : CollatzResearch.WordTrace tailWord_1890777 prefixEnd_1890777 71916845293796597036443 := by
  unfold tailWord_1890777
  simp only [CollatzResearch.WordTrace]
  refine ⟨68962302671045322847814585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45974868447363548565209723 68962302671045322847814585)
  ·
    refine ⟨51721727003283992135860939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68962302671045322847814585 51721727003283992135860939)
    ·
      refine ⟨77582590504925988203791409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51721727003283992135860939 77582590504925988203791409)
      ·
        refine ⟨58186942878694491152843557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77582590504925988203791409 58186942878694491152843557)
        ·
          refine ⟨10910051789755217091158167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58186942878694491152843557 10910051789755217091158167)
          ·
            refine ⟨16365077684632825636737251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910051789755217091158167 16365077684632825636737251)
            ·
              refine ⟨24547616526949238455105877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16365077684632825636737251 24547616526949238455105877)
              ·
                refine ⟨71916845293796597036443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24547616526949238455105877 71916845293796597036443)
                ·
                  rfl

theorem cell22_1890777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 10].length) (baseStart_1890777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890777 prefixEnd_1890777 := by exact prefixLift 1890777
  have htrace : WordTrace (prefixWord ++ tailWord_1890777) baseStart_1890777 baseEnd_1890777 := by
    simpa [prefixWord, tailWord_1890777, baseEnd_1890777] using wordTrace_append hprefix tailTrace_1890777
  have hstable : (prefixWord ++ tailWord_1890777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890777).length < 2 ^ (prefixWord ++ tailWord_1890777).sum := by decide
  have hdescent : baseEnd_1890777 < baseStart_1890777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890798 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1890798 : Nat := 118140960795 + 1890798 * 2 ^ 59
def prefixEnd_1890798 : Nat := 4983230072969 + 3 ^ 40 * 1890798 * 2
def baseEnd_1890798 : Nat := 647258796373332318552923

theorem tailTrace_1890798 : CollatzResearch.WordTrace tailWord_1890798 prefixEnd_1890798 647258796373332318552923 := by
  unfold tailWord_1890798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8620383575496155429291131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45975379069312828956219365 8620383575496155429291131)
  ·
    refine ⟨12930575363244233143936697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8620383575496155429291131 12930575363244233143936697)
    ·
      refine ⟨9697931522433174857952523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12930575363244233143936697 9697931522433174857952523)
      ·
        refine ⟨14546897283649762286928785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697931522433174857952523 14546897283649762286928785)
        ·
          refine ⟨10910172962737321715196589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14546897283649762286928785 10910172962737321715196589)
          ·
            refine ⟨4091314861026495643198721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10910172962737321715196589 4091314861026495643198721)
            ·
              refine ⟨3068486145769871732399041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091314861026495643198721 3068486145769871732399041)
              ·
                refine ⟨2301364609327403799299281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068486145769871732399041 2301364609327403799299281)
                ·
                  refine ⟨1726023456995552849474461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2301364609327403799299281 1726023456995552849474461)
                  ·
                    refine ⟨647258796373332318552923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726023456995552849474461 647258796373332318552923)
                    ·
                      rfl

theorem cell22_1890798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1890798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890798 prefixEnd_1890798 := by exact prefixLift 1890798
  have htrace : WordTrace (prefixWord ++ tailWord_1890798) baseStart_1890798 baseEnd_1890798 := by
    simpa [prefixWord, tailWord_1890798, baseEnd_1890798] using wordTrace_append hprefix tailTrace_1890798
  have hstable : (prefixWord ++ tailWord_1890798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890798).length < 2 ^ (prefixWord ++ tailWord_1890798).sum := by decide
  have hdescent : baseEnd_1890798 < baseStart_1890798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890826 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1890826 : Nat := 118140960795 + 1890826 * 2 ^ 59
def prefixEnd_1890826 : Nat := 4983230072969 + 3 ^ 40 * 1890826 * 2
def baseEnd_1890826 : Nat := 647268381345549578852837

theorem tailTrace_1890826 : CollatzResearch.WordTrace tailWord_1890826 prefixEnd_1890826 647268381345549578852837 := by
  unfold tailWord_1890826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241022461966951054087083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45976059898578536144232221 17241022461966951054087083)
  ·
    refine ⟨25861533692950426581130625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17241022461966951054087083 25861533692950426581130625)
    ·
      refine ⟨19396150269712819935847969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25861533692950426581130625 19396150269712819935847969)
      ·
        refine ⟨14547112702284614951885977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19396150269712819935847969 14547112702284614951885977)
        ·
          refine ⟨10910334526713461213914483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14547112702284614951885977 10910334526713461213914483)
          ·
            refine ⟨16365501790070191820871725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910334526713461213914483 16365501790070191820871725)
            ·
              refine ⟨6137063171276321932826897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16365501790070191820871725 6137063171276321932826897)
              ·
                refine ⟨4602797378457241449620173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6137063171276321932826897 4602797378457241449620173)
                ·
                  refine ⟨1726049016921465543607565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4602797378457241449620173 1726049016921465543607565)
                  ·
                    refine ⟨647268381345549578852837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726049016921465543607565 647268381345549578852837)
                    ·
                      rfl

theorem cell22_1890826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1890826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890826 prefixEnd_1890826 := by exact prefixLift 1890826
  have htrace : WordTrace (prefixWord ++ tailWord_1890826) baseStart_1890826 baseEnd_1890826 := by
    simpa [prefixWord, tailWord_1890826, baseEnd_1890826] using wordTrace_append hprefix tailTrace_1890826
  have hstable : (prefixWord ++ tailWord_1890826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890826).length < 2 ^ (prefixWord ++ tailWord_1890826).sum := by decide
  have hdescent : baseEnd_1890826 < baseStart_1890826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890856 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 7]
def baseStart_1890856 : Nat := 118140960795 + 1890856 * 2 ^ 59
def prefixEnd_1890856 : Nat := 4983230072969 + 3 ^ 40 * 1890856 * 2
def baseEnd_1890856 : Nat := 215759550319546500200915

theorem tailTrace_1890856 : CollatzResearch.WordTrace tailWord_1890856 prefixEnd_1890856 215759550319546500200915 := by
  unfold tailWord_1890856
  simp only [CollatzResearch.WordTrace]
  refine ⟨34482592018879559669970211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45976789358506079559960281 34482592018879559669970211)
  ·
    refine ⟨51723888028319339504955317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34482592018879559669970211 51723888028319339504955317)
    ·
      refine ⟨4849114502654938078589561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51723888028319339504955317 4849114502654938078589561)
      ·
        refine ⟨3636835876991203558942171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4849114502654938078589561 3636835876991203558942171)
        ·
          refine ⟨5455253815486805338413257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636835876991203558942171 5455253815486805338413257)
          ·
            refine ⟨4091440361615104003809943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5455253815486805338413257 4091440361615104003809943)
            ·
              refine ⟨6137160542422656005714915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091440361615104003809943 6137160542422656005714915)
              ·
                refine ⟨9205740813633984008572373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137160542422656005714915 9205740813633984008572373)
                ·
                  refine ⟨215759550319546500200915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9205740813633984008572373 215759550319546500200915)
                  ·
                    rfl

theorem cell22_1890856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_1890856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890856 prefixEnd_1890856 := by exact prefixLift 1890856
  have htrace : WordTrace (prefixWord ++ tailWord_1890856) baseStart_1890856 baseEnd_1890856 := by
    simpa [prefixWord, tailWord_1890856, baseEnd_1890856] using wordTrace_append hprefix tailTrace_1890856
  have hstable : (prefixWord ++ tailWord_1890856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890856).length < 2 ^ (prefixWord ++ tailWord_1890856).sum := by decide
  have hdescent : baseEnd_1890856 < baseStart_1890856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890916 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_1890916 : Nat := 118140960795 + 1890916 * 2 ^ 59
def prefixEnd_1890916 : Nat := 4983230072969 + 3 ^ 40 * 1890916 * 2
def baseEnd_1890916 : Nat := 647299190184819344102561

theorem tailTrace_1890916 : CollatzResearch.WordTrace tailWord_1890916 prefixEnd_1890916 647299190184819344102561 := by
  unfold tailWord_1890916
  simp only [CollatzResearch.WordTrace]
  refine ⟨34483686208770874793562301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45978248278361166391416401 34483686208770874793562301)
  ·
    refine ⟨12931382328289078047585863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34483686208770874793562301 12931382328289078047585863)
    ·
      refine ⟨19397073492433617071378795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12931382328289078047585863 19397073492433617071378795)
      ·
        refine ⟨29095610238650425607068193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19397073492433617071378795 29095610238650425607068193)
        ·
          refine ⟨21821707678987819205301145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29095610238650425607068193 21821707678987819205301145)
          ·
            refine ⟨16366280759240864403975859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21821707678987819205301145 16366280759240864403975859)
            ·
              refine ⟨24549421138861296605963789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16366280759240864403975859 24549421138861296605963789)
              ·
                refine ⟨9206032927072986227236421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24549421138861296605963789 9206032927072986227236421)
                ·
                  refine ⟨1726131173826184917606829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9206032927072986227236421 1726131173826184917606829)
                  ·
                    refine ⟨647299190184819344102561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1726131173826184917606829 647299190184819344102561)
                    ·
                      rfl

theorem cell22_1890916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_1890916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890916 prefixEnd_1890916 := by exact prefixLift 1890916
  have htrace : WordTrace (prefixWord ++ tailWord_1890916) baseStart_1890916 baseEnd_1890916 := by
    simpa [prefixWord, tailWord_1890916, baseEnd_1890916] using wordTrace_append hprefix tailTrace_1890916
  have hstable : (prefixWord ++ tailWord_1890916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890916).length < 2 ^ (prefixWord ++ tailWord_1890916).sum := by decide
  have hdescent : baseEnd_1890916 < baseStart_1890916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890948 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1890948 : Nat := 118140960795 + 1890948 * 2 ^ 59
def prefixEnd_1890948 : Nat := 4983230072969 + 3 ^ 40 * 1890948 * 2
def baseEnd_1890948 : Nat := 647310144438781927302463

theorem tailTrace_1890948 : CollatzResearch.WordTrace tailWord_1890948 prefixEnd_1890948 647310144438781927302463 := by
  unfold tailWord_1890948
  simp only [CollatzResearch.WordTrace]
  refine ⟨34484269776712909526144749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45979026368950546034859665 34484269776712909526144749)
  ·
    refine ⟨12931601166267341072304281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34484269776712909526144749 12931601166267341072304281)
    ·
      refine ⟨9698700874700505804228211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12931601166267341072304281 9698700874700505804228211)
      ·
        refine ⟨14548051312050758706342317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698700874700505804228211 14548051312050758706342317)
        ·
          refine ⟨5455519242019034514878369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14548051312050758706342317 5455519242019034514878369)
          ·
            refine ⟨4091639431514275886158777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5455519242019034514878369 4091639431514275886158777)
            ·
              refine ⟨3068729573635706914619083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091639431514275886158777 3068729573635706914619083)
              ·
                refine ⟨4603094360453560371928625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068729573635706914619083 4603094360453560371928625)
                ·
                  refine ⟨3452320770340170278946469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4603094360453560371928625 3452320770340170278946469)
                  ·
                    refine ⟨647310144438781927302463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3452320770340170278946469 647310144438781927302463)
                    ·
                      rfl

theorem cell22_1890948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1890948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1890948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1890948 prefixEnd_1890948 := by exact prefixLift 1890948
  have htrace : WordTrace (prefixWord ++ tailWord_1890948) baseStart_1890948 baseEnd_1890948 := by
    simpa [prefixWord, tailWord_1890948, baseEnd_1890948] using wordTrace_append hprefix tailTrace_1890948
  have hstable : (prefixWord ++ tailWord_1890948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890948).length < 2 ^ (prefixWord ++ tailWord_1890948).sum := by decide
  have hdescent : baseEnd_1890948 < baseStart_1890948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
