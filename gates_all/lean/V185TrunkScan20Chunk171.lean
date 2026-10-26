import V185TrunkScan20Chunk170

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_1041562 : List Nat := [3, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_1041562 : Nat := 118140960795 + 1041562 * 2 ^ 59
def prefixEnd_1041562 : Nat := 4983230072969 + 3 ^ 40 * 1041562 * 2
def baseEnd_1041562 : Nat := 475397277740763660075511

theorem tailTrace_1041562 : CollatzResearch.WordTrace tailWord_1041562 prefixEnd_1041562 475397277740763660075511 := by
  unfold tailWord_1041562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497221763151558368147735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25325924701737488981727293 9497221763151558368147735)
  ·
    refine ⟨14245832644727337552221603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9497221763151558368147735 14245832644727337552221603)
    ·
      refine ⟨21368748967091006328332405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14245832644727337552221603 21368748967091006328332405)
      ·
        refine ⟨2003320215664781843281163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21368748967091006328332405 2003320215664781843281163)
        ·
          refine ⟨3004980323497172764921745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003320215664781843281163 3004980323497172764921745)
          ·
            refine ⟨2253735242622879573691309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004980323497172764921745 2253735242622879573691309)
            ·
              refine ⟨845150715983579840134241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2253735242622879573691309 845150715983579840134241)
              ·
                refine ⟨633863036987684880100681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845150715983579840134241 633863036987684880100681)
                ·
                  refine ⟨475397277740763660075511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633863036987684880100681 475397277740763660075511)
                  ·
                    rfl

theorem cell20_1041562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_1041562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041562 prefixEnd_1041562 := by exact prefixLift 1041562
  have htrace : WordTrace (prefixWord ++ tailWord_1041562) baseStart_1041562 baseEnd_1041562 := by
    simpa [prefixWord, tailWord_1041562, baseEnd_1041562] using wordTrace_append hprefix tailTrace_1041562
  have hstable : (prefixWord ++ tailWord_1041562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041562).length < 2 ^ (prefixWord ++ tailWord_1041562).sum := by decide
  have hdescent : baseEnd_1041562 < baseStart_1041562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041613 : List Nat := [1, 6, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1041613 : Nat := 118140960795 + 1041613 * 2 ^ 59
def prefixEnd_1041613 : Nat := 4983230072969 + 3 ^ 40 * 1041613 * 2
def baseEnd_1041613 : Nat := 475420555530434149375303

theorem tailTrace_1041613 : CollatzResearch.WordTrace tailWord_1041613 prefixEnd_1041613 475420555530434149375303 := by
  unfold tailWord_1041613
  simp only [CollatzResearch.WordTrace]
  refine ⟨37990747175421469182697493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25327164783614312788464995 37990747175421469182697493)
  ·
    refine ⟨1780816273847881367938945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37990747175421469182697493 1780816273847881367938945)
    ·
      refine ⟨1335612205385911025954209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1780816273847881367938945 1335612205385911025954209)
      ·
        refine ⟨1001709154039433269465657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1335612205385911025954209 1001709154039433269465657)
        ·
          refine ⟨751281865529574952099243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001709154039433269465657 751281865529574952099243)
          ·
            refine ⟨1126922798294362428148865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751281865529574952099243 1126922798294362428148865)
            ·
              refine ⟨845192098720771821111649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126922798294362428148865 845192098720771821111649)
              ·
                refine ⟨633894074040578865833737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845192098720771821111649 633894074040578865833737)
                ·
                  refine ⟨475420555530434149375303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633894074040578865833737 475420555530434149375303)
                  ·
                    rfl

theorem cell20_1041613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1041613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041613 prefixEnd_1041613 := by exact prefixLift 1041613
  have htrace : WordTrace (prefixWord ++ tailWord_1041613) baseStart_1041613 baseEnd_1041613 := by
    simpa [prefixWord, tailWord_1041613, baseEnd_1041613] using wordTrace_append hprefix tailTrace_1041613
  have hstable : (prefixWord ++ tailWord_1041613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041613).length < 2 ^ (prefixWord ++ tailWord_1041613).sum := by decide
  have hdescent : baseEnd_1041613 < baseStart_1041613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041621 : List Nat := [1, 3, 2, 4, 1, 2, 1, 4, 2]
def baseStart_1041621 : Nat := 118140960795 + 1041621 * 2 ^ 59
def prefixEnd_1041621 : Nat := 4983230072969 + 3 ^ 40 * 1041621 * 2
def baseEnd_1041621 : Nat := 475424206948421677108603

theorem tailTrace_1041621 : CollatzResearch.WordTrace tailWord_1041621 prefixEnd_1041621 475424206948421677108603 := by
  unfold tailWord_1041621
  simp only [CollatzResearch.WordTrace]
  refine ⟨37991038959392486548988717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25327359306261657699325811 37991038959392486548988717)
  ·
    refine ⟨14246639609772182455870769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37991038959392486548988717 14246639609772182455870769)
    ·
      refine ⟨10684979707329136841903077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14246639609772182455870769 10684979707329136841903077)
      ·
        refine ⟨2003433695124213157856827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10684979707329136841903077 2003433695124213157856827)
        ·
          refine ⟨3005150542686319736785241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003433695124213157856827 3005150542686319736785241)
          ·
            refine ⟨2253862907014739802588931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3005150542686319736785241 2253862907014739802588931)
            ·
              refine ⟨3380794360522109703883397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253862907014739802588931 3380794360522109703883397)
              ·
                refine ⟨633898942597895569478137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3380794360522109703883397 633898942597895569478137)
                ·
                  refine ⟨475424206948421677108603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633898942597895569478137 475424206948421677108603)
                  ·
                    rfl

theorem cell20_1041621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_1041621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041621 prefixEnd_1041621 := by exact prefixLift 1041621
  have htrace : WordTrace (prefixWord ++ tailWord_1041621) baseStart_1041621 baseEnd_1041621 := by
    simpa [prefixWord, tailWord_1041621, baseEnd_1041621] using wordTrace_append hprefix tailTrace_1041621
  have hstable : (prefixWord ++ tailWord_1041621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041621).length < 2 ^ (prefixWord ++ tailWord_1041621).sum := by decide
  have hdescent : baseEnd_1041621 < baseStart_1041621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041632 : List Nat := [2, 1, 1, 3, 1, 4, 3, 5]
def baseStart_1041632 : Nat := 118140960795 + 1041632 * 2 ^ 59
def prefixEnd_1041632 : Nat := 4983230072969 + 3 ^ 40 * 1041632 * 2
def baseEnd_1041632 : Nat := 158476409216051509247297

theorem tailTrace_1041632 : CollatzResearch.WordTrace tailWord_1041632 prefixEnd_1041632 158476409216051509247297 := by
  unfold tailWord_1041632
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995720081176317713819575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25327626774901756951759433 18995720081176317713819575)
  ·
    refine ⟨28493580121764476570729363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18995720081176317713819575 28493580121764476570729363)
    ·
      refine ⟨42740370182646714856094045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28493580121764476570729363 42740370182646714856094045)
      ·
        refine ⟨16027638818492518071035267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42740370182646714856094045 16027638818492518071035267)
        ·
          refine ⟨24041458227738777106552901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16027638818492518071035267 24041458227738777106552901)
          ·
            refine ⟨4507773417701020707478669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24041458227738777106552901 4507773417701020707478669)
            ·
              refine ⟨1690415031637882765304501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4507773417701020707478669 1690415031637882765304501)
              ·
                refine ⟨158476409216051509247297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1690415031637882765304501 158476409216051509247297)
                ·
                  rfl

theorem cell20_1041632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_1041632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041632 prefixEnd_1041632 := by exact prefixLift 1041632
  have htrace : WordTrace (prefixWord ++ tailWord_1041632) baseStart_1041632 baseEnd_1041632 := by
    simpa [prefixWord, tailWord_1041632, baseEnd_1041632] using wordTrace_append hprefix tailTrace_1041632
  have hstable : (prefixWord ++ tailWord_1041632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041632).length < 2 ^ (prefixWord ++ tailWord_1041632).sum := by decide
  have hdescent : baseEnd_1041632 < baseStart_1041632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041691 : List Nat := [1, 1, 1, 1, 1, 1, 5, 9]
def baseStart_1041691 : Nat := 118140960795 + 1041691 * 2 ^ 59
def prefixEnd_1041691 : Nat := 4983230072969 + 3 ^ 40 * 1041691 * 2
def baseEnd_1041691 : Nat := 158485385618604181591661

theorem tailTrace_1041691 : CollatzResearch.WordTrace tailWord_1041691 prefixEnd_1041691 158485385618604181591661 := by
  unfold tailWord_1041691
  simp only [CollatzResearch.WordTrace]
  refine ⟨37993592069138888504036927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25329061379425925669357951 37993592069138888504036927)
  ·
    refine ⟨56990388103708332756055391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37993592069138888504036927 56990388103708332756055391)
    ·
      refine ⟨85485582155562499134083087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56990388103708332756055391 85485582155562499134083087)
      ·
        refine ⟨128228373233343748701124631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85485582155562499134083087 128228373233343748701124631)
        ·
          refine ⟨192342559850015623051686947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128228373233343748701124631 192342559850015623051686947)
          ·
            refine ⟨288513839775023434577530421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192342559850015623051686947 288513839775023434577530421)
            ·
              refine ⟨27048172478908446991643477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288513839775023434577530421 27048172478908446991643477)
              ·
                refine ⟨158485385618604181591661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27048172478908446991643477 158485385618604181591661)
                ·
                  rfl

theorem cell20_1041691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_1041691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041691 prefixEnd_1041691 := by exact prefixLift 1041691
  have htrace : WordTrace (prefixWord ++ tailWord_1041691) baseStart_1041691 baseEnd_1041691 := by
    simpa [prefixWord, tailWord_1041691, baseEnd_1041691] using wordTrace_append hprefix tailTrace_1041691
  have hstable : (prefixWord ++ tailWord_1041691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041691).length < 2 ^ (prefixWord ++ tailWord_1041691).sum := by decide
  have hdescent : baseEnd_1041691 < baseStart_1041691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041701 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1041701 : Nat := 118140960795 + 1041701 * 2 ^ 59
def prefixEnd_1041701 : Nat := 4983230072969 + 3 ^ 40 * 1041701 * 2
def baseEnd_1041701 : Nat := 475460721128296954441609

theorem tailTrace_1041701 : CollatzResearch.WordTrace tailWord_1041701 prefixEnd_1041701 475460721128296954441609 := by
  unfold tailWord_1041701
  simp only [CollatzResearch.WordTrace]
  refine ⟨37993956799102660211900957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25329304532735106807933971 37993956799102660211900957)
  ·
    refine ⟨14247733799663497579462859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37993956799102660211900957 14247733799663497579462859)
    ·
      refine ⟨21371600699495246369194289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14247733799663497579462859 21371600699495246369194289)
      ·
        refine ⟨16028700524621434776895717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21371600699495246369194289 16028700524621434776895717)
        ·
          refine ⟨3005381348366519020667947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16028700524621434776895717 3005381348366519020667947)
          ·
            refine ⟨4508072022549778531001921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005381348366519020667947 4508072022549778531001921)
            ·
              refine ⟨3381054016912333898251441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508072022549778531001921 3381054016912333898251441)
              ·
                refine ⟨2535790512684250423688581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381054016912333898251441 2535790512684250423688581)
                ·
                  refine ⟨475460721128296954441609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535790512684250423688581 475460721128296954441609)
                  ·
                    rfl

theorem cell20_1041701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1041701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041701 prefixEnd_1041701 := by exact prefixLift 1041701
  have htrace : WordTrace (prefixWord ++ tailWord_1041701) baseStart_1041701 baseEnd_1041701 := by
    simpa [prefixWord, tailWord_1041701, baseEnd_1041701] using wordTrace_append hprefix tailTrace_1041701
  have hstable : (prefixWord ++ tailWord_1041701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041701).length < 2 ^ (prefixWord ++ tailWord_1041701).sum := by decide
  have hdescent : baseEnd_1041701 < baseStart_1041701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041704 : List Nat := [2, 1, 5, 1, 2, 3, 2, 4]
def baseStart_1041704 : Nat := 118140960795 + 1041704 * 2 ^ 59
def prefixEnd_1041704 : Nat := 4983230072969 + 3 ^ 40 * 1041704 * 2
def baseEnd_1041704 : Nat := 158487363470014092447199

theorem tailTrace_1041704 : CollatzResearch.WordTrace tailWord_1041704 prefixEnd_1041704 158487363470014092447199 := by
  unfold tailWord_1041704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997033109045895862130083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25329377478727861149506777 18997033109045895862130083)
  ·
    refine ⟨28495549663568843793195125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18997033109045895862130083 28495549663568843793195125)
    ·
      refine ⟨2671457780959579105612043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28495549663568843793195125 2671457780959579105612043)
      ·
        refine ⟨4007186671439368658418065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671457780959579105612043 4007186671439368658418065)
        ·
          refine ⟨3005390003579526493813549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4007186671439368658418065 3005390003579526493813549)
          ·
            refine ⟨1127021251342322435180081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3005390003579526493813549 1127021251342322435180081)
            ·
              refine ⟨845265938506741826385061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127021251342322435180081 845265938506741826385061)
              ·
                refine ⟨158487363470014092447199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 845265938506741826385061 158487363470014092447199)
                ·
                  rfl

theorem cell20_1041704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_1041704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041704 prefixEnd_1041704 := by exact prefixLift 1041704
  have htrace : WordTrace (prefixWord ++ tailWord_1041704) baseStart_1041704 baseEnd_1041704 := by
    simpa [prefixWord, tailWord_1041704, baseEnd_1041704] using wordTrace_append hprefix tailTrace_1041704
  have hstable : (prefixWord ++ tailWord_1041704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041704).length < 2 ^ (prefixWord ++ tailWord_1041704).sum := by decide
  have hdescent : baseEnd_1041704 < baseStart_1041704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041715 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_1041715 : Nat := 118140960795 + 1041715 * 2 ^ 59
def prefixEnd_1041715 : Nat := 4983230072969 + 3 ^ 40 * 1041715 * 2
def baseEnd_1041715 : Nat := 475467111109775127974885

theorem tailTrace_1041715 : CollatzResearch.WordTrace tailWord_1041715 prefixEnd_1041715 475467111109775127974885 := by
  unfold tailWord_1041715
  simp only [CollatzResearch.WordTrace]
  refine ⟨37994467421051940602910599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25329644947367960401940399 37994467421051940602910599)
  ·
    refine ⟨56991701131577910904365899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37994467421051940602910599 56991701131577910904365899)
    ·
      refine ⟨85487551697366866356548849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56991701131577910904365899 85487551697366866356548849)
      ·
        refine ⟨64115663773025149767411637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85487551697366866356548849 64115663773025149767411637)
        ·
          refine ⟨6010843478721107790694841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64115663773025149767411637 6010843478721107790694841)
          ·
            refine ⟨4508132609040830843021131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010843478721107790694841 4508132609040830843021131)
            ·
              refine ⟨6762198913561246264531697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508132609040830843021131 6762198913561246264531697)
              ·
                refine ⟨5071649185170934698398773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762198913561246264531697 5071649185170934698398773)
                ·
                  refine ⟨475467111109775127974885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5071649185170934698398773 475467111109775127974885)
                  ·
                    rfl

theorem cell20_1041715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_1041715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041715 prefixEnd_1041715 := by exact prefixLift 1041715
  have htrace : WordTrace (prefixWord ++ tailWord_1041715) baseStart_1041715 baseEnd_1041715 := by
    simpa [prefixWord, tailWord_1041715, baseEnd_1041715] using wordTrace_append hprefix tailTrace_1041715
  have hstable : (prefixWord ++ tailWord_1041715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041715).length < 2 ^ (prefixWord ++ tailWord_1041715).sum := by decide
  have hdescent : baseEnd_1041715 < baseStart_1041715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041735 : List Nat := [1, 1, 4, 1, 2, 4, 3, 2, 2]
def baseStart_1041735 : Nat := 118140960795 + 1041735 * 2 ^ 59
def prefixEnd_1041735 : Nat := 4983230072969 + 3 ^ 40 * 1041735 * 2
def baseEnd_1041735 : Nat := 475476239654743947308137

theorem tailTrace_1041735 : CollatzResearch.WordTrace tailWord_1041735 prefixEnd_1041735 475476239654743947308137 := by
  unfold tailWord_1041735
  simp only [CollatzResearch.WordTrace]
  refine ⟨37995196880979484018638659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25330131253986322679092439 37995196880979484018638659)
  ·
    refine ⟨56992795321469226027957989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37995196880979484018638659 56992795321469226027957989)
    ·
      refine ⟨10686149122775479880242123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56992795321469226027957989 10686149122775479880242123)
      ·
        refine ⟨16029223684163219820363185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686149122775479880242123 16029223684163219820363185)
        ·
          refine ⟨12021917763122414865272389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16029223684163219820363185 12021917763122414865272389)
          ·
            refine ⟨2254109580585452787238573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12021917763122414865272389 2254109580585452787238573)
            ·
              refine ⟨845291092719544795214465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2254109580585452787238573 845291092719544795214465)
              ·
                refine ⟨633968319539658596410849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845291092719544795214465 633968319539658596410849)
                ·
                  refine ⟨475476239654743947308137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633968319539658596410849 475476239654743947308137)
                  ·
                    rfl

theorem cell20_1041735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 2].length) (baseStart_1041735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041735 prefixEnd_1041735 := by exact prefixLift 1041735
  have htrace : WordTrace (prefixWord ++ tailWord_1041735) baseStart_1041735 baseEnd_1041735 := by
    simpa [prefixWord, tailWord_1041735, baseEnd_1041735] using wordTrace_append hprefix tailTrace_1041735
  have hstable : (prefixWord ++ tailWord_1041735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041735).length < 2 ^ (prefixWord ++ tailWord_1041735).sum := by decide
  have hdescent : baseEnd_1041735 < baseStart_1041735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041749 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 3]
def baseStart_1041749 : Nat := 118140960795 + 1041749 * 2 ^ 59
def prefixEnd_1041749 : Nat := 4983230072969 + 3 ^ 40 * 1041749 * 2
def baseEnd_1041749 : Nat := 475482629636222120841413

theorem tailTrace_1041749 : CollatzResearch.WordTrace tailWord_1041749 prefixEnd_1041749 475482629636222120841413 := by
  unfold tailWord_1041749
  simp only [CollatzResearch.WordTrace]
  refine ⟨37995707502928764409648301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25330471668619176273098867 37995707502928764409648301)
  ·
    refine ⟨14248390313598286653618113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37995707502928764409648301 14248390313598286653618113)
    ·
      refine ⟨10686292735198714990213585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14248390313598286653618113 10686292735198714990213585)
      ·
        refine ⟨8014719551399036242660189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10686292735198714990213585 8014719551399036242660189)
        ·
          refine ⟨3005519831774638590997571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8014719551399036242660189 3005519831774638590997571)
          ·
            refine ⟨4508279747661957886496357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005519831774638590997571 4508279747661957886496357)
            ·
              refine ⟨845302452686617103718067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4508279747661957886496357 845302452686617103718067)
              ·
                refine ⟨1267953679029925655577101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845302452686617103718067 1267953679029925655577101)
                ·
                  refine ⟨475482629636222120841413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267953679029925655577101 475482629636222120841413)
                  ·
                    rfl

theorem cell20_1041749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_1041749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041749 prefixEnd_1041749 := by exact prefixLift 1041749
  have htrace : WordTrace (prefixWord ++ tailWord_1041749) baseStart_1041749 baseEnd_1041749 := by
    simpa [prefixWord, tailWord_1041749, baseEnd_1041749] using wordTrace_append hprefix tailTrace_1041749
  have hstable : (prefixWord ++ tailWord_1041749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041749).length < 2 ^ (prefixWord ++ tailWord_1041749).sum := by decide
  have hdescent : baseEnd_1041749 < baseStart_1041749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041801 : List Nat := [1, 2, 1, 1, 7, 2, 1, 5]
def baseStart_1041801 : Nat := 118140960795 + 1041801 * 2 ^ 59
def prefixEnd_1041801 : Nat := 4983230072969 + 3 ^ 40 * 1041801 * 2
def baseEnd_1041801 : Nat := 158502121284380350369289

theorem tailTrace_1041801 : CollatzResearch.WordTrace tailWord_1041801 prefixEnd_1041801 158502121284380350369289 := by
  unfold tailWord_1041801
  simp only [CollatzResearch.WordTrace]
  refine ⟨37997604098740377290541257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25331736065826918193694171 37997604098740377290541257)
  ·
    refine ⟨28498203074055282967905943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37997604098740377290541257 28498203074055282967905943)
    ·
      refine ⟨42747304611082924451858915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28498203074055282967905943 42747304611082924451858915)
      ·
        refine ⟨64120956916624386677788373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42747304611082924451858915 64120956916624386677788373)
        ·
          refine ⟨1502834927733384062760665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64120956916624386677788373 1502834927733384062760665)
          ·
            refine ⟨1127126195800038047070499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502834927733384062760665 1127126195800038047070499)
            ·
              refine ⟨1690689293700057070605749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127126195800038047070499 1690689293700057070605749)
              ·
                refine ⟨158502121284380350369289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1690689293700057070605749 158502121284380350369289)
                ·
                  rfl

theorem cell20_1041801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_1041801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041801 prefixEnd_1041801 := by exact prefixLift 1041801
  have htrace : WordTrace (prefixWord ++ tailWord_1041801) baseStart_1041801 baseEnd_1041801 := by
    simpa [prefixWord, tailWord_1041801, baseEnd_1041801] using wordTrace_append hprefix tailTrace_1041801
  have hstable : (prefixWord ++ tailWord_1041801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041801).length < 2 ^ (prefixWord ++ tailWord_1041801).sum := by decide
  have hdescent : baseEnd_1041801 < baseStart_1041801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041853 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1041853 : Nat := 118140960795 + 1041853 * 2 ^ 59
def prefixEnd_1041853 : Nat := 4983230072969 + 3 ^ 40 * 1041853 * 2
def baseEnd_1041853 : Nat := 475530098070059981374321

theorem tailTrace_1041853 : CollatzResearch.WordTrace tailWord_1041853 prefixEnd_1041853 475530098070059981374321 := by
  unfold tailWord_1041853
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999500694551990171434213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25333000463034660114289475 37999500694551990171434213)
  ·
    refine ⟨7124906380228498157143915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37999500694551990171434213 7124906380228498157143915)
    ·
      refine ⟨10687359570342747235715873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124906380228498157143915 10687359570342747235715873)
      ·
        refine ⟨8015519677757060426786905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10687359570342747235715873 8015519677757060426786905)
        ·
          refine ⟨6011639758317795320090179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8015519677757060426786905 6011639758317795320090179)
          ·
            refine ⟨9017459637476692980135269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011639758317795320090179 9017459637476692980135269)
            ·
              refine ⟨1690773682026879933775363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9017459637476692980135269 1690773682026879933775363)
              ·
                refine ⟨2536160523040319900663045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690773682026879933775363 2536160523040319900663045)
                ·
                  refine ⟨475530098070059981374321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536160523040319900663045 475530098070059981374321)
                  ·
                    rfl

theorem cell20_1041853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1041853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041853 prefixEnd_1041853 := by exact prefixLift 1041853
  have htrace : WordTrace (prefixWord ++ tailWord_1041853) baseStart_1041853 baseEnd_1041853 := by
    simpa [prefixWord, tailWord_1041853, baseEnd_1041853] using wordTrace_append hprefix tailTrace_1041853
  have hstable : (prefixWord ++ tailWord_1041853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041853).length < 2 ^ (prefixWord ++ tailWord_1041853).sum := by decide
  have hdescent : baseEnd_1041853 < baseStart_1041853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041867 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 3]
def baseStart_1041867 : Nat := 118140960795 + 1041867 * 2 ^ 59
def prefixEnd_1041867 : Nat := 4983230072969 + 3 ^ 40 * 1041867 * 2
def baseEnd_1041867 : Nat := 475536488051538154907597

theorem tailTrace_1041867 : CollatzResearch.WordTrace tailWord_1041867 prefixEnd_1041867 475536488051538154907597 := by
  unfold tailWord_1041867
  simp only [CollatzResearch.WordTrace]
  refine ⟨38000011316501270562443855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25333340877667513708295903 38000011316501270562443855)
  ·
    refine ⟨57000016974751905843665783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38000011316501270562443855 57000016974751905843665783)
    ·
      refine ⟨85500025462127858765498675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57000016974751905843665783 85500025462127858765498675)
      ·
        refine ⟨128250038193191788148248013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85500025462127858765498675 128250038193191788148248013)
        ·
          refine ⟨48093764322446920555593005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128250038193191788148248013 48093764322446920555593005)
          ·
            refine ⟨18035161620917595208347377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48093764322446920555593005 18035161620917595208347377)
            ·
              refine ⟨13526371215688196406260533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18035161620917595208347377 13526371215688196406260533)
              ·
                refine ⟨1268097301470768413086925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13526371215688196406260533 1268097301470768413086925)
                ·
                  refine ⟨475536488051538154907597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268097301470768413086925 475536488051538154907597)
                  ·
                    rfl

theorem cell20_1041867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_1041867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041867 prefixEnd_1041867 := by exact prefixLift 1041867
  have htrace : WordTrace (prefixWord ++ tailWord_1041867) baseStart_1041867 baseEnd_1041867 := by
    simpa [prefixWord, tailWord_1041867, baseEnd_1041867] using wordTrace_append hprefix tailTrace_1041867
  have hstable : (prefixWord ++ tailWord_1041867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041867).length < 2 ^ (prefixWord ++ tailWord_1041867).sum := by decide
  have hdescent : baseEnd_1041867 < baseStart_1041867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041905 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_1041905 : Nat := 118140960795 + 1041905 * 2 ^ 59
def prefixEnd_1041905 : Nat := 4983230072969 + 3 ^ 40 * 1041905 * 2
def baseEnd_1041905 : Nat := 475553832286978911640775

theorem tailTrace_1041905 : CollatzResearch.WordTrace tailWord_1041905 prefixEnd_1041905 475553832286978911640775 := by
  unfold tailWord_1041905
  simp only [CollatzResearch.WordTrace]
  refine ⟨38001397290363603052327169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25334264860242402034884779 38001397290363603052327169)
  ·
    refine ⟨28501047967772702289245377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38001397290363603052327169 28501047967772702289245377)
    ·
      refine ⟨21375785975829526716934033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28501047967772702289245377 21375785975829526716934033)
      ·
        refine ⟨16031839481872145037700525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21375785975829526716934033 16031839481872145037700525)
        ·
          refine ⟨6011939805702054389137697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16031839481872145037700525 6011939805702054389137697)
          ·
            refine ⟨4508954854276540791853273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6011939805702054389137697 4508954854276540791853273)
            ·
              refine ⟨3381716140707405593889955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508954854276540791853273 3381716140707405593889955)
              ·
                refine ⟨5072574211061108390834933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381716140707405593889955 5072574211061108390834933)
                ·
                  refine ⟨475553832286978911640775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5072574211061108390834933 475553832286978911640775)
                  ·
                    rfl

theorem cell20_1041905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_1041905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041905 prefixEnd_1041905 := by exact prefixLift 1041905
  have htrace : WordTrace (prefixWord ++ tailWord_1041905) baseStart_1041905 baseEnd_1041905 := by
    simpa [prefixWord, tailWord_1041905, baseEnd_1041905] using wordTrace_append hprefix tailTrace_1041905
  have hstable : (prefixWord ++ tailWord_1041905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041905).length < 2 ^ (prefixWord ++ tailWord_1041905).sum := by decide
  have hdescent : baseEnd_1041905 < baseStart_1041905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041918 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1041918 : Nat := 118140960795 + 1041918 * 2 ^ 59
def prefixEnd_1041918 : Nat := 4983230072969 + 3 ^ 40 * 1041918 * 2
def baseEnd_1041918 : Nat := 475559765841208644207389

theorem tailTrace_1041918 : CollatzResearch.WordTrace tailWord_1041918 prefixEnd_1041918 475559765841208644207389 := by
  unfold tailWord_1041918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750233929914563284068801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25334580959544337515033605 4750233929914563284068801)
  ·
    refine ⟨3562675447435922463051601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4750233929914563284068801 3562675447435922463051601)
    ·
      refine ⟨2672006585576941847288701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3562675447435922463051601 2672006585576941847288701)
      ·
        refine ⟨1002002469591353192733263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2672006585576941847288701 1002002469591353192733263)
        ·
          refine ⟨1503003704387029789099895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002002469591353192733263 1503003704387029789099895)
          ·
            refine ⟨2254505556580544683649843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503003704387029789099895 2254505556580544683649843)
            ·
              refine ⟨3381758334870817025474765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254505556580544683649843 3381758334870817025474765)
              ·
                refine ⟨1268159375576556384553037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3381758334870817025474765 1268159375576556384553037)
                ·
                  refine ⟨475559765841208644207389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268159375576556384553037 475559765841208644207389)
                  ·
                    rfl

theorem cell20_1041918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1041918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041918 prefixEnd_1041918 := by exact prefixLift 1041918
  have htrace : WordTrace (prefixWord ++ tailWord_1041918) baseStart_1041918 baseEnd_1041918 := by
    simpa [prefixWord, tailWord_1041918, baseEnd_1041918] using wordTrace_append hprefix tailTrace_1041918
  have hstable : (prefixWord ++ tailWord_1041918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041918).length < 2 ^ (prefixWord ++ tailWord_1041918).sum := by decide
  have hdescent : baseEnd_1041918 < baseStart_1041918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041991 : List Nat := [1, 1, 4, 1, 5, 1, 3, 4]
def baseStart_1041991 : Nat := 118140960795 + 1041991 * 2 ^ 59
def prefixEnd_1041991 : Nat := 4983230072969 + 3 ^ 40 * 1041991 * 2
def baseEnd_1041991 : Nat := 158531028343448278257919

theorem tailTrace_1041991 : CollatzResearch.WordTrace tailWord_1041991 prefixEnd_1041991 158531028343448278257919 := by
  unfold tailWord_1041991
  simp only [CollatzResearch.WordTrace]
  refine ⟨38004533968052039739957827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25336355978701359826638551 38004533968052039739957827)
  ·
    refine ⟨57006800952078059609936741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38004533968052039739957827 57006800952078059609936741)
    ·
      refine ⟨10688775178514636176863139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57006800952078059609936741 10688775178514636176863139)
      ·
        refine ⟨16033162767771954265294709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10688775178514636176863139 16033162767771954265294709)
        ·
          refine ⟨1503109009478620712371379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16033162767771954265294709 1503109009478620712371379)
          ·
            refine ⟨2254663514217931068557069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503109009478620712371379 2254663514217931068557069)
            ·
              refine ⟨845498817831724150708901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2254663514217931068557069 845498817831724150708901)
              ·
                refine ⟨158531028343448278257919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 845498817831724150708901 158531028343448278257919)
                ·
                  rfl

theorem cell20_1041991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_1041991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041991 prefixEnd_1041991 := by exact prefixLift 1041991
  have htrace : WordTrace (prefixWord ++ tailWord_1041991) baseStart_1041991 baseEnd_1041991 := by
    simpa [prefixWord, tailWord_1041991, baseEnd_1041991] using wordTrace_append hprefix tailTrace_1041991
  have hstable : (prefixWord ++ tailWord_1041991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041991).length < 2 ^ (prefixWord ++ tailWord_1041991).sum := by decide
  have hdescent : baseEnd_1041991 < baseStart_1041991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042012 : List Nat := [2, 2, 4, 1, 2, 2, 7]
def baseStart_1042012 : Nat := 118140960795 + 1042012 * 2 ^ 59
def prefixEnd_1042012 : Nat := 4983230072969 + 3 ^ 40 * 1042012 * 2
def baseEnd_1042012 : Nat := 52844741111395788341519

theorem tailTrace_1042012 : CollatzResearch.WordTrace tailWord_1042012 prefixEnd_1042012 52844741111395788341519 := by
  unfold tailWord_1042012
  simp only [CollatzResearch.WordTrace]
  refine ⟨19002649950487980163236145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25336866600650640217648193 19002649950487980163236145)
  ·
    refine ⟨14251987462865985122427109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19002649950487980163236145 14251987462865985122427109)
    ·
      refine ⟨2672247649287372210455083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14251987462865985122427109 2672247649287372210455083)
      ·
        refine ⟨4008371473931058315682625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672247649287372210455083 4008371473931058315682625)
        ·
          refine ⟨3006278605448293736761969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4008371473931058315682625 3006278605448293736761969)
          ·
            refine ⟨2254708954086220302571477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3006278605448293736761969 2254708954086220302571477)
            ·
              refine ⟨52844741111395788341519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2254708954086220302571477 52844741111395788341519)
              ·
                rfl

theorem cell20_1042012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 7].length) (baseStart_1042012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042012 prefixEnd_1042012 := by exact prefixLift 1042012
  have htrace : WordTrace (prefixWord ++ tailWord_1042012) baseStart_1042012 baseEnd_1042012 := by
    simpa [prefixWord, tailWord_1042012, baseEnd_1042012] using wordTrace_append hprefix tailTrace_1042012
  have hstable : (prefixWord ++ tailWord_1042012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042012).length < 2 ^ (prefixWord ++ tailWord_1042012).sum := by decide
  have hdescent : baseEnd_1042012 < baseStart_1042012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042019 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_1042019 : Nat := 118140960795 + 1042019 * 2 ^ 59
def prefixEnd_1042019 : Nat := 4983230072969 + 3 ^ 40 * 1042019 * 2
def baseEnd_1042019 : Nat := 475605864993301181840309

theorem tailTrace_1042019 : CollatzResearch.WordTrace tailWord_1042019 prefixEnd_1042019 475605864993301181840309 := by
  unfold tailWord_1042019
  simp only [CollatzResearch.WordTrace]
  refine ⟨38005555211950600521977111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25337036807967067014651407 38005555211950600521977111)
  ·
    refine ⟨57008332817925900782965667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38005555211950600521977111 57008332817925900782965667)
    ·
      refine ⟨85512499226888851174448501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57008332817925900782965667 85512499226888851174448501)
      ·
        refine ⟨8016796802520829797604547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85512499226888851174448501 8016796802520829797604547)
        ·
          refine ⟨12025195203781244696406821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016796802520829797604547 12025195203781244696406821)
          ·
            refine ⟨2254724100708983380576279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12025195203781244696406821 2254724100708983380576279)
            ·
              refine ⟨3382086151063475070864419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2254724100708983380576279 3382086151063475070864419)
              ·
                refine ⟨5073129226595212606296629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382086151063475070864419 5073129226595212606296629)
                ·
                  refine ⟨475605864993301181840309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5073129226595212606296629 475605864993301181840309)
                  ·
                    rfl

theorem cell20_1042019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_1042019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042019 prefixEnd_1042019 := by exact prefixLift 1042019
  have htrace : WordTrace (prefixWord ++ tailWord_1042019) baseStart_1042019 baseEnd_1042019 := by
    simpa [prefixWord, tailWord_1042019, baseEnd_1042019] using wordTrace_append hprefix tailTrace_1042019
  have hstable : (prefixWord ++ tailWord_1042019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042019).length < 2 ^ (prefixWord ++ tailWord_1042019).sum := by decide
  have hdescent : baseEnd_1042019 < baseStart_1042019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042040 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1042040 : Nat := 118140960795 + 1042040 * 2 ^ 59
def prefixEnd_1042040 : Nat := 4983230072969 + 3 ^ 40 * 1042040 * 2
def baseEnd_1042040 : Nat := 475615449965518442140223

theorem tailTrace_1042040 : CollatzResearch.WordTrace tailWord_1042040 prefixEnd_1042040 475615449965518442140223 := by
  unfold tailWord_1042040
  simp only [CollatzResearch.WordTrace]
  refine ⟨19003160572437260554245787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25337547429916347405661049 19003160572437260554245787)
  ·
    refine ⟨28504740858655890831368681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19003160572437260554245787 28504740858655890831368681)
    ·
      refine ⟨21378555643991918123526511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28504740858655890831368681 21378555643991918123526511)
      ·
        refine ⟨32067833465987877185289767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21378555643991918123526511 32067833465987877185289767)
        ·
          refine ⟨48101750198981815777934651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32067833465987877185289767 48101750198981815777934651)
          ·
            refine ⟨72152625298472723666901977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48101750198981815777934651 72152625298472723666901977)
            ·
              refine ⟨54114468973854542750176483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72152625298472723666901977 54114468973854542750176483)
              ·
                refine ⟨81171703460781814125264725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54114468973854542750176483 81171703460781814125264725)
                ·
                  refine ⟨475615449965518442140223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81171703460781814125264725 475615449965518442140223)
                  ·
                    rfl

theorem cell20_1042040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1042040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042040 prefixEnd_1042040 := by exact prefixLift 1042040
  have htrace : WordTrace (prefixWord ++ tailWord_1042040) baseStart_1042040 baseEnd_1042040 := by
    simpa [prefixWord, tailWord_1042040, baseEnd_1042040] using wordTrace_append hprefix tailTrace_1042040
  have hstable : (prefixWord ++ tailWord_1042040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042040).length < 2 ^ (prefixWord ++ tailWord_1042040).sum := by decide
  have hdescent : baseEnd_1042040 < baseStart_1042040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042056 : List Nat := [2, 1, 3, 5, 1, 2, 1, 3, 2]
def baseStart_1042056 : Nat := 118140960795 + 1042056 * 2 ^ 59
def prefixEnd_1042056 : Nat := 4983230072969 + 3 ^ 40 * 1042056 * 2
def baseEnd_1042056 : Nat := 475622752801493497606825

theorem tailTrace_1042056 : CollatzResearch.WordTrace tailWord_1042056 prefixEnd_1042056 475622752801493497606825 := by
  unfold tailWord_1042056
  simp only [CollatzResearch.WordTrace]
  refine ⟨19003452356408277920537011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25337936475211037227382681 19003452356408277920537011)
  ·
    refine ⟨28505178534612416880805517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19003452356408277920537011 28505178534612416880805517)
    ·
      refine ⟨10689441950479656330302069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28505178534612416880805517 10689441950479656330302069)
      ·
        refine ⟨1002135182857467780965819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10689441950479656330302069 1002135182857467780965819)
        ·
          refine ⟨1503202774286201671448729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002135182857467780965819 1503202774286201671448729)
          ·
            refine ⟨1127402080714651253586547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503202774286201671448729 1127402080714651253586547)
            ·
              refine ⟨1691103121071976880379821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127402080714651253586547 1691103121071976880379821)
              ·
                refine ⟨634163670401991330142433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1691103121071976880379821 634163670401991330142433)
                ·
                  refine ⟨475622752801493497606825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634163670401991330142433 475622752801493497606825)
                  ·
                    rfl

theorem cell20_1042056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_1042056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042056 prefixEnd_1042056 := by exact prefixLift 1042056
  have htrace : WordTrace (prefixWord ++ tailWord_1042056) baseStart_1042056 baseEnd_1042056 := by
    simpa [prefixWord, tailWord_1042056, baseEnd_1042056] using wordTrace_append hprefix tailTrace_1042056
  have hstable : (prefixWord ++ tailWord_1042056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042056).length < 2 ^ (prefixWord ++ tailWord_1042056).sum := by decide
  have hdescent : baseEnd_1042056 < baseStart_1042056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042071 : List Nat := [1, 1, 3, 3, 2, 2, 8]
def baseStart_1042071 : Nat := 118140960795 + 1042071 * 2 ^ 59
def prefixEnd_1042071 : Nat := 4983230072969 + 3 ^ 40 * 1042071 * 2
def baseEnd_1042071 : Nat := 52847733245580012456307

theorem tailTrace_1042071 : CollatzResearch.WordTrace tailWord_1042071 prefixEnd_1042071 52847733245580012456307 := by
  unfold tailWord_1042071
  simp only [CollatzResearch.WordTrace]
  refine ⟨38007451807762213402870067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25338301205174808935246711 38007451807762213402870067)
  ·
    refine ⟨57011177711643320104305101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38007451807762213402870067 57011177711643320104305101)
    ·
      refine ⟨21379191641866245039114413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57011177711643320104305101 21379191641866245039114413)
      ·
        refine ⟨8017196865699841889667905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21379191641866245039114413 8017196865699841889667905)
        ·
          refine ⟨6012897649274881417250929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8017196865699841889667905 6012897649274881417250929)
          ·
            refine ⟨4509673236956161062938197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6012897649274881417250929 4509673236956161062938197)
            ·
              refine ⟨52847733245580012456307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4509673236956161062938197 52847733245580012456307)
              ·
                rfl

theorem cell20_1042071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 8].length) (baseStart_1042071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042071 prefixEnd_1042071 := by exact prefixLift 1042071
  have htrace : WordTrace (prefixWord ++ tailWord_1042071) baseStart_1042071 baseEnd_1042071 := by
    simpa [prefixWord, tailWord_1042071, baseEnd_1042071] using wordTrace_append hprefix tailTrace_1042071
  have hstable : (prefixWord ++ tailWord_1042071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042071).length < 2 ^ (prefixWord ++ tailWord_1042071).sum := by decide
  have hdescent : baseEnd_1042071 < baseStart_1042071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042081 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_1042081 : Nat := 118140960795 + 1042081 * 2 ^ 59
def prefixEnd_1042081 : Nat := 4983230072969 + 3 ^ 40 * 1042081 * 2
def baseEnd_1042081 : Nat := 475634163482704521773389

theorem tailTrace_1042081 : CollatzResearch.WordTrace tailWord_1042081 prefixEnd_1042081 475634163482704521773389 := by
  unfold tailWord_1042081
  simp only [CollatzResearch.WordTrace]
  refine ⟨38007816537725985110734097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25338544358483990073822731 38007816537725985110734097)
  ·
    refine ⟨28505862403294488833050573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38007816537725985110734097 28505862403294488833050573)
    ·
      refine ⟨10689698401235433312393965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28505862403294488833050573 10689698401235433312393965)
      ·
        refine ⟨4008636900463287492147737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10689698401235433312393965 4008636900463287492147737)
        ·
          refine ⟨3006477675347465619110803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4008636900463287492147737 3006477675347465619110803)
          ·
            refine ⟨4509716513021198428666205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006477675347465619110803 4509716513021198428666205)
            ·
              refine ⟨1691143692382949410749827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4509716513021198428666205 1691143692382949410749827)
              ·
                refine ⟨2536715538574424116124741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691143692382949410749827 2536715538574424116124741)
                ·
                  refine ⟨475634163482704521773389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536715538574424116124741 475634163482704521773389)
                  ·
                    rfl

theorem cell20_1042081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_1042081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042081 prefixEnd_1042081 := by exact prefixLift 1042081
  have htrace : WordTrace (prefixWord ++ tailWord_1042081) baseStart_1042081 baseEnd_1042081 := by
    simpa [prefixWord, tailWord_1042081, baseEnd_1042081] using wordTrace_append hprefix tailTrace_1042081
  have hstable : (prefixWord ++ tailWord_1042081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042081).length < 2 ^ (prefixWord ++ tailWord_1042081).sum := by decide
  have hdescent : baseEnd_1042081 < baseStart_1042081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042095 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 3]
def baseStart_1042095 : Nat := 118140960795 + 1042095 * 2 ^ 59
def prefixEnd_1042095 : Nat := 4983230072969 + 3 ^ 40 * 1042095 * 2
def baseEnd_1042095 : Nat := 475640553464182695306665

theorem tailTrace_1042095 : CollatzResearch.WordTrace tailWord_1042095 prefixEnd_1042095 475640553464182695306665 := by
  unfold tailWord_1042095
  simp only [CollatzResearch.WordTrace]
  refine ⟨38008327159675265501743739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25338884773116843667829159 38008327159675265501743739)
  ·
    refine ⟨57012490739512898252615609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38008327159675265501743739 57012490739512898252615609)
    ·
      refine ⟨42759368054634673689461707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57012490739512898252615609 42759368054634673689461707)
      ·
        refine ⟨64139052081952010534192561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42759368054634673689461707 64139052081952010534192561)
        ·
          refine ⟨48104289061464007900644421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64139052081952010534192561 48104289061464007900644421)
          ·
            refine ⟨9019554199024501481370829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48104289061464007900644421 9019554199024501481370829)
            ·
              refine ⟨3382332824634188055514061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9019554199024501481370829 3382332824634188055514061)
              ·
                refine ⟨1268374809237820520817773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3382332824634188055514061 1268374809237820520817773)
                ·
                  refine ⟨475640553464182695306665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268374809237820520817773 475640553464182695306665)
                  ·
                    rfl

theorem cell20_1042095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_1042095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042095 prefixEnd_1042095 := by exact prefixLift 1042095
  have htrace : WordTrace (prefixWord ++ tailWord_1042095) baseStart_1042095 baseEnd_1042095 := by
    simpa [prefixWord, tailWord_1042095, baseEnd_1042095] using wordTrace_append hprefix tailTrace_1042095
  have hstable : (prefixWord ++ tailWord_1042095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042095).length < 2 ^ (prefixWord ++ tailWord_1042095).sum := by decide
  have hdescent : baseEnd_1042095 < baseStart_1042095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042109 : List Nat := [1, 4, 1, 2, 1, 2, 1, 8]
def baseStart_1042109 : Nat := 118140960795 + 1042109 * 2 ^ 59
def prefixEnd_1042109 : Nat := 4983230072969 + 3 ^ 40 * 1042109 * 2
def baseEnd_1042109 : Nat := 158548981148553622946647

theorem tailTrace_1042109 : CollatzResearch.WordTrace tailWord_1042109 prefixEnd_1042109 158548981148553622946647 := by
  unfold tailWord_1042109
  simp only [CollatzResearch.WordTrace]
  refine ⟨38008837781624545892753381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25339225187749697261835587 38008837781624545892753381)
  ·
    refine ⟨7126657084054602354891259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38008837781624545892753381 7126657084054602354891259)
    ·
      refine ⟨10689985626081903532336889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7126657084054602354891259 10689985626081903532336889)
      ·
        refine ⟨8017489219561427649252667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10689985626081903532336889 8017489219561427649252667)
        ·
          refine ⟨12026233829342141473879001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8017489219561427649252667 12026233829342141473879001)
          ·
            refine ⟨9019675372006606105409251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12026233829342141473879001 9019675372006606105409251)
            ·
              refine ⟨13529513058009909158113877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9019675372006606105409251 13529513058009909158113877)
              ·
                refine ⟨158548981148553622946647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13529513058009909158113877 158548981148553622946647)
                ·
                  rfl

theorem cell20_1042109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_1042109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042109 prefixEnd_1042109 := by exact prefixLift 1042109
  have htrace : WordTrace (prefixWord ++ tailWord_1042109) baseStart_1042109 baseEnd_1042109 := by
    simpa [prefixWord, tailWord_1042109, baseEnd_1042109] using wordTrace_append hprefix tailTrace_1042109
  have hstable : (prefixWord ++ tailWord_1042109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042109).length < 2 ^ (prefixWord ++ tailWord_1042109).sum := by decide
  have hdescent : baseEnd_1042109 < baseStart_1042109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042119 : List Nat := [1, 1, 4, 1, 1, 1, 4, 5, 2]
def baseStart_1042119 : Nat := 118140960795 + 1042119 * 2 ^ 59
def prefixEnd_1042119 : Nat := 4983230072969 + 3 ^ 40 * 1042119 * 2
def baseEnd_1042119 : Nat := 475651507718145278506567

theorem tailTrace_1042119 : CollatzResearch.WordTrace tailWord_1042119 prefixEnd_1042119 475651507718145278506567 := by
  unfold tailWord_1042119
  simp only [CollatzResearch.WordTrace]
  refine ⟨38009202511588317600617411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25339468341058878400411607 38009202511588317600617411)
  ·
    refine ⟨57013803767382476400926117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38009202511588317600617411 57013803767382476400926117)
    ·
      refine ⟨10690088206384214325173647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57013803767382476400926117 10690088206384214325173647)
      ·
        refine ⟨16035132309576321487760471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10690088206384214325173647 16035132309576321487760471)
        ·
          refine ⟨24052698464364482231640707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16035132309576321487760471 24052698464364482231640707)
          ·
            refine ⟨36079047696546723347461061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24052698464364482231640707 36079047696546723347461061)
            ·
              refine ⟨6764821443102510627648949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36079047696546723347461061 6764821443102510627648949)
              ·
                refine ⟨634202010290860371342089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6764821443102510627648949 634202010290860371342089)
                ·
                  refine ⟨475651507718145278506567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634202010290860371342089 475651507718145278506567)
                  ·
                    rfl

theorem cell20_1042119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 2].length) (baseStart_1042119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042119 prefixEnd_1042119 := by exact prefixLift 1042119
  have htrace : WordTrace (prefixWord ++ tailWord_1042119) baseStart_1042119 baseEnd_1042119 := by
    simpa [prefixWord, tailWord_1042119, baseEnd_1042119] using wordTrace_append hprefix tailTrace_1042119
  have hstable : (prefixWord ++ tailWord_1042119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042119).length < 2 ^ (prefixWord ++ tailWord_1042119).sum := by decide
  have hdescent : baseEnd_1042119 < baseStart_1042119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042132 : List Nat := [2, 4, 1, 3, 1, 3, 2, 2, 2]
def baseStart_1042132 : Nat := 118140960795 + 1042132 * 2 ^ 59
def prefixEnd_1042132 : Nat := 4983230072969 + 3 ^ 40 * 1042132 * 2
def baseEnd_1042132 : Nat := 475657441272375011073181

theorem tailTrace_1042132 : CollatzResearch.WordTrace tailWord_1042132 prefixEnd_1042132 475657441272375011073181 := by
  unfold tailWord_1042132
  simp only [CollatzResearch.WordTrace]
  refine ⟨19004838330270610410420325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25339784440360813880560433 19004838330270610410420325)
  ·
    refine ⟨3563407186925739451953811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19004838330270610410420325 3563407186925739451953811)
    ·
      refine ⟨5345110780388609177930717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563407186925739451953811 5345110780388609177930717)
      ·
        refine ⟨2004416542645728441724019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5345110780388609177930717 2004416542645728441724019)
        ·
          refine ⟨3006624813968592662586029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004416542645728441724019 3006624813968592662586029)
          ·
            refine ⟨1127484305238222248469761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3006624813968592662586029 1127484305238222248469761)
            ·
              refine ⟨845613228928666686352321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127484305238222248469761 845613228928666686352321)
              ·
                refine ⟨634209921696500014764241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845613228928666686352321 634209921696500014764241)
                ·
                  refine ⟨475657441272375011073181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634209921696500014764241 475657441272375011073181)
                  ·
                    rfl

theorem cell20_1042132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_1042132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042132 prefixEnd_1042132 := by exact prefixLift 1042132
  have htrace : WordTrace (prefixWord ++ tailWord_1042132) baseStart_1042132 baseEnd_1042132 := by
    simpa [prefixWord, tailWord_1042132, baseEnd_1042132] using wordTrace_append hprefix tailTrace_1042132
  have hstable : (prefixWord ++ tailWord_1042132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042132).length < 2 ^ (prefixWord ++ tailWord_1042132).sum := by decide
  have hdescent : baseEnd_1042132 < baseStart_1042132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042157 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1042157 : Nat := 118140960795 + 1042157 * 2 ^ 59
def prefixEnd_1042157 : Nat := 4983230072969 + 3 ^ 40 * 1042157 * 2
def baseEnd_1042157 : Nat := 475668851953586035239745

theorem tailTrace_1042157 : CollatzResearch.WordTrace tailWord_1042157 prefixEnd_1042157 475668851953586035239745 := by
  unfold tailWord_1042157
  simp only [CollatzResearch.WordTrace]
  refine ⟨38010588485450650090500725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25340392323633766727000483 38010588485450650090500725)
  ·
    refine ⟨3563492670510998445984443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38010588485450650090500725 3563492670510998445984443)
    ·
      refine ⟨5345239005766497668976665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563492670510998445984443 5345239005766497668976665)
      ·
        refine ⟨4008929254324873251732499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5345239005766497668976665 4008929254324873251732499)
        ·
          refine ⟨6013393881487309877598749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008929254324873251732499 6013393881487309877598749)
          ·
            refine ⟨2255022705557741204099531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6013393881487309877598749 2255022705557741204099531)
            ·
              refine ⟨3382534058336611806149297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255022705557741204099531 3382534058336611806149297)
              ·
                refine ⟨2536900543752458854611973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3382534058336611806149297 2536900543752458854611973)
                ·
                  refine ⟨475668851953586035239745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2536900543752458854611973 475668851953586035239745)
                  ·
                    rfl

theorem cell20_1042157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1042157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042157 prefixEnd_1042157 := by exact prefixLift 1042157
  have htrace : WordTrace (prefixWord ++ tailWord_1042157) baseStart_1042157 baseEnd_1042157 := by
    simpa [prefixWord, tailWord_1042157, baseEnd_1042157] using wordTrace_append hprefix tailTrace_1042157
  have hstable : (prefixWord ++ tailWord_1042157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042157).length < 2 ^ (prefixWord ++ tailWord_1042157).sum := by decide
  have hdescent : baseEnd_1042157 < baseStart_1042157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042229 : List Nat := [1, 3, 3, 1, 4, 2, 1, 3, 2]
def baseStart_1042229 : Nat := 118140960795 + 1042229 * 2 ^ 59
def prefixEnd_1042229 : Nat := 4983230072969 + 3 ^ 40 * 1042229 * 2
def baseEnd_1042229 : Nat := 475701714715473784839451

theorem tailTrace_1042229 : CollatzResearch.WordTrace tailWord_1042229 prefixEnd_1042229 475701714715473784839451 := by
  unfold tailWord_1042229
  simp only [CollatzResearch.WordTrace]
  refine ⟨38013214541189806387121741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25342143027459870924747827 38013214541189806387121741)
  ·
    refine ⟨14254955452946177395170653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38013214541189806387121741 14254955452946177395170653)
    ·
      refine ⟨5345608294854816523188995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14254955452946177395170653 5345608294854816523188995)
      ·
        refine ⟨8018412442282224784783493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345608294854816523188995 8018412442282224784783493)
        ·
          refine ⟨1503452332927917147146905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8018412442282224784783493 1503452332927917147146905)
          ·
            refine ⟨1127589249695937860360179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503452332927917147146905 1127589249695937860360179)
            ·
              refine ⟨1691383874543906790540269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127589249695937860360179 1691383874543906790540269)
              ·
                refine ⟨634268952953965046452601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1691383874543906790540269 634268952953965046452601)
                ·
                  refine ⟨475701714715473784839451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634268952953965046452601 475701714715473784839451)
                  ·
                    rfl

theorem cell20_1042229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_1042229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042229 prefixEnd_1042229 := by exact prefixLift 1042229
  have htrace : WordTrace (prefixWord ++ tailWord_1042229) baseStart_1042229 baseEnd_1042229 := by
    simpa [prefixWord, tailWord_1042229, baseEnd_1042229] using wordTrace_append hprefix tailTrace_1042229
  have hstable : (prefixWord ++ tailWord_1042229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042229).length < 2 ^ (prefixWord ++ tailWord_1042229).sum := by decide
  have hdescent : baseEnd_1042229 < baseStart_1042229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042250 : List Nat := [3, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_1042250 : Nat := 118140960795 + 1042250 * 2 ^ 59
def prefixEnd_1042250 : Nat := 4983230072969 + 3 ^ 40 * 1042250 * 2
def baseEnd_1042250 : Nat := 475711299687691045139365

theorem tailTrace_1042250 : CollatzResearch.WordTrace tailWord_1042250 prefixEnd_1042250 475711299687691045139365 := by
  unfold tailWord_1042250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9503495118528431743409051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25342653649409151315757469 9503495118528431743409051)
  ·
    refine ⟨14255242677792647615113577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9503495118528431743409051 14255242677792647615113577)
    ·
      refine ⟨10691432008344485711335183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14255242677792647615113577 10691432008344485711335183)
      ·
        refine ⟨16037148012516728567002775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10691432008344485711335183 16037148012516728567002775)
        ·
          refine ⟨24055722018775092850504163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16037148012516728567002775 24055722018775092850504163)
          ·
            refine ⟨36083583028162639275756245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24055722018775092850504163 36083583028162639275756245)
            ·
              refine ⟨845708977222561858025537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36083583028162639275756245 845708977222561858025537)
              ·
                refine ⟨634281732916921393519153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845708977222561858025537 634281732916921393519153)
                ·
                  refine ⟨475711299687691045139365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634281732916921393519153 475711299687691045139365)
                  ·
                    rfl

theorem cell20_1042250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_1042250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042250 prefixEnd_1042250 := by exact prefixLift 1042250
  have htrace : WordTrace (prefixWord ++ tailWord_1042250) baseStart_1042250 baseEnd_1042250 := by
    simpa [prefixWord, tailWord_1042250, baseEnd_1042250] using wordTrace_append hprefix tailTrace_1042250
  have hstable : (prefixWord ++ tailWord_1042250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042250).length < 2 ^ (prefixWord ++ tailWord_1042250).sum := by decide
  have hdescent : baseEnd_1042250 < baseStart_1042250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042261 : List Nat := [1, 3, 2, 2, 2, 2, 1, 7]
def baseStart_1042261 : Nat := 118140960795 + 1042261 * 2 ^ 59
def prefixEnd_1042261 : Nat := 4983230072969 + 3 ^ 40 * 1042261 * 2
def baseEnd_1042261 : Nat := 158572106795807965257551

theorem tailTrace_1042261 : CollatzResearch.WordTrace tailWord_1042261 prefixEnd_1042261 158572106795807965257551 := by
  unfold tailWord_1042261
  simp only [CollatzResearch.WordTrace]
  refine ⟨38014381677073875852286637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25342921118049250568191091 38014381677073875852286637)
  ·
    refine ⟨14255393128902703444607489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38014381677073875852286637 14255393128902703444607489)
    ·
      refine ⟨10691544846677027583455617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14255393128902703444607489 10691544846677027583455617)
      ·
        refine ⟨8018658635007770687591713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10691544846677027583455617 8018658635007770687591713)
        ·
          refine ⟨6013993976255828015693785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8018658635007770687591713 6013993976255828015693785)
          ·
            refine ⟨4510495482191871011770339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6013993976255828015693785 4510495482191871011770339)
            ·
              refine ⟨6765743223287806517655509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510495482191871011770339 6765743223287806517655509)
              ·
                refine ⟨158572106795807965257551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6765743223287806517655509 158572106795807965257551)
                ·
                  rfl

theorem cell20_1042261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_1042261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042261 prefixEnd_1042261 := by exact prefixLift 1042261
  have htrace : WordTrace (prefixWord ++ tailWord_1042261) baseStart_1042261 baseEnd_1042261 := by
    simpa [prefixWord, tailWord_1042261, baseEnd_1042261] using wordTrace_append hprefix tailTrace_1042261
  have hstable : (prefixWord ++ tailWord_1042261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042261).length < 2 ^ (prefixWord ++ tailWord_1042261).sum := by decide
  have hdescent : baseEnd_1042261 < baseStart_1042261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042305 : List Nat := [1, 2, 4, 4, 1, 1, 1, 4, 2]
def baseStart_1042305 : Nat := 118140960795 + 1042305 * 2 ^ 59
def prefixEnd_1042305 : Nat := 4983230072969 + 3 ^ 40 * 1042305 * 2
def baseEnd_1042305 : Nat := 475736403186355298305807

theorem tailTrace_1042305 : CollatzResearch.WordTrace tailWord_1042305 prefixEnd_1042305 475736403186355298305807 := by
  unfold tailWord_1042305
  simp only [CollatzResearch.WordTrace]
  refine ⟨38015986488914471366888369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25343990992609647577925579 38015986488914471366888369)
  ·
    refine ⟨28511989866685853525166277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38015986488914471366888369 28511989866685853525166277)
    ·
      refine ⟨5345998100003597535968677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28511989866685853525166277 5345998100003597535968677)
      ·
        refine ⟨1002374643750674537994127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5345998100003597535968677 1002374643750674537994127)
        ·
          refine ⟨1503561965626011806991191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002374643750674537994127 1503561965626011806991191)
          ·
            refine ⟨2255342948439017710486787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503561965626011806991191 2255342948439017710486787)
            ·
              refine ⟨3383014422658526565730181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255342948439017710486787 3383014422658526565730181)
              ·
                refine ⟨634315204248473731074409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3383014422658526565730181 634315204248473731074409)
                ·
                  refine ⟨475736403186355298305807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634315204248473731074409 475736403186355298305807)
                  ·
                    rfl

theorem cell20_1042305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_1042305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042305 prefixEnd_1042305 := by exact prefixLift 1042305
  have htrace : WordTrace (prefixWord ++ tailWord_1042305) baseStart_1042305 baseEnd_1042305 := by
    simpa [prefixWord, tailWord_1042305, baseEnd_1042305] using wordTrace_append hprefix tailTrace_1042305
  have hstable : (prefixWord ++ tailWord_1042305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042305).length < 2 ^ (prefixWord ++ tailWord_1042305).sum := by decide
  have hdescent : baseEnd_1042305 < baseStart_1042305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042309 : List Nat := [1, 3, 1, 1, 3, 2, 3, 4, 2]
def baseStart_1042309 : Nat := 118140960795 + 1042309 * 2 ^ 59
def prefixEnd_1042309 : Nat := 4983230072969 + 3 ^ 40 * 1042309 * 2
def baseEnd_1042309 : Nat := 475738228895349062172457

theorem tailTrace_1042309 : CollatzResearch.WordTrace tailWord_1042309 prefixEnd_1042309 475738228895349062172457 := by
  unfold tailWord_1042309
  simp only [CollatzResearch.WordTrace]
  refine ⟨38016132380899980050033981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25344088253933320033355987 38016132380899980050033981)
  ·
    refine ⟨14256049642837492518762743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38016132380899980050033981 14256049642837492518762743)
    ·
      refine ⟨21384074464256238778144115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14256049642837492518762743 21384074464256238778144115)
      ·
        refine ⟨32076111696384358167216173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21384074464256238778144115 32076111696384358167216173)
        ·
          refine ⟨12028541886144134312706065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32076111696384358167216173 12028541886144134312706065)
          ·
            refine ⟨9021406414608100734529549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12028541886144134312706065 9021406414608100734529549)
            ·
              refine ⟨3383027405478037775448581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9021406414608100734529549 3383027405478037775448581)
              ·
                refine ⟨634317638527132082896609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3383027405478037775448581 634317638527132082896609)
                ·
                  refine ⟨475738228895349062172457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634317638527132082896609 475738228895349062172457)
                  ·
                    rfl

theorem cell20_1042309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_1042309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042309 prefixEnd_1042309 := by exact prefixLift 1042309
  have htrace : WordTrace (prefixWord ++ tailWord_1042309) baseStart_1042309 baseEnd_1042309 := by
    simpa [prefixWord, tailWord_1042309, baseEnd_1042309] using wordTrace_append hprefix tailTrace_1042309
  have hstable : (prefixWord ++ tailWord_1042309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042309).length < 2 ^ (prefixWord ++ tailWord_1042309).sum := by decide
  have hdescent : baseEnd_1042309 < baseStart_1042309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042330 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1042330 : Nat := 118140960795 + 1042330 * 2 ^ 59
def prefixEnd_1042330 : Nat := 4983230072969 + 3 ^ 40 * 1042330 * 2
def baseEnd_1042330 : Nat := 475747813867566322472371

theorem tailTrace_1042330 : CollatzResearch.WordTrace tailWord_1042330 prefixEnd_1042330 475747813867566322472371 := by
  unfold tailWord_1042330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504224578455975159137111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25344598875882600424365629 9504224578455975159137111)
  ·
    refine ⟨14256336867683962738705667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9504224578455975159137111 14256336867683962738705667)
    ·
      refine ⟨21384505301525944108058501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14256336867683962738705667 21384505301525944108058501)
      ·
        refine ⟨4009594744036114520260969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21384505301525944108058501 4009594744036114520260969)
        ·
          refine ⟨3007196058027085890195727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4009594744036114520260969 3007196058027085890195727)
          ·
            refine ⟨4510794087040628835293591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007196058027085890195727 4510794087040628835293591)
            ·
              refine ⟨6766191130560943252940387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510794087040628835293591 6766191130560943252940387)
              ·
                refine ⟨10149286695841414879410581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6766191130560943252940387 10149286695841414879410581)
                ·
                  refine ⟨475747813867566322472371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10149286695841414879410581 475747813867566322472371)
                  ·
                    rfl

theorem cell20_1042330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1042330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042330 prefixEnd_1042330 := by exact prefixLift 1042330
  have htrace : WordTrace (prefixWord ++ tailWord_1042330) baseStart_1042330 baseEnd_1042330 := by
    simpa [prefixWord, tailWord_1042330, baseEnd_1042330] using wordTrace_append hprefix tailTrace_1042330
  have hstable : (prefixWord ++ tailWord_1042330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042330).length < 2 ^ (prefixWord ++ tailWord_1042330).sum := by decide
  have hdescent : baseEnd_1042330 < baseStart_1042330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042350 : List Nat := [4, 1, 5, 1, 1, 1, 7]
def baseStart_1042350 : Nat := 118140960795 + 1042350 * 2 ^ 59
def prefixEnd_1042350 : Nat := 4983230072969 + 3 ^ 40 * 1042350 * 2
def baseEnd_1042350 : Nat := 52861882490281682422847

theorem tailTrace_1042350 : CollatzResearch.WordTrace tailWord_1042350 prefixEnd_1042350 52861882490281682422847 := by
  unfold tailWord_1042350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752203471718930506534563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25345085182500962701517669 4752203471718930506534563)
  ·
    refine ⟨7128305207578395759801845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4752203471718930506534563 7128305207578395759801845)
    ·
      refine ⟨668278613210474602481423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7128305207578395759801845 668278613210474602481423)
      ·
        refine ⟨1002417919815711903722135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668278613210474602481423 1002417919815711903722135)
        ·
          refine ⟨1503626879723567855583203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002417919815711903722135 1503626879723567855583203)
          ·
            refine ⟨2255440319585351783374805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503626879723567855583203 2255440319585351783374805)
            ·
              refine ⟨52861882490281682422847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2255440319585351783374805 52861882490281682422847)
              ·
                rfl

theorem cell20_1042350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 7].length) (baseStart_1042350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042350 prefixEnd_1042350 := by exact prefixLift 1042350
  have htrace : WordTrace (prefixWord ++ tailWord_1042350) baseStart_1042350 baseEnd_1042350 := by
    simpa [prefixWord, tailWord_1042350, baseEnd_1042350] using wordTrace_append hprefix tailTrace_1042350
  have hstable : (prefixWord ++ tailWord_1042350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042350).length < 2 ^ (prefixWord ++ tailWord_1042350).sum := by decide
  have hdescent : baseEnd_1042350 < baseStart_1042350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042351 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_1042351 : Nat := 118140960795 + 1042351 * 2 ^ 59
def prefixEnd_1042351 : Nat := 4983230072969 + 3 ^ 40 * 1042351 * 2
def baseEnd_1042351 : Nat := 475757398839783582772285

theorem tailTrace_1042351 : CollatzResearch.WordTrace tailWord_1042351 prefixEnd_1042351 475757398839783582772285 := by
  unfold tailWord_1042351
  simp only [CollatzResearch.WordTrace]
  refine ⟨38017664246747821223062907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25345109497831880815375271 38017664246747821223062907)
  ·
    refine ⟨57026496370121731834594361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38017664246747821223062907 57026496370121731834594361)
    ·
      refine ⟨42769872277591298875945771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57026496370121731834594361 42769872277591298875945771)
      ·
        refine ⟨64154808416386948313918657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42769872277591298875945771 64154808416386948313918657)
        ·
          refine ⟨48116106312290211235438993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64154808416386948313918657 48116106312290211235438993)
          ·
            refine ⟨36087079734217658426579245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48116106312290211235438993 36087079734217658426579245)
            ·
              refine ⟨13532654900331621909967217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36087079734217658426579245 13532654900331621909967217)
              ·
                refine ⟨10149491175248716432475413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13532654900331621909967217 10149491175248716432475413)
                ·
                  refine ⟨475757398839783582772285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10149491175248716432475413 475757398839783582772285)
                  ·
                    rfl

theorem cell20_1042351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_1042351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042351 prefixEnd_1042351 := by exact prefixLift 1042351
  have htrace : WordTrace (prefixWord ++ tailWord_1042351) baseStart_1042351 baseEnd_1042351 := by
    simpa [prefixWord, tailWord_1042351, baseEnd_1042351] using wordTrace_append hprefix tailTrace_1042351
  have hstable : (prefixWord ++ tailWord_1042351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042351).length < 2 ^ (prefixWord ++ tailWord_1042351).sum := by decide
  have hdescent : baseEnd_1042351 < baseStart_1042351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042364 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_1042364 : Nat := 118140960795 + 1042364 * 2 ^ 59
def prefixEnd_1042364 : Nat := 4983230072969 + 3 ^ 40 * 1042364 * 2
def baseEnd_1042364 : Nat := 475763332394013315338899

theorem tailTrace_1042364 : CollatzResearch.WordTrace tailWord_1042364 prefixEnd_1042364 475763332394013315338899 := by
  unfold tailWord_1042364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009069197850362221643073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25345425597133816295524097 19009069197850362221643073)
  ·
    refine ⟨14256801898387771666232305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19009069197850362221643073 14256801898387771666232305)
    ·
      refine ⟨10692601423790828749674229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14256801898387771666232305 10692601423790828749674229)
      ·
        refine ⟨1002431383480390195281959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10692601423790828749674229 1002431383480390195281959)
        ·
          refine ⟨1503647075220585292922939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002431383480390195281959 1503647075220585292922939)
          ·
            refine ⟨2255470612830877939384409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503647075220585292922939 2255470612830877939384409)
            ·
              refine ⟨1691602959623158454538307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255470612830877939384409 1691602959623158454538307)
              ·
                refine ⟨2537404439434737681807461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691602959623158454538307 2537404439434737681807461)
                ·
                  refine ⟨475763332394013315338899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537404439434737681807461 475763332394013315338899)
                  ·
                    rfl

theorem cell20_1042364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_1042364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042364 prefixEnd_1042364 := by exact prefixLift 1042364
  have htrace : WordTrace (prefixWord ++ tailWord_1042364) baseStart_1042364 baseEnd_1042364 := by
    simpa [prefixWord, tailWord_1042364, baseEnd_1042364] using wordTrace_append hprefix tailTrace_1042364
  have hstable : (prefixWord ++ tailWord_1042364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042364).length < 2 ^ (prefixWord ++ tailWord_1042364).sum := by decide
  have hdescent : baseEnd_1042364 < baseStart_1042364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042368 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_1042368 : Nat := 118140960795 + 1042368 * 2 ^ 59
def prefixEnd_1042368 : Nat := 4983230072969 + 3 ^ 40 * 1042368 * 2
def baseEnd_1042368 : Nat := 475765158103007079205549

theorem tailTrace_1042368 : CollatzResearch.WordTrace tailWord_1042368 prefixEnd_1042368 475765158103007079205549 := by
  unfold tailWord_1042368
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009142143843116563215879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25345522858457488750954505 19009142143843116563215879)
  ·
    refine ⟨28513713215764674844823819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19009142143843116563215879 28513713215764674844823819)
    ·
      refine ⟨42770569823647012267235729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28513713215764674844823819 42770569823647012267235729)
      ·
        refine ⟨32077927367735259200426797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42770569823647012267235729 32077927367735259200426797)
        ·
          refine ⟨12029222762900722200160049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32077927367735259200426797 12029222762900722200160049)
          ·
            refine ⟨9021917072175541650120037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12029222762900722200160049 9021917072175541650120037)
            ·
              refine ⟨1691609451032914059397507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9021917072175541650120037 1691609451032914059397507)
              ·
                refine ⟨2537414176549371089096261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1691609451032914059397507 2537414176549371089096261)
                ·
                  refine ⟨475765158103007079205549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2537414176549371089096261 475765158103007079205549)
                  ·
                    rfl

theorem cell20_1042368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_1042368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042368 prefixEnd_1042368 := by exact prefixLift 1042368
  have htrace : WordTrace (prefixWord ++ tailWord_1042368) baseStart_1042368 baseEnd_1042368 := by
    simpa [prefixWord, tailWord_1042368, baseEnd_1042368] using wordTrace_append hprefix tailTrace_1042368
  have hstable : (prefixWord ++ tailWord_1042368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042368).length < 2 ^ (prefixWord ++ tailWord_1042368).sum := by decide
  have hdescent : baseEnd_1042368 < baseStart_1042368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042430 : List Nat := [4, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1042430 : Nat := 118140960795 + 1042430 * 2 ^ 59
def prefixEnd_1042430 : Nat := 4983230072969 + 3 ^ 40 * 1042430 * 2
def baseEnd_1042430 : Nat := 158597818864136806379543

theorem tailTrace_1042430 : CollatzResearch.WordTrace tailWord_1042430 prefixEnd_1042430 158597818864136806379543 := by
  unfold tailWord_1042430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752568201682702214398593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25347030408974411810125829 4752568201682702214398593)
  ·
    refine ⟨3564426151262026660798945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4752568201682702214398593 3564426151262026660798945)
    ·
      refine ⟨2673319613446519995599209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3564426151262026660798945 2673319613446519995599209)
      ·
        refine ⟨2004989710084889996699407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673319613446519995599209 2004989710084889996699407)
        ·
          refine ⟨3007484565127334995049111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004989710084889996699407 3007484565127334995049111)
          ·
            refine ⟨4511226847691002492573667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007484565127334995049111 4511226847691002492573667)
            ·
              refine ⟨6766840271536503738860501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4511226847691002492573667 6766840271536503738860501)
              ·
                refine ⟨158597818864136806379543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6766840271536503738860501 158597818864136806379543)
                ·
                  rfl

theorem cell20_1042430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1042430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042430 prefixEnd_1042430 := by exact prefixLift 1042430
  have htrace : WordTrace (prefixWord ++ tailWord_1042430) baseStart_1042430 baseEnd_1042430 := by
    simpa [prefixWord, tailWord_1042430, baseEnd_1042430] using wordTrace_append hprefix tailTrace_1042430
  have hstable : (prefixWord ++ tailWord_1042430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042430).length < 2 ^ (prefixWord ++ tailWord_1042430).sum := by decide
  have hdescent : baseEnd_1042430 < baseStart_1042430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042437 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 3]
def baseStart_1042437 : Nat := 118140960795 + 1042437 * 2 ^ 59
def prefixEnd_1042437 : Nat := 4983230072969 + 3 ^ 40 * 1042437 * 2
def baseEnd_1042437 : Nat := 475796651583149505905267

theorem tailTrace_1042437 : CollatzResearch.WordTrace tailWord_1042437 prefixEnd_1042437 475796651583149505905267 := by
  unfold tailWord_1042437
  simp only [CollatzResearch.WordTrace]
  refine ⟨38020800924436257910693565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25347200616290838607129043 38020800924436257910693565)
  ·
    refine ⟨14257800346663596716510087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38020800924436257910693565 14257800346663596716510087)
    ·
      refine ⟨21386700519995395074765131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14257800346663596716510087 21386700519995395074765131)
      ·
        refine ⟨32080050779993092612147697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21386700519995395074765131 32080050779993092612147697)
        ·
          refine ⟨24060038084994819459110773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32080050779993092612147697 24060038084994819459110773)
          ·
            refine ⟨2255628570468264324291635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24060038084994819459110773 2255628570468264324291635)
            ·
              refine ⟨3383442855702396486437453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255628570468264324291635 3383442855702396486437453)
              ·
                refine ⟨1268791070888398682414045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3383442855702396486437453 1268791070888398682414045)
                ·
                  refine ⟨475796651583149505905267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268791070888398682414045 475796651583149505905267)
                  ·
                    rfl

theorem cell20_1042437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_1042437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042437 prefixEnd_1042437 := by exact prefixLift 1042437
  have htrace : WordTrace (prefixWord ++ tailWord_1042437) baseStart_1042437 baseEnd_1042437 := by
    simpa [prefixWord, tailWord_1042437, baseEnd_1042437] using wordTrace_append hprefix tailTrace_1042437
  have hstable : (prefixWord ++ tailWord_1042437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042437).length < 2 ^ (prefixWord ++ tailWord_1042437).sum := by decide
  have hdescent : baseEnd_1042437 < baseStart_1042437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042468 : List Nat := [2, 3, 1, 4, 3, 7]
def baseStart_1042468 : Nat := 118140960795 + 1042468 * 2 ^ 59
def prefixEnd_1042468 : Nat := 4983230072969 + 3 ^ 40 * 1042468 * 2
def baseEnd_1042468 : Nat := 17622622252883376884141

theorem tailTrace_1042468 : CollatzResearch.WordTrace tailWord_1042468 prefixEnd_1042468 17622622252883376884141 := by
  unfold tailWord_1042468
  simp only [CollatzResearch.WordTrace]
  refine ⟨19010965793661975102536029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25347954391549300136714705 19010965793661975102536029)
  ·
    refine ⟨7129112172623240663451011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19010965793661975102536029 7129112172623240663451011)
    ·
      refine ⟨10693668258934860995176517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7129112172623240663451011 10693668258934860995176517)
      ·
        refine ⟨2005062798550286436595597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10693668258934860995176517 2005062798550286436595597)
        ·
          refine ⟨751898549456357413723349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2005062798550286436595597 751898549456357413723349)
          ·
            refine ⟨17622622252883376884141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 751898549456357413723349 17622622252883376884141)
            ·
              rfl

theorem cell20_1042468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 7].length) (baseStart_1042468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042468 prefixEnd_1042468 := by exact prefixLift 1042468
  have htrace : WordTrace (prefixWord ++ tailWord_1042468) baseStart_1042468 baseEnd_1042468 := by
    simpa [prefixWord, tailWord_1042468, baseEnd_1042468] using wordTrace_append hprefix tailTrace_1042468
  have hstable : (prefixWord ++ tailWord_1042468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042468).length < 2 ^ (prefixWord ++ tailWord_1042468).sum := by decide
  have hdescent : baseEnd_1042468 < baseStart_1042468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042471 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 3]
def baseStart_1042471 : Nat := 118140960795 + 1042471 * 2 ^ 59
def prefixEnd_1042471 : Nat := 4983230072969 + 3 ^ 40 * 1042471 * 2
def baseEnd_1042471 : Nat := 475812170109596498771795

theorem tailTrace_1042471 : CollatzResearch.WordTrace tailWord_1042471 prefixEnd_1042471 475812170109596498771795 := by
  unfold tailWord_1042471
  simp only [CollatzResearch.WordTrace]
  refine ⟨38022041006313081717431267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25348027337542054478287511 38022041006313081717431267)
  ·
    refine ⟨57033061509469622576146901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38022041006313081717431267 57033061509469622576146901)
    ·
      refine ⟨1336712379128194279128443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 57033061509469622576146901 1336712379128194279128443)
      ·
        refine ⟨2005068568692291418692665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336712379128194279128443 2005068568692291418692665)
        ·
          refine ⟨1503801426519218564019499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005068568692291418692665 1503801426519218564019499)
          ·
            refine ⟨2255702139778827846029249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503801426519218564019499 2255702139778827846029249)
            ·
              refine ⟨1691776604834120884521937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2255702139778827846029249 1691776604834120884521937)
              ·
                refine ⟨1268832453625590663391453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1691776604834120884521937 1268832453625590663391453)
                ·
                  refine ⟨475812170109596498771795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268832453625590663391453 475812170109596498771795)
                  ·
                    rfl

theorem cell20_1042471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 3].length) (baseStart_1042471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042471 prefixEnd_1042471 := by exact prefixLift 1042471
  have htrace : WordTrace (prefixWord ++ tailWord_1042471) baseStart_1042471 baseEnd_1042471 := by
    simpa [prefixWord, tailWord_1042471, baseEnd_1042471] using wordTrace_append hprefix tailTrace_1042471
  have hstable : (prefixWord ++ tailWord_1042471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042471).length < 2 ^ (prefixWord ++ tailWord_1042471).sum := by decide
  have hdescent : baseEnd_1042471 < baseStart_1042471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042478 : List Nat := [4, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1042478 : Nat := 118140960795 + 1042478 * 2 ^ 59
def prefixEnd_1042478 : Nat := 4983230072969 + 3 ^ 40 * 1042478 * 2
def baseEnd_1042478 : Nat := 475815365100335585538433

theorem tailTrace_1042478 : CollatzResearch.WordTrace tailWord_1042478 prefixEnd_1042478 475815365100335585538433 := by
  unfold tailWord_1042478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4752787039660965239117011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25348197544858481275290725 4752787039660965239117011)
  ·
    refine ⟨7129180559491447858675517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4752787039660965239117011 7129180559491447858675517)
    ·
      refine ⟨2673442709809292947003319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7129180559491447858675517 2673442709809292947003319)
      ·
        refine ⟨4010164064713939420504979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673442709809292947003319 4010164064713939420504979)
        ·
          refine ⟨6015246097070909130757469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4010164064713939420504979 6015246097070909130757469)
          ·
            refine ⟨2255717286401590924034051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6015246097070909130757469 2255717286401590924034051)
            ·
              refine ⟨3383575929602386386051077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255717286401590924034051 3383575929602386386051077)
              ·
                refine ⟨634420486800447447384577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3383575929602386386051077 634420486800447447384577)
                ·
                  refine ⟨475815365100335585538433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634420486800447447384577 475815365100335585538433)
                  ·
                    rfl

theorem cell20_1042478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1042478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042478 prefixEnd_1042478 := by exact prefixLift 1042478
  have htrace : WordTrace (prefixWord ++ tailWord_1042478) baseStart_1042478 baseEnd_1042478 := by
    simpa [prefixWord, tailWord_1042478, baseEnd_1042478] using wordTrace_append hprefix tailTrace_1042478
  have hstable : (prefixWord ++ tailWord_1042478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042478).length < 2 ^ (prefixWord ++ tailWord_1042478).sum := by decide
  have hdescent : baseEnd_1042478 < baseStart_1042478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042530 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1042530 : Nat := 118140960795 + 1042530 * 2 ^ 59
def prefixEnd_1042530 : Nat := 4983230072969 + 3 ^ 40 * 1042530 * 2
def baseEnd_1042530 : Nat := 475839099317254515804887

theorem tailTrace_1042530 : CollatzResearch.WordTrace tailWord_1042530 prefixEnd_1042530 475839099317254515804887 := by
  unfold tailWord_1042530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506048228274833698457261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25349461942066223195886029 9506048228274833698457261)
  ·
    refine ⟨3564768085603062636921473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9506048228274833698457261 3564768085603062636921473)
    ·
      refine ⟨2673576064202296977691105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3564768085603062636921473 2673576064202296977691105)
      ·
        refine ⟨2005182048151722733268329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673576064202296977691105 2005182048151722733268329)
        ·
          refine ⟨1503886536113792049951247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005182048151722733268329 1503886536113792049951247)
          ·
            refine ⟨2255829804170688074926871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1503886536113792049951247 2255829804170688074926871)
            ·
              refine ⟨3383744706256032112390307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255829804170688074926871 3383744706256032112390307)
              ·
                refine ⟨5075617059384048168585461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3383744706256032112390307 5075617059384048168585461)
                ·
                  refine ⟨475839099317254515804887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5075617059384048168585461 475839099317254515804887)
                  ·
                    rfl

theorem cell20_1042530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1042530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042530 prefixEnd_1042530 := by exact prefixLift 1042530
  have htrace : WordTrace (prefixWord ++ tailWord_1042530) baseStart_1042530 baseEnd_1042530 := by
    simpa [prefixWord, tailWord_1042530, baseEnd_1042530] using wordTrace_append hprefix tailTrace_1042530
  have hstable : (prefixWord ++ tailWord_1042530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042530).length < 2 ^ (prefixWord ++ tailWord_1042530).sum := by decide
  have hdescent : baseEnd_1042530 < baseStart_1042530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042561 : List Nat := [1, 2, 4, 2, 3, 2, 2, 4]
def baseStart_1042561 : Nat := 118140960795 + 1042561 * 2 ^ 59
def prefixEnd_1042561 : Nat := 4983230072969 + 3 ^ 40 * 1042561 * 2
def baseEnd_1042561 : Nat := 158617749520652061923809

theorem tailTrace_1042561 : CollatzResearch.WordTrace tailWord_1042561 prefixEnd_1042561 158617749520652061923809 := by
  unfold tailWord_1042561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38025323575987027088207537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25350215717324684725471691 38025323575987027088207537)
  ·
    refine ⟨28518992681990270316155653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38025323575987027088207537 28518992681990270316155653)
    ·
      refine ⟨5347311127873175684279185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28518992681990270316155653 5347311127873175684279185)
      ·
        refine ⟨4010483345904881763209389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5347311127873175684279185 4010483345904881763209389)
        ·
          refine ⟨1503931254714330661203521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4010483345904881763209389 1503931254714330661203521)
          ·
            refine ⟨1127948441035747995902641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503931254714330661203521 1127948441035747995902641)
            ·
              refine ⟨845961330776810996926981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127948441035747995902641 845961330776810996926981)
              ·
                refine ⟨158617749520652061923809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 845961330776810996926981 158617749520652061923809)
                ·
                  rfl

theorem cell20_1042561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 4].length) (baseStart_1042561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042561 prefixEnd_1042561 := by exact prefixLift 1042561
  have htrace : WordTrace (prefixWord ++ tailWord_1042561) baseStart_1042561 baseEnd_1042561 := by
    simpa [prefixWord, tailWord_1042561, baseEnd_1042561] using wordTrace_append hprefix tailTrace_1042561
  have hstable : (prefixWord ++ tailWord_1042561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042561).length < 2 ^ (prefixWord ++ tailWord_1042561).sum := by decide
  have hdescent : baseEnd_1042561 < baseStart_1042561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042565 : List Nat := [1, 3, 1, 1, 5, 2, 1, 6]
def baseStart_1042565 : Nat := 118140960795 + 1042565 * 2 ^ 59
def prefixEnd_1042565 : Nat := 4983230072969 + 3 ^ 40 * 1042565 * 2
def baseEnd_1042565 : Nat := 158618358090316649879359

theorem tailTrace_1042565 : CollatzResearch.WordTrace tailWord_1042565 prefixEnd_1042565 158618358090316649879359 := by
  unfold tailWord_1042565
  simp only [CollatzResearch.WordTrace]
  refine ⟨38025469467972535771353149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25350312978648357180902099 38025469467972535771353149)
  ·
    refine ⟨14259551050489700914257431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38025469467972535771353149 14259551050489700914257431)
    ·
      refine ⟨21389326575734551371386147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14259551050489700914257431 21389326575734551371386147)
      ·
        refine ⟨32083989863601827057079221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21389326575734551371386147 32083989863601827057079221)
        ·
          refine ⟨3007874049712671286601177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32083989863601827057079221 3007874049712671286601177)
          ·
            refine ⟨2255905537284503464950883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3007874049712671286601177 2255905537284503464950883)
            ·
              refine ⟨3383858305926755197426325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255905537284503464950883 3383858305926755197426325)
              ·
                refine ⟨158618358090316649879359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3383858305926755197426325 158618358090316649879359)
                ·
                  rfl

theorem cell20_1042565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_1042565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042565 prefixEnd_1042565 := by exact prefixLift 1042565
  have htrace : WordTrace (prefixWord ++ tailWord_1042565) baseStart_1042565 baseEnd_1042565 := by
    simpa [prefixWord, tailWord_1042565, baseEnd_1042565] using wordTrace_append hprefix tailTrace_1042565
  have hstable : (prefixWord ++ tailWord_1042565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042565).length < 2 ^ (prefixWord ++ tailWord_1042565).sum := by decide
  have hdescent : baseEnd_1042565 < baseStart_1042565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042592 : List Nat := [2, 1, 1, 4, 2, 3, 3, 2, 2]
def baseStart_1042592 : Nat := 118140960795 + 1042592 * 2 ^ 59
def prefixEnd_1042592 : Nat := 4983230072969 + 3 ^ 40 * 1042592 * 2
def baseEnd_1042592 : Nat := 475867397806657855737967

theorem tailTrace_1042592 : CollatzResearch.WordTrace tailWord_1042592 prefixEnd_1042592 475867397806657855737967 := by
  unfold tailWord_1042592
  simp only [CollatzResearch.WordTrace]
  refine ⟨19013227119437359691293015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25350969492583146255057353 19013227119437359691293015)
  ·
    refine ⟨28519840679156039536939523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19013227119437359691293015 28519840679156039536939523)
    ·
      refine ⟨42779761018734059305409285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28519840679156039536939523 42779761018734059305409285)
      ·
        refine ⟨8021205191012636119764241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42779761018734059305409285 8021205191012636119764241)
        ·
          refine ⟨6015903893259477089823181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8021205191012636119764241 6015903893259477089823181)
          ·
            refine ⟨2255963959972303908683693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6015903893259477089823181 2255963959972303908683693)
            ·
              refine ⟨845986484989613965756385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2255963959972303908683693 845986484989613965756385)
              ·
                refine ⟨634489863742210474317289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845986484989613965756385 634489863742210474317289)
                ·
                  refine ⟨475867397806657855737967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634489863742210474317289 475867397806657855737967)
                  ·
                    rfl

theorem cell20_1042592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_1042592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042592 prefixEnd_1042592 := by exact prefixLift 1042592
  have htrace : WordTrace (prefixWord ++ tailWord_1042592) baseStart_1042592 baseEnd_1042592 := by
    simpa [prefixWord, tailWord_1042592, baseEnd_1042592] using wordTrace_append hprefix tailTrace_1042592
  have hstable : (prefixWord ++ tailWord_1042592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042592).length < 2 ^ (prefixWord ++ tailWord_1042592).sum := by decide
  have hdescent : baseEnd_1042592 < baseStart_1042592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042602 : List Nat := [3, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_1042602 : Nat := 118140960795 + 1042602 * 2 ^ 59
def prefixEnd_1042602 : Nat := 4983230072969 + 3 ^ 40 * 1042602 * 2
def baseEnd_1042602 : Nat := 475871962079142265404593

theorem tailTrace_1042602 : CollatzResearch.WordTrace tailWord_1042602 prefixEnd_1042602 475871962079142265404593 := by
  unfold tailWord_1042602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9506704742209622772612515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25351212645892327393633373 9506704742209622772612515)
  ·
    refine ⟨14260057113314434158918773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9506704742209622772612515 14260057113314434158918773)
    ·
      refine ⟨1336880354373228202398635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14260057113314434158918773 1336880354373228202398635)
      ·
        refine ⟨2005320531559842303597953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336880354373228202398635 2005320531559842303597953)
        ·
          refine ⟨1503990398669881727698465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005320531559842303597953 1503990398669881727698465)
          ·
            refine ⟨1127992799002411295773849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1503990398669881727698465 1127992799002411295773849)
            ·
              refine ⟨845994599251808471830387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127992799002411295773849 845994599251808471830387)
              ·
                refine ⟨1268991898877712707745581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845994599251808471830387 1268991898877712707745581)
                ·
                  refine ⟨475871962079142265404593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268991898877712707745581 475871962079142265404593)
                  ·
                    rfl

theorem cell20_1042602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_1042602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042602 prefixEnd_1042602 := by exact prefixLift 1042602
  have htrace : WordTrace (prefixWord ++ tailWord_1042602) baseStart_1042602 baseEnd_1042602 := by
    simpa [prefixWord, tailWord_1042602, baseEnd_1042602] using wordTrace_append hprefix tailTrace_1042602
  have hstable : (prefixWord ++ tailWord_1042602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042602).length < 2 ^ (prefixWord ++ tailWord_1042602).sum := by decide
  have hdescent : baseEnd_1042602 < baseStart_1042602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042617 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 6]
def baseStart_1042617 : Nat := 118140960795 + 1042617 * 2 ^ 59
def prefixEnd_1042617 : Nat := 4983230072969 + 3 ^ 40 * 1042617 * 2
def baseEnd_1042617 : Nat := 475878808487868879904531

theorem tailTrace_1042617 : CollatzResearch.WordTrace tailWord_1042617 prefixEnd_1042617 475878808487868879904531 := by
  unfold tailWord_1042617
  simp only [CollatzResearch.WordTrace]
  refine ⟨38027366063784148652246105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25351577375856099101497403 38027366063784148652246105)
  ·
    refine ⟨28520524547838111489184579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38027366063784148652246105 28520524547838111489184579)
    ·
      refine ⟨42780786821757167233776869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28520524547838111489184579 42780786821757167233776869)
      ·
        refine ⟨8021397529079468856333163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42780786821757167233776869 8021397529079468856333163)
        ·
          refine ⟨12032096293619203284499745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8021397529079468856333163 12032096293619203284499745)
          ·
            refine ⟨9024072220214402463374809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12032096293619203284499745 9024072220214402463374809)
            ·
              refine ⟨6768054165160801847531107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9024072220214402463374809 6768054165160801847531107)
              ·
                refine ⟨10152081247741202771296661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6768054165160801847531107 10152081247741202771296661)
                ·
                  refine ⟨475878808487868879904531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10152081247741202771296661 475878808487868879904531)
                  ·
                    rfl

theorem cell20_1042617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_1042617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042617 prefixEnd_1042617 := by exact prefixLift 1042617
  have htrace : WordTrace (prefixWord ++ tailWord_1042617) baseStart_1042617 baseEnd_1042617 := by
    simpa [prefixWord, tailWord_1042617, baseEnd_1042617] using wordTrace_append hprefix tailTrace_1042617
  have hstable : (prefixWord ++ tailWord_1042617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042617).length < 2 ^ (prefixWord ++ tailWord_1042617).sum := by decide
  have hdescent : baseEnd_1042617 < baseStart_1042617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042655 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_1042655 : Nat := 118140960795 + 1042655 * 2 ^ 59
def prefixEnd_1042655 : Nat := 4983230072969 + 3 ^ 40 * 1042655 * 2
def baseEnd_1042655 : Nat := 475896152723309636637709

theorem tailTrace_1042655 : CollatzResearch.WordTrace tailWord_1042655 prefixEnd_1042655 475896152723309636637709 := by
  unfold tailWord_1042655
  simp only [CollatzResearch.WordTrace]
  refine ⟨38028752037646481142129419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25352501358430987428086279 38028752037646481142129419)
  ·
    refine ⟨57043128056469721713194129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38028752037646481142129419 57043128056469721713194129)
    ·
      refine ⟨42782346042352291284895597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57043128056469721713194129 42782346042352291284895597)
      ·
        refine ⟨16043379765882109231835849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42782346042352291284895597 16043379765882109231835849)
        ·
          refine ⟨12032534824411581923876887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16043379765882109231835849 12032534824411581923876887)
          ·
            refine ⟨18048802236617372885815331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12032534824411581923876887 18048802236617372885815331)
            ·
              refine ⟨27073203354926059328722997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18048802236617372885815331 27073203354926059328722997)
              ·
                refine ⟨2538112814524318062067781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27073203354926059328722997 2538112814524318062067781)
                ·
                  refine ⟨475896152723309636637709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2538112814524318062067781 475896152723309636637709)
                  ·
                    rfl

theorem cell20_1042655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_1042655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042655 prefixEnd_1042655 := by exact prefixLift 1042655
  have htrace : WordTrace (prefixWord ++ tailWord_1042655) baseStart_1042655 baseEnd_1042655 := by
    simpa [prefixWord, tailWord_1042655, baseEnd_1042655] using wordTrace_append hprefix tailTrace_1042655
  have hstable : (prefixWord ++ tailWord_1042655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042655).length < 2 ^ (prefixWord ++ tailWord_1042655).sum := by decide
  have hdescent : baseEnd_1042655 < baseStart_1042655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042689 : List Nat := [1, 2, 4, 1, 1, 2, 4, 3, 2]
def baseStart_1042689 : Nat := 118140960795 + 1042689 * 2 ^ 59
def prefixEnd_1042689 : Nat := 4983230072969 + 3 ^ 40 * 1042689 * 2
def baseEnd_1042689 : Nat := 475911671249756629504237

theorem tailTrace_1042689 : CollatzResearch.WordTrace tailWord_1042689 prefixEnd_1042689 475911671249756629504237 := by
  unfold tailWord_1042689
  simp only [CollatzResearch.WordTrace]
  refine ⟨38029992119523304948867121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25353328079682203299244747 38029992119523304948867121)
  ·
    refine ⟨28522494089642478711650341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38029992119523304948867121 28522494089642478711650341)
    ·
      refine ⟨5347967641807964758434439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28522494089642478711650341 5347967641807964758434439)
      ·
        refine ⟨8021951462711947137651659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5347967641807964758434439 8021951462711947137651659)
        ·
          refine ⟨12032927194067920706477489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8021951462711947137651659 12032927194067920706477489)
          ·
            refine ⟨9024695395550940529858117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12032927194067920706477489 9024695395550940529858117)
            ·
              refine ⟨1692130386665801349348397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9024695395550940529858117 1692130386665801349348397)
              ·
                refine ⟨634548894999675506005649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1692130386665801349348397 634548894999675506005649)
                ·
                  refine ⟨475911671249756629504237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634548894999675506005649 475911671249756629504237)
                  ·
                    rfl

theorem cell20_1042689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 2].length) (baseStart_1042689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042689 prefixEnd_1042689 := by exact prefixLift 1042689
  have htrace : WordTrace (prefixWord ++ tailWord_1042689) baseStart_1042689 baseEnd_1042689 := by
    simpa [prefixWord, tailWord_1042689, baseEnd_1042689] using wordTrace_append hprefix tailTrace_1042689
  have hstable : (prefixWord ++ tailWord_1042689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042689).length < 2 ^ (prefixWord ++ tailWord_1042689).sum := by decide
  have hdescent : baseEnd_1042689 < baseStart_1042689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042700 : List Nat := [2, 2, 1, 2, 2, 2, 9]
def baseStart_1042700 : Nat := 118140960795 + 1042700 * 2 ^ 59
def prefixEnd_1042700 : Nat := 4983230072969 + 3 ^ 40 * 1042700 * 2
def baseEnd_1042700 : Nat := 52879632438832164459725

theorem tailTrace_1042700 : CollatzResearch.WordTrace tailWord_1042700 prefixEnd_1042700 52879632438832164459725 := by
  unfold tailWord_1042700
  simp only [CollatzResearch.WordTrace]
  refine ⟨19015196661241726913758777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25353595548322302551678369 19015196661241726913758777)
  ·
    refine ⟨14261397495931295185319083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19015196661241726913758777 14261397495931295185319083)
    ·
      refine ⟨21392096243896942777978625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14261397495931295185319083 21392096243896942777978625)
      ·
        refine ⟨16044072182922707083483969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21392096243896942777978625 16044072182922707083483969)
        ·
          refine ⟨12033054137192030312612977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16044072182922707083483969 12033054137192030312612977)
          ·
            refine ⟨9024790602894022734459733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12033054137192030312612977 9024790602894022734459733)
            ·
              refine ⟨52879632438832164459725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9024790602894022734459733 52879632438832164459725)
              ·
                rfl

theorem cell20_1042700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 9].length) (baseStart_1042700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042700 prefixEnd_1042700 := by exact prefixLift 1042700
  have htrace : WordTrace (prefixWord ++ tailWord_1042700) baseStart_1042700 baseEnd_1042700 := by
    simpa [prefixWord, tailWord_1042700, baseEnd_1042700] using wordTrace_append hprefix tailTrace_1042700
  have hstable : (prefixWord ++ tailWord_1042700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042700).length < 2 ^ (prefixWord ++ tailWord_1042700).sum := by decide
  have hdescent : baseEnd_1042700 < baseStart_1042700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042720 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_1042720 : Nat := 118140960795 + 1042720 * 2 ^ 59
def prefixEnd_1042720 : Nat := 4983230072969 + 3 ^ 40 * 1042720 * 2
def baseEnd_1042720 : Nat := 475925820494458299470777

theorem tailTrace_1042720 : CollatzResearch.WordTrace tailWord_1042720 prefixEnd_1042720 475925820494458299470777 := by
  unfold tailWord_1042720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19015561391205498621622807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25354081854940664828830409 19015561391205498621622807)
  ·
    refine ⟨28523342086808247932434211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19015561391205498621622807 28523342086808247932434211)
    ·
      refine ⟨42785013130212371898651317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28523342086808247932434211 42785013130212371898651317)
      ·
        refine ⟨4011094980957409865498561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42785013130212371898651317 4011094980957409865498561)
        ·
          refine ⟨3008321235718057399123921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4011094980957409865498561 3008321235718057399123921)
          ·
            refine ⟨2256240926788543049342941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008321235718057399123921 2256240926788543049342941)
            ·
              refine ⟨846090347545703643503603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2256240926788543049342941 846090347545703643503603)
              ·
                refine ⟨1269135521318555465255405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846090347545703643503603 1269135521318555465255405)
                ·
                  refine ⟨475925820494458299470777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269135521318555465255405 475925820494458299470777)
                  ·
                    rfl

theorem cell20_1042720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_1042720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042720 prefixEnd_1042720 := by exact prefixLift 1042720
  have htrace : WordTrace (prefixWord ++ tailWord_1042720) baseStart_1042720 baseEnd_1042720 := by
    simpa [prefixWord, tailWord_1042720, baseEnd_1042720] using wordTrace_append hprefix tailTrace_1042720
  have hstable : (prefixWord ++ tailWord_1042720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042720).length < 2 ^ (prefixWord ++ tailWord_1042720).sum := by decide
  have hdescent : baseEnd_1042720 < baseStart_1042720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042730 : List Nat := [3, 1, 4, 2, 3, 1, 2, 4]
def baseStart_1042730 : Nat := 118140960795 + 1042730 * 2 ^ 59
def prefixEnd_1042730 : Nat := 4983230072969 + 3 ^ 40 * 1042730 * 2
def baseEnd_1042730 : Nat := 158643461588980903045801

theorem tailTrace_1042730 : CollatzResearch.WordTrace tailWord_1042730 prefixEnd_1042730 158643461588980903045801 := by
  unfold tailWord_1042730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9507871878093692237777411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25354325008249845967406429 9507871878093692237777411)
  ·
    refine ⟨14261807817140538356666117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9507871878093692237777411 14261807817140538356666117)
    ·
      refine ⟨2674088965713850941874897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14261807817140538356666117 2674088965713850941874897)
      ·
        refine ⟨2005566724285388206406173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2674088965713850941874897 2005566724285388206406173)
        ·
          refine ⟨752087521607020577402315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2005566724285388206406173 752087521607020577402315)
          ·
            refine ⟨1128131282410530866103473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752087521607020577402315 1128131282410530866103473)
            ·
              refine ⟨846098461807898149577605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128131282410530866103473 846098461807898149577605)
              ·
                refine ⟨158643461588980903045801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846098461807898149577605 158643461588980903045801)
                ·
                  rfl

theorem cell20_1042730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_1042730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042730 prefixEnd_1042730 := by exact prefixLift 1042730
  have htrace : WordTrace (prefixWord ++ tailWord_1042730) baseStart_1042730 baseEnd_1042730 := by
    simpa [prefixWord, tailWord_1042730, baseEnd_1042730] using wordTrace_append hprefix tailTrace_1042730
  have hstable : (prefixWord ++ tailWord_1042730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042730).length < 2 ^ (prefixWord ++ tailWord_1042730).sum := by decide
  have hdescent : baseEnd_1042730 < baseStart_1042730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042817 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 3]
def baseStart_1042817 : Nat := 118140960795 + 1042817 * 2 ^ 59
def prefixEnd_1042817 : Nat := 4983230072969 + 3 ^ 40 * 1042817 * 2
def baseEnd_1042817 : Nat := 475970093937557073237047

theorem tailTrace_1042817 : CollatzResearch.WordTrace tailWord_1042817 prefixEnd_1042817 475970093937557073237047 := by
  unfold tailWord_1042817
  simp only [CollatzResearch.WordTrace]
  refine ⟨38034660663059582809526705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25356440442039721873017803 38034660663059582809526705)
  ·
    refine ⟨28525995497294687107145029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38034660663059582809526705 28525995497294687107145029)
    ·
      refine ⟨5348624155742753832589693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28525995497294687107145029 5348624155742753832589693)
      ·
        refine ⟨2005734058403532687221135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5348624155742753832589693 2005734058403532687221135)
        ·
          refine ⟨3008601087605299030831703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005734058403532687221135 3008601087605299030831703)
          ·
            refine ⟨4512901631407948546247555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008601087605299030831703 4512901631407948546247555)
            ·
              refine ⟨6769352447111922819371333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512901631407948546247555 6769352447111922819371333)
              ·
                refine ⟨1269253583833485528632125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6769352447111922819371333 1269253583833485528632125)
                ·
                  refine ⟨475970093937557073237047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269253583833485528632125 475970093937557073237047)
                  ·
                    rfl

theorem cell20_1042817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_1042817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042817 prefixEnd_1042817 := by exact prefixLift 1042817
  have htrace : WordTrace (prefixWord ++ tailWord_1042817) baseStart_1042817 baseEnd_1042817 := by
    simpa [prefixWord, tailWord_1042817, baseEnd_1042817] using wordTrace_append hprefix tailTrace_1042817
  have hstable : (prefixWord ++ tailWord_1042817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042817).length < 2 ^ (prefixWord ++ tailWord_1042817).sum := by decide
  have hdescent : baseEnd_1042817 < baseStart_1042817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042852 : List Nat := [2, 3, 1, 2, 1, 1, 2, 8]
def baseStart_1042852 : Nat := 118140960795 + 1042852 * 2 ^ 59
def prefixEnd_1042852 : Nat := 4983230072969 + 3 ^ 40 * 1042852 * 2
def baseEnd_1042852 : Nat := 158662022963750835690079

theorem tailTrace_1042852 : CollatzResearch.WordTrace tailWord_1042852 prefixEnd_1042852 158662022963750835690079 := by
  unfold tailWord_1042852
  simp only [CollatzResearch.WordTrace]
  refine ⟨19017968608966391893525405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25357291478621855858033873 19017968608966391893525405)
  ·
    refine ⟨7131738228362396960072027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19017968608966391893525405 7131738228362396960072027)
    ·
      refine ⟨10697607342543595440108041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7131738228362396960072027 10697607342543595440108041)
      ·
        refine ⟨8023205506907696580081031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10697607342543595440108041 8023205506907696580081031)
        ·
          refine ⟨12034808260361544870121547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023205506907696580081031 12034808260361544870121547)
          ·
            refine ⟨18052212390542317305182321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12034808260361544870121547 18052212390542317305182321)
            ·
              refine ⟨13539159292906737978886741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18052212390542317305182321 13539159292906737978886741)
              ·
                refine ⟨158662022963750835690079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13539159292906737978886741 158662022963750835690079)
                ·
                  rfl

theorem cell20_1042852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_1042852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042852 prefixEnd_1042852 := by exact prefixLift 1042852
  have htrace : WordTrace (prefixWord ++ tailWord_1042852) baseStart_1042852 baseEnd_1042852 := by
    simpa [prefixWord, tailWord_1042852, baseEnd_1042852] using wordTrace_append hprefix tailTrace_1042852
  have hstable : (prefixWord ++ tailWord_1042852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042852).length < 2 ^ (prefixWord ++ tailWord_1042852).sum := by decide
  have hdescent : baseEnd_1042852 < baseStart_1042852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042868 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1042868 : Nat := 118140960795 + 1042868 * 2 ^ 59
def prefixEnd_1042868 : Nat := 4983230072969 + 3 ^ 40 * 1042868 * 2
def baseEnd_1042868 : Nat := 475993371727227562536839

theorem tailTrace_1042868 : CollatzResearch.WordTrace tailWord_1042868 prefixEnd_1042868 475993371727227562536839 := by
  unfold tailWord_1042868
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018260392937409259816629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25357680523916545679755505 19018260392937409259816629)
  ·
    refine ⟨1782961911837882118107809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19018260392937409259816629 1782961911837882118107809)
    ·
      refine ⟨1337221433878411588580857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1782961911837882118107809 1337221433878411588580857)
      ·
        refine ⟨1002916075408808691435643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337221433878411588580857 1002916075408808691435643)
        ·
          refine ⟨1504374113113213037153465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002916075408808691435643 1504374113113213037153465)
          ·
            refine ⟨1128280584834909777865099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1504374113113213037153465 1128280584834909777865099)
            ·
              refine ⟨1692420877252364666797649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128280584834909777865099 1692420877252364666797649)
              ·
                refine ⟨1269315657939273500098237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1692420877252364666797649 1269315657939273500098237)
                ·
                  refine ⟨475993371727227562536839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269315657939273500098237 475993371727227562536839)
                  ·
                    rfl

theorem cell20_1042868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1042868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042868 prefixEnd_1042868 := by exact prefixLift 1042868
  have htrace : WordTrace (prefixWord ++ tailWord_1042868) baseStart_1042868 baseEnd_1042868 := by
    simpa [prefixWord, tailWord_1042868, baseEnd_1042868] using wordTrace_append hprefix tailTrace_1042868
  have hstable : (prefixWord ++ tailWord_1042868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042868).length < 2 ^ (prefixWord ++ tailWord_1042868).sum := by decide
  have hdescent : baseEnd_1042868 < baseStart_1042868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042869 : List Nat := [1, 3, 3, 2, 3, 1, 7]
def baseStart_1042869 : Nat := 118140960795 + 1042869 * 2 ^ 59
def prefixEnd_1042869 : Nat := 4983230072969 + 3 ^ 40 * 1042869 * 2
def baseEnd_1042869 : Nat := 52888203128275111500389

theorem tailTrace_1042869 : CollatzResearch.WordTrace tailWord_1042869 prefixEnd_1042869 52888203128275111500389 := by
  unfold tailWord_1042869
  simp only [CollatzResearch.WordTrace]
  refine ⟨38036557258871195690419661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25357704839247463793613107 38036557258871195690419661)
  ·
    refine ⟨14263708972076698383907373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38036557258871195690419661 14263708972076698383907373)
    ·
      refine ⟨5348890864528761893965265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14263708972076698383907373 5348890864528761893965265)
      ·
        refine ⟨4011668148396571420473949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5348890864528761893965265 4011668148396571420473949)
        ·
          refine ⟨1504375555648714282677731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4011668148396571420473949 1504375555648714282677731)
          ·
            refine ⟨2256563333473071424016597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504375555648714282677731 2256563333473071424016597)
            ·
              refine ⟨52888203128275111500389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2256563333473071424016597 52888203128275111500389)
              ·
                rfl

theorem cell20_1042869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 7].length) (baseStart_1042869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042869 prefixEnd_1042869 := by exact prefixLift 1042869
  have htrace : WordTrace (prefixWord ++ tailWord_1042869) baseStart_1042869 baseEnd_1042869 := by
    simpa [prefixWord, tailWord_1042869, baseEnd_1042869] using wordTrace_append hprefix tailTrace_1042869
  have hstable : (prefixWord ++ tailWord_1042869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042869).length < 2 ^ (prefixWord ++ tailWord_1042869).sum := by decide
  have hdescent : baseEnd_1042869 < baseStart_1042869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042890 : List Nat := [3, 1, 2, 1, 2, 2, 2, 7]
def baseStart_1042890 : Nat := 118140960795 + 1042890 * 2 ^ 59
def prefixEnd_1042890 : Nat := 4983230072969 + 3 ^ 40 * 1042890 * 2
def baseEnd_1042890 : Nat := 158667804375564421267805

theorem tailTrace_1042890 : CollatzResearch.WordTrace tailWord_1042890 prefixEnd_1042890 158667804375564421267805 := by
  unfold tailWord_1042890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9509330797948779069233531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25358215461196744184622749 9509330797948779069233531)
  ·
    refine ⟨14263996196923168603850297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9509330797948779069233531 14263996196923168603850297)
    ·
      refine ⟨10697997147692376452887723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14263996196923168603850297 10697997147692376452887723)
      ·
        refine ⟨16046995721538564679331585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10697997147692376452887723 16046995721538564679331585)
        ·
          refine ⟨12035246791153923509498689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16046995721538564679331585 12035246791153923509498689)
          ·
            refine ⟨9026435093365442632124017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12035246791153923509498689 9026435093365442632124017)
            ·
              refine ⟨6769826320024081974093013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9026435093365442632124017 6769826320024081974093013)
              ·
                refine ⟨158667804375564421267805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6769826320024081974093013 158667804375564421267805)
                ·
                  rfl

theorem cell20_1042890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_1042890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042890 prefixEnd_1042890 := by exact prefixLift 1042890
  have htrace : WordTrace (prefixWord ++ tailWord_1042890) baseStart_1042890 baseEnd_1042890 := by
    simpa [prefixWord, tailWord_1042890, baseEnd_1042890] using wordTrace_append hprefix tailTrace_1042890
  have hstable : (prefixWord ++ tailWord_1042890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042890).length < 2 ^ (prefixWord ++ tailWord_1042890).sum := by decide
  have hdescent : baseEnd_1042890 < baseStart_1042890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042900 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1042900 : Nat := 118140960795 + 1042900 * 2 ^ 59
def prefixEnd_1042900 : Nat := 4983230072969 + 3 ^ 40 * 1042900 * 2
def baseEnd_1042900 : Nat := 476007977399177673470041

theorem tailTrace_1042900 : CollatzResearch.WordTrace tailWord_1042900 prefixEnd_1042900 476007977399177673470041 := by
  unfold tailWord_1042900
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018843960879443992399077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25358458614505925323198769 19018843960879443992399077)
  ·
    refine ⟨3566033242664895748574827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19018843960879443992399077 3566033242664895748574827)
    ·
      refine ⟨5349049863997343622862241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566033242664895748574827 5349049863997343622862241)
      ·
        refine ⟨4011787397998007717146681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5349049863997343622862241 4011787397998007717146681)
        ·
          refine ⟨3008840548498505787860011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4011787397998007717146681 3008840548498505787860011)
          ·
            refine ⟨4513260822747758681790017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008840548498505787860011 4513260822747758681790017)
            ·
              refine ⟨3384945617060819011342513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4513260822747758681790017 3384945617060819011342513)
              ·
                refine ⟨2538709212795614258506885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3384945617060819011342513 2538709212795614258506885)
                ·
                  refine ⟨476007977399177673470041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2538709212795614258506885 476007977399177673470041)
                  ·
                    rfl

theorem cell20_1042900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1042900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042900 prefixEnd_1042900 := by exact prefixLift 1042900
  have htrace : WordTrace (prefixWord ++ tailWord_1042900) baseStart_1042900 baseEnd_1042900 := by
    simpa [prefixWord, tailWord_1042900, baseEnd_1042900] using wordTrace_append hprefix tailTrace_1042900
  have hstable : (prefixWord ++ tailWord_1042900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042900).length < 2 ^ (prefixWord ++ tailWord_1042900).sum := by decide
  have hdescent : baseEnd_1042900 < baseStart_1042900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042934 : List Nat := [5, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_1042934 : Nat := 118140960795 + 1042934 * 2 ^ 59
def prefixEnd_1042934 : Nat := 4983230072969 + 3 ^ 40 * 1042934 * 2
def baseEnd_1042934 : Nat := 476023495925624666336569

theorem tailTrace_1042934 : CollatzResearch.WordTrace tailWord_1042934 prefixEnd_1042934 476023495925624666336569 := by
  unfold tailWord_1042934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377433000227231986970991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25359285335757141194357237 2377433000227231986970991)
  ·
    refine ⟨3566149500340847980456487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2377433000227231986970991 3566149500340847980456487)
    ·
      refine ⟨5349224250511271970684731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566149500340847980456487 5349224250511271970684731)
      ·
        refine ⟨8023836375766907956027097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349224250511271970684731 8023836375766907956027097)
        ·
          refine ⟨6017877281825180967020323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8023836375766907956027097 6017877281825180967020323)
          ·
            refine ⟨9026815922737771450530485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6017877281825180967020323 9026815922737771450530485)
            ·
              refine ⟨846263992756666073487233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9026815922737771450530485 846263992756666073487233)
              ·
                refine ⟨634697994567499555115425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846263992756666073487233 634697994567499555115425)
                ·
                  refine ⟨476023495925624666336569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634697994567499555115425 476023495925624666336569)
                  ·
                    rfl

theorem cell20_1042934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_1042934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042934 prefixEnd_1042934 := by exact prefixLift 1042934
  have htrace : WordTrace (prefixWord ++ tailWord_1042934) baseStart_1042934 baseEnd_1042934 := by
    simpa [prefixWord, tailWord_1042934, baseEnd_1042934] using wordTrace_append hprefix tailTrace_1042934
  have hstable : (prefixWord ++ tailWord_1042934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042934).length < 2 ^ (prefixWord ++ tailWord_1042934).sum := by decide
  have hdescent : baseEnd_1042934 < baseStart_1042934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042945 : List Nat := [1, 2, 4, 1, 3, 2, 2, 5]
def baseStart_1042945 : Nat := 118140960795 + 1042945 * 2 ^ 59
def prefixEnd_1042945 : Nat := 4983230072969 + 3 ^ 40 * 1042945 * 2
def baseEnd_1042945 : Nat := 158676172208452505656619

theorem tailTrace_1042945 : CollatzResearch.WordTrace tailWord_1042945 prefixEnd_1042945 158676172208452505656619 := by
  unfold tailWord_1042945
  simp only [CollatzResearch.WordTrace]
  refine ⟨38039329206595860670186289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25359552804397240446790859 38039329206595860670186289)
  ·
    refine ⟨28529496904946895502639717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38039329206595860670186289 28529496904946895502639717)
    ·
      refine ⟨5349280669677542906744947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28529496904946895502639717 5349280669677542906744947)
      ·
        refine ⟨8023921004516314360117421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349280669677542906744947 8023921004516314360117421)
        ·
          refine ⟨3008970376693617885044033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8023921004516314360117421 3008970376693617885044033)
          ·
            refine ⟨2256727782520213413783025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3008970376693617885044033 2256727782520213413783025)
            ·
              refine ⟨1692545836890160060337269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2256727782520213413783025 1692545836890160060337269)
              ·
                refine ⟨158676172208452505656619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1692545836890160060337269 158676172208452505656619)
                ·
                  rfl

theorem cell20_1042945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_1042945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042945 prefixEnd_1042945 := by exact prefixLift 1042945
  have htrace : WordTrace (prefixWord ++ tailWord_1042945) baseStart_1042945 baseEnd_1042945 := by
    simpa [prefixWord, tailWord_1042945, baseEnd_1042945] using wordTrace_append hprefix tailTrace_1042945
  have hstable : (prefixWord ++ tailWord_1042945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042945).length < 2 ^ (prefixWord ++ tailWord_1042945).sum := by decide
  have hdescent : baseEnd_1042945 < baseStart_1042945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042948 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_1042948 : Nat := 118140960795 + 1042948 * 2 ^ 59
def prefixEnd_1042948 : Nat := 4983230072969 + 3 ^ 40 * 1042948 * 2
def baseEnd_1042948 : Nat := 476029885907102839869845

theorem tailTrace_1042948 : CollatzResearch.WordTrace tailWord_1042948 prefixEnd_1042948 476029885907102839869845 := by
  unfold tailWord_1042948
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019719312792496091272749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25359625750389994788363665 19019719312792496091272749)
  ·
    refine ⟨7132394742297186034227281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19019719312792496091272749 7132394742297186034227281)
    ·
      refine ⟨5349296056722889525670461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7132394742297186034227281 5349296056722889525670461)
      ·
        refine ⟨2005986021271083572126423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5349296056722889525670461 2005986021271083572126423)
        ·
          refine ⟨3008979031906625358189635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005986021271083572126423 3008979031906625358189635)
          ·
            refine ⟨4513468547859938037284453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008979031906625358189635 4513468547859938037284453)
            ·
              refine ⟨846275352723738381990835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4513468547859938037284453 846275352723738381990835)
              ·
                refine ⟨1269413029085607572986253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846275352723738381990835 1269413029085607572986253)
                ·
                  refine ⟨476029885907102839869845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269413029085607572986253 476029885907102839869845)
                  ·
                    rfl

theorem cell20_1042948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_1042948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042948 prefixEnd_1042948 := by exact prefixLift 1042948
  have htrace : WordTrace (prefixWord ++ tailWord_1042948) baseStart_1042948 baseEnd_1042948 := by
    simpa [prefixWord, tailWord_1042948, baseEnd_1042948] using wordTrace_append hprefix tailTrace_1042948
  have hstable : (prefixWord ++ tailWord_1042948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042948).length < 2 ^ (prefixWord ++ tailWord_1042948).sum := by decide
  have hdescent : baseEnd_1042948 < baseStart_1042948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042983 : List Nat := [1, 1, 7, 2, 9]
def baseStart_1042983 : Nat := 118140960795 + 1042983 * 2 ^ 59
def prefixEnd_1042983 : Nat := 4983230072969 + 3 ^ 40 * 1042983 * 2
def baseEnd_1042983 : Nat := 5877109393343188564235

theorem tailTrace_1042983 : CollatzResearch.WordTrace tailWord_1042983 prefixEnd_1042983 5877109393343188564235 := by
  unfold tailWord_1042983
  simp only [CollatzResearch.WordTrace]
  refine ⟨38040715180458193160069603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25360476786972128773379735 38040715180458193160069603)
  ·
    refine ⟨57061072770687289740104405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38040715180458193160069603 57061072770687289740104405)
    ·
      refine ⟨1337368893062983353283697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 57061072770687289740104405 1337368893062983353283697)
      ·
        refine ⟨1003026669797237514962773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337368893062983353283697 1003026669797237514962773)
        ·
          refine ⟨5877109393343188564235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 1003026669797237514962773 5877109393343188564235)
          ·
            rfl

theorem cell20_1042983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 9].length) (baseStart_1042983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042983 prefixEnd_1042983 := by exact prefixLift 1042983
  have htrace : WordTrace (prefixWord ++ tailWord_1042983) baseStart_1042983 baseEnd_1042983 := by
    simpa [prefixWord, tailWord_1042983, baseEnd_1042983] using wordTrace_append hprefix tailTrace_1042983
  have hstable : (prefixWord ++ tailWord_1042983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042983).length < 2 ^ (prefixWord ++ tailWord_1042983).sum := by decide
  have hdescent : baseEnd_1042983 < baseStart_1042983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042993 : List Nat := [1, 2, 2, 3, 1, 1, 6, 2, 2]
def baseStart_1042993 : Nat := 118140960795 + 1042993 * 2 ^ 59
def prefixEnd_1042993 : Nat := 4983230072969 + 3 ^ 40 * 1042993 * 2
def baseEnd_1042993 : Nat := 476050425133282683369661

theorem tailTrace_1042993 : CollatzResearch.WordTrace tailWord_1042993 prefixEnd_1042993 476050425133282683369661 := by
  unfold tailWord_1042993
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041079910421964867933633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25360719940281309911955755 38041079910421964867933633)
  ·
    refine ⟨28530809932816473650950225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38041079910421964867933633 28530809932816473650950225)
    ·
      refine ⟨21398107449612355238212669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28530809932816473650950225 21398107449612355238212669)
      ·
        refine ⟨8024290293604633214329751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21398107449612355238212669 8024290293604633214329751)
        ·
          refine ⟨12036435440406949821494627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8024290293604633214329751 12036435440406949821494627)
          ·
            refine ⟨18054653160610424732241941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12036435440406949821494627 18054653160610424732241941)
            ·
              refine ⟨846311866903613659323841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18054653160610424732241941 846311866903613659323841)
              ·
                refine ⟨634733900177710244492881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846311866903613659323841 634733900177710244492881)
                ·
                  refine ⟨476050425133282683369661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634733900177710244492881 476050425133282683369661)
                  ·
                    rfl

theorem cell20_1042993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 2].length) (baseStart_1042993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042993 prefixEnd_1042993 := by exact prefixLift 1042993
  have htrace : WordTrace (prefixWord ++ tailWord_1042993) baseStart_1042993 baseEnd_1042993 := by
    simpa [prefixWord, tailWord_1042993, baseEnd_1042993] using wordTrace_append hprefix tailTrace_1042993
  have hstable : (prefixWord ++ tailWord_1042993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042993).length < 2 ^ (prefixWord ++ tailWord_1042993).sum := by decide
  have hdescent : baseEnd_1042993 < baseStart_1042993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042996 : List Nat := [2, 5, 1, 3, 2, 1, 1, 5]
def baseStart_1042996 : Nat := 118140960795 + 1042996 * 2 ^ 59
def prefixEnd_1042996 : Nat := 4983230072969 + 3 ^ 40 * 1042996 * 2
def baseEnd_1042996 : Nat := 158683931471676002089883

theorem tailTrace_1042996 : CollatzResearch.WordTrace tailWord_1042996 prefixEnd_1042996 158683931471676002089883 := by
  unfold tailWord_1042996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19020594664705548190146421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25360792886274064253528561 19020594664705548190146421)
  ·
    refine ⟨1783180749816145142826227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19020594664705548190146421 1783180749816145142826227)
    ·
      refine ⟨2674771124724217714239341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783180749816145142826227 2674771124724217714239341)
      ·
        refine ⟨1003039171771581642839753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2674771124724217714239341 1003039171771581642839753)
        ·
          refine ⟨752279378828686232129815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003039171771581642839753 752279378828686232129815)
          ·
            refine ⟨1128419068243029348194723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752279378828686232129815 1128419068243029348194723)
            ·
              refine ⟨1692628602364544022292085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128419068243029348194723 1692628602364544022292085)
              ·
                refine ⟨158683931471676002089883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1692628602364544022292085 158683931471676002089883)
                ·
                  rfl

theorem cell20_1042996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_1042996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042996 prefixEnd_1042996 := by exact prefixLift 1042996
  have htrace : WordTrace (prefixWord ++ tailWord_1042996) baseStart_1042996 baseEnd_1042996 := by
    simpa [prefixWord, tailWord_1042996, baseEnd_1042996] using wordTrace_append hprefix tailTrace_1042996
  have hstable : (prefixWord ++ tailWord_1042996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042996).length < 2 ^ (prefixWord ++ tailWord_1042996).sum := by decide
  have hdescent : baseEnd_1042996 < baseStart_1042996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1042997 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1042997 : Nat := 118140960795 + 1042997 * 2 ^ 59
def prefixEnd_1042997 : Nat := 4983230072969 + 3 ^ 40 * 1042997 * 2
def baseEnd_1042997 : Nat := 476052250842276447236311

theorem tailTrace_1042997 : CollatzResearch.WordTrace tailWord_1042997 prefixEnd_1042997 476052250842276447236311 := by
  unfold tailWord_1042997
  simp only [CollatzResearch.WordTrace]
  refine ⟨38041225802407473551079245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25360817201604982367386163 38041225802407473551079245)
  ·
    refine ⟨14265459675902802581654717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38041225802407473551079245 14265459675902802581654717)
    ·
      refine ⟨5349547378463550968120519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14265459675902802581654717 5349547378463550968120519)
      ·
        refine ⟨8024321067695326452180779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349547378463550968120519 8024321067695326452180779)
        ·
          refine ⟨12036481601542989678271169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8024321067695326452180779 12036481601542989678271169)
          ·
            refine ⟨9027361201157242258703377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12036481601542989678271169 9027361201157242258703377)
            ·
              refine ⟨6770520900867931694027533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9027361201157242258703377 6770520900867931694027533)
              ·
                refine ⟨2538945337825474385260325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6770520900867931694027533 2538945337825474385260325)
                ·
                  refine ⟨476052250842276447236311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2538945337825474385260325 476052250842276447236311)
                  ·
                    rfl

theorem cell20_1042997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1042997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1042997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1042997 prefixEnd_1042997 := by exact prefixLift 1042997
  have htrace : WordTrace (prefixWord ++ tailWord_1042997) baseStart_1042997 baseEnd_1042997 := by
    simpa [prefixWord, tailWord_1042997, baseEnd_1042997] using wordTrace_append hprefix tailTrace_1042997
  have hstable : (prefixWord ++ tailWord_1042997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1042997).length < 2 ^ (prefixWord ++ tailWord_1042997).sum := by decide
  have hdescent : baseEnd_1042997 < baseStart_1042997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1042997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043052 : List Nat := [2, 2, 1, 1, 3, 1, 4, 4, 2]
def baseStart_1043052 : Nat := 118140960795 + 1043052 * 2 ^ 59
def prefixEnd_1043052 : Nat := 4983230072969 + 3 ^ 40 * 1043052 * 2
def baseEnd_1043052 : Nat := 476077354340940700402753

theorem tailTrace_1043052 : CollatzResearch.WordTrace tailWord_1043052 prefixEnd_1043052 476077354340940700402753 := by
  unfold tailWord_1043052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19021615908604108972165705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25362154544805478629554273 19021615908604108972165705)
  ·
    refine ⟨14266211931453081729124279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19021615908604108972165705 14266211931453081729124279)
    ·
      refine ⟨21399317897179622593686419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14266211931453081729124279 21399317897179622593686419)
      ·
        refine ⟨32098976845769433890529629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21399317897179622593686419 32098976845769433890529629)
        ·
          refine ⟨12037116317163537708948611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32098976845769433890529629 12037116317163537708948611)
          ·
            refine ⟨18055674475745306563422917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12037116317163537708948611 18055674475745306563422917)
            ·
              refine ⟨3385438964202244980641797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18055674475745306563422917 3385438964202244980641797)
              ·
                refine ⟨634769805787920933870337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3385438964202244980641797 634769805787920933870337)
                ·
                  refine ⟨476077354340940700402753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634769805787920933870337 476077354340940700402753)
                  ·
                    rfl

theorem cell20_1043052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_1043052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043052 prefixEnd_1043052 := by exact prefixLift 1043052
  have htrace : WordTrace (prefixWord ++ tailWord_1043052) baseStart_1043052 baseEnd_1043052 := by
    simpa [prefixWord, tailWord_1043052, baseEnd_1043052] using wordTrace_append hprefix tailTrace_1043052
  have hstable : (prefixWord ++ tailWord_1043052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043052).length < 2 ^ (prefixWord ++ tailWord_1043052).sum := by decide
  have hdescent : baseEnd_1043052 < baseStart_1043052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043073 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_1043073 : Nat := 118140960795 + 1043073 * 2 ^ 59
def prefixEnd_1043073 : Nat := 4983230072969 + 3 ^ 40 * 1043073 * 2
def baseEnd_1043073 : Nat := 476086939313157960702667

theorem tailTrace_1043073 : CollatzResearch.WordTrace tailWord_1043073 prefixEnd_1043073 476086939313157960702667 := by
  unfold tailWord_1043073
  simp only [CollatzResearch.WordTrace]
  refine ⟨38043997750132138530845873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25362665166754759020563915 38043997750132138530845873)
  ·
    refine ⟨28532998312599103898134405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38043997750132138530845873 28532998312599103898134405)
    ·
      refine ⟨5349937183612331980900201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28532998312599103898134405 5349937183612331980900201)
      ·
        refine ⟨4012452887709248985675151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5349937183612331980900201 4012452887709248985675151)
        ·
          refine ⟨6018679331563873478512727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012452887709248985675151 6018679331563873478512727)
          ·
            refine ⟨9028018997345810217769091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6018679331563873478512727 9028018997345810217769091)
            ·
              refine ⟨13542028496018715326653637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9028018997345810217769091 13542028496018715326653637)
              ·
                refine ⟨2539130343003509123747557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13542028496018715326653637 2539130343003509123747557)
                ·
                  refine ⟨476086939313157960702667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539130343003509123747557 476086939313157960702667)
                  ·
                    rfl

theorem cell20_1043073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_1043073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043073 prefixEnd_1043073 := by exact prefixLift 1043073
  have htrace : WordTrace (prefixWord ++ tailWord_1043073) baseStart_1043073 baseEnd_1043073 := by
    simpa [prefixWord, tailWord_1043073, baseEnd_1043073] using wordTrace_append hprefix tailTrace_1043073
  have hstable : (prefixWord ++ tailWord_1043073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043073).length < 2 ^ (prefixWord ++ tailWord_1043073).sum := by decide
  have hdescent : baseEnd_1043073 < baseStart_1043073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043076 : List Nat := [2, 3, 2, 1, 3, 3, 2, 4]
def baseStart_1043076 : Nat := 118140960795 + 1043076 * 2 ^ 59
def prefixEnd_1043076 : Nat := 4983230072969 + 3 ^ 40 * 1043076 * 2
def baseEnd_1043076 : Nat := 158696102864967761200885

theorem tailTrace_1043076 : CollatzResearch.WordTrace tailWord_1043076 prefixEnd_1043076 158696102864967761200885 := by
  unfold tailWord_1043076
  simp only [CollatzResearch.WordTrace]
  refine ⟨19022053584560635021602541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25362738112747513362136721 19022053584560635021602541)
  ·
    refine ⟨7133270094210238133100953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19022053584560635021602541 7133270094210238133100953)
    ·
      refine ⟨5349952570657678599825715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7133270094210238133100953 5349952570657678599825715)
      ·
        refine ⟨8024928855986517899738573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5349952570657678599825715 8024928855986517899738573)
        ·
          refine ⟨3009348320994944212401965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8024928855986517899738573 3009348320994944212401965)
          ·
            refine ⟨1128505620373104079650737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3009348320994944212401965 1128505620373104079650737)
            ·
              refine ⟨846379215279828059738053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128505620373104079650737 846379215279828059738053)
              ·
                refine ⟨158696102864967761200885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846379215279828059738053 158696102864967761200885)
                ·
                  rfl

theorem cell20_1043076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_1043076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043076 prefixEnd_1043076 := by exact prefixLift 1043076
  have htrace : WordTrace (prefixWord ++ tailWord_1043076) baseStart_1043076 baseEnd_1043076 := by
    simpa [prefixWord, tailWord_1043076, baseEnd_1043076] using wordTrace_append hprefix tailTrace_1043076
  have hstable : (prefixWord ++ tailWord_1043076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043076).length < 2 ^ (prefixWord ++ tailWord_1043076).sum := by decide
  have hdescent : baseEnd_1043076 < baseStart_1043076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043156 : List Nat := [2, 4, 1, 3, 10]
def baseStart_1043156 : Nat := 118140960795 + 1043156 * 2 ^ 59
def prefixEnd_1043156 : Nat := 4983230072969 + 3 ^ 40 * 1043156 * 2
def baseEnd_1043156 : Nat := 5878084231787389641181

theorem tailTrace_1043156 : CollatzResearch.WordTrace tailWord_1043156 prefixEnd_1043156 5878084231787389641181 := by
  unfold tailWord_1043156
  simp only [CollatzResearch.WordTrace]
  refine ⟨19023512504415721853058661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25364683339220962470744881 19023512504415721853058661)
  ·
    refine ⟨3566908594577947847448499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19023512504415721853058661 3566908594577947847448499)
    ·
      refine ⟨5350362891866921771172749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566908594577947847448499 5350362891866921771172749)
      ·
        refine ⟨2006386084450095664189781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5350362891866921771172749 2006386084450095664189781)
        ·
          refine ⟨5878084231787389641181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 2006386084450095664189781 5878084231787389641181)
          ·
            rfl

theorem cell20_1043156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 10].length) (baseStart_1043156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043156 prefixEnd_1043156 := by exact prefixLift 1043156
  have htrace : WordTrace (prefixWord ++ tailWord_1043156) baseStart_1043156 baseEnd_1043156 := by
    simpa [prefixWord, tailWord_1043156, baseEnd_1043156] using wordTrace_append hprefix tailTrace_1043156
  have hstable : (prefixWord ++ tailWord_1043156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043156).length < 2 ^ (prefixWord ++ tailWord_1043156).sum := by decide
  have hdescent : baseEnd_1043156 < baseStart_1043156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043173 : List Nat := [1, 3, 1, 4, 1, 4, 1, 5]
def baseStart_1043173 : Nat := 118140960795 + 1043173 * 2 ^ 59
def prefixEnd_1043173 : Nat := 4983230072969 + 3 ^ 40 * 1043173 * 2
def baseEnd_1043173 : Nat := 158710860679334019122975

theorem tailTrace_1043173 : CollatzResearch.WordTrace tailWord_1043173 prefixEnd_1043173 158710860679334019122975 := by
  unfold tailWord_1043173
  simp only [CollatzResearch.WordTrace]
  refine ⟨38047645049769855609486173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25365096699846570406324115 38047645049769855609486173)
  ·
    refine ⟨14267866893663695853557315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38047645049769855609486173 14267866893663695853557315)
    ·
      refine ⟨21401800340495543780335973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14267866893663695853557315 21401800340495543780335973)
      ·
        refine ⟨4012837563842914458812995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21401800340495543780335973 4012837563842914458812995)
        ·
          refine ⟨6019256345764371688219493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012837563842914458812995 6019256345764371688219493)
          ·
            refine ⟨1128610564830819691541155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6019256345764371688219493 1128610564830819691541155)
            ·
              refine ⟨1692915847246229537311733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128610564830819691541155 1692915847246229537311733)
              ·
                refine ⟨158710860679334019122975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1692915847246229537311733 158710860679334019122975)
                ·
                  rfl

theorem cell20_1043173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_1043173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043173 prefixEnd_1043173 := by exact prefixLift 1043173
  have htrace : WordTrace (prefixWord ++ tailWord_1043173) baseStart_1043173 baseEnd_1043173 := by
    simpa [prefixWord, tailWord_1043173, baseEnd_1043173] using wordTrace_append hprefix tailTrace_1043173
  have hstable : (prefixWord ++ tailWord_1043173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043173).length < 2 ^ (prefixWord ++ tailWord_1043173).sum := by decide
  have hdescent : baseEnd_1043173 < baseStart_1043173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043201 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1043201 : Nat := 118140960795 + 1043201 * 2 ^ 59
def prefixEnd_1043201 : Nat := 4983230072969 + 3 ^ 40 * 1043201 * 2
def baseEnd_1043201 : Nat := 476145362000958404435477

theorem tailTrace_1043201 : CollatzResearch.WordTrace tailWord_1043201 prefixEnd_1043201 476145362000958404435477 := by
  unfold tailWord_1043201
  simp only [CollatzResearch.WordTrace]
  refine ⟨38048666293668416391505457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25365777529112277594336971 38048666293668416391505457)
  ·
    refine ⟨28536499720251312293629093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38048666293668416391505457 28536499720251312293629093)
    ·
      refine ⟨5350593697547121055055455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28536499720251312293629093 5350593697547121055055455)
      ·
        refine ⟨8025890546320681582583183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350593697547121055055455 8025890546320681582583183)
        ·
          refine ⟨12038835819481022373874775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8025890546320681582583183 12038835819481022373874775)
          ·
            refine ⟨18058253729221533560812163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12038835819481022373874775 18058253729221533560812163)
            ·
              refine ⟨27087380593832300341218245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18058253729221533560812163 27087380593832300341218245)
              ·
                refine ⟨5078883861343556313978421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27087380593832300341218245 5078883861343556313978421)
                ·
                  refine ⟨476145362000958404435477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5078883861343556313978421 476145362000958404435477)
                  ·
                    rfl

theorem cell20_1043201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1043201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043201 prefixEnd_1043201 := by exact prefixLift 1043201
  have htrace : WordTrace (prefixWord ++ tailWord_1043201) baseStart_1043201 baseEnd_1043201 := by
    simpa [prefixWord, tailWord_1043201, baseEnd_1043201] using wordTrace_append hprefix tailTrace_1043201
  have hstable : (prefixWord ++ tailWord_1043201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043201).length < 2 ^ (prefixWord ++ tailWord_1043201).sum := by decide
  have hdescent : baseEnd_1043201 < baseStart_1043201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043215 : List Nat := [1, 1, 2, 1, 1, 1, 13]
def baseStart_1043215 : Nat := 118140960795 + 1043215 * 2 ^ 59
def prefixEnd_1043215 : Nat := 4983230072969 + 3 ^ 40 * 1043215 * 2
def baseEnd_1043215 : Nat := 52905750220270730885417

theorem tailTrace_1043215 : CollatzResearch.WordTrace tailWord_1043215 prefixEnd_1043215 52905750220270730885417 := by
  unfold tailWord_1043215
  simp only [CollatzResearch.WordTrace]
  refine ⟨38049176915617696782515099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25366117943745131188343399 38049176915617696782515099)
  ·
    refine ⟨57073765373426545173772649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38049176915617696782515099 57073765373426545173772649)
    ·
      refine ⟨42805324030069908880329487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57073765373426545173772649 42805324030069908880329487)
      ·
        refine ⟨64207986045104863320494231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42805324030069908880329487 64207986045104863320494231)
        ·
          refine ⟨96311979067657294980741347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64207986045104863320494231 96311979067657294980741347)
          ·
            refine ⟨144467968601485942471112021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96311979067657294980741347 144467968601485942471112021)
            ·
              refine ⟨52905750220270730885417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 144467968601485942471112021 52905750220270730885417)
              ·
                rfl

theorem cell20_1043215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_1043215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043215 prefixEnd_1043215 := by exact prefixLift 1043215
  have htrace : WordTrace (prefixWord ++ tailWord_1043215) baseStart_1043215 baseEnd_1043215 := by
    simpa [prefixWord, tailWord_1043215, baseEnd_1043215] using wordTrace_append hprefix tailTrace_1043215
  have hstable : (prefixWord ++ tailWord_1043215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043215).length < 2 ^ (prefixWord ++ tailWord_1043215).sum := by decide
  have hdescent : baseEnd_1043215 < baseStart_1043215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043329 : List Nat := [1, 2, 4, 13]
def baseStart_1043329 : Nat := 118140960795 + 1043329 * 2 ^ 59
def prefixEnd_1043329 : Nat := 4983230072969 + 3 ^ 40 * 1043329 * 2
def baseEnd_1043329 : Nat := 1959686356743863572709

theorem tailTrace_1043329 : CollatzResearch.WordTrace tailWord_1043329 prefixEnd_1043329 1959686356743863572709 := by
  unfold tailWord_1043329
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053334837204694252165041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25368889891469796168110027 38053334837204694252165041)
  ·
    refine ⟨28540001127903520689123781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38053334837204694252165041 28540001127903520689123781)
    ·
      refine ⟨5351250211481910129210709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28540001127903520689123781 5351250211481910129210709)
      ·
        refine ⟨1959686356743863572709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 5351250211481910129210709 1959686356743863572709)
        ·
          rfl

theorem cell20_1043329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 13].length) (baseStart_1043329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043329 prefixEnd_1043329 := by exact prefixLift 1043329
  have htrace : WordTrace (prefixWord ++ tailWord_1043329) baseStart_1043329 baseEnd_1043329 := by
    simpa [prefixWord, tailWord_1043329, baseEnd_1043329] using wordTrace_append hprefix tailTrace_1043329
  have hstable : (prefixWord ++ tailWord_1043329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043329).length < 2 ^ (prefixWord ++ tailWord_1043329).sum := by decide
  have hdescent : baseEnd_1043329 < baseStart_1043329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043335 : List Nat := [1, 1, 4, 2, 3, 1, 4, 2, 2]
def baseStart_1043335 : Nat := 118140960795 + 1043335 * 2 ^ 59
def prefixEnd_1043335 : Nat := 4983230072969 + 3 ^ 40 * 1043335 * 2
def baseEnd_1043335 : Nat := 476206523252249493968263

theorem tailTrace_1043335 : CollatzResearch.WordTrace tailWord_1043335 prefixEnd_1043335 476206523252249493968263 := by
  unfold tailWord_1043335
  simp only [CollatzResearch.WordTrace]
  refine ⟨38053553675182957276883459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25369035783455304851255639 38053553675182957276883459)
  ·
    refine ⟨57080330512774435915325189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38053553675182957276883459 57080330512774435915325189)
    ·
      refine ⟨10702561971145206734123473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57080330512774435915325189 10702561971145206734123473)
      ·
        refine ⟨8026921478358905050592605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10702561971145206734123473 8026921478358905050592605)
        ·
          refine ⟨3010095554384589393972227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8026921478358905050592605 3010095554384589393972227)
          ·
            refine ⟨4515143331576884090958341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010095554384589393972227 4515143331576884090958341)
            ·
              refine ⟨846589374670665767054689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4515143331576884090958341 846589374670665767054689)
              ·
                refine ⟨634942031002999325291017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846589374670665767054689 634942031002999325291017)
                ·
                  refine ⟨476206523252249493968263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 634942031002999325291017 476206523252249493968263)
                  ·
                    rfl

theorem cell20_1043335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 2].length) (baseStart_1043335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043335 prefixEnd_1043335 := by exact prefixLift 1043335
  have htrace : WordTrace (prefixWord ++ tailWord_1043335) baseStart_1043335 baseEnd_1043335 := by
    simpa [prefixWord, tailWord_1043335, baseEnd_1043335] using wordTrace_append hprefix tailTrace_1043335
  have hstable : (prefixWord ++ tailWord_1043335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043335).length < 2 ^ (prefixWord ++ tailWord_1043335).sum := by decide
  have hdescent : baseEnd_1043335 < baseStart_1043335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043356 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 4]
def baseStart_1043356 : Nat := 118140960795 + 1043356 * 2 ^ 59
def prefixEnd_1043356 : Nat := 4983230072969 + 3 ^ 40 * 1043356 * 2
def baseEnd_1043356 : Nat := 476216108224466754268177

theorem tailTrace_1043356 : CollatzResearch.WordTrace tailWord_1043356 prefixEnd_1043356 476216108224466754268177 := by
  unfold tailWord_1043356
  simp only [CollatzResearch.WordTrace]
  refine ⟨19027159804053438931698961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25369546405404585242265281 19027159804053438931698961)
  ·
    refine ⟨14270369853040079198774221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19027159804053438931698961 14270369853040079198774221)
    ·
      refine ⟨5351388694890029699540333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14270369853040079198774221 5351388694890029699540333)
      ·
        refine ⟨2006770760583761137327625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5351388694890029699540333 2006770760583761137327625)
        ·
          refine ⟨1505078070437820852995719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2006770760583761137327625 1505078070437820852995719)
          ·
            refine ⟨2257617105656731279493579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505078070437820852995719 2257617105656731279493579)
            ·
              refine ⟨3386425658485096919240369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2257617105656731279493579 3386425658485096919240369)
              ·
                refine ⟨2539819243863822689430277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3386425658485096919240369 2539819243863822689430277)
                ·
                  refine ⟨476216108224466754268177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2539819243863822689430277 476216108224466754268177)
                  ·
                    rfl

theorem cell20_1043356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_1043356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043356 prefixEnd_1043356 := by exact prefixLift 1043356
  have htrace : WordTrace (prefixWord ++ tailWord_1043356) baseStart_1043356 baseEnd_1043356 := by
    simpa [prefixWord, tailWord_1043356, baseEnd_1043356] using wordTrace_append hprefix tailTrace_1043356
  have hstable : (prefixWord ++ tailWord_1043356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043356).length < 2 ^ (prefixWord ++ tailWord_1043356).sum := by decide
  have hdescent : baseEnd_1043356 < baseStart_1043356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043360 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1043360 : Nat := 118140960795 + 1043360 * 2 ^ 59
def prefixEnd_1043360 : Nat := 4983230072969 + 3 ^ 40 * 1043360 * 2
def baseEnd_1043360 : Nat := 476217933933460518134827

theorem tailTrace_1043360 : CollatzResearch.WordTrace tailWord_1043360 prefixEnd_1043360 476217933933460518134827 := by
  unfold tailWord_1043360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19027232750046193273271767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25369643666728257697695689 19027232750046193273271767)
  ·
    refine ⟨28540849125069289909907651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19027232750046193273271767 28540849125069289909907651)
    ·
      refine ⟨42811273687603934864861477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28540849125069289909907651 42811273687603934864861477)
      ·
        refine ⟨8027113816425737787161527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42811273687603934864861477 8027113816425737787161527)
        ·
          refine ⟨12040670724638606680742291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027113816425737787161527 12040670724638606680742291)
          ·
            refine ⟨18061006086957910021113437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12040670724638606680742291 18061006086957910021113437)
            ·
              refine ⟨6772877282609216257917539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18061006086957910021113437 6772877282609216257917539)
              ·
                refine ⟨10159315923913824386876309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6772877282609216257917539 10159315923913824386876309)
                ·
                  refine ⟨476217933933460518134827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10159315923913824386876309 476217933933460518134827)
                  ·
                    rfl

theorem cell20_1043360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1043360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043360 prefixEnd_1043360 := by exact prefixLift 1043360
  have htrace : WordTrace (prefixWord ++ tailWord_1043360) baseStart_1043360 baseEnd_1043360 := by
    simpa [prefixWord, tailWord_1043360, baseEnd_1043360] using wordTrace_append hprefix tailTrace_1043360
  have hstable : (prefixWord ++ tailWord_1043360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043360).length < 2 ^ (prefixWord ++ tailWord_1043360).sum := by decide
  have hdescent : baseEnd_1043360 < baseStart_1043360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043391 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 3]
def baseStart_1043391 : Nat := 118140960795 + 1043391 * 2 ^ 59
def prefixEnd_1043391 : Nat := 4983230072969 + 3 ^ 40 * 1043391 * 2
def baseEnd_1043391 : Nat := 476232083178162188101367

theorem tailTrace_1043391 : CollatzResearch.WordTrace tailWord_1043391 prefixEnd_1043391 476232083178162188101367 := by
  unfold tailWord_1043391
  simp only [CollatzResearch.WordTrace]
  refine ⟨38055596162980078840922027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25370397441986719227281351 38055596162980078840922027)
  ·
    refine ⟨57083394244470118261383041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38055596162980078840922027 57083394244470118261383041)
    ·
      refine ⟨42812545683352588696037281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57083394244470118261383041 42812545683352588696037281)
      ·
        refine ⟨32109409262514441522027961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42812545683352588696037281 32109409262514441522027961)
        ·
          refine ⟨24082056946885831141520971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32109409262514441522027961 24082056946885831141520971)
          ·
            refine ⟨36123085420328746712281457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24082056946885831141520971 36123085420328746712281457)
            ·
              refine ⟨27092314065246560034211093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36123085420328746712281457 27092314065246560034211093)
              ·
                refine ⟨1269952221808432501603645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27092314065246560034211093 1269952221808432501603645)
                ·
                  refine ⟨476232083178162188101367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1269952221808432501603645 476232083178162188101367)
                  ·
                    rfl

theorem cell20_1043391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_1043391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043391 prefixEnd_1043391 := by exact prefixLift 1043391
  have htrace : WordTrace (prefixWord ++ tailWord_1043391) baseStart_1043391 baseEnd_1043391 := by
    simpa [prefixWord, tailWord_1043391, baseEnd_1043391] using wordTrace_append hprefix tailTrace_1043391
  have hstable : (prefixWord ++ tailWord_1043391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043391).length < 2 ^ (prefixWord ++ tailWord_1043391).sum := by decide
  have hdescent : baseEnd_1043391 < baseStart_1043391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043432 : List Nat := [2, 1, 4, 1, 1, 1, 5, 3, 2]
def baseStart_1043432 : Nat := 118140960795 + 1043432 * 2 ^ 59
def prefixEnd_1043432 : Nat := 4983230072969 + 3 ^ 40 * 1043432 * 2
def baseEnd_1043432 : Nat := 476250796695348267734533

theorem tailTrace_1043432 : CollatzResearch.WordTrace tailWord_1043432 prefixEnd_1043432 476250796695348267734533 := by
  unfold tailWord_1043432
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028545777915771421582275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25371394370554361895443033 19028545777915771421582275)
  ·
    refine ⟨28542818666873657132373413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19028545777915771421582275 28542818666873657132373413)
    ·
      refine ⟨5351778500038810712320015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28542818666873657132373413 5351778500038810712320015)
      ·
        refine ⟨8027667750058216068480023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351778500038810712320015 8027667750058216068480023)
        ·
          refine ⟨12041501625087324102720035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027667750058216068480023 12041501625087324102720035)
          ·
            refine ⟨18062252437630986154080053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12041501625087324102720035 18062252437630986154080053)
            ·
              refine ⟨1693336166027904951945005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18062252437630986154080053 1693336166027904951945005)
              ·
                refine ⟨635001062260464356979377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1693336166027904951945005 635001062260464356979377)
                ·
                  refine ⟨476250796695348267734533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635001062260464356979377 476250796695348267734533)
                  ·
                    rfl

theorem cell20_1043432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_1043432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043432 prefixEnd_1043432 := by exact prefixLift 1043432
  have htrace : WordTrace (prefixWord ++ tailWord_1043432) baseStart_1043432 baseEnd_1043432 := by
    simpa [prefixWord, tailWord_1043432, baseEnd_1043432] using wordTrace_append hprefix tailTrace_1043432
  have hstable : (prefixWord ++ tailWord_1043432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043432).length < 2 ^ (prefixWord ++ tailWord_1043432).sum := by decide
  have hdescent : baseEnd_1043432 < baseStart_1043432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043445 : List Nat := [1, 3, 5, 2, 1, 1, 3, 2, 2]
def baseStart_1043445 : Nat := 118140960795 + 1043445 * 2 ^ 59
def prefixEnd_1043445 : Nat := 4983230072969 + 3 ^ 40 * 1043445 * 2
def baseEnd_1043445 : Nat := 476256730249578000301147

theorem tailTrace_1043445 : CollatzResearch.WordTrace tailWord_1043445 prefixEnd_1043445 476256730249578000301147 := by
  unfold tailWord_1043445
  simp only [CollatzResearch.WordTrace]
  refine ⟨38057565704784446063387789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25371710469856297375591859 38057565704784446063387789)
  ·
    refine ⟨14271587139294167273770421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38057565704784446063387789 14271587139294167273770421)
    ·
      refine ⟨1337961294308828181915977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14271587139294167273770421 1337961294308828181915977)
      ·
        refine ⟨1003470970731621136436983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337961294308828181915977 1003470970731621136436983)
        ·
          refine ⟨1505206456097431704655475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003470970731621136436983 1505206456097431704655475)
          ·
            refine ⟨2257809684146147556983213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505206456097431704655475 2257809684146147556983213)
            ·
              refine ⟨846678631554805333868705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257809684146147556983213 846678631554805333868705)
              ·
                refine ⟨635008973666104000401529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846678631554805333868705 635008973666104000401529)
                ·
                  refine ⟨476256730249578000301147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635008973666104000401529 476256730249578000301147)
                  ·
                    rfl

theorem cell20_1043445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_1043445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043445 prefixEnd_1043445 := by exact prefixLift 1043445
  have htrace : WordTrace (prefixWord ++ tailWord_1043445) baseStart_1043445 baseEnd_1043445 := by
    simpa [prefixWord, tailWord_1043445, baseEnd_1043445] using wordTrace_append hprefix tailTrace_1043445
  have hstable : (prefixWord ++ tailWord_1043445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043445).length < 2 ^ (prefixWord ++ tailWord_1043445).sum := by decide
  have hdescent : baseEnd_1043445 < baseStart_1043445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043446 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1043446 : Nat := 118140960795 + 1043446 * 2 ^ 59
def prefixEnd_1043446 : Nat := 4983230072969 + 3 ^ 40 * 1043446 * 2
def baseEnd_1043446 : Nat := 476257186676826441267809

theorem tailTrace_1043446 : CollatzResearch.WordTrace tailWord_1043446 prefixEnd_1043446 476257186676826441267809 := by
  unfold tailWord_1043446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378600136111301452135887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25371734785187215489449461 2378600136111301452135887)
  ·
    refine ⟨3567900204166952178203831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378600136111301452135887 3567900204166952178203831)
    ·
      refine ⟨5351850306250428267305747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567900204166952178203831 5351850306250428267305747)
      ·
        refine ⟨8027775459375642400958621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351850306250428267305747 8027775459375642400958621)
        ·
          refine ⟨3010415797265865900359483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8027775459375642400958621 3010415797265865900359483)
          ·
            refine ⟨4515623695898798850539225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010415797265865900359483 4515623695898798850539225)
            ·
              refine ⟨3386717771924099137904419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4515623695898798850539225 3386717771924099137904419)
              ·
                refine ⟨5080076657886148706856629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3386717771924099137904419 5080076657886148706856629)
                ·
                  refine ⟨476257186676826441267809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5080076657886148706856629 476257186676826441267809)
                  ·
                    rfl

theorem cell20_1043446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1043446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043446 prefixEnd_1043446 := by exact prefixLift 1043446
  have htrace : WordTrace (prefixWord ++ tailWord_1043446) baseStart_1043446 baseEnd_1043446 := by
    simpa [prefixWord, tailWord_1043446, baseEnd_1043446] using wordTrace_append hprefix tailTrace_1043446
  have hstable : (prefixWord ++ tailWord_1043446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043446).length < 2 ^ (prefixWord ++ tailWord_1043446).sum := by decide
  have hdescent : baseEnd_1043446 < baseStart_1043446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043481 : List Nat := [1, 2, 1, 2, 1, 1, 6, 6]
def baseStart_1043481 : Nat := 118140960795 + 1043481 * 2 ^ 59
def prefixEnd_1043481 : Nat := 4983230072969 + 3 ^ 40 * 1043481 * 2
def baseEnd_1043481 : Nat := 158757720543507291700333

theorem tailTrace_1043481 : CollatzResearch.WordTrace tailWord_1043481 prefixEnd_1043481 158757720543507291700333 := by
  unfold tailWord_1043481
  simp only [CollatzResearch.WordTrace]
  refine ⟨38058878732654024211698297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25372585821769349474465531 38058878732654024211698297)
  ·
    refine ⟨28544159049490518158773723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38058878732654024211698297 28544159049490518158773723)
    ·
      refine ⟨42816238574235777238160585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28544159049490518158773723 42816238574235777238160585)
      ·
        refine ⟨32112178930676832928620439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42816238574235777238160585 32112178930676832928620439)
        ·
          refine ⟨48168268396015249392930659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32112178930676832928620439 48168268396015249392930659)
          ·
            refine ⟨72252402594022874089395989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48168268396015249392930659 72252402594022874089395989)
            ·
              refine ⟨3386831371594822222940437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72252402594022874089395989 3386831371594822222940437)
              ·
                refine ⟨158757720543507291700333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3386831371594822222940437 158757720543507291700333)
                ·
                  rfl

theorem cell20_1043481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_1043481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043481 prefixEnd_1043481 := by exact prefixLift 1043481
  have htrace : WordTrace (prefixWord ++ tailWord_1043481) baseStart_1043481 baseEnd_1043481 := by
    simpa [prefixWord, tailWord_1043481, baseEnd_1043481] using wordTrace_append hprefix tailTrace_1043481
  have hstable : (prefixWord ++ tailWord_1043481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043481).length < 2 ^ (prefixWord ++ tailWord_1043481).sum := by decide
  have hdescent : baseEnd_1043481 < baseStart_1043481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043498 : List Nat := [3, 1, 4, 1, 3, 8]
def baseStart_1043498 : Nat := 118140960795 + 1043498 * 2 ^ 59
def prefixEnd_1043498 : Nat := 4983230072969 + 3 ^ 40 * 1043498 * 2
def baseEnd_1043498 : Nat := 17640034107175754501269

theorem tailTrace_1043498 : CollatzResearch.WordTrace tailWord_1043498 prefixEnd_1043498 17640034107175754501269 := by
  unfold tailWord_1043498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514874693398109028766787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25372999182394957410044765 9514874693398109028766787)
  ·
    refine ⟨14272312040097163543150181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9514874693398109028766787 14272312040097163543150181)
    ·
      refine ⟨2676058507518218164340659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14272312040097163543150181 2676058507518218164340659)
      ·
        refine ⟨4014087761277327246510989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676058507518218164340659 4014087761277327246510989)
        ·
          refine ⟨1505282910478997717441621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4014087761277327246510989 1505282910478997717441621)
          ·
            refine ⟨17640034107175754501269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1505282910478997717441621 17640034107175754501269)
            ·
              rfl

theorem cell20_1043498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 8].length) (baseStart_1043498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043498 prefixEnd_1043498 := by exact prefixLift 1043498
  have htrace : WordTrace (prefixWord ++ tailWord_1043498) baseStart_1043498 baseEnd_1043498 := by
    simpa [prefixWord, tailWord_1043498, baseEnd_1043498] using wordTrace_append hprefix tailTrace_1043498
  have hstable : (prefixWord ++ tailWord_1043498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043498).length < 2 ^ (prefixWord ++ tailWord_1043498).sum := by decide
  have hdescent : baseEnd_1043498 < baseStart_1043498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043557 : List Nat := [1, 3, 1, 3, 2, 1, 9]
def baseStart_1043557 : Nat := 118140960795 + 1043557 * 2 ^ 59
def prefixEnd_1043557 : Nat := 4983230072969 + 3 ^ 40 * 1043557 * 2
def baseEnd_1043557 : Nat := 52923094455711487618595

theorem tailTrace_1043557 : CollatzResearch.WordTrace tailWord_1043557 prefixEnd_1043557 52923094455711487618595 := by
  unfold tailWord_1043557
  simp only [CollatzResearch.WordTrace]
  refine ⟨38061650680378689191464925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25374433786919126127643283 38061650680378689191464925)
  ·
    refine ⟨14273119005142008446799347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38061650680378689191464925 14273119005142008446799347)
    ·
      refine ⟨21409678507713012670199021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14273119005142008446799347 21409678507713012670199021)
      ·
        refine ⟨8028629440392379751324633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21409678507713012670199021 8028629440392379751324633)
        ·
          refine ⟨6021472080294284813493475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8028629440392379751324633 6021472080294284813493475)
          ·
            refine ⟨9032208120441427220240213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021472080294284813493475 9032208120441427220240213)
            ·
              refine ⟨52923094455711487618595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9032208120441427220240213 52923094455711487618595)
              ·
                rfl

theorem cell20_1043557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 9].length) (baseStart_1043557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043557 prefixEnd_1043557 := by exact prefixLift 1043557
  have htrace : WordTrace (prefixWord ++ tailWord_1043557) baseStart_1043557 baseEnd_1043557 := by
    simpa [prefixWord, tailWord_1043557, baseEnd_1043557] using wordTrace_append hprefix tailTrace_1043557
  have hstable : (prefixWord ++ tailWord_1043557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043557).length < 2 ^ (prefixWord ++ tailWord_1043557).sum := by decide
  have hdescent : baseEnd_1043557 < baseStart_1043557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043567 : List Nat := [1, 1, 2, 1, 3, 3, 1, 6, 2]
def baseStart_1043567 : Nat := 118140960795 + 1043567 * 2 ^ 59
def prefixEnd_1043567 : Nat := 4983230072969 + 3 ^ 40 * 1043567 * 2
def baseEnd_1043567 : Nat := 476312414373887798233981

theorem tailTrace_1043567 : CollatzResearch.WordTrace tailWord_1043567 prefixEnd_1043567 476312414373887798233981 := by
  unfold tailWord_1043567
  simp only [CollatzResearch.WordTrace]
  refine ⟨38062015410342460899328955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25374676940228307266219303 38062015410342460899328955)
  ·
    refine ⟨57093023115513691348993433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38062015410342460899328955 57093023115513691348993433)
    ·
      refine ⟨42819767336635268511745075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57093023115513691348993433 42819767336635268511745075)
      ·
        refine ⟨64229651004952902767617613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42819767336635268511745075 64229651004952902767617613)
        ·
          refine ⟨24086119126857338537856605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64229651004952902767617613 24086119126857338537856605)
          ·
            refine ⟨9032294672571501951696227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24086119126857338537856605 9032294672571501951696227)
            ·
              refine ⟨13548442008857252927544341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9032294672571501951696227 13548442008857252927544341)
              ·
                refine ⟨635083219165183730978641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13548442008857252927544341 635083219165183730978641)
                ·
                  refine ⟨476312414373887798233981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635083219165183730978641 476312414373887798233981)
                  ·
                    rfl

theorem cell20_1043567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 2].length) (baseStart_1043567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043567 prefixEnd_1043567 := by exact prefixLift 1043567
  have htrace : WordTrace (prefixWord ++ tailWord_1043567) baseStart_1043567 baseEnd_1043567 := by
    simpa [prefixWord, tailWord_1043567, baseEnd_1043567] using wordTrace_append hprefix tailTrace_1043567
  have hstable : (prefixWord ++ tailWord_1043567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043567).length < 2 ^ (prefixWord ++ tailWord_1043567).sum := by decide
  have hdescent : baseEnd_1043567 < baseStart_1043567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043574 : List Nat := [5, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1043574 : Nat := 118140960795 + 1043574 * 2 ^ 59
def prefixEnd_1043574 : Nat := 4983230072969 + 3 ^ 40 * 1043574 * 2
def baseEnd_1043574 : Nat := 158771869788208961666873

theorem tailTrace_1043574 : CollatzResearch.WordTrace tailWord_1043574 prefixEnd_1043574 158771869788208961666873 := by
  unfold tailWord_1043574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378891920082318818427111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25374847147544734063222517 2378891920082318818427111)
  ·
    refine ⟨3568337880123478227640667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378891920082318818427111 3568337880123478227640667)
    ·
      refine ⟨5352506820185217341461001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3568337880123478227640667 5352506820185217341461001)
      ·
        refine ⟨4014380115138913006095751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5352506820185217341461001 4014380115138913006095751)
        ·
          refine ⟨6021570172708369509143627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014380115138913006095751 6021570172708369509143627)
          ·
            refine ⟨9032355259062554263715441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6021570172708369509143627 9032355259062554263715441)
            ·
              refine ⟨6774266444296915697786581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9032355259062554263715441 6774266444296915697786581)
              ·
                refine ⟨158771869788208961666873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6774266444296915697786581 158771869788208961666873)
                ·
                  rfl

theorem cell20_1043574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1043574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043574 prefixEnd_1043574 := by exact prefixLift 1043574
  have htrace : WordTrace (prefixWord ++ tailWord_1043574) baseStart_1043574 baseEnd_1043574 := by
    simpa [prefixWord, tailWord_1043574, baseEnd_1043574] using wordTrace_append hprefix tailTrace_1043574
  have hstable : (prefixWord ++ tailWord_1043574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043574).length < 2 ^ (prefixWord ++ tailWord_1043574).sum := by decide
  have hdescent : baseEnd_1043574 < baseStart_1043574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043577 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 3]
def baseStart_1043577 : Nat := 118140960795 + 1043577 * 2 ^ 59
def prefixEnd_1043577 : Nat := 4983230072969 + 3 ^ 40 * 1043577 * 2
def baseEnd_1043577 : Nat := 476316978646372207900607

theorem tailTrace_1043577 : CollatzResearch.WordTrace tailWord_1043577 prefixEnd_1043577 476316978646372207900607 := by
  unfold tailWord_1043577
  simp only [CollatzResearch.WordTrace]
  refine ⟨38062380140306232607192985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25374920093537488404795323 38062380140306232607192985)
  ·
    refine ⟨28546785105229674455394739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38062380140306232607192985 28546785105229674455394739)
    ·
      refine ⟨42820177657844511683092109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28546785105229674455394739 42820177657844511683092109)
      ·
        refine ⟨16057566621691691881159541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42820177657844511683092109 16057566621691691881159541)
        ·
          refine ⟨1505396870783596113858707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16057566621691691881159541 1505396870783596113858707)
          ·
            refine ⟨2258095306175394170788061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505396870783596113858707 2258095306175394170788061)
            ·
              refine ⟨846785739815772814045523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2258095306175394170788061 846785739815772814045523)
              ·
                refine ⟨1270178609723659221068285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846785739815772814045523 1270178609723659221068285)
                ·
                  refine ⟨476316978646372207900607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270178609723659221068285 476316978646372207900607)
                  ·
                    rfl

theorem cell20_1043577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_1043577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043577 prefixEnd_1043577 := by exact prefixLift 1043577
  have htrace : WordTrace (prefixWord ++ tailWord_1043577) baseStart_1043577 baseEnd_1043577 := by
    simpa [prefixWord, tailWord_1043577, baseEnd_1043577] using wordTrace_append hprefix tailTrace_1043577
  have hstable : (prefixWord ++ tailWord_1043577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043577).length < 2 ^ (prefixWord ++ tailWord_1043577).sum := by decide
  have hdescent : baseEnd_1043577 < baseStart_1043577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043605 : List Nat := [1, 3, 2, 1, 1, 1, 2, 7, 2]
def baseStart_1043605 : Nat := 118140960795 + 1043605 * 2 ^ 59
def prefixEnd_1043605 : Nat := 4983230072969 + 3 ^ 40 * 1043605 * 2
def baseEnd_1043605 : Nat := 476329758609328554967159

theorem tailTrace_1043605 : CollatzResearch.WordTrace tailWord_1043605 prefixEnd_1043605 476329758609328554967159 := by
  unfold tailWord_1043605
  simp only [CollatzResearch.WordTrace]
  refine ⟨38063401384204793389212269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25375600922803195592808179 38063401384204793389212269)
  ·
    refine ⟨14273775519076797520954601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38063401384204793389212269 14273775519076797520954601)
    ·
      refine ⟨10705331639307598140715951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14273775519076797520954601 10705331639307598140715951)
      ·
        refine ⟨16057997458961397211073927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10705331639307598140715951 16057997458961397211073927)
        ·
          refine ⟨24086996188442095816610891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16057997458961397211073927 24086996188442095816610891)
          ·
            refine ⟨36130494282663143724916337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24086996188442095816610891 36130494282663143724916337)
            ·
              refine ⟨27097870711997357793687253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36130494282663143724916337 27097870711997357793687253)
              ·
                refine ⟨635106344812438073289545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27097870711997357793687253 635106344812438073289545)
                ·
                  refine ⟨476329758609328554967159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635106344812438073289545 476329758609328554967159)
                  ·
                    rfl

theorem cell20_1043605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_1043605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043605 prefixEnd_1043605 := by exact prefixLift 1043605
  have htrace : WordTrace (prefixWord ++ tailWord_1043605) baseStart_1043605 baseEnd_1043605 := by
    simpa [prefixWord, tailWord_1043605, baseEnd_1043605] using wordTrace_append hprefix tailTrace_1043605
  have hstable : (prefixWord ++ tailWord_1043605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043605).length < 2 ^ (prefixWord ++ tailWord_1043605).sum := by decide
  have hdescent : baseEnd_1043605 < baseStart_1043605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043612 : List Nat := [2, 2, 3, 2, 1, 4, 6]
def baseStart_1043612 : Nat := 118140960795 + 1043612 * 2 ^ 59
def prefixEnd_1043612 : Nat := 4983230072969 + 3 ^ 40 * 1043612 * 2
def baseEnd_1043612 : Nat := 52925883733340849081533

theorem tailTrace_1043612 : CollatzResearch.WordTrace tailWord_1043612 prefixEnd_1043612 52925883733340849081533 := by
  unfold tailWord_1043612
  simp only [CollatzResearch.WordTrace]
  refine ⟨19031828347589716792358545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25375771130119622389811393 19031828347589716792358545)
  ·
    refine ⟨14273871260692287594268909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19031828347589716792358545 14273871260692287594268909)
    ·
      refine ⟨5352701722759607847850841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14273871260692287594268909 5352701722759607847850841)
      ·
        refine ⟨4014526292069705885888131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5352701722759607847850841 4014526292069705885888131)
        ·
          refine ⟨6021789438104558828832197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014526292069705885888131 6021789438104558828832197)
          ·
            refine ⟨1129085519644604780406037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6021789438104558828832197 1129085519644604780406037)
            ·
              refine ⟨52925883733340849081533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1129085519644604780406037 52925883733340849081533)
              ·
                rfl

theorem cell20_1043612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 6].length) (baseStart_1043612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043612 prefixEnd_1043612 := by exact prefixLift 1043612
  have htrace : WordTrace (prefixWord ++ tailWord_1043612) baseStart_1043612 baseEnd_1043612 := by
    simpa [prefixWord, tailWord_1043612, baseEnd_1043612] using wordTrace_append hprefix tailTrace_1043612
  have hstable : (prefixWord ++ tailWord_1043612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043612).length < 2 ^ (prefixWord ++ tailWord_1043612).sum := by decide
  have hdescent : baseEnd_1043612 < baseStart_1043612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043618 : List Nat := [3, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_1043618 : Nat := 118140960795 + 1043618 * 2 ^ 59
def prefixEnd_1043618 : Nat := 4983230072969 + 3 ^ 40 * 1043618 * 2
def baseEnd_1043618 : Nat := 476335692163558287533773

theorem tailTrace_1043618 : CollatzResearch.WordTrace tailWord_1043618 prefixEnd_1043618 476335692163558287533773 := by
  unfold tailWord_1043618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9515968883289424152358877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25375917022105131072957005 9515968883289424152358877)
  ·
    refine ⟨3568488331233534057134579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9515968883289424152358877 3568488331233534057134579)
    ·
      refine ⟨5352732496850301085701869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3568488331233534057134579 5352732496850301085701869)
      ·
        refine ⟨2007274686318862907138201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5352732496850301085701869 2007274686318862907138201)
        ·
          refine ⟨1505456014739147180353651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2007274686318862907138201 1505456014739147180353651)
          ·
            refine ⟨2258184022108720770530477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505456014739147180353651 2258184022108720770530477)
            ·
              refine ⟨846819008290770288948929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2258184022108720770530477 846819008290770288948929)
              ·
                refine ⟨635114256218077716711697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846819008290770288948929 635114256218077716711697)
                ·
                  refine ⟨476335692163558287533773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635114256218077716711697 476335692163558287533773)
                  ·
                    rfl

theorem cell20_1043618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_1043618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043618 prefixEnd_1043618 := by exact prefixLift 1043618
  have htrace : WordTrace (prefixWord ++ tailWord_1043618) baseStart_1043618 baseEnd_1043618 := by
    simpa [prefixWord, tailWord_1043618, baseEnd_1043618] using wordTrace_append hprefix tailTrace_1043618
  have hstable : (prefixWord ++ tailWord_1043618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043618).length < 2 ^ (prefixWord ++ tailWord_1043618).sum := by decide
  have hdescent : baseEnd_1043618 < baseStart_1043618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043629 : List Nat := [1, 5, 2, 1, 3, 1, 2, 5]
def baseStart_1043629 : Nat := 118140960795 + 1043629 * 2 ^ 59
def prefixEnd_1043629 : Nat := 4983230072969 + 3 ^ 40 * 1043629 * 2
def baseEnd_1043629 : Nat := 158780237621097046055687

theorem tailTrace_1043629 : CollatzResearch.WordTrace tailWord_1043629 prefixEnd_1043629 158780237621097046055687 := by
  unfold tailWord_1043629
  simp only [CollatzResearch.WordTrace]
  refine ⟨38064276736117845488085941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25376184490745230325390627 38064276736117845488085941)
  ·
    refine ⟨3568525944011048014508057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38064276736117845488085941 3568525944011048014508057)
    ·
      refine ⟨2676394458008286010881043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3568525944011048014508057 2676394458008286010881043)
      ·
        refine ⟨4014591687012429016321565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676394458008286010881043 4014591687012429016321565)
        ·
          refine ⟨1505471882629660881120587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4014591687012429016321565 1505471882629660881120587)
          ·
            refine ⟨2258207823944491321680881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505471882629660881120587 2258207823944491321680881)
            ·
              refine ⟨1693655867958368491260661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258207823944491321680881 1693655867958368491260661)
              ·
                refine ⟨158780237621097046055687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1693655867958368491260661 158780237621097046055687)
                ·
                  rfl

theorem cell20_1043629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 5].length) (baseStart_1043629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043629 prefixEnd_1043629 := by exact prefixLift 1043629
  have htrace : WordTrace (prefixWord ++ tailWord_1043629) baseStart_1043629 baseEnd_1043629 := by
    simpa [prefixWord, tailWord_1043629, baseEnd_1043629] using wordTrace_append hprefix tailTrace_1043629
  have hstable : (prefixWord ++ tailWord_1043629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043629).length < 2 ^ (prefixWord ++ tailWord_1043629).sum := by decide
  have hdescent : baseEnd_1043629 < baseStart_1043629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043640 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_1043640 : Nat := 118140960795 + 1043640 * 2 ^ 59
def prefixEnd_1043640 : Nat := 4983230072969 + 3 ^ 40 * 1043640 * 2
def baseEnd_1043640 : Nat := 476345733563023988800349

theorem tailTrace_1043640 : CollatzResearch.WordTrace tailWord_1043640 prefixEnd_1043640 476345733563023988800349 := by
  unfold tailWord_1043640
  simp only [CollatzResearch.WordTrace]
  refine ⟨19032338969538997183368187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25376451959385329577824249 19032338969538997183368187)
  ·
    refine ⟨28548508454308495775052281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19032338969538997183368187 28548508454308495775052281)
    ·
      refine ⟨21411381340731371831289211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28548508454308495775052281 21411381340731371831289211)
      ·
        refine ⟨32117072011097057746933817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21411381340731371831289211 32117072011097057746933817)
        ·
          refine ⟨24087804008322793310200363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32117072011097057746933817 24087804008322793310200363)
          ·
            refine ⟨36131706012484189965300545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24087804008322793310200363 36131706012484189965300545)
            ·
              refine ⟨27098779509363142473975409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36131706012484189965300545 27098779509363142473975409)
              ·
                refine ⟨20324084632022356855481557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27098779509363142473975409 20324084632022356855481557)
                ·
                  refine ⟨476345733563023988800349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20324084632022356855481557 476345733563023988800349)
                  ·
                    rfl

theorem cell20_1043640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_1043640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043640 prefixEnd_1043640 := by exact prefixLift 1043640
  have htrace : WordTrace (prefixWord ++ tailWord_1043640) baseStart_1043640 baseEnd_1043640 := by
    simpa [prefixWord, tailWord_1043640, baseEnd_1043640] using wordTrace_append hprefix tailTrace_1043640
  have hstable : (prefixWord ++ tailWord_1043640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043640).length < 2 ^ (prefixWord ++ tailWord_1043640).sum := by decide
  have hdescent : baseEnd_1043640 < baseStart_1043640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043670 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1043670 : Nat := 118140960795 + 1043670 * 2 ^ 59
def prefixEnd_1043670 : Nat := 4983230072969 + 3 ^ 40 * 1043670 * 2
def baseEnd_1043670 : Nat := 476359426380477217800227

theorem tailTrace_1043670 : CollatzResearch.WordTrace tailWord_1043670 prefixEnd_1043670 476359426380477217800227 := by
  unfold tailWord_1043670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379110758060581843145529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25377181419312872993552309 2379110758060581843145529)
  ·
    refine ⟨1784333068545436382359147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2379110758060581843145529 1784333068545436382359147)
    ·
      refine ⟨2676499602818154573538721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784333068545436382359147 2676499602818154573538721)
      ·
        refine ⟨2007374702113615930154041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676499602818154573538721 2007374702113615930154041)
        ·
          refine ⟨1505531026585211947615531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2007374702113615930154041 1505531026585211947615531)
          ·
            refine ⟨2258296539877817921423297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505531026585211947615531 2258296539877817921423297)
            ·
              refine ⟨1693722404908363441067473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2258296539877817921423297 1693722404908363441067473)
              ·
                refine ⟨1270291803681272580800605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1693722404908363441067473 1270291803681272580800605)
                ·
                  refine ⟨476359426380477217800227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270291803681272580800605 476359426380477217800227)
                  ·
                    rfl

theorem cell20_1043670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1043670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043670 prefixEnd_1043670 := by exact prefixLift 1043670
  have htrace : WordTrace (prefixWord ++ tailWord_1043670) baseStart_1043670 baseEnd_1043670 := by
    simpa [prefixWord, tailWord_1043670, baseEnd_1043670] using wordTrace_append hprefix tailTrace_1043670
  have hstable : (prefixWord ++ tailWord_1043670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043670).length < 2 ^ (prefixWord ++ tailWord_1043670).sum := by decide
  have hdescent : baseEnd_1043670 < baseStart_1043670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043677 : List Nat := [1, 4, 3, 2, 2, 1, 1, 4, 2]
def baseStart_1043677 : Nat := 118140960795 + 1043677 * 2 ^ 59
def prefixEnd_1043677 : Nat := 4983230072969 + 3 ^ 40 * 1043677 * 2
def baseEnd_1043677 : Nat := 476362621371216304566865

theorem tailTrace_1043677 : CollatzResearch.WordTrace tailWord_1043677 prefixEnd_1043677 476362621371216304566865 := by
  unfold tailWord_1043677
  simp only [CollatzResearch.WordTrace]
  refine ⟨38066027439943949685833285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25377351626629299790555523 38066027439943949685833285)
  ·
    refine ⟨7137380144989490566093741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38066027439943949685833285 7137380144989490566093741)
    ·
      refine ⟨2676517554371058962285153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7137380144989490566093741 2676517554371058962285153)
      ·
        refine ⟨2007388165778294221713865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676517554371058962285153 2007388165778294221713865)
        ·
          refine ⟨1505541124333720666285399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2007388165778294221713865 1505541124333720666285399)
          ·
            refine ⟨2258311686500580999428099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505541124333720666285399 2258311686500580999428099)
            ·
              refine ⟨3387467529750871499142149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258311686500580999428099 3387467529750871499142149)
              ·
                refine ⟨635150161828288406089153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3387467529750871499142149 635150161828288406089153)
                ·
                  refine ⟨476362621371216304566865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635150161828288406089153 476362621371216304566865)
                  ·
                    rfl

theorem cell20_1043677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_1043677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043677 prefixEnd_1043677 := by exact prefixLift 1043677
  have htrace : WordTrace (prefixWord ++ tailWord_1043677) baseStart_1043677 baseEnd_1043677 := by
    simpa [prefixWord, tailWord_1043677, baseEnd_1043677] using wordTrace_append hprefix tailTrace_1043677
  have hstable : (prefixWord ++ tailWord_1043677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043677).length < 2 ^ (prefixWord ++ tailWord_1043677).sum := by decide
  have hdescent : baseEnd_1043677 < baseStart_1043677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043740 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1043740 : Nat := 118140960795 + 1043740 * 2 ^ 59
def prefixEnd_1043740 : Nat := 4983230072969 + 3 ^ 40 * 1043740 * 2
def baseEnd_1043740 : Nat := 476391376287868085466607

theorem tailTrace_1043740 : CollatzResearch.WordTrace tailWord_1043740 prefixEnd_1043740 476391376287868085466607 := by
  unfold tailWord_1043740
  simp only [CollatzResearch.WordTrace]
  refine ⟨19034162619357855722688337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25378883492477140963584449 19034162619357855722688337)
  ·
    refine ⟨14275621964518391792016253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19034162619357855722688337 14275621964518391792016253)
    ·
      refine ⟨5353358236694396922006095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14275621964518391792016253 5353358236694396922006095)
      ·
        refine ⟨8030037355041595383009143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5353358236694396922006095 8030037355041595383009143)
        ·
          refine ⟨12045056032562393074513715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8030037355041595383009143 12045056032562393074513715)
          ·
            refine ⟨18067584048843589611770573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12045056032562393074513715 18067584048843589611770573)
            ·
              refine ⟨6775344018316346104413965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18067584048843589611770573 6775344018316346104413965)
              ·
                refine ⟨2540754006868629789155237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6775344018316346104413965 2540754006868629789155237)
                ·
                  refine ⟨476391376287868085466607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2540754006868629789155237 476391376287868085466607)
                  ·
                    rfl

theorem cell20_1043740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1043740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043740 prefixEnd_1043740 := by exact prefixLift 1043740
  have htrace : WordTrace (prefixWord ++ tailWord_1043740) baseStart_1043740 baseEnd_1043740 := by
    simpa [prefixWord, tailWord_1043740, baseEnd_1043740] using wordTrace_append hprefix tailTrace_1043740
  have hstable : (prefixWord ++ tailWord_1043740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043740).length < 2 ^ (prefixWord ++ tailWord_1043740).sum := by decide
  have hdescent : baseEnd_1043740 < baseStart_1043740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043764 : List Nat := [2, 5, 1, 1, 1, 1, 3, 6]
def baseStart_1043764 : Nat := 118140960795 + 1043764 * 2 ^ 59
def prefixEnd_1043764 : Nat := 4983230072969 + 3 ^ 40 * 1043764 * 2
def baseEnd_1043764 : Nat := 158800776847276889555503

theorem tailTrace_1043764 : CollatzResearch.WordTrace tailWord_1043764 prefixEnd_1043764 158800776847276889555503 := by
  unfold tailWord_1043764
  simp only [CollatzResearch.WordTrace]
  refine ⟨19034600295314381772125173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25379467060419175696166897 19034600295314381772125173)
  ·
    refine ⟨1784493777685723291136735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19034600295314381772125173 1784493777685723291136735)
    ·
      refine ⟨2676740666528584936705103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784493777685723291136735 2676740666528584936705103)
      ·
        refine ⟨4015110999792877405057655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676740666528584936705103 4015110999792877405057655)
        ·
          refine ⟨6022666499689316107586483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015110999792877405057655 6022666499689316107586483)
          ·
            refine ⟨9033999749533974161379725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022666499689316107586483 9033999749533974161379725)
            ·
              refine ⟨3387749906075240310517397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9033999749533974161379725 3387749906075240310517397)
              ·
                refine ⟨158800776847276889555503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3387749906075240310517397 158800776847276889555503)
                ·
                  rfl

theorem cell20_1043764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_1043764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043764 prefixEnd_1043764 := by exact prefixLift 1043764
  have htrace : WordTrace (prefixWord ++ tailWord_1043764) baseStart_1043764 baseEnd_1043764 := by
    simpa [prefixWord, tailWord_1043764, baseEnd_1043764] using wordTrace_append hprefix tailTrace_1043764
  have hstable : (prefixWord ++ tailWord_1043764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043764).length < 2 ^ (prefixWord ++ tailWord_1043764).sum := by decide
  have hdescent : baseEnd_1043764 < baseStart_1043764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043792 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1043792 : Nat := 118140960795 + 1043792 * 2 ^ 59
def prefixEnd_1043792 : Nat := 4983230072969 + 3 ^ 40 * 1043792 * 2
def baseEnd_1043792 : Nat := 476415110504787015733061

theorem tailTrace_1043792 : CollatzResearch.WordTrace tailWord_1043792 prefixEnd_1043792 476415110504787015733061 := by
  unfold tailWord_1043792
  simp only [CollatzResearch.WordTrace]
  refine ⟨19035110917263662163134815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25380147889684882884179753 19035110917263662163134815)
  ·
    refine ⟨28552666375895493244702223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19035110917263662163134815 28552666375895493244702223)
    ·
      refine ⟨42828999563843239867053335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28552666375895493244702223 42828999563843239867053335)
      ·
        refine ⟨64243499345764859800580003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42828999563843239867053335 64243499345764859800580003)
        ·
          refine ⟨96365249018647289700870005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64243499345764859800580003 96365249018647289700870005)
          ·
            refine ⟨9034242095498183409456563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96365249018647289700870005 9034242095498183409456563)
            ·
              refine ⟨13551363143247275114184845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9034242095498183409456563 13551363143247275114184845)
              ·
                refine ⟨5081761178717728167819317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13551363143247275114184845 5081761178717728167819317)
                ·
                  refine ⟨476415110504787015733061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5081761178717728167819317 476415110504787015733061)
                  ·
                    rfl

theorem cell20_1043792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1043792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043792 prefixEnd_1043792 := by exact prefixLift 1043792
  have htrace : WordTrace (prefixWord ++ tailWord_1043792) baseStart_1043792 baseEnd_1043792 := by
    simpa [prefixWord, tailWord_1043792, baseEnd_1043792] using wordTrace_append hprefix tailTrace_1043792
  have hstable : (prefixWord ++ tailWord_1043792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043792).length < 2 ^ (prefixWord ++ tailWord_1043792).sum := by decide
  have hdescent : baseEnd_1043792 < baseStart_1043792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043847 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 3]
def baseStart_1043847 : Nat := 118140960795 + 1043847 * 2 ^ 59
def prefixEnd_1043847 : Nat := 4983230072969 + 3 ^ 40 * 1043847 * 2
def baseEnd_1043847 : Nat := 476440214003451268899503

theorem tailTrace_1043847 : CollatzResearch.WordTrace tailWord_1043847 prefixEnd_1043847 476440214003451268899503 := by
  unfold tailWord_1043847
  simp only [CollatzResearch.WordTrace]
  refine ⟨38072227849328068719521795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25381485232885379146347863 38072227849328068719521795)
  ·
    refine ⟨57108341773992103079282693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38072227849328068719521795 57108341773992103079282693)
    ·
      refine ⟨10707814082623519327365505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57108341773992103079282693 10707814082623519327365505)
      ·
        refine ⟨8030860561967639495524129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10707814082623519327365505 8030860561967639495524129)
        ·
          refine ⟨6023145421475729621643097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8030860561967639495524129 6023145421475729621643097)
          ·
            refine ⟨4517359066106797216232323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6023145421475729621643097 4517359066106797216232323)
            ·
              refine ⟨6776038599160195824348485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517359066106797216232323 6776038599160195824348485)
              ·
                refine ⟨1270507237342536717065341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6776038599160195824348485 1270507237342536717065341)
                ·
                  refine ⟨476440214003451268899503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270507237342536717065341 476440214003451268899503)
                  ·
                    rfl

theorem cell20_1043847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_1043847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043847 prefixEnd_1043847 := by exact prefixLift 1043847
  have htrace : WordTrace (prefixWord ++ tailWord_1043847) baseStart_1043847 baseEnd_1043847 := by
    simpa [prefixWord, tailWord_1043847, baseEnd_1043847] using wordTrace_append hprefix tailTrace_1043847
  have hstable : (prefixWord ++ tailWord_1043847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043847).length < 2 ^ (prefixWord ++ tailWord_1043847).sum := by decide
  have hdescent : baseEnd_1043847 < baseStart_1043847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043861 : List Nat := [1, 3, 2, 1, 1, 2, 5, 5]
def baseStart_1043861 : Nat := 118140960795 + 1043861 * 2 ^ 59
def prefixEnd_1043861 : Nat := 4983230072969 + 3 ^ 40 * 1043861 * 2
def baseEnd_1043861 : Nat := 158815534661643147477593

theorem tailTrace_1043861 : CollatzResearch.WordTrace tailWord_1043861 prefixEnd_1043861 158815534661643147477593 := by
  unfold tailWord_1043861
  simp only [CollatzResearch.WordTrace]
  refine ⟨38072738471277349110531437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25381825647518232740354291 38072738471277349110531437)
  ·
    refine ⟨14277276926729005916449289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38072738471277349110531437 14277276926729005916449289)
    ·
      refine ⟨10707957695046754437336967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14277276926729005916449289 10707957695046754437336967)
      ·
        refine ⟨16061936542570131656005451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10707957695046754437336967 16061936542570131656005451)
        ·
          refine ⟨24092904813855197484008177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16061936542570131656005451 24092904813855197484008177)
          ·
            refine ⟨18069678610391398113006133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24092904813855197484008177 18069678610391398113006133)
            ·
              refine ⟨1694032369724193573094325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18069678610391398113006133 1694032369724193573094325)
              ·
                refine ⟨158815534661643147477593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1694032369724193573094325 158815534661643147477593)
                ·
                  rfl

theorem cell20_1043861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_1043861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043861 prefixEnd_1043861 := by exact prefixLift 1043861
  have htrace : WordTrace (prefixWord ++ tailWord_1043861) baseStart_1043861 baseEnd_1043861 := by
    simpa [prefixWord, tailWord_1043861, baseEnd_1043861] using wordTrace_append hprefix tailTrace_1043861
  have hstable : (prefixWord ++ tailWord_1043861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043861).length < 2 ^ (prefixWord ++ tailWord_1043861).sum := by decide
  have hdescent : baseEnd_1043861 < baseStart_1043861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043930 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_1043930 : Nat := 118140960795 + 1043930 * 2 ^ 59
def prefixEnd_1043930 : Nat := 4983230072969 + 3 ^ 40 * 1043930 * 2
def baseEnd_1043930 : Nat := 476478097465071869132497

theorem tailTrace_1043930 : CollatzResearch.WordTrace tailWord_1043930 prefixEnd_1043930 476478097465071869132497 := by
  unfold tailWord_1043930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518813777006843473698311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25383503405351582596528829 9518813777006843473698311)
  ·
    refine ⟨14278220665510265210547467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9518813777006843473698311 14278220665510265210547467)
    ·
      refine ⟨21417330998265397815821201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14278220665510265210547467 21417330998265397815821201)
      ·
        refine ⟨16062998248699048361865901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21417330998265397815821201 16062998248699048361865901)
        ·
          refine ⟨6023624343262143135699713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16062998248699048361865901 6023624343262143135699713)
          ·
            refine ⟨4517718257446607351774785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6023624343262143135699713 4517718257446607351774785)
            ·
              refine ⟨3388288693084955513831089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517718257446607351774785 3388288693084955513831089)
              ·
                refine ⟨2541216519813716635373317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388288693084955513831089 2541216519813716635373317)
                ·
                  refine ⟨476478097465071869132497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541216519813716635373317 476478097465071869132497)
                  ·
                    rfl

theorem cell20_1043930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_1043930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043930 prefixEnd_1043930 := by exact prefixLift 1043930
  have htrace : WordTrace (prefixWord ++ tailWord_1043930) baseStart_1043930 baseEnd_1043930 := by
    simpa [prefixWord, tailWord_1043930, baseEnd_1043930] using wordTrace_append hprefix tailTrace_1043930
  have hstable : (prefixWord ++ tailWord_1043930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043930).length < 2 ^ (prefixWord ++ tailWord_1043930).sum := by decide
  have hdescent : baseEnd_1043930 < baseStart_1043930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043933 : List Nat := [1, 4, 3, 1, 1, 4, 2, 4]
def baseStart_1043933 : Nat := 118140960795 + 1043933 * 2 ^ 59
def prefixEnd_1043933 : Nat := 4983230072969 + 3 ^ 40 * 1043933 * 2
def baseEnd_1043933 : Nat := 158826488915605730677495

theorem tailTrace_1043933 : CollatzResearch.WordTrace tailWord_1043933 prefixEnd_1043933 158826488915605730677495 := by
  unfold tailWord_1043933
  simp only [CollatzResearch.WordTrace]
  refine ⟨38075364527016505407152453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25383576351344336938101635 38075364527016505407152453)
  ·
    refine ⟨7139130848815594763841085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38075364527016505407152453 7139130848815594763841085)
    ·
      refine ⟨2677174068305848036440407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7139130848815594763841085 2677174068305848036440407)
      ·
        refine ⟨4015761102458772054660611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677174068305848036440407 4015761102458772054660611)
        ·
          refine ⟨6023641653688158081990917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015761102458772054660611 6023641653688158081990917)
          ·
            refine ⟨1129432810066529640373297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6023641653688158081990917 1129432810066529640373297)
            ·
              refine ⟨847074607549897230279973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129432810066529640373297 847074607549897230279973)
              ·
                refine ⟨158826488915605730677495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847074607549897230279973 158826488915605730677495)
                ·
                  rfl

theorem cell20_1043933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_1043933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043933 prefixEnd_1043933 := by exact prefixLift 1043933
  have htrace : WordTrace (prefixWord ++ tailWord_1043933) baseStart_1043933 baseEnd_1043933 := by
    simpa [prefixWord, tailWord_1043933, baseEnd_1043933] using wordTrace_append hprefix tailTrace_1043933
  have hstable : (prefixWord ++ tailWord_1043933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043933).length < 2 ^ (prefixWord ++ tailWord_1043933).sum := by decide
  have hdescent : baseEnd_1043933 < baseStart_1043933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043937 : List Nat := [1, 2, 3, 1, 2, 4, 1, 6]
def baseStart_1043937 : Nat := 118140960795 + 1043937 * 2 ^ 59
def prefixEnd_1043937 : Nat := 4983230072969 + 3 ^ 40 * 1043937 * 2
def baseEnd_1043937 : Nat := 158827097485270318633045

theorem tailTrace_1043937 : CollatzResearch.WordTrace tailWord_1043937 prefixEnd_1043937 158827097485270318633045 := by
  unfold tailWord_1043937
  simp only [CollatzResearch.WordTrace]
  refine ⟨38075510419002014090298065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25383673612668009393532043 38075510419002014090298065)
  ·
    refine ⟨28556632814251510567723549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38075510419002014090298065 28556632814251510567723549)
    ·
      refine ⟨10708737305344316462896331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28556632814251510567723549 10708737305344316462896331)
      ·
        refine ⟨16063105958016474694344497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10708737305344316462896331 16063105958016474694344497)
        ·
          refine ⟨12047329468512356020758373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16063105958016474694344497 12047329468512356020758373)
          ·
            refine ⟨2258874275346066753892195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12047329468512356020758373 2258874275346066753892195)
            ·
              refine ⟨3388311413019100130838293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2258874275346066753892195 3388311413019100130838293)
              ·
                refine ⟨158827097485270318633045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3388311413019100130838293 158827097485270318633045)
                ·
                  rfl

theorem cell20_1043937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_1043937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043937 prefixEnd_1043937 := by exact prefixLift 1043937
  have htrace : WordTrace (prefixWord ++ tailWord_1043937) baseStart_1043937 baseEnd_1043937 := by
    simpa [prefixWord, tailWord_1043937, baseEnd_1043937] using wordTrace_append hprefix tailTrace_1043937
  have hstable : (prefixWord ++ tailWord_1043937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043937).length < 2 ^ (prefixWord ++ tailWord_1043937).sum := by decide
  have hdescent : baseEnd_1043937 < baseStart_1043937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043944 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1043944 : Nat := 118140960795 + 1043944 * 2 ^ 59
def prefixEnd_1043944 : Nat := 4983230072969 + 3 ^ 40 * 1043944 * 2
def baseEnd_1043944 : Nat := 476484487446550042665773

theorem tailTrace_1043944 : CollatzResearch.WordTrace tailWord_1043944 prefixEnd_1043944 476484487446550042665773 := by
  unfold tailWord_1043944
  simp only [CollatzResearch.WordTrace]
  refine ⟨19037882864988327142901443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25383843819984436190535257 19037882864988327142901443)
  ·
    refine ⟨28556824297482490714352165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19037882864988327142901443 28556824297482490714352165)
    ·
      refine ⟨5354404555777967008941031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28556824297482490714352165 5354404555777967008941031)
      ·
        refine ⟨8031606833666950513411547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354404555777967008941031 8031606833666950513411547)
        ·
          refine ⟨12047410250500425770117321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031606833666950513411547 12047410250500425770117321)
          ·
            refine ⟨9035557687875319327587991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12047410250500425770117321 9035557687875319327587991)
            ·
              refine ⟨13553336531812978991381987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9035557687875319327587991 13553336531812978991381987)
              ·
                refine ⟨20330004797719468487072981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13553336531812978991381987 20330004797719468487072981)
                ·
                  refine ⟨476484487446550042665773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20330004797719468487072981 476484487446550042665773)
                  ·
                    rfl

theorem cell20_1043944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1043944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043944 prefixEnd_1043944 := by exact prefixLift 1043944
  have htrace : WordTrace (prefixWord ++ tailWord_1043944) baseStart_1043944 baseEnd_1043944 := by
    simpa [prefixWord, tailWord_1043944, baseEnd_1043944] using wordTrace_append hprefix tailTrace_1043944
  have hstable : (prefixWord ++ tailWord_1043944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043944).length < 2 ^ (prefixWord ++ tailWord_1043944).sum := by decide
  have hdescent : baseEnd_1043944 < baseStart_1043944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043951 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_1043951 : Nat := 118140960795 + 1043951 * 2 ^ 59
def prefixEnd_1043951 : Nat := 4983230072969 + 3 ^ 40 * 1043951 * 2
def baseEnd_1043951 : Nat := 476487682437289129432411

theorem tailTrace_1043951 : CollatzResearch.WordTrace tailWord_1043951 prefixEnd_1043951 476487682437289129432411 := by
  unfold tailWord_1043951
  simp only [CollatzResearch.WordTrace]
  refine ⟨38076021040951294481307707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25384014027300862987538471 38076021040951294481307707)
  ·
    refine ⟨57114031561426941721961561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38076021040951294481307707 57114031561426941721961561)
    ·
      refine ⟨42835523671070206291471171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57114031561426941721961561 42835523671070206291471171)
      ·
        refine ⟨64253285506605309437206757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42835523671070206291471171 64253285506605309437206757)
        ·
          refine ⟨12047491032488495519476267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64253285506605309437206757 12047491032488495519476267)
          ·
            refine ⟨18071236548732743279214401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12047491032488495519476267 18071236548732743279214401)
            ·
              refine ⟨13553427411549557459410801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18071236548732743279214401 13553427411549557459410801)
              ·
                refine ⟨10165070558662168094558101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13553427411549557459410801 10165070558662168094558101)
                ·
                  refine ⟨476487682437289129432411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10165070558662168094558101 476487682437289129432411)
                  ·
                    rfl

theorem cell20_1043951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_1043951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043951 prefixEnd_1043951 := by exact prefixLift 1043951
  have htrace : WordTrace (prefixWord ++ tailWord_1043951) baseStart_1043951 baseEnd_1043951 := by
    simpa [prefixWord, tailWord_1043951, baseEnd_1043951] using wordTrace_append hprefix tailTrace_1043951
  have hstable : (prefixWord ++ tailWord_1043951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043951).length < 2 ^ (prefixWord ++ tailWord_1043951).sum := by decide
  have hdescent : baseEnd_1043951 < baseStart_1043951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043954 : List Nat := [3, 2, 1, 4, 1, 3, 6]
def baseStart_1043954 : Nat := 118140960795 + 1043954 * 2 ^ 59
def prefixEnd_1043954 : Nat := 4983230072969 + 3 ^ 40 * 1043954 * 2
def baseEnd_1043954 : Nat := 52943227968781605814711

theorem tailTrace_1043954 : CollatzResearch.WordTrace tailWord_1043954 prefixEnd_1043954 52943227968781605814711 := by
  unfold tailWord_1043954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9519032614985106498416729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25384086973293617329111277 9519032614985106498416729)
  ·
    refine ⟨7139274461238829873812547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9519032614985106498416729 7139274461238829873812547)
    ·
      refine ⟨10708911691858244810718821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7139274461238829873812547 10708911691858244810718821)
      ·
        refine ⟨2007920942223420902009779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10708911691858244810718821 2007920942223420902009779)
        ·
          refine ⟨3011881413335131353014669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007920942223420902009779 3011881413335131353014669)
          ·
            refine ⟨1129455530000674257380501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3011881413335131353014669 1129455530000674257380501)
            ·
              refine ⟨52943227968781605814711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1129455530000674257380501 52943227968781605814711)
              ·
                rfl

theorem cell20_1043954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 6].length) (baseStart_1043954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043954 prefixEnd_1043954 := by exact prefixLift 1043954
  have htrace : WordTrace (prefixWord ++ tailWord_1043954) baseStart_1043954 baseEnd_1043954 := by
    simpa [prefixWord, tailWord_1043954, baseEnd_1043954] using wordTrace_append hprefix tailTrace_1043954
  have hstable : (prefixWord ++ tailWord_1043954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043954).length < 2 ^ (prefixWord ++ tailWord_1043954).sum := by decide
  have hdescent : baseEnd_1043954 < baseStart_1043954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043975 : List Nat := [1, 1, 4, 3, 2, 1, 1, 7]
def baseStart_1043975 : Nat := 118140960795 + 1043975 * 2 ^ 59
def prefixEnd_1043975 : Nat := 4983230072969 + 3 ^ 40 * 1043975 * 2
def baseEnd_1043975 : Nat := 158832878897083904210771

theorem tailTrace_1043975 : CollatzResearch.WordTrace tailWord_1043975 prefixEnd_1043975 158832878897083904210771 := by
  unfold tailWord_1043975
  simp only [CollatzResearch.WordTrace]
  refine ⟨38076896392864346580181379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25384597595242897720120919 38076896392864346580181379)
  ·
    refine ⟨57115344589296519870272069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38076896392864346580181379 57115344589296519870272069)
    ·
      refine ⟨10709127110493097475676013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57115344589296519870272069 10709127110493097475676013)
      ·
        refine ⟨4015922666434911553378505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10709127110493097475676013 4015922666434911553378505)
        ·
          refine ⟨3011941999826183665033879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4015922666434911553378505 3011941999826183665033879)
          ·
            refine ⟨4517912999739275497550819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011941999826183665033879 4517912999739275497550819)
            ·
              refine ⟨6776869499608913246326229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4517912999739275497550819 6776869499608913246326229)
              ·
                refine ⟨158832878897083904210771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6776869499608913246326229 158832878897083904210771)
                ·
                  rfl

theorem cell20_1043975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_1043975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043975 prefixEnd_1043975 := by exact prefixLift 1043975
  have htrace : WordTrace (prefixWord ++ tailWord_1043975) baseStart_1043975 baseEnd_1043975 := by
    simpa [prefixWord, tailWord_1043975, baseEnd_1043975] using wordTrace_append hprefix tailTrace_1043975
  have hstable : (prefixWord ++ tailWord_1043975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043975).length < 2 ^ (prefixWord ++ tailWord_1043975).sum := by decide
  have hdescent : baseEnd_1043975 < baseStart_1043975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1043978 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1043978 : Nat := 118140960795 + 1043978 * 2 ^ 59
def prefixEnd_1043978 : Nat := 4983230072969 + 3 ^ 40 * 1043978 * 2
def baseEnd_1043978 : Nat := 476500005972997035532301

theorem tailTrace_1043978 : CollatzResearch.WordTrace tailWord_1043978 prefixEnd_1043978 476500005972997035532301 := by
  unfold tailWord_1043978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9519251452963369523135147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25384670541235652061693725 9519251452963369523135147)
  ·
    refine ⟨14278877179445054284702721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9519251452963369523135147 14278877179445054284702721)
    ·
      refine ⟨10709157884583790713527041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14278877179445054284702721 10709157884583790713527041)
      ·
        refine ⟨8031868413437843035145281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10709157884583790713527041 8031868413437843035145281)
        ·
          refine ⟨6023901310078382276358961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8031868413437843035145281 6023901310078382276358961)
          ·
            refine ⟨4517925982558786707269221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6023901310078382276358961 4517925982558786707269221)
            ·
              refine ⟨847111121729772507612979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4517925982558786707269221 847111121729772507612979)
              ·
                refine ⟨1270666682594658761419469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847111121729772507612979 1270666682594658761419469)
                ·
                  refine ⟨476500005972997035532301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270666682594658761419469 476500005972997035532301)
                  ·
                    rfl

theorem cell20_1043978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1043978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1043978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1043978 prefixEnd_1043978 := by exact prefixLift 1043978
  have htrace : WordTrace (prefixWord ++ tailWord_1043978) baseStart_1043978 baseEnd_1043978 := by
    simpa [prefixWord, tailWord_1043978, baseEnd_1043978] using wordTrace_append hprefix tailTrace_1043978
  have hstable : (prefixWord ++ tailWord_1043978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1043978).length < 2 ^ (prefixWord ++ tailWord_1043978).sum := by decide
  have hdescent : baseEnd_1043978 < baseStart_1043978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1043978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044023 : List Nat := [1, 1, 3, 1, 2, 5, 1, 4, 2]
def baseStart_1044023 : Nat := 118140960795 + 1044023 * 2 ^ 59
def prefixEnd_1044023 : Nat := 4983230072969 + 3 ^ 40 * 1044023 * 2
def baseEnd_1044023 : Nat := 476520545199176879032117

theorem tailTrace_1044023 : CollatzResearch.WordTrace tailWord_1044023 prefixEnd_1044023 476520545199176879032117 := by
  unfold tailWord_1044023
  simp only [CollatzResearch.WordTrace]
  refine ⟨38078647096690450777928723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25385764731126967185285815 38078647096690450777928723)
  ·
    refine ⟨57117970645035676166893085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38078647096690450777928723 57117970645035676166893085)
    ·
      refine ⟨21419238991888378562584907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57117970645035676166893085 21419238991888378562584907)
      ·
        refine ⟨32128858487832567843877361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21419238991888378562584907 32128858487832567843877361)
        ·
          refine ⟨24096643865874425882908021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32128858487832567843877361 24096643865874425882908021)
          ·
            refine ⟨2259060362425727426522627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24096643865874425882908021 2259060362425727426522627)
            ·
              refine ⟨3388590543638591139783941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259060362425727426522627 3388590543638591139783941)
              ·
                refine ⟨635360726932235838709489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3388590543638591139783941 635360726932235838709489)
                ·
                  refine ⟨476520545199176879032117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635360726932235838709489 476520545199176879032117)
                  ·
                    rfl

theorem cell20_1044023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 2].length) (baseStart_1044023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044023 prefixEnd_1044023 := by exact prefixLift 1044023
  have htrace : WordTrace (prefixWord ++ tailWord_1044023) baseStart_1044023 baseEnd_1044023 := by
    simpa [prefixWord, tailWord_1044023, baseEnd_1044023] using wordTrace_append hprefix tailTrace_1044023
  have hstable : (prefixWord ++ tailWord_1044023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044023).length < 2 ^ (prefixWord ++ tailWord_1044023).sum := by decide
  have hdescent : baseEnd_1044023 < baseStart_1044023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044044 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1044044 : Nat := 118140960795 + 1044044 * 2 ^ 59
def prefixEnd_1044044 : Nat := 4983230072969 + 3 ^ 40 * 1044044 * 2
def baseEnd_1044044 : Nat := 476530130171394139332031

theorem tailTrace_1044044 : CollatzResearch.WordTrace tailWord_1044044 prefixEnd_1044044 476530130171394139332031 := by
  unfold tailWord_1044044
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039706514807185682221593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25386275353076247576295457 19039706514807185682221593)
  ·
    refine ⟨14279779886105389261666195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19039706514807185682221593 14279779886105389261666195)
    ·
      refine ⟨21419669829158083892499293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14279779886105389261666195 21419669829158083892499293)
      ·
        refine ⟨8032376185934281459687235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21419669829158083892499293 8032376185934281459687235)
        ·
          refine ⟨12048564278901422189530853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032376185934281459687235 12048564278901422189530853)
          ·
            refine ⟨2259105802294016660537035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12048564278901422189530853 2259105802294016660537035)
            ·
              refine ⟨3388658703441024990805553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259105802294016660537035 3388658703441024990805553)
              ·
                refine ⟨2541494027580768743104165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388658703441024990805553 2541494027580768743104165)
                ·
                  refine ⟨476530130171394139332031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541494027580768743104165 476530130171394139332031)
                  ·
                    rfl

theorem cell20_1044044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1044044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044044 prefixEnd_1044044 := by exact prefixLift 1044044
  have htrace : WordTrace (prefixWord ++ tailWord_1044044) baseStart_1044044 baseEnd_1044044 := by
    simpa [prefixWord, tailWord_1044044, baseEnd_1044044] using wordTrace_append hprefix tailTrace_1044044
  have hstable : (prefixWord ++ tailWord_1044044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044044).length < 2 ^ (prefixWord ++ tailWord_1044044).sum := by decide
  have hdescent : baseEnd_1044044 < baseStart_1044044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044065 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1044065 : Nat := 118140960795 + 1044065 * 2 ^ 59
def prefixEnd_1044065 : Nat := 4983230072969 + 3 ^ 40 * 1044065 * 2
def baseEnd_1044065 : Nat := 476539715143611399631945

theorem tailTrace_1044065 : CollatzResearch.WordTrace tailWord_1044065 prefixEnd_1044065 476539715143611399631945 := by
  unfold tailWord_1044065
  simp only [CollatzResearch.WordTrace]
  refine ⟨38080178962538291950957649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25386785975025527967305099 38080178962538291950957649)
  ·
    refine ⟨28560134221903718963218237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38080178962538291950957649 28560134221903718963218237)
    ·
      refine ⟨10710050333213894611206839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28560134221903718963218237 10710050333213894611206839)
      ·
        refine ⟨16065075499820841916810259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710050333213894611206839 16065075499820841916810259)
        ·
          refine ⟨24097613249731262875215389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16065075499820841916810259 24097613249731262875215389)
          ·
            refine ⟨9036604968649223578205771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24097613249731262875215389 9036604968649223578205771)
            ·
              refine ⟨13554907452973835367308657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9036604968649223578205771 13554907452973835367308657)
              ·
                refine ⟨10166180589730376525481493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13554907452973835367308657 10166180589730376525481493)
                ·
                  refine ⟨476539715143611399631945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10166180589730376525481493 476539715143611399631945)
                  ·
                    rfl

theorem cell20_1044065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1044065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044065 prefixEnd_1044065 := by exact prefixLift 1044065
  have htrace : WordTrace (prefixWord ++ tailWord_1044065) baseStart_1044065 baseEnd_1044065 := by
    simpa [prefixWord, tailWord_1044065, baseEnd_1044065] using wordTrace_append hprefix tailTrace_1044065
  have hstable : (prefixWord ++ tailWord_1044065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044065).length < 2 ^ (prefixWord ++ tailWord_1044065).sum := by decide
  have hdescent : baseEnd_1044065 < baseStart_1044065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044082 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1044082 : Nat := 118140960795 + 1044082 * 2 ^ 59
def prefixEnd_1044082 : Nat := 4983230072969 + 3 ^ 40 * 1044082 * 2
def baseEnd_1044082 : Nat := 476547474406834896065209

theorem tailTrace_1044082 : CollatzResearch.WordTrace tailWord_1044082 prefixEnd_1044082 476547474406834896065209 := by
  unfold tailWord_1044082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520199750869175963581625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25387199335651135902884333 9520199750869175963581625)
  ·
    refine ⟨7140149813151881972686219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9520199750869175963581625 7140149813151881972686219)
    ·
      refine ⟨10710224719727822959029329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7140149813151881972686219 10710224719727822959029329)
      ·
        refine ⟨8032668539795867219271997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10710224719727822959029329 8032668539795867219271997)
        ·
          refine ⟨3012250702423450207226999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8032668539795867219271997 3012250702423450207226999)
          ·
            refine ⟨4518376053635175310840499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012250702423450207226999 4518376053635175310840499)
            ·
              refine ⟨6777564080452762966260749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4518376053635175310840499 6777564080452762966260749)
              ·
                refine ⟨2541586530169786112347781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6777564080452762966260749 2541586530169786112347781)
                ·
                  refine ⟨476547474406834896065209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2541586530169786112347781 476547474406834896065209)
                  ·
                    rfl

theorem cell20_1044082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1044082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044082 prefixEnd_1044082 := by exact prefixLift 1044082
  have htrace : WordTrace (prefixWord ++ tailWord_1044082) baseStart_1044082 baseEnd_1044082 := by
    simpa [prefixWord, tailWord_1044082, baseEnd_1044082] using wordTrace_append hprefix tailTrace_1044082
  have hstable : (prefixWord ++ tailWord_1044082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044082).length < 2 ^ (prefixWord ++ tailWord_1044082).sum := by decide
  have hdescent : baseEnd_1044082 < baseStart_1044082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044106 : List Nat := [3, 1, 2, 3, 2, 1, 4, 4]
def baseStart_1044106 : Nat := 118140960795 + 1044106 * 2 ^ 59
def prefixEnd_1044106 : Nat := 4983230072969 + 3 ^ 40 * 1044106 * 2
def baseEnd_1044106 : Nat := 158852809553599159755037

theorem tailTrace_1044106 : CollatzResearch.WordTrace tailWord_1044106 prefixEnd_1044106 158852809553599159755037 := by
  unfold tailWord_1044106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520418588847438988300043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25387782903593170635466781 9520418588847438988300043)
  ·
    refine ⟨14280627883271158482450065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9520418588847438988300043 14280627883271158482450065)
    ·
      refine ⟨10710470912453368861837549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14280627883271158482450065 10710470912453368861837549)
      ·
        refine ⟨4016426592170013323189081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10710470912453368861837549 4016426592170013323189081)
        ·
          refine ⟨3012319944127509992391811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4016426592170013323189081 3012319944127509992391811)
          ·
            refine ⟨4518479916191264988587717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012319944127509992391811 4518479916191264988587717)
            ·
              refine ⟨847214984285862185360197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4518479916191264988587717 847214984285862185360197)
              ·
                refine ⟨158852809553599159755037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847214984285862185360197 158852809553599159755037)
                ·
                  rfl

theorem cell20_1044106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_1044106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044106 prefixEnd_1044106 := by exact prefixLift 1044106
  have htrace : WordTrace (prefixWord ++ tailWord_1044106) baseStart_1044106 baseEnd_1044106 := by
    simpa [prefixWord, tailWord_1044106, baseEnd_1044106] using wordTrace_append hprefix tailTrace_1044106
  have hstable : (prefixWord ++ tailWord_1044106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044106).length < 2 ^ (prefixWord ++ tailWord_1044106).sum := by decide
  have hdescent : baseEnd_1044106 < baseStart_1044106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044151 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 3]
def baseStart_1044151 : Nat := 118140960795 + 1044151 * 2 ^ 59
def prefixEnd_1044151 : Nat := 4983230072969 + 3 ^ 40 * 1044151 * 2
def baseEnd_1044151 : Nat := 476578967886977322764927

theorem tailTrace_1044151 : CollatzResearch.WordTrace tailWord_1044151 prefixEnd_1044151 476578967886977322764927 := by
  unfold tailWord_1044151
  simp only [CollatzResearch.WordTrace]
  refine ⟨38083315640226728638588307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25388877093484485759058871 38083315640226728638588307)
  ·
    refine ⟨57124973460340092957882461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38083315640226728638588307 57124973460340092957882461)
    ·
      refine ⟨21421865047627534859205923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57124973460340092957882461 21421865047627534859205923)
      ·
        refine ⟨32132797571441302288808885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21421865047627534859205923 32132797571441302288808885)
        ·
          refine ⟨3012449772322622089575833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32132797571441302288808885 3012449772322622089575833)
          ·
            refine ⟨2259337329241966567181875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012449772322622089575833 2259337329241966567181875)
            ·
              refine ⟨3389005993862949850772813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259337329241966567181875 3389005993862949850772813)
              ·
                refine ⟨1270877247698606194039805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3389005993862949850772813 1270877247698606194039805)
                ·
                  refine ⟨476578967886977322764927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1270877247698606194039805 476578967886977322764927)
                  ·
                    rfl

theorem cell20_1044151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 3].length) (baseStart_1044151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044151 prefixEnd_1044151 := by exact prefixLift 1044151
  have htrace : WordTrace (prefixWord ++ tailWord_1044151) baseStart_1044151 baseEnd_1044151 := by
    simpa [prefixWord, tailWord_1044151, baseEnd_1044151] using wordTrace_append hprefix tailTrace_1044151
  have hstable : (prefixWord ++ tailWord_1044151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044151).length < 2 ^ (prefixWord ++ tailWord_1044151).sum := by decide
  have hdescent : baseEnd_1044151 < baseStart_1044151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044182 : List Nat := [5, 2, 1, 3, 9]
def baseStart_1044182 : Nat := 118140960795 + 1044182 * 2 ^ 59
def prefixEnd_1044182 : Nat := 4983230072969 + 3 ^ 40 * 1044182 * 2
def baseEnd_1044182 : Nat := 5883865643600975218907

theorem tailTrace_1044182 : CollatzResearch.WordTrace tailWord_1044182 prefixEnd_1044182 5883865643600975218907 := by
  unfold tailWord_1044182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2380277893944651308310425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25389630868742947288644533 2380277893944651308310425)
  ·
    refine ⟨1785208420458488481232819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2380277893944651308310425 1785208420458488481232819)
    ·
      refine ⟨2677812630687732721849229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785208420458488481232819 2677812630687732721849229)
      ·
        refine ⟨1004179736507899770693461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2677812630687732721849229 1004179736507899770693461)
        ·
          refine ⟨5883865643600975218907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 1004179736507899770693461 5883865643600975218907)
          ·
            rfl

theorem cell20_1044182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 9].length) (baseStart_1044182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044182 prefixEnd_1044182 := by exact prefixLift 1044182
  have htrace : WordTrace (prefixWord ++ tailWord_1044182) baseStart_1044182 baseEnd_1044182 := by
    simpa [prefixWord, tailWord_1044182, baseEnd_1044182] using wordTrace_append hprefix tailTrace_1044182
  have hstable : (prefixWord ++ tailWord_1044182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044182).length < 2 ^ (prefixWord ++ tailWord_1044182).sum := by decide
  have hdescent : baseEnd_1044182 < baseStart_1044182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044186 : List Nat := [3, 1, 1, 2, 2, 11]
def baseStart_1044186 : Nat := 118140960795 + 1044186 * 2 ^ 59
def prefixEnd_1044186 : Nat := 4983230072969 + 3 ^ 40 * 1044186 * 2
def baseEnd_1044186 : Nat := 17651664549654546540671

theorem tailTrace_1044186 : CollatzResearch.WordTrace tailWord_1044186 prefixEnd_1044186 17651664549654546540671 := by
  unfold tailWord_1044186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9521148048774982404028103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25389728130066619744074941 9521148048774982404028103)
  ·
    refine ⟨14281722073162473606042155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9521148048774982404028103 14281722073162473606042155)
    ·
      refine ⟨21422583109743710409063233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14281722073162473606042155 21422583109743710409063233)
      ·
        refine ⟨16066937332307782806797425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21422583109743710409063233 16066937332307782806797425)
        ·
          refine ⟨12050202999230837105098069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16066937332307782806797425 12050202999230837105098069)
          ·
            refine ⟨17651664549654546540671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 12050202999230837105098069 17651664549654546540671)
            ·
              rfl

theorem cell20_1044186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 11].length) (baseStart_1044186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044186 prefixEnd_1044186 := by exact prefixLift 1044186
  have htrace : WordTrace (prefixWord ++ tailWord_1044186) baseStart_1044186 baseEnd_1044186 := by
    simpa [prefixWord, tailWord_1044186, baseEnd_1044186] using wordTrace_append hprefix tailTrace_1044186
  have hstable : (prefixWord ++ tailWord_1044186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044186).length < 2 ^ (prefixWord ++ tailWord_1044186).sum := by decide
  have hdescent : baseEnd_1044186 < baseStart_1044186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044188 : List Nat := [2, 2, 5, 1, 2, 2, 2, 2, 2]
def baseStart_1044188 : Nat := 118140960795 + 1044188 * 2 ^ 59
def prefixEnd_1044188 : Nat := 4983230072969 + 3 ^ 40 * 1044188 * 2
def baseEnd_1044188 : Nat := 476595855695169638531443

theorem tailTrace_1044188 : CollatzResearch.WordTrace tailWord_1044188 prefixEnd_1044188 476595855695169638531443 := by
  unfold tailWord_1044188
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042332570546341978842609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25389776760728455971790145 19042332570546341978842609)
  ·
    refine ⟨14281749427909756484131957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19042332570546341978842609 14281749427909756484131957)
    ·
      refine ⟨1338914008866539670387371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14281749427909756484131957 1338914008866539670387371)
      ·
        refine ⟨2008371013299809505581057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1338914008866539670387371 2008371013299809505581057)
        ·
          refine ⟨1506278259974857129185793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2008371013299809505581057 1506278259974857129185793)
          ·
            refine ⟨1129708694981142846889345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506278259974857129185793 1129708694981142846889345)
            ·
              refine ⟨847281521235857135167009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129708694981142846889345 847281521235857135167009)
              ·
                refine ⟨635461140926892851375257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847281521235857135167009 635461140926892851375257)
                ·
                  refine ⟨476595855695169638531443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635461140926892851375257 476595855695169638531443)
                  ·
                    rfl

theorem cell20_1044188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_1044188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044188 prefixEnd_1044188 := by exact prefixLift 1044188
  have htrace : WordTrace (prefixWord ++ tailWord_1044188) baseStart_1044188 baseEnd_1044188 := by
    simpa [prefixWord, tailWord_1044188, baseEnd_1044188] using wordTrace_append hprefix tailTrace_1044188
  have hstable : (prefixWord ++ tailWord_1044188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044188).length < 2 ^ (prefixWord ++ tailWord_1044188).sum := by decide
  have hdescent : baseEnd_1044188 < baseStart_1044188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044199 : List Nat := [1, 1, 5, 4, 1, 2, 1, 5]
def baseStart_1044199 : Nat := 118140960795 + 1044199 * 2 ^ 59
def prefixEnd_1044199 : Nat := 4983230072969 + 3 ^ 40 * 1044199 * 2
def baseEnd_1044199 : Nat := 158866958798300829721577

theorem tailTrace_1044199 : CollatzResearch.WordTrace tailWord_1044199 prefixEnd_1044199 158866958798300829721577 := by
  unfold tailWord_1044199
  simp only [CollatzResearch.WordTrace]
  refine ⟨38085066344052832836335651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25390044229368555224223767 38085066344052832836335651)
  ·
    refine ⟨57127599516079249254503477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38085066344052832836335651 57127599516079249254503477)
    ·
      refine ⟨5355712454632429617609701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57127599516079249254503477 5355712454632429617609701)
      ·
        refine ⟨1004196085243580553301819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5355712454632429617609701 1004196085243580553301819)
        ·
          refine ⟨1506294127865370829952729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004196085243580553301819 1506294127865370829952729)
          ·
            refine ⟨1129720595899028122464547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506294127865370829952729 1129720595899028122464547)
            ·
              refine ⟨1694580893848542183696821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129720595899028122464547 1694580893848542183696821)
              ·
                refine ⟨158866958798300829721577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1694580893848542183696821 158866958798300829721577)
                ·
                  rfl

theorem cell20_1044199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_1044199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044199 prefixEnd_1044199 := by exact prefixLift 1044199
  have htrace : WordTrace (prefixWord ++ tailWord_1044199) baseStart_1044199 baseEnd_1044199 := by
    simpa [prefixWord, tailWord_1044199, baseEnd_1044199] using wordTrace_append hprefix tailTrace_1044199
  have hstable : (prefixWord ++ tailWord_1044199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044199).length < 2 ^ (prefixWord ++ tailWord_1044199).sum := by decide
  have hdescent : baseEnd_1044199 < baseStart_1044199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044275 : List Nat := [1, 1, 1, 2, 8, 1, 2, 4]
def baseStart_1044275 : Nat := 118140960795 + 1044275 * 2 ^ 59
def prefixEnd_1044275 : Nat := 4983230072969 + 3 ^ 40 * 1044275 * 2
def baseEnd_1044275 : Nat := 158878521621928000877029

theorem tailTrace_1044275 : CollatzResearch.WordTrace tailWord_1044275 prefixEnd_1044275 158878521621928000877029 := by
  unfold tailWord_1044275
  simp only [CollatzResearch.WordTrace]
  refine ⟨38087838291777497816102279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25391892194518331877401519 38087838291777497816102279)
  ·
    refine ⟨57131757437666246724153419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38087838291777497816102279 57131757437666246724153419)
    ·
      refine ⟨85697636156499370086230129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57131757437666246724153419 85697636156499370086230129)
      ·
        refine ⟨64273227117374527564672597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85697636156499370086230129 64273227117374527564672597)
        ·
          refine ⟨753201880281732744898507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 64273227117374527564672597 753201880281732744898507)
          ·
            refine ⟨1129802820422599117347761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753201880281732744898507 1129802820422599117347761)
            ·
              refine ⟨847352115316949338010821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129802820422599117347761 847352115316949338010821)
              ·
                refine ⟨158878521621928000877029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847352115316949338010821 158878521621928000877029)
                ·
                  rfl

theorem cell20_1044275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 4].length) (baseStart_1044275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044275 prefixEnd_1044275 := by exact prefixLift 1044275
  have htrace : WordTrace (prefixWord ++ tailWord_1044275) baseStart_1044275 baseEnd_1044275 := by
    simpa [prefixWord, tailWord_1044275, baseEnd_1044275] using wordTrace_append hprefix tailTrace_1044275
  have hstable : (prefixWord ++ tailWord_1044275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044275).length < 2 ^ (prefixWord ++ tailWord_1044275).sum := by decide
  have hdescent : baseEnd_1044275 < baseStart_1044275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044306 : List Nat := [3, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_1044306 : Nat := 118140960795 + 1044306 * 2 ^ 59
def prefixEnd_1044306 : Nat := 4983230072969 + 3 ^ 40 * 1044306 * 2
def baseEnd_1044306 : Nat := 476649714110485672597627

theorem tailTrace_1044306 : CollatzResearch.WordTrace tailWord_1044306 prefixEnd_1044306 476649714110485672597627 := by
  unfold tailWord_1044306
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522242238666297527620193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25392645969776793406987181 9522242238666297527620193)
  ·
    refine ⟨7141681678999723145715145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9522242238666297527620193 7141681678999723145715145)
    ·
      refine ⟨5356261259249792359286359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7141681678999723145715145 5356261259249792359286359)
      ·
        refine ⟨8034391888874688538929539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5356261259249792359286359 8034391888874688538929539)
        ·
          refine ⟨12051587833312032808394309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8034391888874688538929539 12051587833312032808394309)
          ·
            refine ⟨2259672718746006151573933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12051587833312032808394309 2259672718746006151573933)
            ·
              refine ⟨847377269529752306840225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2259672718746006151573933 847377269529752306840225)
              ·
                refine ⟨635532952147314230130169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847377269529752306840225 635532952147314230130169)
                ·
                  refine ⟨476649714110485672597627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635532952147314230130169 476649714110485672597627)
                  ·
                    rfl

theorem cell20_1044306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_1044306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044306 prefixEnd_1044306 := by exact prefixLift 1044306
  have htrace : WordTrace (prefixWord ++ tailWord_1044306) baseStart_1044306 baseEnd_1044306 := by
    simpa [prefixWord, tailWord_1044306, baseEnd_1044306] using wordTrace_append hprefix tailTrace_1044306
  have hstable : (prefixWord ++ tailWord_1044306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044306).length < 2 ^ (prefixWord ++ tailWord_1044306).sum := by decide
  have hdescent : baseEnd_1044306 < baseStart_1044306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044316 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 3]
def baseStart_1044316 : Nat := 118140960795 + 1044316 * 2 ^ 59
def prefixEnd_1044316 : Nat := 4983230072969 + 3 ^ 40 * 1044316 * 2
def baseEnd_1044316 : Nat := 476654278382970082264253

theorem tailTrace_1044316 : CollatzResearch.WordTrace tailWord_1044316 prefixEnd_1044316 476654278382970082264253 := by
  unfold tailWord_1044316
  simp only [CollatzResearch.WordTrace]
  refine ⟨19044666842314480909172401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25392889123085974545563201 19044666842314480909172401)
  ·
    refine ⟨14283500131735860681879301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19044666842314480909172401 14283500131735860681879301)
    ·
      refine ⟨2678156274700473877852369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14283500131735860681879301 2678156274700473877852369)
      ·
        refine ⟨2008617206025355408389277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2678156274700473877852369 2008617206025355408389277)
        ·
          refine ⟨753231452259508278145979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2008617206025355408389277 753231452259508278145979)
          ·
            refine ⟨1129847178389262417218969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753231452259508278145979 1129847178389262417218969)
            ·
              refine ⟨847385383791946812914227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129847178389262417218969 847385383791946812914227)
              ·
                refine ⟨1271078075687920219371341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847385383791946812914227 1271078075687920219371341)
                ·
                  refine ⟨476654278382970082264253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271078075687920219371341 476654278382970082264253)
                  ·
                    rfl

theorem cell20_1044316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_1044316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044316 prefixEnd_1044316 := by exact prefixLift 1044316
  have htrace : WordTrace (prefixWord ++ tailWord_1044316) baseStart_1044316 baseEnd_1044316 := by
    simpa [prefixWord, tailWord_1044316, baseEnd_1044316] using wordTrace_append hprefix tailTrace_1044316
  have hstable : (prefixWord ++ tailWord_1044316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044316).length < 2 ^ (prefixWord ++ tailWord_1044316).sum := by decide
  have hdescent : baseEnd_1044316 < baseStart_1044316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044320 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_1044320 : Nat := 118140960795 + 1044320 * 2 ^ 59
def prefixEnd_1044320 : Nat := 4983230072969 + 3 ^ 40 * 1044320 * 2
def baseEnd_1044320 : Nat := 476656104091963846130903

theorem tailTrace_1044320 : CollatzResearch.WordTrace tailWord_1044320 prefixEnd_1044320 476656104091963846130903 := by
  unfold tailWord_1044320
  simp only [CollatzResearch.WordTrace]
  refine ⟨19044739788307235250745207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25392986384409647000993609 19044739788307235250745207)
  ·
    refine ⟨28567109682460852876117811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19044739788307235250745207 28567109682460852876117811)
    ·
      refine ⟨42850664523691279314176717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28567109682460852876117811 42850664523691279314176717)
      ·
        refine ⟨16068999196384229742816269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42850664523691279314176717 16068999196384229742816269)
        ·
          refine ⟨6025874698644086153556101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16068999196384229742816269 6025874698644086153556101)
          ·
            refine ⟨1129851505995766153791769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6025874698644086153556101 1129851505995766153791769)
            ·
              refine ⟨847388629496824615343827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129851505995766153791769 847388629496824615343827)
              ·
                refine ⟨1271082944245236923015741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847388629496824615343827 1271082944245236923015741)
                ·
                  refine ⟨476656104091963846130903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271082944245236923015741 476656104091963846130903)
                  ·
                    rfl

theorem cell20_1044320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_1044320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044320 prefixEnd_1044320 := by exact prefixLift 1044320
  have htrace : WordTrace (prefixWord ++ tailWord_1044320) baseStart_1044320 baseEnd_1044320 := by
    simpa [prefixWord, tailWord_1044320, baseEnd_1044320] using wordTrace_append hprefix tailTrace_1044320
  have hstable : (prefixWord ++ tailWord_1044320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044320).length < 2 ^ (prefixWord ++ tailWord_1044320).sum := by decide
  have hdescent : baseEnd_1044320 < baseStart_1044320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044372 : List Nat := [2, 4, 2, 1, 1, 4, 1, 5]
def baseStart_1044372 : Nat := 118140960795 + 1044372 * 2 ^ 59
def prefixEnd_1044372 : Nat := 4983230072969 + 3 ^ 40 * 1044372 * 2
def baseEnd_1044372 : Nat := 158893279436294258799119

theorem tailTrace_1044372 : CollatzResearch.WordTrace tailWord_1044372 prefixEnd_1044372 158893279436294258799119 := by
  unfold tailWord_1044372
  simp only [CollatzResearch.WordTrace]
  refine ⟨19045688086213041691191685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25394250781617388921588913 19045688086213041691191685)
  ·
    refine ⟨3571066516164945317098441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19045688086213041691191685 3571066516164945317098441)
    ·
      refine ⟨2678299887123708987823831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3571066516164945317098441 2678299887123708987823831)
      ·
        refine ⟨4017449830685563481735747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678299887123708987823831 4017449830685563481735747)
        ·
          refine ⟨6026174746028345222603621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017449830685563481735747 6026174746028345222603621)
          ·
            refine ⟨1129907764880314729238179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6026174746028345222603621 1129907764880314729238179)
            ·
              refine ⟨1694861647320472093857269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129907764880314729238179 1694861647320472093857269)
              ·
                refine ⟨158893279436294258799119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1694861647320472093857269 158893279436294258799119)
                ·
                  rfl

theorem cell20_1044372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_1044372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044372 prefixEnd_1044372 := by exact prefixLift 1044372
  have htrace : WordTrace (prefixWord ++ tailWord_1044372) baseStart_1044372 baseEnd_1044372 := by
    simpa [prefixWord, tailWord_1044372, baseEnd_1044372] using wordTrace_append hprefix tailTrace_1044372
  have hstable : (prefixWord ++ tailWord_1044372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044372).length < 2 ^ (prefixWord ++ tailWord_1044372).sum := by decide
  have hdescent : baseEnd_1044372 < baseStart_1044372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044382 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1044382 : Nat := 118140960795 + 1044382 * 2 ^ 59
def prefixEnd_1044382 : Nat := 4983230072969 + 3 ^ 40 * 1044382 * 2
def baseEnd_1044382 : Nat := 476684402581367186063983

theorem tailTrace_1044382 : CollatzResearch.WordTrace tailWord_1044382 prefixEnd_1044382 476684402581367186063983 := by
  unfold tailWord_1044382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4761467612798731886280925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25394493934926570060164933 4761467612798731886280925)
  ·
    refine ⟨1785550354799524457355347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4761467612798731886280925 1785550354799524457355347)
    ·
      refine ⟨2678325532199286686033021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785550354799524457355347 2678325532199286686033021)
      ·
        refine ⟨1004372074574732507262383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2678325532199286686033021 1004372074574732507262383)
        ·
          refine ⟨1506558111862098760893575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004372074574732507262383 1506558111862098760893575)
          ·
            refine ⟨2259837167793148141340363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506558111862098760893575 2259837167793148141340363)
            ·
              refine ⟨3389755751689722212010545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259837167793148141340363 3389755751689722212010545)
              ·
                refine ⟨2542316813767291659007909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3389755751689722212010545 2542316813767291659007909)
                ·
                  refine ⟨476684402581367186063983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542316813767291659007909 476684402581367186063983)
                  ·
                    rfl

theorem cell20_1044382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1044382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044382 prefixEnd_1044382 := by exact prefixLift 1044382
  have htrace : WordTrace (prefixWord ++ tailWord_1044382) baseStart_1044382 baseEnd_1044382 := by
    simpa [prefixWord, tailWord_1044382, baseEnd_1044382] using wordTrace_append hprefix tailTrace_1044382
  have hstable : (prefixWord ++ tailWord_1044382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044382).length < 2 ^ (prefixWord ++ tailWord_1044382).sum := by decide
  have hdescent : baseEnd_1044382 < baseStart_1044382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044424 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_1044424 : Nat := 118140960795 + 1044424 * 2 ^ 59
def prefixEnd_1044424 : Nat := 4983230072969 + 3 ^ 40 * 1044424 * 2
def baseEnd_1044424 : Nat := 476703572525801706663811

theorem tailTrace_1044424 : CollatzResearch.WordTrace tailWord_1044424 prefixEnd_1044424 476703572525801706663811 := by
  unfold tailWord_1044424
  simp only [CollatzResearch.WordTrace]
  refine ⟨19046636384118848131638163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25395515178825130842184217 19046636384118848131638163)
  ·
    refine ⟨28569954576178272197457245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19046636384118848131638163 28569954576178272197457245)
    ·
      refine ⟨10713732966066852074046467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28569954576178272197457245 10713732966066852074046467)
      ·
        refine ⟨16070599449100278111069701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10713732966066852074046467 16070599449100278111069701)
        ·
          refine ⟨3013237396706302145825569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16070599449100278111069701 3013237396706302145825569)
          ·
            refine ⟨2259928047529726609369177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3013237396706302145825569 2259928047529726609369177)
            ·
              refine ⟨1694946035647294957026883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259928047529726609369177 1694946035647294957026883)
              ·
                refine ⟨2542419053470942435540325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1694946035647294957026883 2542419053470942435540325)
                ·
                  refine ⟨476703572525801706663811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2542419053470942435540325 476703572525801706663811)
                  ·
                    rfl

theorem cell20_1044424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_1044424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044424 prefixEnd_1044424 := by exact prefixLift 1044424
  have htrace : WordTrace (prefixWord ++ tailWord_1044424) baseStart_1044424 baseEnd_1044424 := by
    simpa [prefixWord, tailWord_1044424, baseEnd_1044424] using wordTrace_append hprefix tailTrace_1044424
  have hstable : (prefixWord ++ tailWord_1044424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044424).length < 2 ^ (prefixWord ++ tailWord_1044424).sum := by decide
  have hdescent : baseEnd_1044424 < baseStart_1044424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044452 : List Nat := [2, 3, 1, 1, 1, 1, 5, 6]
def baseStart_1044452 : Nat := 118140960795 + 1044452 * 2 ^ 59
def prefixEnd_1044452 : Nat := 4983230072969 + 3 ^ 40 * 1044452 * 2
def baseEnd_1044452 : Nat := 158905450829586017910121

theorem tailTrace_1044452 : CollatzResearch.WordTrace tailWord_1044452 prefixEnd_1044452 158905450829586017910121 := by
  unfold tailWord_1044452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19047147006068128522647805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25396196008090838030197073 19047147006068128522647805)
  ·
    refine ⟨7142680127275548195992927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19047147006068128522647805 7142680127275548195992927)
    ·
      refine ⟨10714020190913322293989391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7142680127275548195992927 10714020190913322293989391)
      ·
        refine ⟨16071030286369983440984087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10714020190913322293989391 16071030286369983440984087)
        ·
          refine ⟨24106545429554975161476131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16071030286369983440984087 24106545429554975161476131)
          ·
            refine ⟨36159818144332462742214197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24106545429554975161476131 36159818144332462742214197)
            ·
              refine ⟨3389982951031168382082581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36159818144332462742214197 3389982951031168382082581)
              ·
                refine ⟨158905450829586017910121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3389982951031168382082581 158905450829586017910121)
                ·
                  rfl

theorem cell20_1044452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_1044452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044452 prefixEnd_1044452 := by exact prefixLift 1044452
  have htrace : WordTrace (prefixWord ++ tailWord_1044452) baseStart_1044452 baseEnd_1044452 := by
    simpa [prefixWord, tailWord_1044452, baseEnd_1044452] using wordTrace_append hprefix tailTrace_1044452
  have hstable : (prefixWord ++ tailWord_1044452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044452).length < 2 ^ (prefixWord ++ tailWord_1044452).sum := by decide
  have hdescent : baseEnd_1044452 < baseStart_1044452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044476 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1044476 : Nat := 118140960795 + 1044476 * 2 ^ 59
def prefixEnd_1044476 : Nat := 4983230072969 + 3 ^ 40 * 1044476 * 2
def baseEnd_1044476 : Nat := 476727306742720636930265

theorem tailTrace_1044476 : CollatzResearch.WordTrace tailWord_1044476 prefixEnd_1044476 476727306742720636930265 := by
  unfold tailWord_1044476
  simp only [CollatzResearch.WordTrace]
  refine ⟨19047584682024654572084641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25396779576032872762779521 19047584682024654572084641)
  ·
    refine ⟨14285688511518490929063481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19047584682024654572084641 14285688511518490929063481)
    ·
      refine ⟨10714266383638868196797611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14285688511518490929063481 10714266383638868196797611)
      ·
        refine ⟨16071399575458302295196417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10714266383638868196797611 16071399575458302295196417)
        ·
          refine ⟨12053549681593726721397313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16071399575458302295196417 12053549681593726721397313)
          ·
            refine ⟨9040162261195295041047985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12053549681593726721397313 9040162261195295041047985)
            ·
              refine ⟨6780121695896471280785989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9040162261195295041047985 6780121695896471280785989)
              ·
                refine ⟨1271272817980588365147373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6780121695896471280785989 1271272817980588365147373)
                ·
                  refine ⟨476727306742720636930265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271272817980588365147373 476727306742720636930265)
                  ·
                    rfl

theorem cell20_1044476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1044476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044476 prefixEnd_1044476 := by exact prefixLift 1044476
  have htrace : WordTrace (prefixWord ++ tailWord_1044476) baseStart_1044476 baseEnd_1044476 := by
    simpa [prefixWord, tailWord_1044476, baseEnd_1044476] using wordTrace_append hprefix tailTrace_1044476
  have hstable : (prefixWord ++ tailWord_1044476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044476).length < 2 ^ (prefixWord ++ tailWord_1044476).sum := by decide
  have hdescent : baseEnd_1044476 < baseStart_1044476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044535 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_1044535 : Nat := 118140960795 + 1044535 * 2 ^ 59
def prefixEnd_1044535 : Nat := 4983230072969 + 3 ^ 40 * 1044535 * 2
def baseEnd_1044535 : Nat := 476754235950378653963357

theorem tailTrace_1044535 : CollatzResearch.WordTrace tailWord_1044535 prefixEnd_1044535 476754235950378653963357 := by
  unfold tailWord_1044535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38097321270835562220567059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25398214180557041480378039 38097321270835562220567059)
  ·
    refine ⟨57145981906253343330850589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38097321270835562220567059 57145981906253343330850589)
    ·
      refine ⟨21429743214845003749068971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57145981906253343330850589 21429743214845003749068971)
      ·
        refine ⟨32144614822267505623603457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21429743214845003749068971 32144614822267505623603457)
        ·
          refine ⟨24108461116700629217702593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32144614822267505623603457 24108461116700629217702593)
          ·
            refine ⟨18081345837525471913276945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24108461116700629217702593 18081345837525471913276945)
            ·
              refine ⟨13561009378144103934957709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18081345837525471913276945 13561009378144103934957709)
              ·
                refine ⟨5085378516804038975609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13561009378144103934957709 5085378516804038975609141)
                ·
                  refine ⟨476754235950378653963357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085378516804038975609141 476754235950378653963357)
                  ·
                    rfl

theorem cell20_1044535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_1044535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044535 prefixEnd_1044535 := by exact prefixLift 1044535
  have htrace : WordTrace (prefixWord ++ tailWord_1044535) baseStart_1044535 baseEnd_1044535 := by
    simpa [prefixWord, tailWord_1044535, baseEnd_1044535] using wordTrace_append hprefix tailTrace_1044535
  have hstable : (prefixWord ++ tailWord_1044535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044535).length < 2 ^ (prefixWord ++ tailWord_1044535).sum := by decide
  have hdescent : baseEnd_1044535 < baseStart_1044535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044545 : List Nat := [1, 2, 5, 1, 2, 1, 3, 5]
def baseStart_1044545 : Nat := 118140960795 + 1044545 * 2 ^ 59
def prefixEnd_1044545 : Nat := 4983230072969 + 3 ^ 40 * 1044545 * 2
def baseEnd_1044545 : Nat := 158919600074287687876661

theorem tailTrace_1044545 : CollatzResearch.WordTrace tailWord_1044545 prefixEnd_1044545 158919600074287687876661 := by
  unfold tailWord_1044545
  simp only [CollatzResearch.WordTrace]
  refine ⟨38097686000799333928431089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25398457333866222618954059 38097686000799333928431089)
  ·
    refine ⟨28573264500599500446323317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38097686000799333928431089 28573264500599500446323317)
    ·
      refine ⟨2678743546931203166842811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28573264500599500446323317 2678743546931203166842811)
      ·
        refine ⟨4018115320396804750264217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678743546931203166842811 4018115320396804750264217)
        ·
          refine ⟨3013586490297603562698163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4018115320396804750264217 3013586490297603562698163)
          ·
            refine ⟨4520379735446405344047245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013586490297603562698163 4520379735446405344047245)
            ·
              refine ⟨1695142400792402004017717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4520379735446405344047245 1695142400792402004017717)
              ·
                refine ⟨158919600074287687876661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1695142400792402004017717 158919600074287687876661)
                ·
                  rfl

theorem cell20_1044545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_1044545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044545 prefixEnd_1044545 := by exact prefixLift 1044545
  have htrace : WordTrace (prefixWord ++ tailWord_1044545) baseStart_1044545 baseEnd_1044545 := by
    simpa [prefixWord, tailWord_1044545, baseEnd_1044545] using wordTrace_append hprefix tailTrace_1044545
  have hstable : (prefixWord ++ tailWord_1044545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044545).length < 2 ^ (prefixWord ++ tailWord_1044545).sum := by decide
  have hdescent : baseEnd_1044545 < baseStart_1044545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044562 : List Nat := [3, 2, 2, 1, 4, 1, 3, 4]
def baseStart_1044562 : Nat := 118140960795 + 1044562 * 2 ^ 59
def prefixEnd_1044562 : Nat := 4983230072969 + 3 ^ 40 * 1044562 * 2
def baseEnd_1044562 : Nat := 158922186495362186687749

theorem tailTrace_1044562 : CollatzResearch.WordTrace tailWord_1044562 prefixEnd_1044562 158922186495362186687749 := by
  unfold tailWord_1044562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524576510434436457949985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25398870694491830554533293 9524576510434436457949985)
  ·
    refine ⟨7143432382825827343462489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9524576510434436457949985 7143432382825827343462489)
    ·
      refine ⟨5357574287119370507596867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7143432382825827343462489 5357574287119370507596867)
      ·
        refine ⟨8036361430679055761395301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5357574287119370507596867 8036361430679055761395301)
        ·
          refine ⟨1506817768252322955261619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8036361430679055761395301 1506817768252322955261619)
          ·
            refine ⟨2260226652378484432892429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506817768252322955261619 2260226652378484432892429)
            ·
              refine ⟨847584994641931662334661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260226652378484432892429 847584994641931662334661)
              ·
                refine ⟨158922186495362186687749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847584994641931662334661 158922186495362186687749)
                ·
                  rfl

theorem cell20_1044562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_1044562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044562 prefixEnd_1044562 := by exact prefixLift 1044562
  have htrace : WordTrace (prefixWord ++ tailWord_1044562) baseStart_1044562 baseEnd_1044562 := by
    simpa [prefixWord, tailWord_1044562, baseEnd_1044562] using wordTrace_append hprefix tailTrace_1044562
  have hstable : (prefixWord ++ tailWord_1044562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044562).length < 2 ^ (prefixWord ++ tailWord_1044562).sum := by decide
  have hdescent : baseEnd_1044562 < baseStart_1044562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044576 : List Nat := [2, 1, 1, 3, 2, 3, 1, 5, 2]
def baseStart_1044576 : Nat := 118140960795 + 1044576 * 2 ^ 59
def prefixEnd_1044576 : Nat := 4983230072969 + 3 ^ 40 * 1044576 * 2
def baseEnd_1044576 : Nat := 476772949467564733596523

theorem tailTrace_1044576 : CollatzResearch.WordTrace tailWord_1044576 prefixEnd_1044576 476772949467564733596523 := by
  unfold tailWord_1044576
  simp only [CollatzResearch.WordTrace]
  refine ⟨19049408331843513111404791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25399211109124684148539721 19049408331843513111404791)
  ·
    refine ⟨28574112497765269667107187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19049408331843513111404791 28574112497765269667107187)
    ·
      refine ⟨42861168746647904500660781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28574112497765269667107187 42861168746647904500660781)
      ·
        refine ⟨16072938279992964187747793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42861168746647904500660781 16072938279992964187747793)
        ·
          refine ⟨12054703709994723140810845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16072938279992964187747793 12054703709994723140810845)
          ·
            refine ⟨4520513891248021177804067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12054703709994723140810845 4520513891248021177804067)
            ·
              refine ⟨6780770836872031766706101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4520513891248021177804067 6780770836872031766706101)
              ·
                refine ⟨635697265956752978128697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6780770836872031766706101 635697265956752978128697)
                ·
                  refine ⟨476772949467564733596523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635697265956752978128697 476772949467564733596523)
                  ·
                    rfl

theorem cell20_1044576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_1044576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044576 prefixEnd_1044576 := by exact prefixLift 1044576
  have htrace : WordTrace (prefixWord ++ tailWord_1044576) baseStart_1044576 baseEnd_1044576 := by
    simpa [prefixWord, tailWord_1044576, baseEnd_1044576] using wordTrace_append hprefix tailTrace_1044576
  have hstable : (prefixWord ++ tailWord_1044576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044576).length < 2 ^ (prefixWord ++ tailWord_1044576).sum := by decide
  have hdescent : baseEnd_1044576 < baseStart_1044576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044586 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_1044586 : Nat := 118140960795 + 1044586 * 2 ^ 59
def prefixEnd_1044586 : Nat := 4983230072969 + 3 ^ 40 * 1044586 * 2
def baseEnd_1044586 : Nat := 476777513740049143263149

theorem tailTrace_1044586 : CollatzResearch.WordTrace tailWord_1044586 prefixEnd_1044586 476777513740049143263149 := by
  unfold tailWord_1044586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524795348412699482668403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25399454262433865287115741 9524795348412699482668403)
  ·
    refine ⟨14287193022619049224002605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9524795348412699482668403 14287193022619049224002605)
    ·
      refine ⟨5357697383482143459000977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14287193022619049224002605 5357697383482143459000977)
      ·
        refine ⟨4018273037611607594250733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5357697383482143459000977 4018273037611607594250733)
        ·
          refine ⟨1506852389104352847844025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4018273037611607594250733 1506852389104352847844025)
          ·
            refine ⟨1130139291828264635883019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506852389104352847844025 1130139291828264635883019)
            ·
              refine ⟨1695208937742396953824529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130139291828264635883019 1695208937742396953824529)
              ·
                refine ⟨1271406703306797715368397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695208937742396953824529 1271406703306797715368397)
                ·
                  refine ⟨476777513740049143263149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271406703306797715368397 476777513740049143263149)
                  ·
                    rfl

theorem cell20_1044586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_1044586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044586 prefixEnd_1044586 := by exact prefixLift 1044586
  have htrace : WordTrace (prefixWord ++ tailWord_1044586) baseStart_1044586 baseEnd_1044586 := by
    simpa [prefixWord, tailWord_1044586, baseEnd_1044586] using wordTrace_append hprefix tailTrace_1044586
  have hstable : (prefixWord ++ tailWord_1044586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044586).length < 2 ^ (prefixWord ++ tailWord_1044586).sum := by decide
  have hdescent : baseEnd_1044586 < baseStart_1044586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044590 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1044590 : Nat := 118140960795 + 1044590 * 2 ^ 59
def prefixEnd_1044590 : Nat := 4983230072969 + 3 ^ 40 * 1044590 * 2
def baseEnd_1044590 : Nat := 476779339449042907129799

theorem tailTrace_1044590 : CollatzResearch.WordTrace tailWord_1044590 prefixEnd_1044590 476779339449042907129799 := by
  unfold tailWord_1044590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762415910704538326727403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25399551523757537742546149 4762415910704538326727403)
  ·
    refine ⟨7143623866056807490091105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4762415910704538326727403 7143623866056807490091105)
    ·
      refine ⟨5357717899542605617568329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7143623866056807490091105 5357717899542605617568329)
      ·
        refine ⟨4018288424656954213176247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5357717899542605617568329 4018288424656954213176247)
        ·
          refine ⟨6027432636985431319764371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018288424656954213176247 6027432636985431319764371)
          ·
            refine ⟨9041148955478146979646557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6027432636985431319764371 9041148955478146979646557)
            ·
              refine ⟨3390430858304305117367459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9041148955478146979646557 3390430858304305117367459)
              ·
                refine ⟨5085646287456457676051189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3390430858304305117367459 5085646287456457676051189)
                ·
                  refine ⟨476779339449042907129799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5085646287456457676051189 476779339449042907129799)
                  ·
                    rfl

theorem cell20_1044590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1044590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044590 prefixEnd_1044590 := by exact prefixLift 1044590
  have htrace : WordTrace (prefixWord ++ tailWord_1044590) baseStart_1044590 baseEnd_1044590 := by
    simpa [prefixWord, tailWord_1044590, baseEnd_1044590] using wordTrace_append hprefix tailTrace_1044590
  have hstable : (prefixWord ++ tailWord_1044590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044590).length < 2 ^ (prefixWord ++ tailWord_1044590).sum := by decide
  have hdescent : baseEnd_1044590 < baseStart_1044590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044638 : List Nat := [4, 3, 1, 1, 3, 2, 6]
def baseStart_1044638 : Nat := 118140960795 + 1044638 * 2 ^ 59
def prefixEnd_1044638 : Nat := 4983230072969 + 3 ^ 40 * 1044638 * 2
def baseEnd_1044638 : Nat := 52977916439663119281067

theorem tailTrace_1044638 : CollatzResearch.WordTrace tailWord_1044638 prefixEnd_1044638 52977916439663119281067 := by
  unfold tailWord_1044638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762634748682801351445821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25400718659641607207711045 4762634748682801351445821)
  ·
    refine ⟨1785988030756050506792183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4762634748682801351445821 1785988030756050506792183)
    ·
      refine ⟨2678982046134075760188275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785988030756050506792183 2678982046134075760188275)
      ·
        refine ⟨4018473069201113640282413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678982046134075760188275 4018473069201113640282413)
        ·
          refine ⟨1506927400950417615105905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4018473069201113640282413 1506927400950417615105905)
          ·
            refine ⟨1130195550712813211329429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506927400950417615105905 1130195550712813211329429)
            ·
              refine ⟨52977916439663119281067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1130195550712813211329429 52977916439663119281067)
              ·
                rfl

theorem cell20_1044638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 6].length) (baseStart_1044638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044638 prefixEnd_1044638 := by exact prefixLift 1044638
  have htrace : WordTrace (prefixWord ++ tailWord_1044638) baseStart_1044638 baseEnd_1044638 := by
    simpa [prefixWord, tailWord_1044638, baseEnd_1044638] using wordTrace_append hprefix tailTrace_1044638
  have hstable : (prefixWord ++ tailWord_1044638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044638).length < 2 ^ (prefixWord ++ tailWord_1044638).sum := by decide
  have hdescent : baseEnd_1044638 < baseStart_1044638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044704 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_1044704 : Nat := 118140960795 + 1044704 * 2 ^ 59
def prefixEnd_1044704 : Nat := 4983230072969 + 3 ^ 40 * 1044704 * 2
def baseEnd_1044704 : Nat := 476831372155365177329333

theorem tailTrace_1044704 : CollatzResearch.WordTrace tailWord_1044704 prefixEnd_1044704 476831372155365177329333 := by
  unfold tailWord_1044704
  simp only [CollatzResearch.WordTrace]
  refine ⟨19051742603611652041734583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25402323471482202722312777 19051742603611652041734583)
  ·
    refine ⟨28577613905417478062601875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19051742603611652041734583 28577613905417478062601875)
    ·
      refine ⟨42866420858126217093902813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28577613905417478062601875 42866420858126217093902813)
      ·
        refine ⟨16074907821797331410213555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42866420858126217093902813 16074907821797331410213555)
        ·
          refine ⟨24112361732695997115320333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16074907821797331410213555 24112361732695997115320333)
          ·
            refine ⟨9042135649760998918245125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24112361732695997115320333 9042135649760998918245125)
            ·
              refine ⟨1695400434330187297170961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9042135649760998918245125 1695400434330187297170961)
              ·
                refine ⟨1271550325747640472878221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695400434330187297170961 1271550325747640472878221)
                ·
                  refine ⟨476831372155365177329333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271550325747640472878221 476831372155365177329333)
                  ·
                    rfl

theorem cell20_1044704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_1044704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044704 prefixEnd_1044704 := by exact prefixLift 1044704
  have htrace : WordTrace (prefixWord ++ tailWord_1044704) baseStart_1044704 baseEnd_1044704 := by
    simpa [prefixWord, tailWord_1044704, baseEnd_1044704] using wordTrace_append hprefix tailTrace_1044704
  have hstable : (prefixWord ++ tailWord_1044704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044704).length < 2 ^ (prefixWord ++ tailWord_1044704).sum := by decide
  have hdescent : baseEnd_1044704 < baseStart_1044704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044759 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 3]
def baseStart_1044759 : Nat := 118140960795 + 1044759 * 2 ^ 59
def prefixEnd_1044759 : Nat := 4983230072969 + 3 ^ 40 * 1044759 * 2
def baseEnd_1044759 : Nat := 476856475654029430495775

theorem tailTrace_1044759 : CollatzResearch.WordTrace tailWord_1044759 prefixEnd_1044759 476856475654029430495775 := by
  unfold tailWord_1044759
  simp only [CollatzResearch.WordTrace]
  refine ⟨38105491222024048476721331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25403660814682698984480887 38105491222024048476721331)
  ·
    refine ⟨57158236833036072715081997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38105491222024048476721331 57158236833036072715081997)
    ·
      refine ⟨21434338812388527268155749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57158236833036072715081997 21434338812388527268155749)
      ·
        refine ⟨4018938527322848862779203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21434338812388527268155749 4018938527322848862779203)
        ·
          refine ⟨6028407790984273294168805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4018938527322848862779203 6028407790984273294168805)
          ·
            refine ⟨1130326460809551242656651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6028407790984273294168805 1130326460809551242656651)
            ·
              refine ⟨1695489691214326863984977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130326460809551242656651 1695489691214326863984977)
              ·
                refine ⟨1271617268410745147988733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695489691214326863984977 1271617268410745147988733)
                ·
                  refine ⟨476856475654029430495775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271617268410745147988733 476856475654029430495775)
                  ·
                    rfl

theorem cell20_1044759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_1044759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044759 prefixEnd_1044759 := by exact prefixLift 1044759
  have htrace : WordTrace (prefixWord ++ tailWord_1044759) baseStart_1044759 baseEnd_1044759 := by
    simpa [prefixWord, tailWord_1044759, baseEnd_1044759] using wordTrace_append hprefix tailTrace_1044759
  have hstable : (prefixWord ++ tailWord_1044759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044759).length < 2 ^ (prefixWord ++ tailWord_1044759).sum := by decide
  have hdescent : baseEnd_1044759 < baseStart_1044759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044776 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_1044776 : Nat := 118140960795 + 1044776 * 2 ^ 59
def prefixEnd_1044776 : Nat := 4983230072969 + 3 ^ 40 * 1044776 * 2
def baseEnd_1044776 : Nat := 476864234917252926929039

theorem tailTrace_1044776 : CollatzResearch.WordTrace tailWord_1044776 prefixEnd_1044776 476864234917252926929039 := by
  unfold tailWord_1044776
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053055631481230190045091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25404074175308306920060121 19053055631481230190045091)
  ·
    refine ⟨28579583447221845285067637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19053055631481230190045091 28579583447221845285067637)
    ·
      refine ⟨2679335948177047995475091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28579583447221845285067637 2679335948177047995475091)
      ·
        refine ⟨4019003922265571993212637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679335948177047995475091 4019003922265571993212637)
        ·
          refine ⟨1507126470849589497454739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4019003922265571993212637 1507126470849589497454739)
          ·
            refine ⟨2260689706274384246182109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507126470849589497454739 2260689706274384246182109)
            ·
              refine ⟨847758639852894092318291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260689706274384246182109 847758639852894092318291)
              ·
                refine ⟨1271637959779341138477437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847758639852894092318291 1271637959779341138477437)
                ·
                  refine ⟨476864234917252926929039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271637959779341138477437 476864234917252926929039)
                  ·
                    rfl

theorem cell20_1044776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_1044776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044776 prefixEnd_1044776 := by exact prefixLift 1044776
  have htrace : WordTrace (prefixWord ++ tailWord_1044776) baseStart_1044776 baseEnd_1044776 := by
    simpa [prefixWord, tailWord_1044776, baseEnd_1044776] using wordTrace_append hprefix tailTrace_1044776
  have hstable : (prefixWord ++ tailWord_1044776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044776).length < 2 ^ (prefixWord ++ tailWord_1044776).sum := by decide
  have hdescent : baseEnd_1044776 < baseStart_1044776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044794 : List Nat := [3, 1, 1, 1, 4, 3, 1, 6]
def baseStart_1044794 : Nat := 118140960795 + 1044794 * 2 ^ 59
def prefixEnd_1044794 : Nat := 4983230072969 + 3 ^ 40 * 1044794 * 2
def baseEnd_1044794 : Nat := 158957483535908288109655

theorem tailTrace_1044794 : CollatzResearch.WordTrace tailWord_1044794 prefixEnd_1044794 158957483535908288109655 := by
  unfold tailWord_1044794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526691944224312363561359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25404511851264832969496957 9526691944224312363561359)
  ·
    refine ⟨14290037916336468545342039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9526691944224312363561359 14290037916336468545342039)
    ·
      refine ⟨21435056874504702818013059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14290037916336468545342039 21435056874504702818013059)
      ·
        refine ⟨32152585311757054227019589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21435056874504702818013059 32152585311757054227019589)
        ·
          refine ⟨6028609745954447667566173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32152585311757054227019589 6028609745954447667566173)
          ·
            refine ⟨2260728654732917875337315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6028609745954447667566173 2260728654732917875337315)
            ·
              refine ⟨3391092982099376813005973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260728654732917875337315 3391092982099376813005973)
              ·
                refine ⟨158957483535908288109655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3391092982099376813005973 158957483535908288109655)
                ·
                  rfl

theorem cell20_1044794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_1044794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044794 prefixEnd_1044794 := by exact prefixLift 1044794
  have htrace : WordTrace (prefixWord ++ tailWord_1044794) baseStart_1044794 baseEnd_1044794 := by
    simpa [prefixWord, tailWord_1044794, baseEnd_1044794] using wordTrace_append hprefix tailTrace_1044794
  have hstable : (prefixWord ++ tailWord_1044794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044794).length < 2 ^ (prefixWord ++ tailWord_1044794).sum := by decide
  have hdescent : baseEnd_1044794 < baseStart_1044794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044808 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1044808 : Nat := 118140960795 + 1044808 * 2 ^ 59
def prefixEnd_1044808 : Nat := 4983230072969 + 3 ^ 40 * 1044808 * 2
def baseEnd_1044808 : Nat := 476878840589203037862241

theorem tailTrace_1044808 : CollatzResearch.WordTrace tailWord_1044808 prefixEnd_1044808 476878840589203037862241 := by
  unfold tailWord_1044808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053639199423264922627539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25404852265897686563503385 19053639199423264922627539)
  ·
    refine ⟨28580458799134897383941309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19053639199423264922627539 28580458799134897383941309)
    ·
      refine ⟨10717672049675586518977991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28580458799134897383941309 10717672049675586518977991)
      ·
        refine ⟨16076508074513379778466987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10717672049675586518977991 16076508074513379778466987)
        ·
          refine ⟨24114762111770069667700481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16076508074513379778466987 24114762111770069667700481)
          ·
            refine ⟨18086071583827552250775361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24114762111770069667700481 18086071583827552250775361)
            ·
              refine ⟨13564553687870664188081521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18086071583827552250775361 13564553687870664188081521)
              ·
                refine ⟨10173415265902998141061141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13564553687870664188081521 10173415265902998141061141)
                ·
                  refine ⟨476878840589203037862241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10173415265902998141061141 476878840589203037862241)
                  ·
                    rfl

theorem cell20_1044808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1044808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044808 prefixEnd_1044808 := by exact prefixLift 1044808
  have htrace : WordTrace (prefixWord ++ tailWord_1044808) baseStart_1044808 baseEnd_1044808 := by
    simpa [prefixWord, tailWord_1044808, baseEnd_1044808] using wordTrace_append hprefix tailTrace_1044808
  have hstable : (prefixWord ++ tailWord_1044808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044808).length < 2 ^ (prefixWord ++ tailWord_1044808).sum := by decide
  have hdescent : baseEnd_1044808 < baseStart_1044808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044821 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 4]
def baseStart_1044821 : Nat := 118140960795 + 1044821 * 2 ^ 59
def prefixEnd_1044821 : Nat := 4983230072969 + 3 ^ 40 * 1044821 * 2
def baseEnd_1044821 : Nat := 476884774143432770428855

theorem tailTrace_1044821 : CollatzResearch.WordTrace tailWord_1044821 prefixEnd_1044821 476884774143432770428855 := by
  unfold tailWord_1044821
  simp only [CollatzResearch.WordTrace]
  refine ⟨38107752547799433065478317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25405168365199622043652211 38107752547799433065478317)
  ·
    refine ⟨14290407205424787399554369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38107752547799433065478317 14290407205424787399554369)
    ·
      refine ⟨10717805404068590549665777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14290407205424787399554369 10717805404068590549665777)
      ·
        refine ⟨8038354053051442912249333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10717805404068590549665777 8038354053051442912249333)
        ·
          refine ⟨753595692473572773023375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8038354053051442912249333 753595692473572773023375)
          ·
            refine ⟨1130393538710359159535063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753595692473572773023375 1130393538710359159535063)
            ·
              refine ⟨1695590308065538739302595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130393538710359159535063 1695590308065538739302595)
              ·
                refine ⟨2543385462098308108953893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1695590308065538739302595 2543385462098308108953893)
                ·
                  refine ⟨476884774143432770428855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543385462098308108953893 476884774143432770428855)
                  ·
                    rfl

theorem cell20_1044821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_1044821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044821 prefixEnd_1044821 := by exact prefixLift 1044821
  have htrace : WordTrace (prefixWord ++ tailWord_1044821) baseStart_1044821 baseEnd_1044821 := by
    simpa [prefixWord, tailWord_1044821, baseEnd_1044821] using wordTrace_append hprefix tailTrace_1044821
  have hstable : (prefixWord ++ tailWord_1044821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044821).length < 2 ^ (prefixWord ++ tailWord_1044821).sum := by decide
  have hdescent : baseEnd_1044821 < baseStart_1044821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044828 : List Nat := [2, 2, 4, 3, 1, 1, 2, 5]
def baseStart_1044828 : Nat := 118140960795 + 1044828 * 2 ^ 59
def prefixEnd_1044828 : Nat := 4983230072969 + 3 ^ 40 * 1044828 * 2
def baseEnd_1044828 : Nat := 158962656378057285731831

theorem tailTrace_1044828 : CollatzResearch.WordTrace tailWord_1044828 prefixEnd_1044828 158962656378057285731831 := by
  unfold tailWord_1044828
  simp only [CollatzResearch.WordTrace]
  refine ⟨19054003929387036630491569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25405338572516048840655425 19054003929387036630491569)
  ·
    refine ⟨14290502947040277472868677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19054003929387036630491569 14290502947040277472868677)
    ·
      refine ⟨2679469302570052026162877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14290502947040277472868677 2679469302570052026162877)
      ·
        refine ⟨1004800988463769509811079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2679469302570052026162877 1004800988463769509811079)
        ·
          refine ⟨1507201482695654264716619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004800988463769509811079 1507201482695654264716619)
          ·
            refine ⟨2260802224043481397074929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507201482695654264716619 2260802224043481397074929)
            ·
              refine ⟨1695601668032611047806197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2260802224043481397074929 1695601668032611047806197)
              ·
                refine ⟨158962656378057285731831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1695601668032611047806197 158962656378057285731831)
                ·
                  rfl

theorem cell20_1044828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_1044828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044828 prefixEnd_1044828 := by exact prefixLift 1044828
  have htrace : WordTrace (prefixWord ++ tailWord_1044828) baseStart_1044828 baseEnd_1044828 := by
    simpa [prefixWord, tailWord_1044828, baseEnd_1044828] using wordTrace_append hprefix tailTrace_1044828
  have hstable : (prefixWord ++ tailWord_1044828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044828).length < 2 ^ (prefixWord ++ tailWord_1044828).sum := by decide
  have hdescent : baseEnd_1044828 < baseStart_1044828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044866 : List Nat := [3, 4, 2, 1, 3, 7]
def baseStart_1044866 : Nat := 118140960795 + 1044866 * 2 ^ 59
def prefixEnd_1044866 : Nat := 4983230072969 + 3 ^ 40 * 1044866 * 2
def baseEnd_1044866 : Nat := 17663159754430096812173

theorem tailTrace_1044866 : CollatzResearch.WordTrace tailWord_1044866 prefixEnd_1044866 17663159754430096812173 := by
  unfold tailWord_1044866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527348458159101437716613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25406262555090937167244301 9527348458159101437716613)
  ·
    refine ⟨1786377835904831519571865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9527348458159101437716613 1786377835904831519571865)
    ·
      refine ⟨1339783376928623639678899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1786377835904831519571865 1339783376928623639678899)
      ·
        refine ⟨2009675065392935459518349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339783376928623639678899 2009675065392935459518349)
        ·
          refine ⟨753628149522350797319381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2009675065392935459518349 753628149522350797319381)
          ·
            refine ⟨17663159754430096812173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 753628149522350797319381 17663159754430096812173)
            ·
              rfl

theorem cell20_1044866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 7].length) (baseStart_1044866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044866 prefixEnd_1044866 := by exact prefixLift 1044866
  have htrace : WordTrace (prefixWord ++ tailWord_1044866) baseStart_1044866 baseEnd_1044866 := by
    simpa [prefixWord, tailWord_1044866, baseEnd_1044866] using wordTrace_append hprefix tailTrace_1044866
  have hstable : (prefixWord ++ tailWord_1044866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044866).length < 2 ^ (prefixWord ++ tailWord_1044866).sum := by decide
  have hdescent : baseEnd_1044866 < baseStart_1044866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044904 : List Nat := [2, 1, 6, 1, 1, 2, 3, 4]
def baseStart_1044904 : Nat := 118140960795 + 1044904 * 2 ^ 59
def prefixEnd_1044904 : Nat := 4983230072969 + 3 ^ 40 * 1044904 * 2
def baseEnd_1044904 : Nat := 158974219201684456887283

theorem tailTrace_1044904 : CollatzResearch.WordTrace tailWord_1044904 prefixEnd_1044904 158974219201684456887283 := by
  unfold tailWord_1044904
  simp only [CollatzResearch.WordTrace]
  refine ⟨19055389903249369120374883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25407186537665825493833177 19055389903249369120374883)
  ·
    refine ⟨28583084854874053680562325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19055389903249369120374883 28583084854874053680562325)
    ·
      refine ⟨1339832102572221266276359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28583084854874053680562325 1339832102572221266276359)
      ·
        refine ⟨2009748153858331899414539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339832102572221266276359 2009748153858331899414539)
        ·
          refine ⟨3014622230787497849121809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009748153858331899414539 3014622230787497849121809)
          ·
            refine ⟨2260966673090623386841357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014622230787497849121809 2260966673090623386841357)
            ·
              refine ⟨847862502408983770065509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260966673090623386841357 847862502408983770065509)
              ·
                refine ⟨158974219201684456887283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847862502408983770065509 158974219201684456887283)
                ·
                  rfl

theorem cell20_1044904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 4].length) (baseStart_1044904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044904 prefixEnd_1044904 := by exact prefixLift 1044904
  have htrace : WordTrace (prefixWord ++ tailWord_1044904) baseStart_1044904 baseEnd_1044904 := by
    simpa [prefixWord, tailWord_1044904, baseEnd_1044904] using wordTrace_append hprefix tailTrace_1044904
  have hstable : (prefixWord ++ tailWord_1044904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044904).length < 2 ^ (prefixWord ++ tailWord_1044904).sum := by decide
  have hdescent : baseEnd_1044904 < baseStart_1044904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044949 : List Nat := [1, 3, 2, 3, 1, 3, 3, 1, 3]
def baseStart_1044949 : Nat := 118140960795 + 1044949 * 2 ^ 59
def prefixEnd_1044949 : Nat := 4983230072969 + 3 ^ 40 * 1044949 * 2
def baseEnd_1044949 : Nat := 476943196831233214161665

theorem tailTrace_1044949 : CollatzResearch.WordTrace tailWord_1044949 prefixEnd_1044949 476943196831233214161665 := by
  unfold tailWord_1044949
  simp only [CollatzResearch.WordTrace]
  refine ⟨38112421091335710926137901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25408280727557140617425267 38112421091335710926137901)
  ·
    refine ⟨14292157909250891597301713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38112421091335710926137901 14292157909250891597301713)
    ·
      refine ⟨10719118431938168697976285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14292157909250891597301713 10719118431938168697976285)
      ·
        refine ⟨4019669411976813261741107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10719118431938168697976285 4019669411976813261741107)
        ·
          refine ⟨6029504117965219892611661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4019669411976813261741107 6029504117965219892611661)
          ·
            refine ⟨2261064044236957459729373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6029504117965219892611661 2261064044236957459729373)
            ·
              refine ⟨847899016588859047398515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2261064044236957459729373 847899016588859047398515)
              ·
                refine ⟨1271848524883288571097773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847899016588859047398515 1271848524883288571097773)
                ·
                  refine ⟨476943196831233214161665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271848524883288571097773 476943196831233214161665)
                  ·
                    rfl

theorem cell20_1044949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_1044949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044949 prefixEnd_1044949 := by exact prefixLift 1044949
  have htrace : WordTrace (prefixWord ++ tailWord_1044949) baseStart_1044949 baseEnd_1044949 := by
    simpa [prefixWord, tailWord_1044949, baseEnd_1044949] using wordTrace_append hprefix tailTrace_1044949
  have hstable : (prefixWord ++ tailWord_1044949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044949).length < 2 ^ (prefixWord ++ tailWord_1044949).sum := by decide
  have hdescent : baseEnd_1044949 < baseStart_1044949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044960 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_1044960 : Nat := 118140960795 + 1044960 * 2 ^ 59
def prefixEnd_1044960 : Nat := 4983230072969 + 3 ^ 40 * 1044960 * 2
def baseEnd_1044960 : Nat := 476948217530966064794953

theorem tailTrace_1044960 : CollatzResearch.WordTrace tailWord_1044960 prefixEnd_1044960 476948217530966064794953 := by
  unfold tailWord_1044960
  simp only [CollatzResearch.WordTrace]
  refine ⟨19056411147147929902394167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25408548196197239869858889 19056411147147929902394167)
  ·
    refine ⟨28584616720721894853591251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19056411147147929902394167 28584616720721894853591251)
    ·
      refine ⟨42876925081082842280386877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28584616720721894853591251 42876925081082842280386877)
      ·
        refine ⟨16078846905406065855145079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42876925081082842280386877 16078846905406065855145079)
        ·
          refine ⟨24118270358109098782717619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16078846905406065855145079 24118270358109098782717619)
          ·
            refine ⟨36177405537163648174076429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24118270358109098782717619 36177405537163648174076429)
            ·
              refine ⟨13566527076436368065278661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36177405537163648174076429 13566527076436368065278661)
              ·
                refine ⟨2543723826831819012239749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13566527076436368065278661 2543723826831819012239749)
                ·
                  refine ⟨476948217530966064794953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2543723826831819012239749 476948217530966064794953)
                  ·
                    rfl

theorem cell20_1044960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_1044960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044960 prefixEnd_1044960 := by exact prefixLift 1044960
  have htrace : WordTrace (prefixWord ++ tailWord_1044960) baseStart_1044960 baseEnd_1044960 := by
    simpa [prefixWord, tailWord_1044960, baseEnd_1044960] using wordTrace_append hprefix tailTrace_1044960
  have hstable : (prefixWord ++ tailWord_1044960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044960).length < 2 ^ (prefixWord ++ tailWord_1044960).sum := by decide
  have hdescent : baseEnd_1044960 < baseStart_1044960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044973 : List Nat := [1, 5, 1, 3, 1, 1, 3, 3, 2]
def baseStart_1044973 : Nat := 118140960795 + 1044973 * 2 ^ 59
def prefixEnd_1044973 : Nat := 4983230072969 + 3 ^ 40 * 1044973 * 2
def baseEnd_1044973 : Nat := 476954151085195797361567

theorem tailTrace_1044973 : CollatzResearch.WordTrace tailWord_1044973 prefixEnd_1044973 476954151085195797361567 := by
  unfold tailWord_1044973
  simp only [CollatzResearch.WordTrace]
  refine ⟨38113296443248763025011573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25408864295499175350007715 38113296443248763025011573)
  ·
    refine ⟨3573121541554571533594835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38113296443248763025011573 3573121541554571533594835)
    ·
      refine ⟨5359682312331857300392253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573121541554571533594835 5359682312331857300392253)
      ·
        refine ⟨2009880867124446487647095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5359682312331857300392253 2009880867124446487647095)
        ·
          refine ⟨3014821300686669731470643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009880867124446487647095 3014821300686669731470643)
          ·
            refine ⟨4522231951030004597205965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3014821300686669731470643 4522231951030004597205965)
            ·
              refine ⟨1695836981636251723952237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4522231951030004597205965 1695836981636251723952237)
              ·
                refine ⟨635938868113594396482089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1695836981636251723952237 635938868113594396482089)
                ·
                  refine ⟨476954151085195797361567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635938868113594396482089 476954151085195797361567)
                  ·
                    rfl

theorem cell20_1044973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_1044973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044973 prefixEnd_1044973 := by exact prefixLift 1044973
  have htrace : WordTrace (prefixWord ++ tailWord_1044973) baseStart_1044973 baseEnd_1044973 := by
    simpa [prefixWord, tailWord_1044973, baseEnd_1044973] using wordTrace_append hprefix tailTrace_1044973
  have hstable : (prefixWord ++ tailWord_1044973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044973).length < 2 ^ (prefixWord ++ tailWord_1044973).sum := by decide
  have hdescent : baseEnd_1044973 < baseStart_1044973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1044991 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 3]
def baseStart_1044991 : Nat := 118140960795 + 1044991 * 2 ^ 59
def prefixEnd_1044991 : Nat := 4983230072969 + 3 ^ 40 * 1044991 * 2
def baseEnd_1044991 : Nat := 476962366775667734761493

theorem tailTrace_1044991 : CollatzResearch.WordTrace tailWord_1044991 prefixEnd_1044991 476962366775667734761493 := by
  unfold tailWord_1044991
  simp only [CollatzResearch.WordTrace]
  refine ⟨38113952957183552099166827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25409301971455701399444551 38113952957183552099166827)
  ·
    refine ⟨57170929435775328148750241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38113952957183552099166827 57170929435775328148750241)
    ·
      refine ⟨42878197076831496111562681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57170929435775328148750241 42878197076831496111562681)
      ·
        refine ⟨32158647807623622083672011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42878197076831496111562681 32158647807623622083672011)
        ·
          refine ⟨48237971711435433125508017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32158647807623622083672011 48237971711435433125508017)
          ·
            refine ⟨36178478783576574844131013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48237971711435433125508017 36178478783576574844131013)
            ·
              refine ⟨6783464771920607783274565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36178478783576574844131013 6783464771920607783274565)
              ·
                refine ⟨1271899644735113959363981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6783464771920607783274565 1271899644735113959363981)
                ·
                  refine ⟨476962366775667734761493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271899644735113959363981 476962366775667734761493)
                  ·
                    rfl

theorem cell20_1044991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 3].length) (baseStart_1044991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1044991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1044991 prefixEnd_1044991 := by exact prefixLift 1044991
  have htrace : WordTrace (prefixWord ++ tailWord_1044991) baseStart_1044991 baseEnd_1044991 := by
    simpa [prefixWord, tailWord_1044991, baseEnd_1044991] using wordTrace_append hprefix tailTrace_1044991
  have hstable : (prefixWord ++ tailWord_1044991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1044991).length < 2 ^ (prefixWord ++ tailWord_1044991).sum := by decide
  have hdescent : baseEnd_1044991 < baseStart_1044991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1044991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045067 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 3]
def baseStart_1045067 : Nat := 118140960795 + 1045067 * 2 ^ 59
def prefixEnd_1045067 : Nat := 4983230072969 + 3 ^ 40 * 1045067 * 2
def baseEnd_1045067 : Nat := 476997055246549248227849

theorem tailTrace_1045067 : CollatzResearch.WordTrace tailWord_1045067 prefixEnd_1045067 476997055246549248227849 := by
  unfold tailWord_1045067
  simp only [CollatzResearch.WordTrace]
  refine ⟨38116724904908217078933455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25411149936605478052622303 38116724904908217078933455)
  ·
    refine ⟨57175087357362325618400183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38116724904908217078933455 57175087357362325618400183)
    ·
      refine ⟨85762631036043488427600275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57175087357362325618400183 85762631036043488427600275)
      ·
        refine ⟨128643946554065232641400413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85762631036043488427600275 128643946554065232641400413)
        ·
          refine ⟨48241479957774462240525155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128643946554065232641400413 48241479957774462240525155)
          ·
            refine ⟨72362219936661693360787733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48241479957774462240525155 72362219936661693360787733)
            ·
              refine ⟨3391979059531016876286925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72362219936661693360787733 3391979059531016876286925)
              ·
                refine ⟨1271992147324131328607597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3391979059531016876286925 1271992147324131328607597)
                ·
                  refine ⟨476997055246549248227849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1271992147324131328607597 476997055246549248227849)
                  ·
                    rfl

theorem cell20_1045067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_1045067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045067 prefixEnd_1045067 := by exact prefixLift 1045067
  have htrace : WordTrace (prefixWord ++ tailWord_1045067) baseStart_1045067 baseEnd_1045067 := by
    simpa [prefixWord, tailWord_1045067, baseEnd_1045067] using wordTrace_append hprefix tailTrace_1045067
  have hstable : (prefixWord ++ tailWord_1045067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045067).length < 2 ^ (prefixWord ++ tailWord_1045067).sum := by decide
  have hdescent : baseEnd_1045067 < baseStart_1045067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045101 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1045101 : Nat := 118140960795 + 1045101 * 2 ^ 59
def prefixEnd_1045101 : Nat := 4983230072969 + 3 ^ 40 * 1045101 * 2
def baseEnd_1045101 : Nat := 477012573772996241094377

theorem tailTrace_1045101 : CollatzResearch.WordTrace tailWord_1045101 prefixEnd_1045101 477012573772996241094377 := by
  unfold tailWord_1045101
  simp only [CollatzResearch.WordTrace]
  refine ⟨38117964986785040885671157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25411976657856693923780771 38117964986785040885671157)
  ·
    refine ⟨3573559217511097583031671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38117964986785040885671157 3573559217511097583031671)
    ·
      refine ⟨5360338826266646374547507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573559217511097583031671 5360338826266646374547507)
      ·
        refine ⟨8040508239399969561821261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360338826266646374547507 8040508239399969561821261)
        ·
          refine ⟨3015190589774988585682973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8040508239399969561821261 3015190589774988585682973)
          ·
            refine ⟨1130696471165620719631115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3015190589774988585682973 1130696471165620719631115)
            ·
              refine ⟨1696044706748431079446673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130696471165620719631115 1696044706748431079446673)
              ·
                refine ⟨1272033530061323309585005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696044706748431079446673 1272033530061323309585005)
                ·
                  refine ⟨477012573772996241094377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272033530061323309585005 477012573772996241094377)
                  ·
                    rfl

theorem cell20_1045101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1045101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045101 prefixEnd_1045101 := by exact prefixLift 1045101
  have htrace : WordTrace (prefixWord ++ tailWord_1045101) baseStart_1045101 baseEnd_1045101 := by
    simpa [prefixWord, tailWord_1045101, baseEnd_1045101] using wordTrace_append hprefix tailTrace_1045101
  have hstable : (prefixWord ++ tailWord_1045101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045101).length < 2 ^ (prefixWord ++ tailWord_1045101).sum := by decide
  have hdescent : baseEnd_1045101 < baseStart_1045101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045153 : List Nat := [1, 2, 3, 3, 4, 1, 6]
def baseStart_1045153 : Nat := 118140960795 + 1045153 * 2 ^ 59
def prefixEnd_1045153 : Nat := 4983230072969 + 3 ^ 40 * 1045153 * 2
def baseEnd_1045153 : Nat := 53004034221101685706759

theorem tailTrace_1045153 : CollatzResearch.WordTrace tailWord_1045153 prefixEnd_1045153 53004034221101685706759 := by
  unfold tailWord_1045153
  simp only [CollatzResearch.WordTrace]
  refine ⟨38119861582596653766564113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25413241055064435844376075 38119861582596653766564113)
  ·
    refine ⟨28589896186947490324923085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38119861582596653766564113 28589896186947490324923085)
    ·
      refine ⟨10721211070105308871846157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28589896186947490324923085 10721211070105308871846157)
      ·
        refine ⟨4020454151289490826942309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10721211070105308871846157 4020454151289490826942309)
        ·
          refine ⟨753835153366779530051683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4020454151289490826942309 753835153366779530051683)
          ·
            refine ⟨1130752730050169295077525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753835153366779530051683 1130752730050169295077525)
            ·
              refine ⟨53004034221101685706759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1130752730050169295077525 53004034221101685706759)
              ·
                rfl

theorem cell20_1045153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 6].length) (baseStart_1045153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045153 prefixEnd_1045153 := by exact prefixLift 1045153
  have htrace : WordTrace (prefixWord ++ tailWord_1045153) baseStart_1045153 baseEnd_1045153 := by
    simpa [prefixWord, tailWord_1045153, baseEnd_1045153] using wordTrace_append hprefix tailTrace_1045153
  have hstable : (prefixWord ++ tailWord_1045153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045153).length < 2 ^ (prefixWord ++ tailWord_1045153).sum := by decide
  have hdescent : baseEnd_1045153 < baseStart_1045153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045167 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 4]
def baseStart_1045167 : Nat := 118140960795 + 1045167 * 2 ^ 59
def prefixEnd_1045167 : Nat := 4983230072969 + 3 ^ 40 * 1045167 * 2
def baseEnd_1045167 : Nat := 477042697971393344894107

theorem tailTrace_1045167 : CollatzResearch.WordTrace tailWord_1045167 prefixEnd_1045167 477042697971393344894107 := by
  unfold tailWord_1045167
  simp only [CollatzResearch.WordTrace]
  refine ⟨38120372204545934157573755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25413581469697289438382503 38120372204545934157573755)
  ·
    refine ⟨57180558306818901236360633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38120372204545934157573755 57180558306818901236360633)
    ·
      refine ⟨42885418730114175927270475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57180558306818901236360633 42885418730114175927270475)
      ·
        refine ⟨64328128095171263890905713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42885418730114175927270475 64328128095171263890905713)
        ·
          refine ⟨48246096071378447918179285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64328128095171263890905713 48246096071378447918179285)
          ·
            refine ⟨1130767876672932373082327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 48246096071378447918179285 1130767876672932373082327)
            ·
              refine ⟨1696151815009398559623491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130767876672932373082327 1696151815009398559623491)
              ·
                refine ⟨2544227722514097839435237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696151815009398559623491 2544227722514097839435237)
                ·
                  refine ⟨477042697971393344894107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544227722514097839435237 477042697971393344894107)
                  ·
                    rfl

theorem cell20_1045167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 4].length) (baseStart_1045167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045167 prefixEnd_1045167 := by exact prefixLift 1045167
  have htrace : WordTrace (prefixWord ++ tailWord_1045167) baseStart_1045167 baseEnd_1045167 := by
    simpa [prefixWord, tailWord_1045167, baseEnd_1045167] using wordTrace_append hprefix tailTrace_1045167
  have hstable : (prefixWord ++ tailWord_1045167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045167).length < 2 ^ (prefixWord ++ tailWord_1045167).sum := by decide
  have hdescent : baseEnd_1045167 < baseStart_1045167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045212 : List Nat := [2, 2, 5, 1, 1, 9]
def baseStart_1045212 : Nat := 118140960795 + 1045212 * 2 ^ 59
def prefixEnd_1045212 : Nat := 4983230072969 + 3 ^ 40 * 1045212 * 2
def baseEnd_1045212 : Nat := 17669008785095303273849

theorem tailTrace_1045212 : CollatzResearch.WordTrace tailWord_1045212 prefixEnd_1045212 17669008785095303273849 := by
  unfold tailWord_1045212
  simp only [CollatzResearch.WordTrace]
  refine ⟨19061006744691453421480945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25414675659588604561974593 19061006744691453421480945)
  ·
    refine ⟨14295755058518590066110709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19061006744691453421480945 14295755058518590066110709)
    ·
      refine ⟨1340227036736117818697879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14295755058518590066110709 1340227036736117818697879)
      ·
        refine ⟨2010340555104176728046819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340227036736117818697879 2010340555104176728046819)
        ·
          refine ⟨3015510832656265092070229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010340555104176728046819 3015510832656265092070229)
          ·
            refine ⟨17669008785095303273849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3015510832656265092070229 17669008785095303273849)
            ·
              rfl

theorem cell20_1045212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 9].length) (baseStart_1045212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045212 prefixEnd_1045212 := by exact prefixLift 1045212
  have htrace : WordTrace (prefixWord ++ tailWord_1045212) baseStart_1045212 baseEnd_1045212 := by
    simpa [prefixWord, tailWord_1045212, baseEnd_1045212] using wordTrace_append hprefix tailTrace_1045212
  have hstable : (prefixWord ++ tailWord_1045212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045212).length < 2 ^ (prefixWord ++ tailWord_1045212).sum := by decide
  have hdescent : baseEnd_1045212 < baseStart_1045212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045226 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1045226 : Nat := 118140960795 + 1045226 * 2 ^ 59
def prefixEnd_1045226 : Nat := 4983230072969 + 3 ^ 40 * 1045226 * 2
def baseEnd_1045226 : Nat := 477069627179051361927199

theorem tailTrace_1045226 : CollatzResearch.WordTrace tailWord_1045226 prefixEnd_1045226 477069627179051361927199 := by
  unfold tailWord_1045226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530631027833046808492883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25415016074221458155981021 9530631027833046808492883)
  ·
    refine ⟨14295946541749570212739325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9530631027833046808492883 14295946541749570212739325)
    ·
      refine ⟨5360979953156088829777247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14295946541749570212739325 5360979953156088829777247)
      ·
        refine ⟨8041469929734133244665871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360979953156088829777247 8041469929734133244665871)
        ·
          refine ⟨12062204894601199866998807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041469929734133244665871 12062204894601199866998807)
          ·
            refine ⟨18093307341901799800498211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12062204894601199866998807 18093307341901799800498211)
            ·
              refine ⟨27139961012852699700747317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18093307341901799800498211 27139961012852699700747317)
              ·
                refine ⟨2544371344954940596945061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27139961012852699700747317 2544371344954940596945061)
                ·
                  refine ⟨477069627179051361927199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544371344954940596945061 477069627179051361927199)
                  ·
                    rfl

theorem cell20_1045226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1045226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045226 prefixEnd_1045226 := by exact prefixLift 1045226
  have htrace : WordTrace (prefixWord ++ tailWord_1045226) baseStart_1045226 baseEnd_1045226 := by
    simpa [prefixWord, tailWord_1045226, baseEnd_1045226] using wordTrace_append hprefix tailTrace_1045226
  have hstable : (prefixWord ++ tailWord_1045226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045226).length < 2 ^ (prefixWord ++ tailWord_1045226).sum := by decide
  have hdescent : baseEnd_1045226 < baseStart_1045226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045281 : List Nat := [1, 2, 3, 2, 1, 2, 1, 6, 2]
def baseStart_1045281 : Nat := 118140960795 + 1045281 * 2 ^ 59
def prefixEnd_1045281 : Nat := 4983230072969 + 3 ^ 40 * 1045281 * 2
def baseEnd_1045281 : Nat := 477094730677715615093641

theorem tailTrace_1045281 : CollatzResearch.WordTrace tailWord_1045281 prefixEnd_1045281 477094730677715615093641 := by
  unfold tailWord_1045281
  simp only [CollatzResearch.WordTrace]
  refine ⟨38124530126132931627223697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25416353417421954418149131 38124530126132931627223697)
  ·
    refine ⟨28593397594599698720417773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38124530126132931627223697 28593397594599698720417773)
    ·
      refine ⟨10722524097974887020156665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28593397594599698720417773 10722524097974887020156665)
      ·
        refine ⟨8041893073481165265117499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10722524097974887020156665 8041893073481165265117499)
        ·
          refine ⟨12062839610221747897676249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041893073481165265117499 12062839610221747897676249)
          ·
            refine ⟨9047129707666310923257187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062839610221747897676249 9047129707666310923257187)
            ·
              refine ⟨13570694561499466384885781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047129707666310923257187 13570694561499466384885781)
              ·
                refine ⟨636126307570287486791521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13570694561499466384885781 636126307570287486791521)
                ·
                  refine ⟨477094730677715615093641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636126307570287486791521 477094730677715615093641)
                  ·
                    rfl

theorem cell20_1045281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_1045281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045281 prefixEnd_1045281 := by exact prefixLift 1045281
  have htrace : WordTrace (prefixWord ++ tailWord_1045281) baseStart_1045281 baseEnd_1045281 := by
    simpa [prefixWord, tailWord_1045281, baseEnd_1045281] using wordTrace_append hprefix tailTrace_1045281
  have hstable : (prefixWord ++ tailWord_1045281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045281).length < 2 ^ (prefixWord ++ tailWord_1045281).sum := by decide
  have hdescent : baseEnd_1045281 < baseStart_1045281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045333 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 3]
def baseStart_1045333 : Nat := 118140960795 + 1045333 * 2 ^ 59
def prefixEnd_1045333 : Nat := 4983230072969 + 3 ^ 40 * 1045333 * 2
def baseEnd_1045333 : Nat := 477118464894634545360095

theorem tailTrace_1045333 : CollatzResearch.WordTrace tailWord_1045333 prefixEnd_1045333 477118464894634545360095 := by
  unfold tailWord_1045333
  simp only [CollatzResearch.WordTrace]
  refine ⟨38126426721944544508116653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25417617814629696338744435 38126426721944544508116653)
  ·
    refine ⟨14297410020729204190543745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38126426721944544508116653 14297410020729204190543745)
    ·
      refine ⟨10723057515546903142907809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14297410020729204190543745 10723057515546903142907809)
      ·
        refine ⟨8042293136660177357180857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10723057515546903142907809 8042293136660177357180857)
        ·
          refine ⟨6031719852495133017885643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8042293136660177357180857 6031719852495133017885643)
          ·
            refine ⟨9047579778742699526828465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031719852495133017885643 9047579778742699526828465)
            ·
              refine ⟨6785684834057024645121349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9047579778742699526828465 6785684834057024645121349)
              ·
                refine ⟨1272315906385692120960253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6785684834057024645121349 1272315906385692120960253)
                ·
                  refine ⟨477118464894634545360095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272315906385692120960253 477118464894634545360095)
                  ·
                    rfl

theorem cell20_1045333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_1045333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045333 prefixEnd_1045333 := by exact prefixLift 1045333
  have htrace : WordTrace (prefixWord ++ tailWord_1045333) baseStart_1045333 baseEnd_1045333 := by
    simpa [prefixWord, tailWord_1045333, baseEnd_1045333] using wordTrace_append hprefix tailTrace_1045333
  have hstable : (prefixWord ++ tailWord_1045333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045333).length < 2 ^ (prefixWord ++ tailWord_1045333).sum := by decide
  have hdescent : baseEnd_1045333 < baseStart_1045333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045346 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1045346 : Nat := 118140960795 + 1045346 * 2 ^ 59
def prefixEnd_1045346 : Nat := 4983230072969 + 3 ^ 40 * 1045346 * 2
def baseEnd_1045346 : Nat := 477124398448864277926709

theorem tailTrace_1045346 : CollatzResearch.WordTrace tailWord_1045346 prefixEnd_1045346 477124398448864277926709 := by
  unfold tailWord_1045346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9531725217724361932084973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25417933913931631818893261 9531725217724361932084973)
  ·
    refine ⟨3574396956646635724531865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9531725217724361932084973 3574396956646635724531865)
    ·
      refine ⟨2680797717484976793398899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3574396956646635724531865 2680797717484976793398899)
      ·
        refine ⟨4021196576227465190098349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680797717484976793398899 4021196576227465190098349)
        ·
          refine ⟨1507948716085299446286881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4021196576227465190098349 1507948716085299446286881)
          ·
            refine ⟨1130961537063974584715161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507948716085299446286881 1130961537063974584715161)
            ·
              refine ⟨848221152797980938536371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130961537063974584715161 848221152797980938536371)
              ·
                refine ⟨1272331729196971407804557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848221152797980938536371 1272331729196971407804557)
                ·
                  refine ⟨477124398448864277926709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272331729196971407804557 477124398448864277926709)
                  ·
                    rfl

theorem cell20_1045346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1045346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045346 prefixEnd_1045346 := by exact prefixLift 1045346
  have htrace : WordTrace (prefixWord ++ tailWord_1045346) baseStart_1045346 baseEnd_1045346 := by
    simpa [prefixWord, tailWord_1045346, baseEnd_1045346] using wordTrace_append hprefix tailTrace_1045346
  have hstable : (prefixWord ++ tailWord_1045346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045346).length < 2 ^ (prefixWord ++ tailWord_1045346).sum := by decide
  have hdescent : baseEnd_1045346 < baseStart_1045346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045347 : List Nat := [1, 1, 1, 5, 3, 1, 1, 7]
def baseStart_1045347 : Nat := 118140960795 + 1045347 * 2 ^ 59
def prefixEnd_1045347 : Nat := 4983230072969 + 3 ^ 40 * 1045347 * 2
def baseEnd_1045347 : Nat := 159041618292037572964457

theorem tailTrace_1045347 : CollatzResearch.WordTrace tailWord_1045347 prefixEnd_1045347 159041618292037572964457 := by
  unfold tailWord_1045347
  simp only [CollatzResearch.WordTrace]
  refine ⟨38126937343893824899126295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25417958229262549932750863 38126937343893824899126295)
  ·
    refine ⟨57190406015840737348689443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38126937343893824899126295 57190406015840737348689443)
    ·
      refine ⟨85785609023761106023034165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57190406015840737348689443 85785609023761106023034165)
      ·
        refine ⟨8042400845977603689659453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85785609023761106023034165 8042400845977603689659453)
        ·
          refine ⟨3015900317241601383622295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8042400845977603689659453 3015900317241601383622295)
          ·
            refine ⟨4523850475862402075433443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015900317241601383622295 4523850475862402075433443)
            ·
              refine ⟨6785775713793603113150165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523850475862402075433443 6785775713793603113150165)
              ·
                refine ⟨159041618292037572964457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6785775713793603113150165 159041618292037572964457)
                ·
                  rfl

theorem cell20_1045347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_1045347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045347 prefixEnd_1045347 := by exact prefixLift 1045347
  have htrace : WordTrace (prefixWord ++ tailWord_1045347) baseStart_1045347 baseEnd_1045347 := by
    simpa [prefixWord, tailWord_1045347, baseEnd_1045347] using wordTrace_append hprefix tailTrace_1045347
  have hstable : (prefixWord ++ tailWord_1045347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045347).length < 2 ^ (prefixWord ++ tailWord_1045347).sum := by decide
  have hdescent : baseEnd_1045347 < baseStart_1045347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045398 : List Nat := [5, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1045398 : Nat := 118140960795 + 1045398 * 2 ^ 59
def prefixEnd_1045398 : Nat := 4983230072969 + 3 ^ 40 * 1045398 * 2
def baseEnd_1045398 : Nat := 159049377555261069397721

theorem tailTrace_1045398 : CollatzResearch.WordTrace tailWord_1045398 prefixEnd_1045398 159049377555261069397721 := by
  unfold tailWord_1045398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383049841669316288077053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25419198311139373739488565 2383049841669316288077053)
  ·
    refine ⟨893643690625993608028895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2383049841669316288077053 893643690625993608028895)
    ·
      refine ⟨1340465535938990412043343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893643690625993608028895 1340465535938990412043343)
      ·
        refine ⟨2010698303908485618065015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340465535938990412043343 2010698303908485618065015)
        ·
          refine ⟨3016047455862728427097523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010698303908485618065015 3016047455862728427097523)
          ·
            refine ⟨4524071183794092640646285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016047455862728427097523 4524071183794092640646285)
            ·
              refine ⟨1696526693922784740242357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4524071183794092640646285 1696526693922784740242357)
              ·
                refine ⟨159049377555261069397721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1696526693922784740242357 159049377555261069397721)
                ·
                  rfl

theorem cell20_1045398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1045398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045398 prefixEnd_1045398 := by exact prefixLift 1045398
  have htrace : WordTrace (prefixWord ++ tailWord_1045398) baseStart_1045398 baseEnd_1045398 := by
    simpa [prefixWord, tailWord_1045398, baseEnd_1045398] using wordTrace_append hprefix tailTrace_1045398
  have hstable : (prefixWord ++ tailWord_1045398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045398).length < 2 ^ (prefixWord ++ tailWord_1045398).sum := by decide
  have hdescent : baseEnd_1045398 < baseStart_1045398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045433 : List Nat := [1, 2, 1, 4, 2, 2, 1, 5, 2]
def baseStart_1045433 : Nat := 118140960795 + 1045433 * 2 ^ 59
def prefixEnd_1045433 : Nat := 4983230072969 + 3 ^ 40 * 1045433 * 2
def baseEnd_1045433 : Nat := 477164107619478642026353

theorem tailTrace_1045433 : CollatzResearch.WordTrace tailWord_1045433 prefixEnd_1045433 477164107619478642026353 := by
  unfold tailWord_1045433
  simp only [CollatzResearch.WordTrace]
  refine ⟨38130074021582261586756953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25420049347721507724504635 38130074021582261586756953)
  ·
    refine ⟨28597555516186696190067715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38130074021582261586756953 28597555516186696190067715)
    ·
      refine ⟨42896333274280044285101573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28597555516186696190067715 42896333274280044285101573)
      ·
        refine ⟨8043062488927508303456545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42896333274280044285101573 8043062488927508303456545)
        ·
          refine ⟨6032296866695631227592409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8043062488927508303456545 6032296866695631227592409)
          ·
            refine ⟨4524222650021723420694307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6032296866695631227592409 4524222650021723420694307)
            ·
              refine ⟨6786333975032585131041461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524222650021723420694307 6786333975032585131041461)
              ·
                refine ⟨636218810159304856035137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6786333975032585131041461 636218810159304856035137)
                ·
                  refine ⟨477164107619478642026353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636218810159304856035137 477164107619478642026353)
                  ·
                    rfl

theorem cell20_1045433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_1045433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045433 prefixEnd_1045433 := by exact prefixLift 1045433
  have htrace : WordTrace (prefixWord ++ tailWord_1045433) baseStart_1045433 baseEnd_1045433 := by
    simpa [prefixWord, tailWord_1045433, baseEnd_1045433] using wordTrace_append hprefix tailTrace_1045433
  have hstable : (prefixWord ++ tailWord_1045433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045433).length < 2 ^ (prefixWord ++ tailWord_1045433).sum := by decide
  have hdescent : baseEnd_1045433 < baseStart_1045433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045447 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 3]
def baseStart_1045447 : Nat := 118140960795 + 1045447 * 2 ^ 59
def prefixEnd_1045447 : Nat := 4983230072969 + 3 ^ 40 * 1045447 * 2
def baseEnd_1045447 : Nat := 477170497600956815559629

theorem tailTrace_1045447 : CollatzResearch.WordTrace tailWord_1045447 prefixEnd_1045447 477170497600956815559629 := by
  unfold tailWord_1045447
  simp only [CollatzResearch.WordTrace]
  refine ⟨38130584643531541977766595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25420389762354361318511063 38130584643531541977766595)
  ·
    refine ⟨57195876965297312966649893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38130584643531541977766595 57195876965297312966649893)
    ·
      refine ⟨10724226930993246181246855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57195876965297312966649893 10724226930993246181246855)
      ·
        refine ⟨16086340396489869271870283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10724226930993246181246855 16086340396489869271870283)
        ·
          refine ⟨24129510594734803907805425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16086340396489869271870283 24129510594734803907805425)
          ·
            refine ⟨18097132946051102930854069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24129510594734803907805425 18097132946051102930854069)
            ·
              refine ⟨1696606213692290899767569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18097132946051102930854069 1696606213692290899767569)
              ·
                refine ⟨1272454660269218174825677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1696606213692290899767569 1272454660269218174825677)
                ·
                  refine ⟨477170497600956815559629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272454660269218174825677 477170497600956815559629)
                  ·
                    rfl

theorem cell20_1045447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 3].length) (baseStart_1045447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045447 prefixEnd_1045447 := by exact prefixLift 1045447
  have htrace : WordTrace (prefixWord ++ tailWord_1045447) baseStart_1045447 baseEnd_1045447 := by
    simpa [prefixWord, tailWord_1045447, baseEnd_1045447] using wordTrace_append hprefix tailTrace_1045447
  have hstable : (prefixWord ++ tailWord_1045447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045447).length < 2 ^ (prefixWord ++ tailWord_1045447).sum := by decide
  have hdescent : baseEnd_1045447 < baseStart_1045447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045454 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1045454 : Nat := 118140960795 + 1045454 * 2 ^ 59
def prefixEnd_1045454 : Nat := 4983230072969 + 3 ^ 40 * 1045454 * 2
def baseEnd_1045454 : Nat := 477173692591695902326267

theorem tailTrace_1045454 : CollatzResearch.WordTrace tailWord_1045454 prefixEnd_1045454 477173692591695902326267 := by
  unfold tailWord_1045454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4766354994313272771658927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25420559969670788115514277 4766354994313272771658927)
  ·
    refine ⟨7149532491469909157488391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4766354994313272771658927 7149532491469909157488391)
    ·
      refine ⟨10724298737204863736232587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7149532491469909157488391 10724298737204863736232587)
      ·
        refine ⟨16086448105807295604348881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10724298737204863736232587 16086448105807295604348881)
        ·
          refine ⟨12064836079355471703261661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16086448105807295604348881 12064836079355471703261661)
          ·
            refine ⟨4524313529758301888723123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12064836079355471703261661 4524313529758301888723123)
            ·
              refine ⟨6786470294637452833084685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524313529758301888723123 6786470294637452833084685)
              ·
                refine ⟨2544926360489044812406757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6786470294637452833084685 2544926360489044812406757)
                ·
                  refine ⟨477173692591695902326267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544926360489044812406757 477173692591695902326267)
                  ·
                    rfl

theorem cell20_1045454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1045454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045454 prefixEnd_1045454 := by exact prefixLift 1045454
  have htrace : WordTrace (prefixWord ++ tailWord_1045454) baseStart_1045454 baseEnd_1045454 := by
    simpa [prefixWord, tailWord_1045454, baseEnd_1045454] using wordTrace_append hprefix tailTrace_1045454
  have hstable : (prefixWord ++ tailWord_1045454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045454).length < 2 ^ (prefixWord ++ tailWord_1045454).sum := by decide
  have hdescent : baseEnd_1045454 < baseStart_1045454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045464 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 3]
def baseStart_1045464 : Nat := 118140960795 + 1045464 * 2 ^ 59
def prefixEnd_1045464 : Nat := 4983230072969 + 3 ^ 40 * 1045464 * 2
def baseEnd_1045464 : Nat := 477178256864180311992893

theorem tailTrace_1045464 : CollatzResearch.WordTrace tailWord_1045464 prefixEnd_1045464 477178256864180311992893 := by
  unfold tailWord_1045464
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065602342234976940567723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25420803122979969254090297 19065602342234976940567723)
  ·
    refine ⟨28598403513352465410851585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19065602342234976940567723 28598403513352465410851585)
    ·
      refine ⟨21448802635014349058138689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28598403513352465410851585 21448802635014349058138689)
      ·
        refine ⟨16086601976260761793604017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21448802635014349058138689 16086601976260761793604017)
        ·
          refine ⟨12064951482195571345203013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16086601976260761793604017 12064951482195571345203013)
          ·
            refine ⟨2262178402911669627225565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12064951482195571345203013 2262178402911669627225565)
            ·
              refine ⟨848316901091876110209587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2262178402911669627225565 848316901091876110209587)
              ·
                refine ⟨1272475351637814165314381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848316901091876110209587 1272475351637814165314381)
                ·
                  refine ⟨477178256864180311992893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272475351637814165314381 477178256864180311992893)
                  ·
                    rfl

theorem cell20_1045464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_1045464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045464 prefixEnd_1045464 := by exact prefixLift 1045464
  have htrace : WordTrace (prefixWord ++ tailWord_1045464) baseStart_1045464 baseEnd_1045464 := by
    simpa [prefixWord, tailWord_1045464, baseEnd_1045464] using wordTrace_append hprefix tailTrace_1045464
  have hstable : (prefixWord ++ tailWord_1045464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045464).length < 2 ^ (prefixWord ++ tailWord_1045464).sum := by decide
  have hdescent : baseEnd_1045464 < baseStart_1045464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045474 : List Nat := [3, 3, 3, 1, 1, 3, 2, 4]
def baseStart_1045474 : Nat := 118140960795 + 1045474 * 2 ^ 59
def prefixEnd_1045474 : Nat := 4983230072969 + 3 ^ 40 * 1045474 * 2
def baseEnd_1045474 : Nat := 159060940378888240553173

theorem tailTrace_1045474 : CollatzResearch.WordTrace tailWord_1045474 prefixEnd_1045474 159060940378888240553173 := by
  unfold tailWord_1045474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532892353608431397249869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25421046276289150392666317 9532892353608431397249869)
  ·
    refine ⟨3574834632603161773968701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9532892353608431397249869 3574834632603161773968701)
    ·
      refine ⟨1340562987226185665238263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3574834632603161773968701 1340562987226185665238263)
      ·
        refine ⟨2010844480839278497857395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340562987226185665238263 2010844480839278497857395)
        ·
          refine ⟨3016266721258917746786093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010844480839278497857395 3016266721258917746786093)
          ·
            refine ⟨1131100020472094155044785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3016266721258917746786093 1131100020472094155044785)
            ·
              refine ⟨848325015354070616283589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131100020472094155044785 848325015354070616283589)
              ·
                refine ⟨159060940378888240553173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848325015354070616283589 159060940378888240553173)
                ·
                  rfl

theorem cell20_1045474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_1045474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045474 prefixEnd_1045474 := by exact prefixLift 1045474
  have htrace : WordTrace (prefixWord ++ tailWord_1045474) baseStart_1045474 baseEnd_1045474 := by
    simpa [prefixWord, tailWord_1045474, baseEnd_1045474] using wordTrace_append hprefix tailTrace_1045474
  have hstable : (prefixWord ++ tailWord_1045474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045474).length < 2 ^ (prefixWord ++ tailWord_1045474).sum := by decide
  have hdescent : baseEnd_1045474 < baseStart_1045474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045537 : List Nat := [1, 2, 3, 2, 3, 1, 2, 6]
def baseStart_1045537 : Nat := 118140960795 + 1045537 * 2 ^ 59
def prefixEnd_1045537 : Nat := 4983230072969 + 3 ^ 40 * 1045537 * 2
def baseEnd_1045537 : Nat := 159070525351105500853087

theorem tailTrace_1045537 : CollatzResearch.WordTrace tailWord_1045537 prefixEnd_1045537 159070525351105500853087 := by
  unfold tailWord_1045537
  simp only [CollatzResearch.WordTrace]
  refine ⟨38133867213205487348542865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25422578142136991565695243 38133867213205487348542865)
  ·
    refine ⟨28600400409904115511407149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38133867213205487348542865 28600400409904115511407149)
    ·
      refine ⟨10725150153714043316777681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28600400409904115511407149 10725150153714043316777681)
      ·
        refine ⟨8043862615285532487583261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10725150153714043316777681 8043862615285532487583261)
        ·
          refine ⟨3016448480732074682843723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8043862615285532487583261 3016448480732074682843723)
          ·
            refine ⟨4524672721098112024265585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016448480732074682843723 4524672721098112024265585)
            ·
              refine ⟨3393504540823584018199189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4524672721098112024265585 3393504540823584018199189)
              ·
                refine ⟨159070525351105500853087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3393504540823584018199189 159070525351105500853087)
                ·
                  rfl

theorem cell20_1045537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_1045537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045537 prefixEnd_1045537 := by exact prefixLift 1045537
  have htrace : WordTrace (prefixWord ++ tailWord_1045537) baseStart_1045537 baseEnd_1045537 := by
    simpa [prefixWord, tailWord_1045537, baseEnd_1045537] using wordTrace_append hprefix tailTrace_1045537
  have hstable : (prefixWord ++ tailWord_1045537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045537).length < 2 ^ (prefixWord ++ tailWord_1045537).sum := by decide
  have hdescent : baseEnd_1045537 < baseStart_1045537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045561 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 3]
def baseStart_1045561 : Nat := 118140960795 + 1045561 * 2 ^ 59
def prefixEnd_1045561 : Nat := 4983230072969 + 3 ^ 40 * 1045561 * 2
def baseEnd_1045561 : Nat := 477222530307279085759163

theorem tailTrace_1045561 : CollatzResearch.WordTrace tailWord_1045561 prefixEnd_1045561 477222530307279085759163 := by
  unfold tailWord_1045561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38134742565118539447416537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25423161710079026298277691 38134742565118539447416537)
  ·
    refine ⟨28601056923838904585562403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38134742565118539447416537 28601056923838904585562403)
    ·
      refine ⟨42901585385758356878343605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28601056923838904585562403 42901585385758356878343605)
      ·
        refine ⟨4022023629914845957344713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42901585385758356878343605 4022023629914845957344713)
        ·
          refine ⟨3016517722436134468008535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4022023629914845957344713 3016517722436134468008535)
          ·
            refine ⟨4524776583654201702012803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016517722436134468008535 4524776583654201702012803)
            ·
              refine ⟨6787164875481302553019205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524776583654201702012803 6787164875481302553019205)
              ·
                refine ⟨1272593414152744228691101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6787164875481302553019205 1272593414152744228691101)
                ·
                  refine ⟨477222530307279085759163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272593414152744228691101 477222530307279085759163)
                  ·
                    rfl

theorem cell20_1045561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_1045561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045561 prefixEnd_1045561 := by exact prefixLift 1045561
  have htrace : WordTrace (prefixWord ++ tailWord_1045561) baseStart_1045561 baseEnd_1045561 := by
    simpa [prefixWord, tailWord_1045561, baseEnd_1045561] using wordTrace_append hprefix tailTrace_1045561
  have hstable : (prefixWord ++ tailWord_1045561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045561).length < 2 ^ (prefixWord ++ tailWord_1045561).sum := by decide
  have hdescent : baseEnd_1045561 < baseStart_1045561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045564 : List Nat := [2, 2, 2, 2, 2, 2, 4, 2, 2]
def baseStart_1045564 : Nat := 118140960795 + 1045564 * 2 ^ 59
def prefixEnd_1045564 : Nat := 4983230072969 + 3 ^ 40 * 1045564 * 2
def baseEnd_1045564 : Nat := 477223899589024408659151

theorem tailTrace_1045564 : CollatzResearch.WordTrace tailWord_1045564 prefixEnd_1045564 477223899589024408659151 := by
  unfold tailWord_1045564
  simp only [CollatzResearch.WordTrace]
  refine ⟨19067425992053835479887873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25423234656071780639850497 19067425992053835479887873)
  ·
    refine ⟨14300569494040376609915905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19067425992053835479887873 14300569494040376609915905)
    ·
      refine ⟨10725427120530282457436929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14300569494040376609915905 10725427120530282457436929)
      ·
        refine ⟨8044070340397711843077697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10725427120530282457436929 8044070340397711843077697)
        ·
          refine ⟨6033052755298283882308273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8044070340397711843077697 6033052755298283882308273)
          ·
            refine ⟨4524789566473712911731205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033052755298283882308273 4524789566473712911731205)
            ·
              refine ⟨848398043713821170949601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4524789566473712911731205 848398043713821170949601)
              ·
                refine ⟨636298532785365878212201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848398043713821170949601 636298532785365878212201)
                ·
                  refine ⟨477223899589024408659151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636298532785365878212201 477223899589024408659151)
                  ·
                    rfl

theorem cell20_1045564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_1045564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045564 prefixEnd_1045564 := by exact prefixLift 1045564
  have htrace : WordTrace (prefixWord ++ tailWord_1045564) baseStart_1045564 baseEnd_1045564 := by
    simpa [prefixWord, tailWord_1045564, baseEnd_1045564] using wordTrace_append hprefix tailTrace_1045564
  have hstable : (prefixWord ++ tailWord_1045564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045564).length < 2 ^ (prefixWord ++ tailWord_1045564).sum := by decide
  have hdescent : baseEnd_1045564 < baseStart_1045564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045575 : List Nat := [1, 1, 4, 1, 3, 2, 3, 5]
def baseStart_1045575 : Nat := 118140960795 + 1045575 * 2 ^ 59
def prefixEnd_1045575 : Nat := 4983230072969 + 3 ^ 40 * 1045575 * 2
def baseEnd_1045575 : Nat := 159076306762919086430813

theorem tailTrace_1045575 : CollatzResearch.WordTrace tailWord_1045575 prefixEnd_1045575 159076306762919086430813 := by
  unfold tailWord_1045575
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135253187067819838426179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25423502124711879892284119 38135253187067819838426179)
  ·
    refine ⟨57202879780601729757639269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38135253187067819838426179 57202879780601729757639269)
    ·
      refine ⟨10725539958862824329557363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57202879780601729757639269 10725539958862824329557363)
      ·
        refine ⟨16088309938294236494336045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10725539958862824329557363 16088309938294236494336045)
        ·
          refine ⟨6033116226860338685376017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16088309938294236494336045 6033116226860338685376017)
          ·
            refine ⟨4524837170145254014032013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033116226860338685376017 4524837170145254014032013)
            ·
              refine ⟨1696813938804470255262005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4524837170145254014032013 1696813938804470255262005)
              ·
                refine ⟨159076306762919086430813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1696813938804470255262005 159076306762919086430813)
                ·
                  rfl

theorem cell20_1045575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_1045575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045575 prefixEnd_1045575 := by exact prefixLift 1045575
  have htrace : WordTrace (prefixWord ++ tailWord_1045575) baseStart_1045575 baseEnd_1045575 := by
    simpa [prefixWord, tailWord_1045575, baseEnd_1045575] using wordTrace_append hprefix tailTrace_1045575
  have hstable : (prefixWord ++ tailWord_1045575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045575).length < 2 ^ (prefixWord ++ tailWord_1045575).sum := by decide
  have hdescent : baseEnd_1045575 < baseStart_1045575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045598 : List Nat := [4, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1045598 : Nat := 118140960795 + 1045598 * 2 ^ 59
def prefixEnd_1045598 : Nat := 4983230072969 + 3 ^ 40 * 1045598 * 2
def baseEnd_1045598 : Nat := 477239418115471401525679

theorem tailTrace_1045598 : CollatzResearch.WordTrace tailWord_1045598 prefixEnd_1045598 477239418115471401525679 := by
  unfold tailWord_1045598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767011508248061845814181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25424061377322996511008965 4767011508248061845814181)
  ·
    refine ⟨893814657796511596090159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4767011508248061845814181 893814657796511596090159)
    ·
      refine ⟨1340721986694767394135239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893814657796511596090159 1340721986694767394135239)
      ·
        refine ⟨2011082980042151091202859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340721986694767394135239 2011082980042151091202859)
        ·
          refine ⟨3016624470063226636804289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011082980042151091202859 3016624470063226636804289)
          ·
            refine ⟨2262468352547419977603217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3016624470063226636804289 2262468352547419977603217)
            ·
              refine ⟨1696851264410564983202413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262468352547419977603217 1696851264410564983202413)
              ·
                refine ⟨636319224153961868700905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696851264410564983202413 636319224153961868700905)
                ·
                  refine ⟨477239418115471401525679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636319224153961868700905 477239418115471401525679)
                  ·
                    rfl

theorem cell20_1045598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1045598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045598 prefixEnd_1045598 := by exact prefixLift 1045598
  have htrace : WordTrace (prefixWord ++ tailWord_1045598) baseStart_1045598 baseEnd_1045598 := by
    simpa [prefixWord, tailWord_1045598, baseEnd_1045598] using wordTrace_append hprefix tailTrace_1045598
  have hstable : (prefixWord ++ tailWord_1045598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045598).length < 2 ^ (prefixWord ++ tailWord_1045598).sum := by decide
  have hdescent : baseEnd_1045598 < baseStart_1045598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045602 : List Nat := [3, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1045602 : Nat := 118140960795 + 1045602 * 2 ^ 59
def prefixEnd_1045602 : Nat := 4983230072969 + 3 ^ 40 * 1045602 * 2
def baseEnd_1045602 : Nat := 477241243824465165392329

theorem tailTrace_1045602 : CollatzResearch.WordTrace tailWord_1045602 prefixEnd_1045602 477241243824465165392329 := by
  unfold tailWord_1045602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534059489492500862414765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25424158638646668966439373 9534059489492500862414765)
  ·
    refine ⟨3575272308559687823405537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9534059489492500862414765 3575272308559687823405537)
    ·
      refine ⟨2681454231419765867554153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3575272308559687823405537 2681454231419765867554153)
      ·
        refine ⟨2011090673564824400665615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2681454231419765867554153 2011090673564824400665615)
        ·
          refine ⟨3016636010347236600998423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011090673564824400665615 3016636010347236600998423)
          ·
            refine ⟨4524954015520854901497635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016636010347236600998423 4524954015520854901497635)
            ·
              refine ⟨6787431023281282352246453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524954015520854901497635 6787431023281282352246453)
              ·
                refine ⟨636321658432620220523105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6787431023281282352246453 636321658432620220523105)
                ·
                  refine ⟨477241243824465165392329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636321658432620220523105 477241243824465165392329)
                  ·
                    rfl

theorem cell20_1045602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1045602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045602 prefixEnd_1045602 := by exact prefixLift 1045602
  have htrace : WordTrace (prefixWord ++ tailWord_1045602) baseStart_1045602 baseEnd_1045602 := by
    simpa [prefixWord, tailWord_1045602, baseEnd_1045602] using wordTrace_append hprefix tailTrace_1045602
  have hstable : (prefixWord ++ tailWord_1045602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045602).length < 2 ^ (prefixWord ++ tailWord_1045602).sum := by decide
  have hdescent : baseEnd_1045602 < baseStart_1045602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045613 : List Nat := [1, 5, 1, 1, 2, 3, 7]
def baseStart_1045613 : Nat := 118140960795 + 1045613 * 2 ^ 59
def prefixEnd_1045613 : Nat := 4983230072969 + 3 ^ 40 * 1045613 * 2
def baseEnd_1045613 : Nat := 53027362724910890669513

theorem tailTrace_1045613 : CollatzResearch.WordTrace tailWord_1045613 prefixEnd_1045613 53027362724910890669513 := by
  unfold tailWord_1045613
  simp only [CollatzResearch.WordTrace]
  refine ⟨38136639160930152328309493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25424426107286768218872995 38136639160930152328309493)
  ·
    refine ⟨3575309921337201780779015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38136639160930152328309493 3575309921337201780779015)
    ·
      refine ⟨5362964882005802671168523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575309921337201780779015 5362964882005802671168523)
      ·
        refine ⟨8044447323008704006752785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362964882005802671168523 8044447323008704006752785)
        ·
          refine ⟨6033335492256528005064589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8044447323008704006752785 6033335492256528005064589)
          ·
            refine ⟨2262500809596198001899221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6033335492256528005064589 2262500809596198001899221)
            ·
              refine ⟨53027362724910890669513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2262500809596198001899221 53027362724910890669513)
              ·
                rfl

theorem cell20_1045613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_1045613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045613 prefixEnd_1045613 := by exact prefixLift 1045613
  have htrace : WordTrace (prefixWord ++ tailWord_1045613) baseStart_1045613 baseEnd_1045613 := by
    simpa [prefixWord, tailWord_1045613, baseEnd_1045613] using wordTrace_append hprefix tailTrace_1045613
  have hstable : (prefixWord ++ tailWord_1045613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045613).length < 2 ^ (prefixWord ++ tailWord_1045613).sum := by decide
  have hdescent : baseEnd_1045613 < baseStart_1045613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045651 : List Nat := [1, 1, 1, 2, 1, 2, 8, 4]
def baseStart_1045651 : Nat := 118140960795 + 1045651 * 2 ^ 59
def prefixEnd_1045651 : Nat := 4983230072969 + 3 ^ 40 * 1045651 * 2
def baseEnd_1045651 : Nat := 159087869586546257586265

theorem tailTrace_1045651 : CollatzResearch.WordTrace tailWord_1045651 prefixEnd_1045651 159087869586546257586265 := by
  unfold tailWord_1045651
  simp only [CollatzResearch.WordTrace]
  refine ⟨38138025134792484818192807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25425350089861656545461871 38138025134792484818192807)
  ·
    refine ⟨57207037702188727227289211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38138025134792484818192807 57207037702188727227289211)
    ·
      refine ⟨85810556553283090840933817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57207037702188727227289211 85810556553283090840933817)
      ·
        refine ⟨64357917414962318130700363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85810556553283090840933817 64357917414962318130700363)
        ·
          refine ⟨96536876122443477196050545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64357917414962318130700363 96536876122443477196050545)
          ·
            refine ⟨72402657091832607897037909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96536876122443477196050545 72402657091832607897037909)
            ·
              refine ⟨848468637794913373793413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 72402657091832607897037909 848468637794913373793413)
              ·
                refine ⟨159087869586546257586265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848468637794913373793413 159087869586546257586265)
                ·
                  rfl

theorem cell20_1045651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_1045651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045651 prefixEnd_1045651 := by exact prefixLift 1045651
  have htrace : WordTrace (prefixWord ++ tailWord_1045651) baseStart_1045651 baseEnd_1045651 := by
    simpa [prefixWord, tailWord_1045651, baseEnd_1045651] using wordTrace_append hprefix tailTrace_1045651
  have hstable : (prefixWord ++ tailWord_1045651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045651).length < 2 ^ (prefixWord ++ tailWord_1045651).sum := by decide
  have hdescent : baseEnd_1045651 < baseStart_1045651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045682 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1045682 : Nat := 118140960795 + 1045682 * 2 ^ 59
def prefixEnd_1045682 : Nat := 4983230072969 + 3 ^ 40 * 1045682 * 2
def baseEnd_1045682 : Nat := 477277758004340442725335

theorem tailTrace_1045682 : CollatzResearch.WordTrace tailWord_1045682 prefixEnd_1045682 477277758004340442725335 := by
  unfold tailWord_1045682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534788949420044278142825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25426103865120118075047533 9534788949420044278142825)
  ·
    refine ⟨7151091712065033208607119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9534788949420044278142825 7151091712065033208607119)
    ·
      refine ⟨10726637568097549812910679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7151091712065033208607119 10726637568097549812910679)
      ·
        refine ⟨16089956352146324719366019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10726637568097549812910679 16089956352146324719366019)
        ·
          refine ⟨24134934528219487079049029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16089956352146324719366019 24134934528219487079049029)
          ·
            refine ⟨4525300224041153827321693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24134934528219487079049029 4525300224041153827321693)
            ·
              refine ⟨1696987584015432685245635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4525300224041153827321693 1696987584015432685245635)
              ·
                refine ⟨2545481376023149027868453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696987584015432685245635 2545481376023149027868453)
                ·
                  refine ⟨477277758004340442725335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545481376023149027868453 477277758004340442725335)
                  ·
                    rfl

theorem cell20_1045682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1045682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045682 prefixEnd_1045682 := by exact prefixLift 1045682
  have htrace : WordTrace (prefixWord ++ tailWord_1045682) baseStart_1045682 baseEnd_1045682 := by
    simpa [prefixWord, tailWord_1045682, baseEnd_1045682] using wordTrace_append hprefix tailTrace_1045682
  have hstable : (prefixWord ++ tailWord_1045682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045682).length < 2 ^ (prefixWord ++ tailWord_1045682).sum := by decide
  have hdescent : baseEnd_1045682 < baseStart_1045682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045689 : List Nat := [1, 2, 1, 4, 1, 4, 2, 5]
def baseStart_1045689 : Nat := 118140960795 + 1045689 * 2 ^ 59
def prefixEnd_1045689 : Nat := 4983230072969 + 3 ^ 40 * 1045689 * 2
def baseEnd_1045689 : Nat := 159093650998359843163991

theorem tailTrace_1045689 : CollatzResearch.WordTrace tailWord_1045689 prefixEnd_1045689 159093650998359843163991 := by
  unfold tailWord_1045689
  simp only [CollatzResearch.WordTrace]
  refine ⟨38139411108654817308076121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25426274072436544872050747 38139411108654817308076121)
  ·
    refine ⟨28604558331491112981057091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38139411108654817308076121 28604558331491112981057091)
    ·
      refine ⟨42906837497236669471585637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28604558331491112981057091 42906837497236669471585637)
      ·
        refine ⟨8045032030731875525922307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42906837497236669471585637 8045032030731875525922307)
        ·
          refine ⟨12067548046097813288883461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8045032030731875525922307 12067548046097813288883461)
          ·
            refine ⟨2262665258643339991665649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12067548046097813288883461 2262665258643339991665649)
            ·
              refine ⟨1696998943982504993749237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262665258643339991665649 1696998943982504993749237)
              ·
                refine ⟨159093650998359843163991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1696998943982504993749237 159093650998359843163991)
                ·
                  rfl

theorem cell20_1045689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_1045689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045689 prefixEnd_1045689 := by exact prefixLift 1045689
  have htrace : WordTrace (prefixWord ++ tailWord_1045689) baseStart_1045689 baseEnd_1045689 := by
    simpa [prefixWord, tailWord_1045689, baseEnd_1045689] using wordTrace_append hprefix tailTrace_1045689
  have hstable : (prefixWord ++ tailWord_1045689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045689).length < 2 ^ (prefixWord ++ tailWord_1045689).sum := by decide
  have hdescent : baseEnd_1045689 < baseStart_1045689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045692 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_1045692 : Nat := 118140960795 + 1045692 * 2 ^ 59
def prefixEnd_1045692 : Nat := 4983230072969 + 3 ^ 40 * 1045692 * 2
def baseEnd_1045692 : Nat := 477282322276824852391961

theorem tailTrace_1045692 : CollatzResearch.WordTrace tailWord_1045692 prefixEnd_1045692 477282322276824852391961 := by
  unfold tailWord_1045692
  simp only [CollatzResearch.WordTrace]
  refine ⟨19069760263821974410217665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25426347018429299213623553 19069760263821974410217665)
  ·
    refine ⟨14302320197866480807663249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19069760263821974410217665 14302320197866480807663249)
    ·
      refine ⟨10726740148399860605747437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14302320197866480807663249 10726740148399860605747437)
      ·
        refine ⟨4022527555649947727155289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10726740148399860605747437 4022527555649947727155289)
        ·
          refine ⟨3016895666737460795366467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4022527555649947727155289 3016895666737460795366467)
          ·
            refine ⟨4525343500106191193049701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016895666737460795366467 4525343500106191193049701)
            ·
              refine ⟨848501906269910848696819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4525343500106191193049701 848501906269910848696819)
              ·
                refine ⟨1272752859404866273045229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848501906269910848696819 1272752859404866273045229)
                ·
                  refine ⟨477282322276824852391961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272752859404866273045229 477282322276824852391961)
                  ·
                    rfl

theorem cell20_1045692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_1045692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045692 prefixEnd_1045692 := by exact prefixLift 1045692
  have htrace : WordTrace (prefixWord ++ tailWord_1045692) baseStart_1045692 baseEnd_1045692 := by
    simpa [prefixWord, tailWord_1045692, baseEnd_1045692] using wordTrace_append hprefix tailTrace_1045692
  have hstable : (prefixWord ++ tailWord_1045692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045692).length < 2 ^ (prefixWord ++ tailWord_1045692).sum := by decide
  have hdescent : baseEnd_1045692 < baseStart_1045692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045703 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_1045703 : Nat := 118140960795 + 1045703 * 2 ^ 59
def prefixEnd_1045703 : Nat := 4983230072969 + 3 ^ 40 * 1045703 * 2
def baseEnd_1045703 : Nat := 477287342976557703025249

theorem tailTrace_1045703 : CollatzResearch.WordTrace tailWord_1045703 prefixEnd_1045703 477287342976557703025249 := by
  unfold tailWord_1045703
  simp only [CollatzResearch.WordTrace]
  refine ⟨38139921730604097699085763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25426614487069398466057175 38139921730604097699085763)
  ·
    refine ⟨57209882595906146548628645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38139921730604097699085763 57209882595906146548628645)
    ·
      refine ⟨10726852986732402477867871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57209882595906146548628645 10726852986732402477867871)
      ·
        refine ⟨16090279480098603716801807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10726852986732402477867871 16090279480098603716801807)
        ·
          refine ⟨24135419220147905575202711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16090279480098603716801807 24135419220147905575202711)
          ·
            refine ⟨36203128830221858362804067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24135419220147905575202711 36203128830221858362804067)
            ·
              refine ⟨54304693245332787544206101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36203128830221858362804067 54304693245332787544206101)
              ·
                refine ⟨2545532495874974416134661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54304693245332787544206101 2545532495874974416134661)
                ·
                  refine ⟨477287342976557703025249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545532495874974416134661 477287342976557703025249)
                  ·
                    rfl

theorem cell20_1045703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_1045703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045703 prefixEnd_1045703 := by exact prefixLift 1045703
  have htrace : WordTrace (prefixWord ++ tailWord_1045703) baseStart_1045703 baseEnd_1045703 := by
    simpa [prefixWord, tailWord_1045703, baseEnd_1045703] using wordTrace_append hprefix tailTrace_1045703
  have hstable : (prefixWord ++ tailWord_1045703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045703).length < 2 ^ (prefixWord ++ tailWord_1045703).sum := by decide
  have hdescent : baseEnd_1045703 < baseStart_1045703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045733 : List Nat := [1, 3, 1, 4, 3, 2, 2, 2, 2]
def baseStart_1045733 : Nat := 118140960795 + 1045733 * 2 ^ 59
def prefixEnd_1045733 : Nat := 4983230072969 + 3 ^ 40 * 1045733 * 2
def baseEnd_1045733 : Nat := 477301035794010932025127

theorem tailTrace_1045733 : CollatzResearch.WordTrace tailWord_1045733 prefixEnd_1045733 477301035794010932025127 := by
  unfold tailWord_1045733
  simp only [CollatzResearch.WordTrace]
  refine ⟨38141015920495412822677853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25427343946996941881785235 38141015920495412822677853)
  ·
    refine ⟨14302880970185779808504195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38141015920495412822677853 14302880970185779808504195)
    ·
      refine ⟨21454321455278669712756293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14302880970185779808504195 21454321455278669712756293)
      ·
        refine ⟨4022685272864750571141805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21454321455278669712756293 4022685272864750571141805)
        ·
          refine ⟨1508506977324281464178177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4022685272864750571141805 1508506977324281464178177)
          ·
            refine ⟨1131380232993211098133633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508506977324281464178177 1131380232993211098133633)
            ·
              refine ⟨848535174744908323600225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131380232993211098133633 848535174744908323600225)
              ·
                refine ⟨636401381058681242700169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848535174744908323600225 636401381058681242700169)
                ·
                  refine ⟨477301035794010932025127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636401381058681242700169 477301035794010932025127)
                  ·
                    rfl

theorem cell20_1045733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_1045733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045733 prefixEnd_1045733 := by exact prefixLift 1045733
  have htrace : WordTrace (prefixWord ++ tailWord_1045733) baseStart_1045733 baseEnd_1045733 := by
    simpa [prefixWord, tailWord_1045733, baseEnd_1045733] using wordTrace_append hprefix tailTrace_1045733
  have hstable : (prefixWord ++ tailWord_1045733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045733).length < 2 ^ (prefixWord ++ tailWord_1045733).sum := by decide
  have hdescent : baseEnd_1045733 < baseStart_1045733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045758 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1045758 : Nat := 118140960795 + 1045758 * 2 ^ 59
def prefixEnd_1045758 : Nat := 4983230072969 + 3 ^ 40 * 1045758 * 2
def baseEnd_1045758 : Nat := 477312446475221956191691

theorem tailTrace_1045758 : CollatzResearch.WordTrace tailWord_1045758 prefixEnd_1045758 477312446475221956191691 := by
  unfold tailWord_1045758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767740968175605261542241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25427951830269894728225285 4767740968175605261542241)
  ·
    refine ⟨3575805726131703946156681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4767740968175605261542241 3575805726131703946156681)
    ·
      refine ⟨2681854294598777959617511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3575805726131703946156681 2681854294598777959617511)
      ·
        refine ⟨4022781441898166939426267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681854294598777959617511 4022781441898166939426267)
        ·
          refine ⟨6034172162847250409139401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022781441898166939426267 6034172162847250409139401)
          ·
            refine ⟨4525629122135437806854551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6034172162847250409139401 4525629122135437806854551)
            ·
              refine ⟨6788443683203156710281827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525629122135437806854551 6788443683203156710281827)
              ·
                refine ⟨10182665524804735065422741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788443683203156710281827 10182665524804735065422741)
                ·
                  refine ⟨477312446475221956191691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10182665524804735065422741 477312446475221956191691)
                  ·
                    rfl

theorem cell20_1045758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1045758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045758 prefixEnd_1045758 := by exact prefixLift 1045758
  have htrace : WordTrace (prefixWord ++ tailWord_1045758) baseStart_1045758 baseEnd_1045758 := by
    simpa [prefixWord, tailWord_1045758, baseEnd_1045758] using wordTrace_append hprefix tailTrace_1045758
  have hstable : (prefixWord ++ tailWord_1045758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045758).length < 2 ^ (prefixWord ++ tailWord_1045758).sum := by decide
  have hdescent : baseEnd_1045758 < baseStart_1045758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045765 : List Nat := [1, 3, 1, 1, 2, 1, 7, 4]
def baseStart_1045765 : Nat := 118140960795 + 1045765 * 2 ^ 59
def prefixEnd_1045765 : Nat := 4983230072969 + 3 ^ 40 * 1045765 * 2
def baseEnd_1045765 : Nat := 159105213821987014319443

theorem tailTrace_1045765 : CollatzResearch.WordTrace tailWord_1045765 prefixEnd_1045765 159105213821987014319443 := by
  unfold tailWord_1045765
  simp only [CollatzResearch.WordTrace]
  refine ⟨38142183056379482287842749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25428122037586321525228499 38142183056379482287842749)
  ·
    refine ⟨14303318646142305857941031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38142183056379482287842749 14303318646142305857941031)
    ·
      refine ⟨21454977969213458786911547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303318646142305857941031 21454977969213458786911547)
      ·
        refine ⟨32182466953820188180367321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21454977969213458786911547 32182466953820188180367321)
        ·
          refine ⟨24136850215365141135275491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32182466953820188180367321 24136850215365141135275491)
          ·
            refine ⟨36205275323047711702913237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24136850215365141135275491 36205275323047711702913237)
            ·
              refine ⟨848561140383930743037029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36205275323047711702913237 848561140383930743037029)
              ·
                refine ⟨159105213821987014319443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848561140383930743037029 159105213821987014319443)
                ·
                  rfl

theorem cell20_1045765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_1045765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045765 prefixEnd_1045765 := by exact prefixLift 1045765
  have htrace : WordTrace (prefixWord ++ tailWord_1045765) baseStart_1045765 baseEnd_1045765 := by
    simpa [prefixWord, tailWord_1045765, baseEnd_1045765] using wordTrace_append hprefix tailTrace_1045765
  have hstable : (prefixWord ++ tailWord_1045765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045765).length < 2 ^ (prefixWord ++ tailWord_1045765).sum := by decide
  have hdescent : baseEnd_1045765 < baseStart_1045765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045789 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1045789 : Nat := 118140960795 + 1045789 * 2 ^ 59
def prefixEnd_1045789 : Nat := 4983230072969 + 3 ^ 40 * 1045789 * 2
def baseEnd_1045789 : Nat := 477326595719923626158231

theorem tailTrace_1045789 : CollatzResearch.WordTrace tailWord_1045789 prefixEnd_1045789 477326595719923626158231 := by
  unfold tailWord_1045789
  simp only [CollatzResearch.WordTrace]
  refine ⟨38143058408292534386716421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25428705605528356257810947 38143058408292534386716421)
  ·
    refine ⟨7151823451554850197509329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38143058408292534386716421 7151823451554850197509329)
    ·
      refine ⟨5363867588666137648131997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7151823451554850197509329 5363867588666137648131997)
      ·
        refine ⟨2011450345749801618049499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5363867588666137648131997 2011450345749801618049499)
        ·
          refine ⟨3017175518624702427074249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011450345749801618049499 3017175518624702427074249)
          ·
            refine ⟨2262881638968526820305687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3017175518624702427074249 2262881638968526820305687)
            ·
              refine ⟨3394322458452790230458531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262881638968526820305687 3394322458452790230458531)
              ·
                refine ⟨5091483687679185345687797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394322458452790230458531 5091483687679185345687797)
                ·
                  refine ⟨477326595719923626158231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5091483687679185345687797 477326595719923626158231)
                  ·
                    rfl

theorem cell20_1045789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1045789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045789 prefixEnd_1045789 := by exact prefixLift 1045789
  have htrace : WordTrace (prefixWord ++ tailWord_1045789) baseStart_1045789 baseEnd_1045789 := by
    simpa [prefixWord, tailWord_1045789, baseEnd_1045789] using wordTrace_append hprefix tailTrace_1045789
  have hstable : (prefixWord ++ tailWord_1045789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045789).length < 2 ^ (prefixWord ++ tailWord_1045789).sum := by decide
  have hdescent : baseEnd_1045789 < baseStart_1045789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045796 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1045796 : Nat := 118140960795 + 1045796 * 2 ^ 59
def prefixEnd_1045796 : Nat := 4983230072969 + 3 ^ 40 * 1045796 * 2
def baseEnd_1045796 : Nat := 477329790710662712924869

theorem tailTrace_1045796 : CollatzResearch.WordTrace tailWord_1045796 prefixEnd_1045796 477329790710662712924869 := by
  unfold tailWord_1045796
  simp only [CollatzResearch.WordTrace]
  refine ⟨19071656859633587291110621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25428875812844783054814161 19071656859633587291110621)
  ·
    refine ⟨7151871322362595234166483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19071656859633587291110621 7151871322362595234166483)
    ·
      refine ⟨10727806983543892851249725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7151871322362595234166483 10727806983543892851249725)
      ·
        refine ⟨4022927618828959819218647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10727806983543892851249725 4022927618828959819218647)
        ·
          refine ⟨6034391428243439728827971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022927618828959819218647 6034391428243439728827971)
          ·
            refine ⟨9051587142365159593241957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034391428243439728827971 9051587142365159593241957)
            ·
              refine ⟨1697172589193467423732867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9051587142365159593241957 1697172589193467423732867)
              ·
                refine ⟨2545758883790201135599301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697172589193467423732867 2545758883790201135599301)
                ·
                  refine ⟨477329790710662712924869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545758883790201135599301 477329790710662712924869)
                  ·
                    rfl

theorem cell20_1045796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1045796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045796 prefixEnd_1045796 := by exact prefixLift 1045796
  have htrace : WordTrace (prefixWord ++ tailWord_1045796) baseStart_1045796 baseEnd_1045796 := by
    simpa [prefixWord, tailWord_1045796, baseEnd_1045796] using wordTrace_append hprefix tailTrace_1045796
  have hstable : (prefixWord ++ tailWord_1045796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045796).length < 2 ^ (prefixWord ++ tailWord_1045796).sum := by decide
  have hdescent : baseEnd_1045796 < baseStart_1045796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045820 : List Nat := [2, 2, 2, 2, 1, 5, 2, 4]
def baseStart_1045820 : Nat := 118140960795 + 1045820 * 2 ^ 59
def prefixEnd_1045820 : Nat := 4983230072969 + 3 ^ 40 * 1045820 * 2
def baseEnd_1045820 : Nat := 159113581654875098708257

theorem tailTrace_1045820 : CollatzResearch.WordTrace tailWord_1045820 prefixEnd_1045820 159113581654875098708257 := by
  unfold tailWord_1045820
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072094535590113340547457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25429459380786817787396609 19072094535590113340547457)
  ·
    refine ⟨14304070901692585005410593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19072094535590113340547457 14304070901692585005410593)
    ·
      refine ⟨10728053176269438754057945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14304070901692585005410593 10728053176269438754057945)
      ·
        refine ⟨8046039882202079065543459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10728053176269438754057945 8046039882202079065543459)
        ·
          refine ⟨12069059823303118598315189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046039882202079065543459 12069059823303118598315189)
          ·
            refine ⟨1131474358434667368592049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12069059823303118598315189 1131474358434667368592049)
            ·
              refine ⟨848605768826000526444037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131474358434667368592049 848605768826000526444037)
              ·
                refine ⟨159113581654875098708257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848605768826000526444037 159113581654875098708257)
                ·
                  rfl

theorem cell20_1045820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_1045820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045820 prefixEnd_1045820 := by exact prefixLift 1045820
  have htrace : WordTrace (prefixWord ++ tailWord_1045820) baseStart_1045820 baseEnd_1045820 := by
    simpa [prefixWord, tailWord_1045820, baseEnd_1045820] using wordTrace_append hprefix tailTrace_1045820
  have hstable : (prefixWord ++ tailWord_1045820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045820).length < 2 ^ (prefixWord ++ tailWord_1045820).sum := by decide
  have hdescent : baseEnd_1045820 < baseStart_1045820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045824 : List Nat := [2, 1, 1, 2, 2, 1, 5, 6]
def baseStart_1045824 : Nat := 118140960795 + 1045824 * 2 ^ 59
def prefixEnd_1045824 : Nat := 4983230072969 + 3 ^ 40 * 1045824 * 2
def baseEnd_1045824 : Nat := 159114190224539686663807

theorem tailTrace_1045824 : CollatzResearch.WordTrace tailWord_1045824 prefixEnd_1045824 159114190224539686663807 := by
  unfold tailWord_1045824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072167481582867682120263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25429556642110490242827017 19072167481582867682120263)
  ·
    refine ⟨28608251222374301523180395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19072167481582867682120263 28608251222374301523180395)
    ·
      refine ⟨42912376833561452284770593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28608251222374301523180395 42912376833561452284770593)
      ·
        refine ⟨32184282625171089213577945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42912376833561452284770593 32184282625171089213577945)
        ·
          refine ⟨24138211968878316910183459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32184282625171089213577945 24138211968878316910183459)
          ·
            refine ⟨36207317953317475365275189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24138211968878316910183459 36207317953317475365275189)
            ·
              refine ⟨3394436058123513315494549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36207317953317475365275189 3394436058123513315494549)
              ·
                refine ⟨159114190224539686663807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3394436058123513315494549 159114190224539686663807)
                ·
                  rfl

theorem cell20_1045824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_1045824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045824 prefixEnd_1045824 := by exact prefixLift 1045824
  have htrace : WordTrace (prefixWord ++ tailWord_1045824) baseStart_1045824 baseEnd_1045824 := by
    simpa [prefixWord, tailWord_1045824, baseEnd_1045824] using wordTrace_append hprefix tailTrace_1045824
  have hstable : (prefixWord ++ tailWord_1045824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045824).length < 2 ^ (prefixWord ++ tailWord_1045824).sum := by decide
  have hdescent : baseEnd_1045824 < baseStart_1045824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045837 : List Nat := [1, 6, 1, 3, 1, 2, 6]
def baseStart_1045837 : Nat := 118140960795 + 1045837 * 2 ^ 59
def prefixEnd_1045837 : Nat := 4983230072969 + 3 ^ 40 * 1045837 * 2
def baseEnd_1045837 : Nat := 53038722691983199173115

theorem tailTrace_1045837 : CollatzResearch.WordTrace tailWord_1045837 prefixEnd_1045837 53038722691983199173115 := by
  unfold tailWord_1045837
  simp only [CollatzResearch.WordTrace]
  refine ⟨38144809112118638584463765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25429872741412425722975843 38144809112118638584463765)
  ·
    refine ⟨1788037927130561183646739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38144809112118638584463765 1788037927130561183646739)
    ·
      refine ⟨2682056890695841775470109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1788037927130561183646739 2682056890695841775470109)
      ·
        refine ⟨1005771334010940665801291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2682056890695841775470109 1005771334010940665801291)
        ·
          refine ⟨1508657001016410998701937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005771334010940665801291 1508657001016410998701937)
          ·
            refine ⟨1131492750762308249026453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508657001016410998701937 1131492750762308249026453)
            ·
              refine ⟨53038722691983199173115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1131492750762308249026453 53038722691983199173115)
              ·
                rfl

theorem cell20_1045837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 6].length) (baseStart_1045837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045837 prefixEnd_1045837 := by exact prefixLift 1045837
  have htrace : WordTrace (prefixWord ++ tailWord_1045837) baseStart_1045837 baseEnd_1045837 := by
    simpa [prefixWord, tailWord_1045837, baseEnd_1045837] using wordTrace_append hprefix tailTrace_1045837
  have hstable : (prefixWord ++ tailWord_1045837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045837).length < 2 ^ (prefixWord ++ tailWord_1045837).sum := by decide
  have hdescent : baseEnd_1045837 < baseStart_1045837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045848 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_1045848 : Nat := 118140960795 + 1045848 * 2 ^ 59
def prefixEnd_1045848 : Nat := 4983230072969 + 3 ^ 40 * 1045848 * 2
def baseEnd_1045848 : Nat := 477353524927581643191323

theorem tailTrace_1045848 : CollatzResearch.WordTrace tailWord_1045848 prefixEnd_1045848 477353524927581643191323 := by
  unfold tailWord_1045848
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072605157539393731557099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25430140210052524975409465 19072605157539393731557099)
  ·
    refine ⟨28608907736309090597335649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19072605157539393731557099 28608907736309090597335649)
    ·
      refine ⟨21456680802231817948001737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28608907736309090597335649 21456680802231817948001737)
      ·
        refine ⟨16092510601673863461001303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21456680802231817948001737 16092510601673863461001303)
        ·
          refine ⟨24138765902510795191501955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16092510601673863461001303 24138765902510795191501955)
          ·
            refine ⟨36208148853766192787252933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24138765902510795191501955 36208148853766192787252933)
            ·
              refine ⟨6789027910081161147609925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36208148853766192787252933 6789027910081161147609925)
              ·
                refine ⟨1272942733140217715176861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6789027910081161147609925 1272942733140217715176861)
                ·
                  refine ⟨477353524927581643191323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1272942733140217715176861 477353524927581643191323)
                  ·
                    rfl

theorem cell20_1045848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_1045848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045848 prefixEnd_1045848 := by exact prefixLift 1045848
  have htrace : WordTrace (prefixWord ++ tailWord_1045848) baseStart_1045848 baseEnd_1045848 := by
    simpa [prefixWord, tailWord_1045848, baseEnd_1045848] using wordTrace_append hprefix tailTrace_1045848
  have hstable : (prefixWord ++ tailWord_1045848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045848).length < 2 ^ (prefixWord ++ tailWord_1045848).sum := by decide
  have hdescent : baseEnd_1045848 < baseStart_1045848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045902 : List Nat := [4, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_1045902 : Nat := 118140960795 + 1045902 * 2 ^ 59
def prefixEnd_1045902 : Nat := 4983230072969 + 3 ^ 40 * 1045902 * 2
def baseEnd_1045902 : Nat := 477378171998997455391103

theorem tailTrace_1045902 : CollatzResearch.WordTrace tailWord_1045902 prefixEnd_1045902 477378171998997455391103 := by
  unfold tailWord_1045902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768397482110394335697495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25431453237922103123719973 4768397482110394335697495)
  ·
    refine ⟨7152596223165591503546243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4768397482110394335697495 7152596223165591503546243)
    ·
      refine ⟨10728894334748387255319365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152596223165591503546243 10728894334748387255319365)
      ·
        refine ⟨2011667687765322610372381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10728894334748387255319365 2011667687765322610372381)
        ·
          refine ⟨754375382911995978889643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2011667687765322610372381 754375382911995978889643)
          ·
            refine ⟨1131563074367993968334465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754375382911995978889643 1131563074367993968334465)
            ·
              refine ⟨848672305775995476250849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131563074367993968334465 848672305775995476250849)
              ·
                refine ⟨636504229331996607188137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848672305775995476250849 636504229331996607188137)
                ·
                  refine ⟨477378171998997455391103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636504229331996607188137 477378171998997455391103)
                  ·
                    rfl

theorem cell20_1045902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_1045902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045902 prefixEnd_1045902 := by exact prefixLift 1045902
  have htrace : WordTrace (prefixWord ++ tailWord_1045902) baseStart_1045902 baseEnd_1045902 := by
    simpa [prefixWord, tailWord_1045902, baseEnd_1045902] using wordTrace_append hprefix tailTrace_1045902
  have hstable : (prefixWord ++ tailWord_1045902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045902).length < 2 ^ (prefixWord ++ tailWord_1045902).sum := by decide
  have hdescent : baseEnd_1045902 < baseStart_1045902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045917 : List Nat := [1, 4, 2, 1, 3, 1, 3, 5]
def baseStart_1045917 : Nat := 118140960795 + 1045917 * 2 ^ 59
def prefixEnd_1045917 : Nat := 4983230072969 + 3 ^ 40 * 1045917 * 2
def baseEnd_1045917 : Nat := 159128339469241356630347

theorem tailTrace_1045917 : CollatzResearch.WordTrace tailWord_1045917 prefixEnd_1045917 159128339469241356630347 := by
  unfold tailWord_1045917
  simp only [CollatzResearch.WordTrace]
  refine ⟨38147726951828812247376005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25431817967885874831584003 38147726951828812247376005)
  ·
    refine ⟨7152698803467902296383001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38147726951828812247376005 7152698803467902296383001)
    ·
      refine ⟨5364524102600926722287251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7152698803467902296383001 5364524102600926722287251)
      ·
        refine ⟨8046786153901390083430877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364524102600926722287251 8046786153901390083430877)
        ·
          refine ⟨3017544807713021281286579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8046786153901390083430877 3017544807713021281286579)
          ·
            refine ⟨4526317211569531921929869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017544807713021281286579 4526317211569531921929869)
            ·
              refine ⟨1697368954338574470723701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4526317211569531921929869 1697368954338574470723701)
              ·
                refine ⟨159128339469241356630347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1697368954338574470723701 159128339469241356630347)
                ·
                  rfl

theorem cell20_1045917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_1045917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045917 prefixEnd_1045917 := by exact prefixLift 1045917
  have htrace : WordTrace (prefixWord ++ tailWord_1045917) baseStart_1045917 baseEnd_1045917 := by
    simpa [prefixWord, tailWord_1045917, baseEnd_1045917] using wordTrace_append hprefix tailTrace_1045917
  have hstable : (prefixWord ++ tailWord_1045917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045917).length < 2 ^ (prefixWord ++ tailWord_1045917).sum := by decide
  have hdescent : baseEnd_1045917 < baseStart_1045917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045954 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1045954 : Nat := 118140960795 + 1045954 * 2 ^ 59
def prefixEnd_1045954 : Nat := 4983230072969 + 3 ^ 40 * 1045954 * 2
def baseEnd_1045954 : Nat := 477401906215916385657557

theorem tailTrace_1045954 : CollatzResearch.WordTrace tailWord_1045954 prefixEnd_1045954 477401906215916385657557 := by
  unfold tailWord_1045954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537269113173691891618229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25432717635129845044315277 9537269113173691891618229)
  ·
    refine ⟨894118979360033614839209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9537269113173691891618229 894118979360033614839209)
    ·
      refine ⟨670589234520025211129407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 894118979360033614839209 670589234520025211129407)
      ·
        refine ⟨1005883851780037816694111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670589234520025211129407 1005883851780037816694111)
        ·
          refine ⟨1508825777670056725041167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005883851780037816694111 1508825777670056725041167)
          ·
            refine ⟨2263238666505085087561751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508825777670056725041167 2263238666505085087561751)
            ·
              refine ⟨3394857999757627631342627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263238666505085087561751 3394857999757627631342627)
              ·
                refine ⟨5092286999636441447013941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394857999757627631342627 5092286999636441447013941)
                ·
                  refine ⟨477401906215916385657557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5092286999636441447013941 477401906215916385657557)
                  ·
                    rfl

theorem cell20_1045954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1045954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045954 prefixEnd_1045954 := by exact prefixLift 1045954
  have htrace : WordTrace (prefixWord ++ tailWord_1045954) baseStart_1045954 baseEnd_1045954 := by
    simpa [prefixWord, tailWord_1045954, baseEnd_1045954] using wordTrace_append hprefix tailTrace_1045954
  have hstable : (prefixWord ++ tailWord_1045954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045954).length < 2 ^ (prefixWord ++ tailWord_1045954).sum := by decide
  have hdescent : baseEnd_1045954 < baseStart_1045954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1045962 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1045962 : Nat := 118140960795 + 1045962 * 2 ^ 59
def prefixEnd_1045962 : Nat := 4983230072969 + 3 ^ 40 * 1045962 * 2
def baseEnd_1045962 : Nat := 477405557633903913390857

theorem tailTrace_1045962 : CollatzResearch.WordTrace tailWord_1045962 prefixEnd_1045962 477405557633903913390857 := by
  unfold tailWord_1045962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537342059166446233191035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25432912157777189955176093 9537342059166446233191035)
  ·
    refine ⟨14306013088749669349786553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9537342059166446233191035 14306013088749669349786553)
    ·
      refine ⟨10729509816562252012339915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14306013088749669349786553 10729509816562252012339915)
      ·
        refine ⟨16094264724843378018509873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729509816562252012339915 16094264724843378018509873)
        ·
          refine ⟨12070698543632533513882405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16094264724843378018509873 12070698543632533513882405)
          ·
            refine ⟨2263255976931100033852951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12070698543632533513882405 2263255976931100033852951)
            ·
              refine ⟨3394883965396650050779427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2263255976931100033852951 3394883965396650050779427)
              ·
                refine ⟨5092325948094975076169141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394883965396650050779427 5092325948094975076169141)
                ·
                  refine ⟨477405557633903913390857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5092325948094975076169141 477405557633903913390857)
                  ·
                    rfl

theorem cell20_1045962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1045962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1045962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1045962 prefixEnd_1045962 := by exact prefixLift 1045962
  have htrace : WordTrace (prefixWord ++ tailWord_1045962) baseStart_1045962 baseEnd_1045962 := by
    simpa [prefixWord, tailWord_1045962, baseEnd_1045962] using wordTrace_append hprefix tailTrace_1045962
  have hstable : (prefixWord ++ tailWord_1045962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1045962).length < 2 ^ (prefixWord ++ tailWord_1045962).sum := by decide
  have hdescent : baseEnd_1045962 < baseStart_1045962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1045962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046020 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 4]
def baseStart_1046020 : Nat := 118140960795 + 1046020 * 2 ^ 59
def prefixEnd_1046020 : Nat := 4983230072969 + 3 ^ 40 * 1046020 * 2
def baseEnd_1046020 : Nat := 477432030414313489457287

theorem tailTrace_1046020 : CollatzResearch.WordTrace tailWord_1046020 prefixEnd_1046020 477432030414313489457287 := by
  unfold tailWord_1046020
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075741835227830419187757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25434322446970440558917009 19075741835227830419187757)
  ·
    refine ⟨7153403188210436407195409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19075741835227830419187757 7153403188210436407195409)
    ·
      refine ⟨5365052391157827305396557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7153403188210436407195409 5365052391157827305396557)
      ·
        refine ⟨2011894646684185239523709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5365052391157827305396557 2011894646684185239523709)
        ·
          refine ⟨754460492506569464821391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2011894646684185239523709 754460492506569464821391)
          ·
            refine ⟨1131690738759854197232087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754460492506569464821391 1131690738759854197232087)
            ·
              refine ⟨1697536108139781295848131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131690738759854197232087 1697536108139781295848131)
              ·
                refine ⟨2546304162209671943772197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697536108139781295848131 2546304162209671943772197)
                ·
                  refine ⟨477432030414313489457287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546304162209671943772197 477432030414313489457287)
                  ·
                    rfl

theorem cell20_1046020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_1046020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046020 prefixEnd_1046020 := by exact prefixLift 1046020
  have htrace : WordTrace (prefixWord ++ tailWord_1046020) baseStart_1046020 baseEnd_1046020 := by
    simpa [prefixWord, tailWord_1046020, baseEnd_1046020] using wordTrace_append hprefix tailTrace_1046020
  have hstable : (prefixWord ++ tailWord_1046020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046020).length < 2 ^ (prefixWord ++ tailWord_1046020).sum := by decide
  have hdescent : baseEnd_1046020 < baseStart_1046020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046024 : List Nat := [2, 1, 3, 2, 1, 1, 2, 6, 2]
def baseStart_1046024 : Nat := 118140960795 + 1046024 * 2 ^ 59
def prefixEnd_1046024 : Nat := 4983230072969 + 3 ^ 40 * 1046024 * 2
def baseEnd_1046024 : Nat := 477433856123307253323937

theorem tailTrace_1046024 : CollatzResearch.WordTrace tailWord_1046024 prefixEnd_1046024 477433856123307253323937 := by
  unfold tailWord_1046024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19075814781220584760760563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25434419708294113014347417 19075814781220584760760563)
  ·
    refine ⟨28613722171830877141140845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19075814781220584760760563 28613722171830877141140845)
    ·
      refine ⟨10730145814436578927927817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28613722171830877141140845 10730145814436578927927817)
      ·
        refine ⟨8047609360827434195945863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10730145814436578927927817 8047609360827434195945863)
        ·
          refine ⟨12071414041241151293918795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047609360827434195945863 12071414041241151293918795)
          ·
            refine ⟨18107121061861726940878193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12071414041241151293918795 18107121061861726940878193)
            ·
              refine ⟨13580340796396295205658645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18107121061861726940878193 13580340796396295205658645)
              ·
                refine ⟨636578474831076337765249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13580340796396295205658645 636578474831076337765249)
                ·
                  refine ⟨477433856123307253323937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636578474831076337765249 477433856123307253323937)
                  ·
                    rfl

theorem cell20_1046024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_1046024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046024 prefixEnd_1046024 := by exact prefixLift 1046024
  have htrace : WordTrace (prefixWord ++ tailWord_1046024) baseStart_1046024 baseEnd_1046024 := by
    simpa [prefixWord, tailWord_1046024, baseEnd_1046024] using wordTrace_append hprefix tailTrace_1046024
  have hstable : (prefixWord ++ tailWord_1046024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046024).length < 2 ^ (prefixWord ++ tailWord_1046024).sum := by decide
  have hdescent : baseEnd_1046024 < baseStart_1046024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046045 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1046045 : Nat := 118140960795 + 1046045 * 2 ^ 59
def prefixEnd_1046045 : Nat := 4983230072969 + 3 ^ 40 * 1046045 * 2
def baseEnd_1046045 : Nat := 477443441095524513623851

theorem tailTrace_1046045 : CollatzResearch.WordTrace tailWord_1046045 prefixEnd_1046045 477443441095524513623851 := by
  unfold tailWord_1046045
  simp only [CollatzResearch.WordTrace]
  refine ⟨38152395495365090108035589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25434930330243393405357059 38152395495365090108035589)
  ·
    refine ⟨7153574155380954395256673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38152395495365090108035589 7153574155380954395256673)
    ·
      refine ⟨5365180616535715796442505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7153574155380954395256673 5365180616535715796442505)
      ·
        refine ⟨4023885462401786847331879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5365180616535715796442505 4023885462401786847331879)
        ·
          refine ⟨6035828193602680270997819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023885462401786847331879 6035828193602680270997819)
          ·
            refine ⟨9053742290404020406496729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035828193602680270997819 9053742290404020406496729)
            ·
              refine ⟨6790306717803015304872547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9053742290404020406496729 6790306717803015304872547)
              ·
                refine ⟨10185460076704522957308821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790306717803015304872547 10185460076704522957308821)
                ·
                  refine ⟨477443441095524513623851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10185460076704522957308821 477443441095524513623851)
                  ·
                    rfl

theorem cell20_1046045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1046045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046045 prefixEnd_1046045 := by exact prefixLift 1046045
  have htrace : WordTrace (prefixWord ++ tailWord_1046045) baseStart_1046045 baseEnd_1046045 := by
    simpa [prefixWord, tailWord_1046045, baseEnd_1046045] using wordTrace_append hprefix tailTrace_1046045
  have hstable : (prefixWord ++ tailWord_1046045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046045).length < 2 ^ (prefixWord ++ tailWord_1046045).sum := by decide
  have hdescent : baseEnd_1046045 < baseStart_1046045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046079 : List Nat := [1, 1, 2, 2, 3, 3, 4, 2, 2]
def baseStart_1046079 : Nat := 118140960795 + 1046079 * 2 ^ 59
def prefixEnd_1046079 : Nat := 4983230072969 + 3 ^ 40 * 1046079 * 2
def baseEnd_1046079 : Nat := 477458959621971506490379

theorem tailTrace_1046079 : CollatzResearch.WordTrace tailWord_1046079 prefixEnd_1046079 477458959621971506490379 := by
  unfold tailWord_1046079
  simp only [CollatzResearch.WordTrace]
  refine ⟨38153635577241913914773291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25435757051494609276515527 38153635577241913914773291)
  ·
    refine ⟨57230453365862870872159937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38153635577241913914773291 57230453365862870872159937)
    ·
      refine ⟨42922840024397153154119953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57230453365862870872159937 42922840024397153154119953)
      ·
        refine ⟨32192130018297864865589965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42922840024397153154119953 32192130018297864865589965)
        ·
          refine ⟨12072048756861699324596237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32192130018297864865589965 12072048756861699324596237)
          ·
            refine ⟨4527018283823137246723589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12072048756861699324596237 4527018283823137246723589)
            ·
              refine ⟨848815928216838233760673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4527018283823137246723589 848815928216838233760673)
              ·
                refine ⟨636611946162628675320505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848815928216838233760673 636611946162628675320505)
                ·
                  refine ⟨477458959621971506490379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636611946162628675320505 477458959621971506490379)
                  ·
                    rfl

theorem cell20_1046079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 2].length) (baseStart_1046079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046079 prefixEnd_1046079 := by exact prefixLift 1046079
  have htrace : WordTrace (prefixWord ++ tailWord_1046079) baseStart_1046079 baseEnd_1046079 := by
    simpa [prefixWord, tailWord_1046079, baseEnd_1046079] using wordTrace_append hprefix tailTrace_1046079
  have hstable : (prefixWord ++ tailWord_1046079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046079).length < 2 ^ (prefixWord ++ tailWord_1046079).sum := by decide
  have hdescent : baseEnd_1046079 < baseStart_1046079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046117 : List Nat := [1, 3, 1, 3, 3, 2, 2, 3, 2]
def baseStart_1046117 : Nat := 118140960795 + 1046117 * 2 ^ 59
def prefixEnd_1046117 : Nat := 4983230072969 + 3 ^ 40 * 1046117 * 2
def baseEnd_1046117 : Nat := 477476303857412263223557

theorem tailTrace_1046117 : CollatzResearch.WordTrace tailWord_1046117 prefixEnd_1046117 477476303857412263223557 := by
  unfold tailWord_1046117
  simp only [CollatzResearch.WordTrace]
  refine ⟨38155021551104246404656605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25436681034069497603104403 38155021551104246404656605)
  ·
    refine ⟨14308133081664092401746227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38155021551104246404656605 14308133081664092401746227)
    ·
      refine ⟨21462199622496138602619341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14308133081664092401746227 21462199622496138602619341)
      ·
        refine ⟨8048324858436051975982253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21462199622496138602619341 8048324858436051975982253)
        ·
          refine ⟨3018121821913519490993345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8048324858436051975982253 3018121821913519490993345)
          ·
            refine ⟨2263591366435139618245009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3018121821913519490993345 2263591366435139618245009)
            ·
              refine ⟨1697693524826354713683757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263591366435139618245009 1697693524826354713683757)
              ·
                refine ⟨636635071809883017631409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1697693524826354713683757 636635071809883017631409)
                ·
                  refine ⟨477476303857412263223557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636635071809883017631409 477476303857412263223557)
                  ·
                    rfl

theorem cell20_1046117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_1046117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046117 prefixEnd_1046117 := by exact prefixLift 1046117
  have htrace : WordTrace (prefixWord ++ tailWord_1046117) baseStart_1046117 baseEnd_1046117 := by
    simpa [prefixWord, tailWord_1046117, baseEnd_1046117] using wordTrace_append hprefix tailTrace_1046117
  have hstable : (prefixWord ++ tailWord_1046117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046117).length < 2 ^ (prefixWord ++ tailWord_1046117).sum := by decide
  have hdescent : baseEnd_1046117 < baseStart_1046117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046128 : List Nat := [2, 1, 1, 1, 6, 2, 7]
def baseStart_1046128 : Nat := 118140960795 + 1046128 * 2 ^ 59
def prefixEnd_1046128 : Nat := 4983230072969 + 3 ^ 40 * 1046128 * 2
def baseEnd_1046128 : Nat := 53053480506349457095205

theorem tailTrace_1046128 : CollatzResearch.WordTrace tailWord_1046128 prefixEnd_1046128 53053480506349457095205 := by
  unfold tailWord_1046128
  simp only [CollatzResearch.WordTrace]
  refine ⟨19077711377032197641653519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25436948502709596855538025 19077711377032197641653519)
  ·
    refine ⟨28616567065548296462480279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19077711377032197641653519 28616567065548296462480279)
    ·
      refine ⟨42924850598322444693720419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28616567065548296462480279 42924850598322444693720419)
      ·
        refine ⟨64387275897483667040580629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42924850598322444693720419 64387275897483667040580629)
        ·
          refine ⟨3018153557694546892527217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64387275897483667040580629 3018153557694546892527217)
          ·
            refine ⟨2263615168270910169395413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3018153557694546892527217 2263615168270910169395413)
            ·
              refine ⟨53053480506349457095205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2263615168270910169395413 53053480506349457095205)
              ·
                rfl

theorem cell20_1046128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 7].length) (baseStart_1046128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046128 prefixEnd_1046128 := by exact prefixLift 1046128
  have htrace : WordTrace (prefixWord ++ tailWord_1046128) baseStart_1046128 baseEnd_1046128 := by
    simpa [prefixWord, tailWord_1046128, baseEnd_1046128] using wordTrace_append hprefix tailTrace_1046128
  have hstable : (prefixWord ++ tailWord_1046128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046128).length < 2 ^ (prefixWord ++ tailWord_1046128).sum := by decide
  have hdescent : baseEnd_1046128 < baseStart_1046128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046148 : List Nat := [2, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_1046148 : Nat := 118140960795 + 1046148 * 2 ^ 59
def prefixEnd_1046148 : Nat := 4983230072969 + 3 ^ 40 * 1046148 * 2
def baseEnd_1046148 : Nat := 477490453102113933190097

theorem tailTrace_1046148 : CollatzResearch.WordTrace tailWord_1046148 prefixEnd_1046148 477490453102113933190097 := by
  unfold tailWord_1046148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078076106995969349517549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25437434809327959132690065 19078076106995969349517549)
  ·
    refine ⟨7154278540123488506069081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19078076106995969349517549 7154278540123488506069081)
    ·
      refine ⟨5365708905092616379551811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7154278540123488506069081 5365708905092616379551811)
      ·
        refine ⟨8048563357638924569327717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5365708905092616379551811 8048563357638924569327717)
        ·
          refine ⟨1509105629557298356748947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8048563357638924569327717 1509105629557298356748947)
          ·
            refine ⟨2263658444335947535123421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509105629557298356748947 2263658444335947535123421)
            ·
              refine ⟨848871916625980325671283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2263658444335947535123421 848871916625980325671283)
              ·
                refine ⟨1273307874938970488506925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848871916625980325671283 1273307874938970488506925)
                ·
                  refine ⟨477490453102113933190097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273307874938970488506925 477490453102113933190097)
                  ·
                    rfl

theorem cell20_1046148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_1046148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046148 prefixEnd_1046148 := by exact prefixLift 1046148
  have htrace : WordTrace (prefixWord ++ tailWord_1046148) baseStart_1046148 baseEnd_1046148 := by
    simpa [prefixWord, tailWord_1046148, baseEnd_1046148] using wordTrace_append hprefix tailTrace_1046148
  have hstable : (prefixWord ++ tailWord_1046148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046148).length < 2 ^ (prefixWord ++ tailWord_1046148).sum := by decide
  have hdescent : baseEnd_1046148 < baseStart_1046148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046172 : List Nat := [2, 2, 3, 2, 3, 2, 1, 3, 2]
def baseStart_1046172 : Nat := 118140960795 + 1046172 * 2 ^ 59
def prefixEnd_1046172 : Nat := 4983230072969 + 3 ^ 40 * 1046172 * 2
def baseEnd_1046172 : Nat := 477501407356076516389999

theorem tailTrace_1046172 : CollatzResearch.WordTrace tailWord_1046172 prefixEnd_1046172 477501407356076516389999 := by
  unfold tailWord_1046172
  simp only [CollatzResearch.WordTrace]
  refine ⟨19078513782952495398954385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25438018377269993865272513 19078513782952495398954385)
  ·
    refine ⟨14308885337214371549215789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19078513782952495398954385 14308885337214371549215789)
    ·
      refine ⟨5365832001455389330955921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14308885337214371549215789 5365832001455389330955921)
      ·
        refine ⟨4024374001091541998216941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5365832001455389330955921 4024374001091541998216941)
        ·
          refine ⟨1509140250409328249331353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4024374001091541998216941 1509140250409328249331353)
          ·
            refine ⟨1131855187806996186998515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509140250409328249331353 1131855187806996186998515)
            ·
              refine ⟨1697782781710494280497773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131855187806996186998515 1697782781710494280497773)
              ·
                refine ⟨636668543141435355186665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1697782781710494280497773 636668543141435355186665)
                ·
                  refine ⟨477501407356076516389999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636668543141435355186665 477501407356076516389999)
                  ·
                    rfl

theorem cell20_1046172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_1046172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046172 prefixEnd_1046172 := by exact prefixLift 1046172
  have htrace : WordTrace (prefixWord ++ tailWord_1046172) baseStart_1046172 baseEnd_1046172 := by
    simpa [prefixWord, tailWord_1046172, baseEnd_1046172] using wordTrace_append hprefix tailTrace_1046172
  have hstable : (prefixWord ++ tailWord_1046172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046172).length < 2 ^ (prefixWord ++ tailWord_1046172).sum := by decide
  have hdescent : baseEnd_1046172 < baseStart_1046172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046204 : List Nat := [2, 2, 2, 3, 1, 2, 1, 7]
def baseStart_1046204 : Nat := 118140960795 + 1046204 * 2 ^ 59
def prefixEnd_1046204 : Nat := 4983230072969 + 3 ^ 40 * 1046204 * 2
def baseEnd_1046204 : Nat := 159172004342675542441067

theorem tailTrace_1046204 : CollatzResearch.WordTrace tailWord_1046204 prefixEnd_1046204 159172004342675542441067 := by
  unfold tailWord_1046204
  simp only [CollatzResearch.WordTrace]
  refine ⟨19079097350894530131536833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25438796467859373508715777 19079097350894530131536833)
  ·
    refine ⟨14309323013170897598652625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19079097350894530131536833 14309323013170897598652625)
    ·
      refine ⟨10731992259878173198989469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14309323013170897598652625 10731992259878173198989469)
      ·
        refine ⟨4024497097454314949621051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10731992259878173198989469 4024497097454314949621051)
        ·
          refine ⟨6036745646181472424431577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024497097454314949621051 6036745646181472424431577)
          ·
            refine ⟨4527559234636104318323683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036745646181472424431577 4527559234636104318323683)
            ·
              refine ⟨6791338851954156477485525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527559234636104318323683 6791338851954156477485525)
              ·
                refine ⟨159172004342675542441067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6791338851954156477485525 159172004342675542441067)
                ·
                  rfl

theorem cell20_1046204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_1046204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046204 prefixEnd_1046204 := by exact prefixLift 1046204
  have htrace : WordTrace (prefixWord ++ tailWord_1046204) baseStart_1046204 baseEnd_1046204 := by
    simpa [prefixWord, tailWord_1046204, baseEnd_1046204] using wordTrace_append hprefix tailTrace_1046204
  have hstable : (prefixWord ++ tailWord_1046204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046204).length < 2 ^ (prefixWord ++ tailWord_1046204).sum := by decide
  have hdescent : baseEnd_1046204 < baseStart_1046204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046248 : List Nat := [2, 1, 4, 1, 3, 3, 2, 2, 2]
def baseStart_1046248 : Nat := 118140960795 + 1046248 * 2 ^ 59
def prefixEnd_1046248 : Nat := 4983230072969 + 3 ^ 40 * 1046248 * 2
def baseEnd_1046248 : Nat := 477536095826958029856355

theorem tailTrace_1046248 : CollatzResearch.WordTrace tailWord_1046248 prefixEnd_1046248 477536095826958029856355 := by
  unfold tailWord_1046248
  simp only [CollatzResearch.WordTrace]
  refine ⟨19079899756814827888837699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25439866342419770518450265 19079899756814827888837699)
  ·
    refine ⟨28619849635222241833256549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19079899756814827888837699 28619849635222241833256549)
    ·
      refine ⟨5366221806604170343735603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28619849635222241833256549 5366221806604170343735603)
      ·
        refine ⟨8049332709906255515603405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366221806604170343735603 8049332709906255515603405)
        ·
          refine ⟨3018499766214845818351277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8049332709906255515603405 3018499766214845818351277)
          ·
            refine ⟨1131937412330567181881729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3018499766214845818351277 1131937412330567181881729)
            ·
              refine ⟨848953059247925386411297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131937412330567181881729 848953059247925386411297)
              ·
                refine ⟨636714794435944039808473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848953059247925386411297 636714794435944039808473)
                ·
                  refine ⟨477536095826958029856355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636714794435944039808473 477536095826958029856355)
                  ·
                    rfl

theorem cell20_1046248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_1046248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046248 prefixEnd_1046248 := by exact prefixLift 1046248
  have htrace : WordTrace (prefixWord ++ tailWord_1046248) baseStart_1046248 baseEnd_1046248 := by
    simpa [prefixWord, tailWord_1046248, baseEnd_1046248] using wordTrace_append hprefix tailTrace_1046248
  have hstable : (prefixWord ++ tailWord_1046248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046248).length < 2 ^ (prefixWord ++ tailWord_1046248).sum := by decide
  have hdescent : baseEnd_1046248 < baseStart_1046248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046321 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 3]
def baseStart_1046321 : Nat := 118140960795 + 1046321 * 2 ^ 59
def prefixEnd_1046321 : Nat := 4983230072969 + 3 ^ 40 * 1046321 * 2
def baseEnd_1046321 : Nat := 477569415016094220422723

theorem tailTrace_1046321 : CollatzResearch.WordTrace tailWord_1046321 prefixEnd_1046321 477569415016094220422723 := by
  unfold tailWord_1046321
  simp only [CollatzResearch.WordTrace]
  refine ⟨38162462042365189245082817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25441641361576792830055211 38162462042365189245082817)
  ·
    refine ⟨28621846531773891933812113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38162462042365189245082817 28621846531773891933812113)
    ·
      refine ⟨21466384898830418950359085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28621846531773891933812113 21466384898830418950359085)
      ·
        refine ⟨8049894337061407106384657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21466384898830418950359085 8049894337061407106384657)
        ·
          refine ⟨6037420752796055329788493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8049894337061407106384657 6037420752796055329788493)
          ·
            refine ⟨2264032782298520748670685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6037420752796055329788493 2264032782298520748670685)
            ·
              refine ⟨849012293361945280751507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2264032782298520748670685 849012293361945280751507)
              ·
                refine ⟨1273518440042917921127261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849012293361945280751507 1273518440042917921127261)
                ·
                  refine ⟨477569415016094220422723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273518440042917921127261 477569415016094220422723)
                  ·
                    rfl

theorem cell20_1046321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_1046321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046321 prefixEnd_1046321 := by exact prefixLift 1046321
  have htrace : WordTrace (prefixWord ++ tailWord_1046321) baseStart_1046321 baseEnd_1046321 := by
    simpa [prefixWord, tailWord_1046321, baseEnd_1046321] using wordTrace_append hprefix tailTrace_1046321
  have hstable : (prefixWord ++ tailWord_1046321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046321).length < 2 ^ (prefixWord ++ tailWord_1046321).sum := by decide
  have hdescent : baseEnd_1046321 < baseStart_1046321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046356 : List Nat := [2, 4, 1, 1, 3, 1, 8]
def baseStart_1046356 : Nat := 118140960795 + 1046356 * 2 ^ 59
def prefixEnd_1046356 : Nat := 4983230072969 + 3 ^ 40 * 1046356 * 2
def baseEnd_1046356 : Nat := 53065043329976628250657

theorem tailTrace_1046356 : CollatzResearch.WordTrace tailWord_1046356 prefixEnd_1046356 53065043329976628250657 := by
  unfold tailWord_1046356
  simp only [CollatzResearch.WordTrace]
  refine ⟨19081869298619195111303461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25442492398158926815071281 19081869298619195111303461)
  ·
    refine ⟨3577850493491099083369399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19081869298619195111303461 3577850493491099083369399)
    ·
      refine ⟨5366775740236648625054099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3577850493491099083369399 5366775740236648625054099)
      ·
        refine ⟨8050163610354972937581149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366775740236648625054099 8050163610354972937581149)
        ·
          refine ⟨3018811353883114851592931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8050163610354972937581149 3018811353883114851592931)
          ·
            refine ⟨4528217030824672277389397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018811353883114851592931 4528217030824672277389397)
            ·
              refine ⟨53065043329976628250657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4528217030824672277389397 53065043329976628250657)
              ·
                rfl

theorem cell20_1046356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 8].length) (baseStart_1046356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046356 prefixEnd_1046356 := by exact prefixLift 1046356
  have htrace : WordTrace (prefixWord ++ tailWord_1046356) baseStart_1046356 baseEnd_1046356 := by
    simpa [prefixWord, tailWord_1046356, baseEnd_1046356] using wordTrace_append hprefix tailTrace_1046356
  have hstable : (prefixWord ++ tailWord_1046356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046356).length < 2 ^ (prefixWord ++ tailWord_1046356).sum := by decide
  have hdescent : baseEnd_1046356 < baseStart_1046356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046380 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 3]
def baseStart_1046380 : Nat := 118140960795 + 1046380 * 2 ^ 59
def prefixEnd_1046380 : Nat := 4983230072969 + 3 ^ 40 * 1046380 * 2
def baseEnd_1046380 : Nat := 477596344223752237455815

theorem tailTrace_1046380 : CollatzResearch.WordTrace tailWord_1046380 prefixEnd_1046380 477596344223752237455815 := by
  unfold tailWord_1046380
  simp only [CollatzResearch.WordTrace]
  refine ⟨19082306974575721160740297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25443075966100961547653729 19082306974575721160740297)
  ·
    refine ⟨14311730230931790870555223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19082306974575721160740297 14311730230931790870555223)
    ·
      refine ⟨21467595346397686305832835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14311730230931790870555223 21467595346397686305832835)
      ·
        refine ⟨32201393019596529458749253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21467595346397686305832835 32201393019596529458749253)
        ·
          refine ⟨6037761191174349273515485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32201393019596529458749253 6037761191174349273515485)
          ·
            refine ⟨2264160446690380977568307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6037761191174349273515485 2264160446690380977568307)
            ·
              refine ⟨3396240670035571466352461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264160446690380977568307 3396240670035571466352461)
              ·
                refine ⟨1273590251263339299882173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3396240670035571466352461 1273590251263339299882173)
                ·
                  refine ⟨477596344223752237455815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273590251263339299882173 477596344223752237455815)
                  ·
                    rfl

theorem cell20_1046380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_1046380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046380 prefixEnd_1046380 := by exact prefixLift 1046380
  have htrace : WordTrace (prefixWord ++ tailWord_1046380) baseStart_1046380 baseEnd_1046380 := by
    simpa [prefixWord, tailWord_1046380, baseEnd_1046380] using wordTrace_append hprefix tailTrace_1046380
  have hstable : (prefixWord ++ tailWord_1046380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046380).length < 2 ^ (prefixWord ++ tailWord_1046380).sum := by decide
  have hdescent : baseEnd_1046380 < baseStart_1046380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046414 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_1046414 : Nat := 118140960795 + 1046414 * 2 ^ 59
def prefixEnd_1046414 : Nat := 4983230072969 + 3 ^ 40 * 1046414 * 2
def baseEnd_1046414 : Nat := 477611862750199230322343

theorem tailTrace_1046414 : CollatzResearch.WordTrace tailWord_1046414 prefixEnd_1046414 477611862750199230322343 := by
  unfold tailWord_1046414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770731753878533266027287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25443902687352177418812197 4770731753878533266027287)
  ·
    refine ⟨7156097630817799899040931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4770731753878533266027287 7156097630817799899040931)
    ·
      refine ⟨10734146446226699848561397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7156097630817799899040931 10734146446226699848561397)
      ·
        refine ⟨1006326229333753110802631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10734146446226699848561397 1006326229333753110802631)
        ·
          refine ⟨1509489344000629666203947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006326229333753110802631 1509489344000629666203947)
          ·
            refine ⟨2264234016000944499305921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1509489344000629666203947 2264234016000944499305921)
            ·
              refine ⟨1698175512000708374479441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2264234016000944499305921 1698175512000708374479441)
              ·
                refine ⟨1273631634000531280859581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698175512000708374479441 1273631634000531280859581)
                ·
                  refine ⟨477611862750199230322343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273631634000531280859581 477611862750199230322343)
                  ·
                    rfl

theorem cell20_1046414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_1046414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046414 prefixEnd_1046414 := by exact prefixLift 1046414
  have htrace : WordTrace (prefixWord ++ tailWord_1046414) baseStart_1046414 baseEnd_1046414 := by
    simpa [prefixWord, tailWord_1046414, baseEnd_1046414] using wordTrace_append hprefix tailTrace_1046414
  have hstable : (prefixWord ++ tailWord_1046414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046414).length < 2 ^ (prefixWord ++ tailWord_1046414).sum := by decide
  have hdescent : baseEnd_1046414 < baseStart_1046414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046449 : List Nat := [1, 2, 2, 4, 2, 2, 3, 4]
def baseStart_1046449 : Nat := 118140960795 + 1046449 * 2 ^ 59
def prefixEnd_1046449 : Nat := 4983230072969 + 3 ^ 40 * 1046449 * 2
def baseEnd_1046449 : Nat := 159209279234631554718511

theorem tailTrace_1046449 : CollatzResearch.WordTrace tailWord_1046449 prefixEnd_1046449 159209279234631554718511 := by
  unfold tailWord_1046449
  simp only [CollatzResearch.WordTrace]
  refine ⟨38167130585901467105742401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25444753723934311403828267 38167130585901467105742401)
  ·
    refine ⟨28625347939426100329306801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38167130585901467105742401 28625347939426100329306801)
    ·
      refine ⟨21469010954569575246980101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28625347939426100329306801 21469010954569575246980101)
      ·
        refine ⟨4025439553981795358808769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21469010954569575246980101 4025439553981795358808769)
        ·
          refine ⟨3019079665486346519106577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025439553981795358808769 3019079665486346519106577)
          ·
            refine ⟨2264309749114759889329933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3019079665486346519106577 2264309749114759889329933)
            ·
              refine ⟨849116155918034958498725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2264309749114759889329933 849116155918034958498725)
              ·
                refine ⟨159209279234631554718511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 849116155918034958498725 159209279234631554718511)
                ·
                  rfl

theorem cell20_1046449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 4].length) (baseStart_1046449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046449 prefixEnd_1046449 := by exact prefixLift 1046449
  have htrace : WordTrace (prefixWord ++ tailWord_1046449) baseStart_1046449 baseEnd_1046449 := by
    simpa [prefixWord, tailWord_1046449, baseEnd_1046449] using wordTrace_append hprefix tailTrace_1046449
  have hstable : (prefixWord ++ tailWord_1046449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046449).length < 2 ^ (prefixWord ++ tailWord_1046449).sum := by decide
  have hdescent : baseEnd_1046449 < baseStart_1046449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046535 : List Nat := [1, 1, 4, 3, 1, 3, 3, 2, 2]
def baseStart_1046535 : Nat := 118140960795 + 1046535 * 2 ^ 59
def prefixEnd_1046535 : Nat := 4983230072969 + 3 ^ 40 * 1046535 * 2
def baseEnd_1046535 : Nat := 477667090447260587288515

theorem tailTrace_1046535 : CollatzResearch.WordTrace tailWord_1046535 prefixEnd_1046535 477667090447260587288515 := by
  unfold tailWord_1046535
  simp only [CollatzResearch.WordTrace]
  refine ⟨38170267263589903793373059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25446844842393269195582039 38170267263589903793373059)
  ·
    refine ⟨57255400895384855690059589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38170267263589903793373059 57255400895384855690059589)
    ·
      refine ⟨10735387667884660441886173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57255400895384855690059589 10735387667884660441886173)
      ·
        refine ⟨4025770375456747665707315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10735387667884660441886173 4025770375456747665707315)
        ·
          refine ⟨6038655563185121498560973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025770375456747665707315 6038655563185121498560973)
          ·
            refine ⟨2264495836194420561960365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6038655563185121498560973 2264495836194420561960365)
            ·
              refine ⟨849185938572907710735137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2264495836194420561960365 849185938572907710735137)
              ·
                refine ⟨636889453929680783051353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849185938572907710735137 636889453929680783051353)
                ·
                  refine ⟨477667090447260587288515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636889453929680783051353 477667090447260587288515)
                  ·
                    rfl

theorem cell20_1046535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 2].length) (baseStart_1046535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046535 prefixEnd_1046535 := by exact prefixLift 1046535
  have htrace : WordTrace (prefixWord ++ tailWord_1046535) baseStart_1046535 baseEnd_1046535 := by
    simpa [prefixWord, tailWord_1046535, baseEnd_1046535] using wordTrace_append hprefix tailTrace_1046535
  have hstable : (prefixWord ++ tailWord_1046535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046535).length < 2 ^ (prefixWord ++ tailWord_1046535).sum := by decide
  have hdescent : baseEnd_1046535 < baseStart_1046535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046541 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1046541 : Nat := 118140960795 + 1046541 * 2 ^ 59
def prefixEnd_1046541 : Nat := 4983230072969 + 3 ^ 40 * 1046541 * 2
def baseEnd_1046541 : Nat := 477669829010751233088491

theorem tailTrace_1046541 : CollatzResearch.WordTrace tailWord_1046541 prefixEnd_1046541 477669829010751233088491 := by
  unfold tailWord_1046541
  simp only [CollatzResearch.WordTrace]
  refine ⟨38170486101568166818091477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25446990734378777878727651 38170486101568166818091477)
  ·
    refine ⟨894620768005503909799019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38170486101568166818091477 894620768005503909799019)
    ·
      refine ⟨1341931152008255864698529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894620768005503909799019 1341931152008255864698529)
      ·
        refine ⟨1006448364006191898523897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1341931152008255864698529 1006448364006191898523897)
        ·
          refine ⟨754836273004643923892923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006448364006191898523897 754836273004643923892923)
          ·
            refine ⟨1132254409506965885839385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754836273004643923892923 1132254409506965885839385)
            ·
              refine ⟨849190807130224414379539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132254409506965885839385 849190807130224414379539)
              ·
                refine ⟨1273786210695336621569309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849190807130224414379539 1273786210695336621569309)
                ·
                  refine ⟨477669829010751233088491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273786210695336621569309 477669829010751233088491)
                  ·
                    rfl

theorem cell20_1046541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1046541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046541 prefixEnd_1046541 := by exact prefixLift 1046541
  have htrace : WordTrace (prefixWord ++ tailWord_1046541) baseStart_1046541 baseEnd_1046541 := by
    simpa [prefixWord, tailWord_1046541, baseEnd_1046541] using wordTrace_append hprefix tailTrace_1046541
  have hstable : (prefixWord ++ tailWord_1046541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046541).length < 2 ^ (prefixWord ++ tailWord_1046541).sum := by decide
  have hdescent : baseEnd_1046541 < baseStart_1046541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046584 : List Nat := [2, 1, 2, 1, 7, 7]
def baseStart_1046584 : Nat := 118140960795 + 1046584 * 2 ^ 59
def prefixEnd_1046584 : Nat := 4983230072969 + 3 ^ 40 * 1046584 * 2
def baseEnd_1046584 : Nat := 17692202051201266468703

theorem tailTrace_1046584 : CollatzResearch.WordTrace tailWord_1046584 prefixEnd_1046584 17692202051201266468703 := by
  unfold tailWord_1046584
  simp only [CollatzResearch.WordTrace]
  refine ⟨19086027220206192580953403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25448036293608256774604537 19086027220206192580953403)
  ·
    refine ⟨28629040830309288871430105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19086027220206192580953403 28629040830309288871430105)
    ·
      refine ⟨21471780622731966653572579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28629040830309288871430105 21471780622731966653572579)
      ·
        refine ⟨32207670934097949980358869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21471780622731966653572579 32207670934097949980358869)
        ·
          refine ⟨754867287517920702664661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32207670934097949980358869 754867287517920702664661)
          ·
            refine ⟨17692202051201266468703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 754867287517920702664661 17692202051201266468703)
            ·
              rfl

theorem cell20_1046584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 7].length) (baseStart_1046584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046584 prefixEnd_1046584 := by exact prefixLift 1046584
  have htrace : WordTrace (prefixWord ++ tailWord_1046584) baseStart_1046584 baseEnd_1046584 := by
    simpa [prefixWord, tailWord_1046584, baseEnd_1046584] using wordTrace_append hprefix tailTrace_1046584
  have hstable : (prefixWord ++ tailWord_1046584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046584).length < 2 ^ (prefixWord ++ tailWord_1046584).sum := by decide
  have hdescent : baseEnd_1046584 < baseStart_1046584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046591 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 3]
def baseStart_1046591 : Nat := 118140960795 + 1046591 * 2 ^ 59
def prefixEnd_1046591 : Nat := 4983230072969 + 3 ^ 40 * 1046591 * 2
def baseEnd_1046591 : Nat := 477692650373173281421619

theorem tailTrace_1046591 : CollatzResearch.WordTrace tailWord_1046591 prefixEnd_1046591 477692650373173281421619 := by
  unfold tailWord_1046591
  simp only [CollatzResearch.WordTrace]
  refine ⟨38172309751387025357411627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25448206500924683571607751 38172309751387025357411627)
  ·
    refine ⟨57258464627080538036117441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38172309751387025357411627 57258464627080538036117441)
    ·
      refine ⟨42943848470310403527088081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57258464627080538036117441 42943848470310403527088081)
      ·
        refine ⟨32207886352732802645316061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42943848470310403527088081 32207886352732802645316061)
        ·
          refine ⟨12077957382274800991993523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32207886352732802645316061 12077957382274800991993523)
          ·
            refine ⟨18116936073412201487990285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12077957382274800991993523 18116936073412201487990285)
            ·
              refine ⟨6793851027529575557996357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18116936073412201487990285 6793851027529575557996357)
              ·
                refine ⟨1273847067661795417124317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6793851027529575557996357 1273847067661795417124317)
                ·
                  refine ⟨477692650373173281421619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1273847067661795417124317 477692650373173281421619)
                  ·
                    rfl

theorem cell20_1046591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_1046591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046591 prefixEnd_1046591 := by exact prefixLift 1046591
  have htrace : WordTrace (prefixWord ++ tailWord_1046591) baseStart_1046591 baseEnd_1046591 := by
    simpa [prefixWord, tailWord_1046591, baseEnd_1046591] using wordTrace_append hprefix tailTrace_1046591
  have hstable : (prefixWord ++ tailWord_1046591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046591).length < 2 ^ (prefixWord ++ tailWord_1046591).sum := by decide
  have hdescent : baseEnd_1046591 < baseStart_1046591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046646 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1046646 : Nat := 118140960795 + 1046646 * 2 ^ 59
def prefixEnd_1046646 : Nat := 4983230072969 + 3 ^ 40 * 1046646 * 2
def baseEnd_1046646 : Nat := 477717753871837534588061

theorem tailTrace_1046646 : CollatzResearch.WordTrace tailWord_1046646 prefixEnd_1046646 477717753871837534588061 := by
  unfold tailWord_1046646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385894735386735609416487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25449543844125179833775861 2385894735386735609416487)
  ·
    refine ⟨3578842103080103414124731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385894735386735609416487 3578842103080103414124731)
    ·
      refine ⟨5368263154620155121187097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3578842103080103414124731 5368263154620155121187097)
      ·
        refine ⟨4026197365965116340890323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5368263154620155121187097 4026197365965116340890323)
        ·
          refine ⟨6039296048947674511335485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026197365965116340890323 6039296048947674511335485)
          ·
            refine ⟨2264736018355377941750807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6039296048947674511335485 2264736018355377941750807)
            ·
              refine ⟨3397104027533066912626211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264736018355377941750807 3397104027533066912626211)
              ·
                refine ⟨5095656041299600368939317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397104027533066912626211 5095656041299600368939317)
                ·
                  refine ⟨477717753871837534588061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5095656041299600368939317 477717753871837534588061)
                  ·
                    rfl

theorem cell20_1046646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1046646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046646 prefixEnd_1046646 := by exact prefixLift 1046646
  have htrace : WordTrace (prefixWord ++ tailWord_1046646) baseStart_1046646 baseEnd_1046646 := by
    simpa [prefixWord, tailWord_1046646, baseEnd_1046646] using wordTrace_append hprefix tailTrace_1046646
  have hstable : (prefixWord ++ tailWord_1046646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046646).length < 2 ^ (prefixWord ++ tailWord_1046646).sum := by decide
  have hdescent : baseEnd_1046646 < baseStart_1046646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046653 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1046653 : Nat := 118140960795 + 1046653 * 2 ^ 59
def prefixEnd_1046653 : Nat := 4983230072969 + 3 ^ 40 * 1046653 * 2
def baseEnd_1046653 : Nat := 477720948862576621354699

theorem tailTrace_1046653 : CollatzResearch.WordTrace tailWord_1046653 prefixEnd_1046653 477720948862576621354699 := by
  unfold tailWord_1046653
  simp only [CollatzResearch.WordTrace]
  refine ⟨38174571077162409946168613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25449714051441606630779075 38174571077162409946168613)
  ·
    refine ⟨7157732076967951864906615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38174571077162409946168613 7157732076967951864906615)
    ·
      refine ⟨10736598115451927797359923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7157732076967951864906615 10736598115451927797359923)
      ·
        refine ⟨16104897173177891696039885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10736598115451927797359923 16104897173177891696039885)
        ·
          refine ⟨6039336439941709386014957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16104897173177891696039885 6039336439941709386014957)
          ·
            refine ⟨2264751164978141019755609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6039336439941709386014957 2264751164978141019755609)
            ·
              refine ⟨1698563373733605764816707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2264751164978141019755609 1698563373733605764816707)
              ·
                refine ⟨2547845060600408647225061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698563373733605764816707 2547845060600408647225061)
                ·
                  refine ⟨477720948862576621354699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2547845060600408647225061 477720948862576621354699)
                  ·
                    rfl

theorem cell20_1046653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1046653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046653 prefixEnd_1046653 := by exact prefixLift 1046653
  have htrace : WordTrace (prefixWord ++ tailWord_1046653) baseStart_1046653 baseEnd_1046653 := by
    simpa [prefixWord, tailWord_1046653, baseEnd_1046653] using wordTrace_append hprefix tailTrace_1046653
  have hstable : (prefixWord ++ tailWord_1046653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046653).length < 2 ^ (prefixWord ++ tailWord_1046653).sum := by decide
  have hdescent : baseEnd_1046653 < baseStart_1046653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046687 : List Nat := [1, 1, 2, 6, 1, 3, 1, 3, 2]
def baseStart_1046687 : Nat := 118140960795 + 1046687 * 2 ^ 59
def prefixEnd_1046687 : Nat := 4983230072969 + 3 ^ 40 * 1046687 * 2
def baseEnd_1046687 : Nat := 477736467389023614221227

theorem tailTrace_1046687 : CollatzResearch.WordTrace tailWord_1046687 prefixEnd_1046687 477736467389023614221227 := by
  unfold tailWord_1046687
  simp only [CollatzResearch.WordTrace]
  refine ⟨38175811159039233752906315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25450540772692822501937543 38175811159039233752906315)
  ·
    refine ⟨57263716738558850629359473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38175811159039233752906315 57263716738558850629359473)
    ·
      refine ⟨42947787553919137972019605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57263716738558850629359473 42947787553919137972019605)
      ·
        refine ⟨2013177541589959592438419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42947787553919137972019605 2013177541589959592438419)
        ·
          refine ⟨3019766312384939388657629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013177541589959592438419 3019766312384939388657629)
          ·
            refine ⟨1132412367144352270746611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3019766312384939388657629 1132412367144352270746611)
            ·
              refine ⟨1698618550716528406119917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132412367144352270746611 1698618550716528406119917)
              ·
                refine ⟨636981956518698152294969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1698618550716528406119917 636981956518698152294969)
                ·
                  refine ⟨477736467389023614221227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636981956518698152294969 477736467389023614221227)
                  ·
                    rfl

theorem cell20_1046687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 2].length) (baseStart_1046687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046687 prefixEnd_1046687 := by exact prefixLift 1046687
  have htrace : WordTrace (prefixWord ++ tailWord_1046687) baseStart_1046687 baseEnd_1046687 := by
    simpa [prefixWord, tailWord_1046687, baseEnd_1046687] using wordTrace_append hprefix tailTrace_1046687
  have hstable : (prefixWord ++ tailWord_1046687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046687).length < 2 ^ (prefixWord ++ tailWord_1046687).sum := by decide
  have hdescent : baseEnd_1046687 < baseStart_1046687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046718 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1046718 : Nat := 118140960795 + 1046718 * 2 ^ 59
def prefixEnd_1046718 : Nat := 4983230072969 + 3 ^ 40 * 1046718 * 2
def baseEnd_1046718 : Nat := 477750616633725284187767

theorem tailTrace_1046718 : CollatzResearch.WordTrace tailWord_1046718 prefixEnd_1046718 477750616633725284187767 := by
  unfold tailWord_1046718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4772117727740865755910601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25451294547951284031523205 4772117727740865755910601)
  ·
    refine ⟨3579088295805649316932951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4772117727740865755910601 3579088295805649316932951)
    ·
      refine ⟨5368632443708473975399427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579088295805649316932951 5368632443708473975399427)
      ·
        refine ⟨8052948665562710963099141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368632443708473975399427 8052948665562710963099141)
        ·
          refine ⟨1509927874793008305581089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8052948665562710963099141 1509927874793008305581089)
          ·
            refine ⟨1132445906094756229185817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509927874793008305581089 1132445906094756229185817)
            ·
              refine ⟨849334429571067171889363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132445906094756229185817 849334429571067171889363)
              ·
                refine ⟨1274001644356600757834045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849334429571067171889363 1274001644356600757834045)
                ·
                  refine ⟨477750616633725284187767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274001644356600757834045 477750616633725284187767)
                  ·
                    rfl

theorem cell20_1046718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1046718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046718 prefixEnd_1046718 := by exact prefixLift 1046718
  have htrace : WordTrace (prefixWord ++ tailWord_1046718) baseStart_1046718 baseEnd_1046718 := by
    simpa [prefixWord, tailWord_1046718, baseEnd_1046718] using wordTrace_append hprefix tailTrace_1046718
  have hstable : (prefixWord ++ tailWord_1046718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046718).length < 2 ^ (prefixWord ++ tailWord_1046718).sum := by decide
  have hdescent : baseEnd_1046718 < baseStart_1046718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046757 : List Nat := [1, 3, 1, 4, 2, 9]
def baseStart_1046757 : Nat := 118140960795 + 1046757 * 2 ^ 59
def prefixEnd_1046757 : Nat := 4983230072969 + 3 ^ 40 * 1046757 * 2
def baseEnd_1046757 : Nat := 17695126566533869699541

theorem tailTrace_1046757 : CollatzResearch.WordTrace tailWord_1046757 prefixEnd_1046757 17695126566533869699541 := by
  unfold tailWord_1046757
  simp only [CollatzResearch.WordTrace]
  refine ⟨38178364268785635707954525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25452242845857090471969683 38178364268785635707954525)
  ·
    refine ⟨14316886600794613390482947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38178364268785635707954525 14316886600794613390482947)
    ·
      refine ⟨21475329901191920085724421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14316886600794613390482947 21475329901191920085724421)
      ·
        refine ⟨4026624356473485016073329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21475329901191920085724421 4026624356473485016073329)
        ·
          refine ⟨3019968267355113762054997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4026624356473485016073329 3019968267355113762054997)
          ·
            refine ⟨17695126566533869699541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3019968267355113762054997 17695126566533869699541)
            ·
              rfl

theorem cell20_1046757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 9].length) (baseStart_1046757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046757 prefixEnd_1046757 := by exact prefixLift 1046757
  have htrace : WordTrace (prefixWord ++ tailWord_1046757) baseStart_1046757 baseEnd_1046757 := by
    simpa [prefixWord, tailWord_1046757, baseEnd_1046757] using wordTrace_append hprefix tailTrace_1046757
  have hstable : (prefixWord ++ tailWord_1046757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046757).length < 2 ^ (prefixWord ++ tailWord_1046757).sum := by decide
  have hdescent : baseEnd_1046757 < baseStart_1046757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046760 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_1046760 : Nat := 118140960795 + 1046760 * 2 ^ 59
def prefixEnd_1046760 : Nat := 4983230072969 + 3 ^ 40 * 1046760 * 2
def baseEnd_1046760 : Nat := 477769786578159804787595

theorem tailTrace_1046760 : CollatzResearch.WordTrace tailWord_1046760 prefixEnd_1046760 477769786578159804787595 := by
  unfold tailWord_1046760
  simp only [CollatzResearch.WordTrace]
  refine ⟨19089236843887383610156867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25452315791849844813542489 19089236843887383610156867)
  ·
    refine ⟨28633855265831075415235301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19089236843887383610156867 28633855265831075415235301)
    ·
      refine ⟨5368847862343326640356619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28633855265831075415235301 5368847862343326640356619)
      ·
        refine ⟨8053271793514989960534929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368847862343326640356619 8053271793514989960534929)
        ·
          refine ⟨6039953845136242470401197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8053271793514989960534929 6039953845136242470401197)
          ·
            refine ⟨2264982691926090926400449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6039953845136242470401197 2264982691926090926400449)
            ·
              refine ⟨1698737018944568194800337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2264982691926090926400449 1698737018944568194800337)
              ·
                refine ⟨1274052764208426146100253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698737018944568194800337 1274052764208426146100253)
                ·
                  refine ⟨477769786578159804787595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274052764208426146100253 477769786578159804787595)
                  ·
                    rfl

theorem cell20_1046760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_1046760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046760 prefixEnd_1046760 := by exact prefixLift 1046760
  have htrace : WordTrace (prefixWord ++ tailWord_1046760) baseStart_1046760 baseEnd_1046760 := by
    simpa [prefixWord, tailWord_1046760, baseEnd_1046760] using wordTrace_append hprefix tailTrace_1046760
  have hstable : (prefixWord ++ tailWord_1046760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046760).length < 2 ^ (prefixWord ++ tailWord_1046760).sum := by decide
  have hdescent : baseEnd_1046760 < baseStart_1046760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046774 : List Nat := [5, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1046774 : Nat := 118140960795 + 1046774 * 2 ^ 59
def prefixEnd_1046774 : Nat := 4983230072969 + 3 ^ 40 * 1046774 * 2
def baseEnd_1046774 : Nat := 159258725519879326106957

theorem tailTrace_1046774 : CollatzResearch.WordTrace tailWord_1046774 prefixEnd_1046774 159258725519879326106957 := by
  unfold tailWord_1046774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386186519357752975707711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25452656206482698407548917 2386186519357752975707711)
  ·
    refine ⟨3579279779036629463561567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2386186519357752975707711 3579279779036629463561567)
    ·
      refine ⟨5368919668554944195342351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579279779036629463561567 5368919668554944195342351)
      ·
        refine ⟨8053379502832416293013527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5368919668554944195342351 8053379502832416293013527)
        ·
          refine ⟨12080069254248624439520291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053379502832416293013527 12080069254248624439520291)
          ·
            refine ⟨18120103881372936659280437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12080069254248624439520291 18120103881372936659280437)
            ·
              refine ⟨1698759738878712811807541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18120103881372936659280437 1698759738878712811807541)
              ·
                refine ⟨159258725519879326106957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1698759738878712811807541 159258725519879326106957)
                ·
                  rfl

theorem cell20_1046774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1046774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046774 prefixEnd_1046774 := by exact prefixLift 1046774
  have htrace : WordTrace (prefixWord ++ tailWord_1046774) baseStart_1046774 baseEnd_1046774 := by
    simpa [prefixWord, tailWord_1046774, baseEnd_1046774] using wordTrace_append hprefix tailTrace_1046774
  have hstable : (prefixWord ++ tailWord_1046774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046774).length < 2 ^ (prefixWord ++ tailWord_1046774).sum := by decide
  have hdescent : baseEnd_1046774 < baseStart_1046774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046805 : List Nat := [1, 3, 2, 1, 2, 1, 3, 5, 2]
def baseStart_1046805 : Nat := 118140960795 + 1046805 * 2 ^ 59
def prefixEnd_1046805 : Nat := 4983230072969 + 3 ^ 40 * 1046805 * 2
def baseEnd_1046805 : Nat := 477790325804339648287411

theorem tailTrace_1046805 : CollatzResearch.WordTrace tailWord_1046805 prefixEnd_1046805 477790325804339648287411 := by
  unfold tailWord_1046805
  simp only [CollatzResearch.WordTrace]
  refine ⟨38180114972611739905701869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25453409981741159937134579 38180114972611739905701869)
  ·
    refine ⟨14317543114729402464638201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38180114972611739905701869 14317543114729402464638201)
    ·
      refine ⟨10738157336047051848478651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14317543114729402464638201 10738157336047051848478651)
      ·
        refine ⟨16107236004070577772717977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738157336047051848478651 16107236004070577772717977)
        ·
          refine ⟨12080427003052933329538483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16107236004070577772717977 12080427003052933329538483)
          ·
            refine ⟨18120640504579399994307725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12080427003052933329538483 18120640504579399994307725)
            ·
              refine ⟨6795240189217274997865397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18120640504579399994307725 6795240189217274997865397)
              ·
                refine ⟨637053767739119531049881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6795240189217274997865397 637053767739119531049881)
                ·
                  refine ⟨477790325804339648287411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637053767739119531049881 477790325804339648287411)
                  ·
                    rfl

theorem cell20_1046805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_1046805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046805 prefixEnd_1046805 := by exact prefixLift 1046805
  have htrace : WordTrace (prefixWord ++ tailWord_1046805) baseStart_1046805 baseEnd_1046805 := by
    simpa [prefixWord, tailWord_1046805, baseEnd_1046805] using wordTrace_append hprefix tailTrace_1046805
  have hstable : (prefixWord ++ tailWord_1046805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046805).length < 2 ^ (prefixWord ++ tailWord_1046805).sum := by decide
  have hdescent : baseEnd_1046805 < baseStart_1046805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046888 : List Nat := [2, 1, 4, 2, 2, 2, 2, 5]
def baseStart_1046888 : Nat := 118140960795 + 1046888 * 2 ^ 59
def prefixEnd_1046888 : Nat := 4983230072969 + 3 ^ 40 * 1046888 * 2
def baseEnd_1046888 : Nat := 159276069755320082840135

theorem tailTrace_1046888 : CollatzResearch.WordTrace tailWord_1046888 prefixEnd_1046888 159276069755320082840135 := by
  unfold tailWord_1046888
  simp only [CollatzResearch.WordTrace]
  refine ⟨19091571115655522540486659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25455428154207363387315545 19091571115655522540486659)
  ·
    refine ⟨28637356673483283810729989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19091571115655522540486659 28637356673483283810729989)
    ·
      refine ⟨5369504376278115714511873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28637356673483283810729989 5369504376278115714511873)
      ·
        refine ⟨4027128282208586785883905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5369504376278115714511873 4027128282208586785883905)
        ·
          refine ⟨3020346211656440089412929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4027128282208586785883905 3020346211656440089412929)
          ·
            refine ⟨2265259658742330067059697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3020346211656440089412929 2265259658742330067059697)
            ·
              refine ⟨1698944744056747550294773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265259658742330067059697 1698944744056747550294773)
              ·
                refine ⟨159276069755320082840135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1698944744056747550294773 159276069755320082840135)
                ·
                  rfl

theorem cell20_1046888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_1046888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046888 prefixEnd_1046888 := by exact prefixLift 1046888
  have htrace : WordTrace (prefixWord ++ tailWord_1046888) baseStart_1046888 baseEnd_1046888 := by
    simpa [prefixWord, tailWord_1046888, baseEnd_1046888] using wordTrace_append hprefix tailTrace_1046888
  have hstable : (prefixWord ++ tailWord_1046888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046888).length < 2 ^ (prefixWord ++ tailWord_1046888).sum := by decide
  have hdescent : baseEnd_1046888 < baseStart_1046888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046909 : List Nat := [1, 4, 1, 1, 2, 3, 2, 6]
def baseStart_1046909 : Nat := 118140960795 + 1046909 * 2 ^ 59
def prefixEnd_1046909 : Nat := 4983230072969 + 3 ^ 40 * 1046909 * 2
def baseEnd_1046909 : Nat := 159279264746059169606773

theorem tailTrace_1046909 : CollatzResearch.WordTrace tailWord_1046909 prefixEnd_1046909 159279264746059169606773 := by
  unfold tailWord_1046909
  simp only [CollatzResearch.WordTrace]
  refine ⟨38183908164234965667487781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25455938776156643778325187 38183908164234965667487781)
  ·
    refine ⟨7159482780794056062653959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38183908164234965667487781 7159482780794056062653959)
    ·
      refine ⟨10739224171191084093980939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7159482780794056062653959 10739224171191084093980939)
      ·
        refine ⟨16108836256786626140971409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739224171191084093980939 16108836256786626140971409)
        ·
          refine ⟨12081627192589969605728557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16108836256786626140971409 12081627192589969605728557)
          ·
            refine ⟨4530610197221238602148209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12081627192589969605728557 4530610197221238602148209)
            ·
              refine ⟨3397957647915928951611157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4530610197221238602148209 3397957647915928951611157)
              ·
                refine ⟨159279264746059169606773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3397957647915928951611157 159279264746059169606773)
                ·
                  rfl

theorem cell20_1046909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_1046909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046909 prefixEnd_1046909 := by exact prefixLift 1046909
  have htrace : WordTrace (prefixWord ++ tailWord_1046909) baseStart_1046909 baseEnd_1046909 := by
    simpa [prefixWord, tailWord_1046909, baseEnd_1046909] using wordTrace_append hprefix tailTrace_1046909
  have hstable : (prefixWord ++ tailWord_1046909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046909).length < 2 ^ (prefixWord ++ tailWord_1046909).sum := by decide
  have hdescent : baseEnd_1046909 < baseStart_1046909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046919 : List Nat := [1, 1, 4, 2, 2, 1, 2, 5, 2]
def baseStart_1046919 : Nat := 118140960795 + 1046919 * 2 ^ 59
def prefixEnd_1046919 : Nat := 4983230072969 + 3 ^ 40 * 1046919 * 2
def baseEnd_1046919 : Nat := 477842358510661918486945

theorem tailTrace_1046919 : CollatzResearch.WordTrace tailWord_1046919 prefixEnd_1046919 477842358510661918486945 := by
  unfold tailWord_1046919
  simp only [CollatzResearch.WordTrace]
  refine ⟨38184272894198737375351811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25456181929465824916901207 38184272894198737375351811)
  ·
    refine ⟨57276409341298106063027717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38184272894198737375351811 57276409341298106063027717)
    ·
      refine ⟨10739326751493394886817697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57276409341298106063027717 10739326751493394886817697)
      ·
        refine ⟨8054495063620046165113273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10739326751493394886817697 8054495063620046165113273)
        ·
          refine ⟨6040871297715034623834955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8054495063620046165113273 6040871297715034623834955)
          ·
            refine ⟨9061306946572551935752433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040871297715034623834955 9061306946572551935752433)
            ·
              refine ⟨6795980209929413951814325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9061306946572551935752433 6795980209929413951814325)
              ·
                refine ⟨637123144680882557982593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6795980209929413951814325 637123144680882557982593)
                ·
                  refine ⟨477842358510661918486945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637123144680882557982593 477842358510661918486945)
                  ·
                    rfl

theorem cell20_1046919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 2].length) (baseStart_1046919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046919 prefixEnd_1046919 := by exact prefixLift 1046919
  have htrace : WordTrace (prefixWord ++ tailWord_1046919) baseStart_1046919 baseEnd_1046919 := by
    simpa [prefixWord, tailWord_1046919, baseEnd_1046919] using wordTrace_append hprefix tailTrace_1046919
  have hstable : (prefixWord ++ tailWord_1046919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046919).length < 2 ^ (prefixWord ++ tailWord_1046919).sum := by decide
  have hdescent : baseEnd_1046919 < baseStart_1046919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046932 : List Nat := [2, 4, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1046932 : Nat := 118140960795 + 1046932 * 2 ^ 59
def prefixEnd_1046932 : Nat := 4983230072969 + 3 ^ 40 * 1046932 * 2
def baseEnd_1046932 : Nat := 477848292064891651053559

theorem tailTrace_1046932 : CollatzResearch.WordTrace tailWord_1046932 prefixEnd_1046932 477848292064891651053559 := by
  unfold tailWord_1046932
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092373521575820297787525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25456498028767760397050033 19092373521575820297787525)
  ·
    refine ⟨3579820035295466305835161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19092373521575820297787525 3579820035295466305835161)
    ·
      refine ⟨2684865026471599729376371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3579820035295466305835161 2684865026471599729376371)
      ·
        refine ⟨4027297539707399594064557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2684865026471599729376371 4027297539707399594064557)
        ·
          refine ⟨1510236577390274847774209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4027297539707399594064557 1510236577390274847774209)
          ·
            refine ⟨1132677433042706135830657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510236577390274847774209 1132677433042706135830657)
            ·
              refine ⟨849508074782029601872993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132677433042706135830657 849508074782029601872993)
              ·
                refine ⟨637131056086522201404745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849508074782029601872993 637131056086522201404745)
                ·
                  refine ⟨477848292064891651053559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637131056086522201404745 477848292064891651053559)
                  ·
                    rfl

theorem cell20_1046932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1046932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046932 prefixEnd_1046932 := by exact prefixLift 1046932
  have htrace : WordTrace (prefixWord ++ tailWord_1046932) baseStart_1046932 baseEnd_1046932 := by
    simpa [prefixWord, tailWord_1046932, baseEnd_1046932] using wordTrace_append hprefix tailTrace_1046932
  have hstable : (prefixWord ++ tailWord_1046932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046932).length < 2 ^ (prefixWord ++ tailWord_1046932).sum := by decide
  have hdescent : baseEnd_1046932 < baseStart_1046932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046936 : List Nat := [2, 1, 2, 5, 1, 2, 1, 4, 2]
def baseStart_1046936 : Nat := 118140960795 + 1046936 * 2 ^ 59
def prefixEnd_1046936 : Nat := 4983230072969 + 3 ^ 40 * 1046936 * 2
def baseEnd_1046936 : Nat := 477850117773885414920209

theorem tailTrace_1046936 : CollatzResearch.WordTrace tailWord_1046936 prefixEnd_1046936 477850117773885414920209 := by
  unfold tailWord_1046936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19092446467568574639360331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25456595290091432852480441 19092446467568574639360331)
  ·
    refine ⟨28638669701352861959040497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19092446467568574639360331 28638669701352861959040497)
    ·
      refine ⟨21479002276014646469280373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28638669701352861959040497 21479002276014646469280373)
      ·
        refine ⟨2013656463376373106495035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21479002276014646469280373 2013656463376373106495035)
        ·
          refine ⟨3020484695064559659742553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013656463376373106495035 3020484695064559659742553)
          ·
            refine ⟨2265363521298419744806915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3020484695064559659742553 2265363521298419744806915)
            ·
              refine ⟨3398045281947629617210373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265363521298419744806915 3398045281947629617210373)
              ·
                refine ⟨637133490365180553226945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3398045281947629617210373 637133490365180553226945)
                ·
                  refine ⟨477850117773885414920209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637133490365180553226945 477850117773885414920209)
                  ·
                    rfl

theorem cell20_1046936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_1046936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046936 prefixEnd_1046936 := by exact prefixLift 1046936
  have htrace : WordTrace (prefixWord ++ tailWord_1046936) baseStart_1046936 baseEnd_1046936 := by
    simpa [prefixWord, tailWord_1046936, baseEnd_1046936] using wordTrace_append hprefix tailTrace_1046936
  have hstable : (prefixWord ++ tailWord_1046936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046936).length < 2 ^ (prefixWord ++ tailWord_1046936).sum := by decide
  have hdescent : baseEnd_1046936 < baseStart_1046936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1046947 : List Nat := [1, 1, 1, 4, 1, 4, 3, 5]
def baseStart_1046947 : Nat := 118140960795 + 1046947 * 2 ^ 59
def prefixEnd_1046947 : Nat := 4983230072969 + 3 ^ 40 * 1046947 * 2
def baseEnd_1046947 : Nat := 159285046157872755184499

theorem tailTrace_1046947 : CollatzResearch.WordTrace tailWord_1046947 prefixEnd_1046947 159285046157872755184499 := by
  unfold tailWord_1046947
  simp only [CollatzResearch.WordTrace]
  refine ⟨38185294138097298157371095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25456862758731532104914063 38185294138097298157371095)
  ·
    refine ⟨57277941207145947236056643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38185294138097298157371095 57277941207145947236056643)
    ·
      refine ⟨85916911810718920854084965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57277941207145947236056643 85916911810718920854084965)
      ·
        refine ⟨16109420964509797660140931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85916911810718920854084965 16109420964509797660140931)
        ·
          refine ⟨24164131446764696490211397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16109420964509797660140931 24164131446764696490211397)
          ·
            refine ⟨4530774646268380591914637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24164131446764696490211397 4530774646268380591914637)
            ·
              refine ⟨1699040492350642721967989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4530774646268380591914637 1699040492350642721967989)
              ·
                refine ⟨159285046157872755184499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699040492350642721967989 159285046157872755184499)
                ·
                  rfl

theorem cell20_1046947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_1046947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1046947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1046947 prefixEnd_1046947 := by exact prefixLift 1046947
  have htrace : WordTrace (prefixWord ++ tailWord_1046947) baseStart_1046947 baseEnd_1046947 := by
    simpa [prefixWord, tailWord_1046947, baseEnd_1046947] using wordTrace_append hprefix tailTrace_1046947
  have hstable : (prefixWord ++ tailWord_1046947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1046947).length < 2 ^ (prefixWord ++ tailWord_1046947).sum := by decide
  have hdescent : baseEnd_1046947 < baseStart_1046947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1046947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047016 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_1047016 : Nat := 118140960795 + 1047016 * 2 ^ 59
def prefixEnd_1047016 : Nat := 4983230072969 + 3 ^ 40 * 1047016 * 2
def baseEnd_1047016 : Nat := 477886631953760692253215

theorem tailTrace_1047016 : CollatzResearch.WordTrace tailWord_1047016 prefixEnd_1047016 477886631953760692253215 := by
  unfold tailWord_1047016
  simp only [CollatzResearch.WordTrace]
  refine ⟨19093905387423661470816451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25458540516564881961088601 19093905387423661470816451)
  ·
    refine ⟨28640858081135492206224677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19093905387423661470816451 28640858081135492206224677)
    ·
      refine ⟨5370160890212904788667127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28640858081135492206224677 5370160890212904788667127)
      ·
        refine ⟨8055241335319357183000691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5370160890212904788667127 8055241335319357183000691)
        ·
          refine ⟨12082862002979035774501037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055241335319357183000691 12082862002979035774501037)
          ·
            refine ⟨4531073251117138415437889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12082862002979035774501037 4531073251117138415437889)
            ·
              refine ⟨3398304938337853811578417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4531073251117138415437889 3398304938337853811578417)
              ·
                refine ⟨2548728703753390358683813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3398304938337853811578417 2548728703753390358683813)
                ·
                  refine ⟨477886631953760692253215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2548728703753390358683813 477886631953760692253215)
                  ·
                    rfl

theorem cell20_1047016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_1047016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047016 prefixEnd_1047016 := by exact prefixLift 1047016
  have htrace : WordTrace (prefixWord ++ tailWord_1047016) baseStart_1047016 baseEnd_1047016 := by
    simpa [prefixWord, tailWord_1047016, baseEnd_1047016] using wordTrace_append hprefix tailTrace_1047016
  have hstable : (prefixWord ++ tailWord_1047016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047016).length < 2 ^ (prefixWord ++ tailWord_1047016).sum := by decide
  have hdescent : baseEnd_1047016 < baseStart_1047016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047033 : List Nat := [1, 2, 1, 3, 1, 2, 5, 3, 2]
def baseStart_1047033 : Nat := 118140960795 + 1047033 * 2 ^ 59
def prefixEnd_1047033 : Nat := 4983230072969 + 3 ^ 40 * 1047033 * 2
def baseEnd_1047033 : Nat := 477894391216984188686479

theorem tailTrace_1047033 : CollatzResearch.WordTrace tailWord_1047033 prefixEnd_1047033 477894391216984188686479 := by
  unfold tailWord_1047033
  simp only [CollatzResearch.WordTrace]
  refine ⟨38188430815785734845001753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25458953877190489896667835 38188430815785734845001753)
  ·
    refine ⟨28641323111839301133751315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38188430815785734845001753 28641323111839301133751315)
    ·
      refine ⟨42961984667758951700626973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28641323111839301133751315 42961984667758951700626973)
      ·
        refine ⟨16110744250409606887735115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42961984667758951700626973 16110744250409606887735115)
        ·
          refine ⟨24166116375614410331602673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16110744250409606887735115 24166116375614410331602673)
          ·
            refine ⟨18124587281710807748702005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24166116375614410331602673 18124587281710807748702005)
            ·
              refine ⟨1699180057660388226440813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18124587281710807748702005 1699180057660388226440813)
              ·
                refine ⟨637192521622645584915305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1699180057660388226440813 637192521622645584915305)
                ·
                  refine ⟨477894391216984188686479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637192521622645584915305 477894391216984188686479)
                  ·
                    rfl

theorem cell20_1047033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_1047033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047033 prefixEnd_1047033 := by exact prefixLift 1047033
  have htrace : WordTrace (prefixWord ++ tailWord_1047033) baseStart_1047033 baseEnd_1047033 := by
    simpa [prefixWord, tailWord_1047033, baseEnd_1047033] using wordTrace_append hprefix tailTrace_1047033
  have hstable : (prefixWord ++ tailWord_1047033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047033).length < 2 ^ (prefixWord ++ tailWord_1047033).sum := by decide
  have hdescent : baseEnd_1047033 < baseStart_1047033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047046 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1047046 : Nat := 118140960795 + 1047046 * 2 ^ 59
def prefixEnd_1047046 : Nat := 4983230072969 + 3 ^ 40 * 1047046 * 2
def baseEnd_1047046 : Nat := 477900324771213921253093

theorem tailTrace_1047046 : CollatzResearch.WordTrace tailWord_1047046 prefixEnd_1047046 477900324771213921253093 := by
  unfold tailWord_1047046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193403280148082439538281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25459269976492425376816661 1193403280148082439538281)
  ·
    refine ⟨895052460111061829653711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1193403280148082439538281 895052460111061829653711)
    ·
      refine ⟨1342578690166592744480567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895052460111061829653711 1342578690166592744480567)
      ·
        refine ⟨2013868035249889116720851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342578690166592744480567 2013868035249889116720851)
        ·
          refine ⟨3020802052874833675081277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013868035249889116720851 3020802052874833675081277)
          ·
            refine ⟨1132800769828062628155479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3020802052874833675081277 1132800769828062628155479)
            ·
              refine ⟨1699201154742093942233219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132800769828062628155479 1699201154742093942233219)
              ·
                refine ⟨2548801732113140913349829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699201154742093942233219 2548801732113140913349829)
                ·
                  refine ⟨477900324771213921253093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2548801732113140913349829 477900324771213921253093)
                  ·
                    rfl

theorem cell20_1047046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1047046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047046 prefixEnd_1047046 := by exact prefixLift 1047046
  have htrace : WordTrace (prefixWord ++ tailWord_1047046) baseStart_1047046 baseEnd_1047046 := by
    simpa [prefixWord, tailWord_1047046, baseEnd_1047046] using wordTrace_append hprefix tailTrace_1047046
  have hstable : (prefixWord ++ tailWord_1047046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047046).length < 2 ^ (prefixWord ++ tailWord_1047046).sum := by decide
  have hdescent : baseEnd_1047046 < baseStart_1047046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047050 : List Nat := [3, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_1047050 : Nat := 118140960795 + 1047050 * 2 ^ 59
def prefixEnd_1047050 : Nat := 4983230072969 + 3 ^ 40 * 1047050 * 2
def baseEnd_1047050 : Nat := 477902150480207685119743

theorem tailTrace_1047050 : CollatzResearch.WordTrace tailWord_1047050 prefixEnd_1047050 477902150480207685119743 := by
  unfold tailWord_1047050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9547262714181036687092651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25459367237816097832247069 9547262714181036687092651)
  ·
    refine ⟨14320894071271555030638977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9547262714181036687092651 14320894071271555030638977)
    ·
      refine ⟨10740670553453666272979233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14320894071271555030638977 10740670553453666272979233)
      ·
        refine ⟨8055502915090249704734425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10740670553453666272979233 8055502915090249704734425)
        ·
          refine ⟨6041627186317687278550819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8055502915090249704734425 6041627186317687278550819)
          ·
            refine ⟨9062440779476530917826229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041627186317687278550819 9062440779476530917826229)
            ·
              refine ⟨849603823075924773546209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9062440779476530917826229 849603823075924773546209)
              ·
                refine ⟨637202867306943580159657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849603823075924773546209 637202867306943580159657)
                ·
                  refine ⟨477902150480207685119743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637202867306943580159657 477902150480207685119743)
                  ·
                    rfl

theorem cell20_1047050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_1047050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047050 prefixEnd_1047050 := by exact prefixLift 1047050
  have htrace : WordTrace (prefixWord ++ tailWord_1047050) baseStart_1047050 baseEnd_1047050 := by
    simpa [prefixWord, tailWord_1047050, baseEnd_1047050] using wordTrace_append hprefix tailTrace_1047050
  have hstable : (prefixWord ++ tailWord_1047050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047050).length < 2 ^ (prefixWord ++ tailWord_1047050).sum := by decide
  have hdescent : baseEnd_1047050 < baseStart_1047050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047060 : List Nat := [2, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1047060 : Nat := 118140960795 + 1047060 * 2 ^ 59
def prefixEnd_1047060 : Nat := 4983230072969 + 3 ^ 40 * 1047060 * 2
def baseEnd_1047060 : Nat := 477906714752692094786369

theorem tailTrace_1047060 : CollatzResearch.WordTrace tailWord_1047060 prefixEnd_1047060 477906714752692094786369 := by
  unfold tailWord_1047060
  simp only [CollatzResearch.WordTrace]
  refine ⟨19094707793343959228117317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25459610391125278970823089 19094707793343959228117317)
  ·
    refine ⟨3580257711251992355271997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19094707793343959228117317 3580257711251992355271997)
    ·
      refine ⟨1342596641719497133226999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3580257711251992355271997 1342596641719497133226999)
      ·
        refine ⟨2013894962579245699840499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342596641719497133226999 2013894962579245699840499)
        ·
          refine ⟨3020842443868868549760749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013894962579245699840499 3020842443868868549760749)
          ·
            refine ⟨1132815916450825706160281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3020842443868868549760749 1132815916450825706160281)
            ·
              refine ⟨849611937338119279620211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132815916450825706160281 849611937338119279620211)
              ·
                refine ⟨1274417906007178919430317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849611937338119279620211 1274417906007178919430317)
                ·
                  refine ⟨477906714752692094786369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274417906007178919430317 477906714752692094786369)
                  ·
                    rfl

theorem cell20_1047060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1047060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047060 prefixEnd_1047060 := by exact prefixLift 1047060
  have htrace : WordTrace (prefixWord ++ tailWord_1047060) baseStart_1047060 baseEnd_1047060 := by
    simpa [prefixWord, tailWord_1047060, baseEnd_1047060] using wordTrace_append hprefix tailTrace_1047060
  have hstable : (prefixWord ++ tailWord_1047060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047060).length < 2 ^ (prefixWord ++ tailWord_1047060).sum := by decide
  have hdescent : baseEnd_1047060 < baseStart_1047060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047061 : List Nat := [1, 3, 2, 1, 3, 1, 4, 5]
def baseStart_1047061 : Nat := 118140960795 + 1047061 * 2 ^ 59
def prefixEnd_1047061 : Nat := 4983230072969 + 3 ^ 40 * 1047061 * 2
def baseEnd_1047061 : Nat := 159302390393313511917677

theorem tailTrace_1047061 : CollatzResearch.WordTrace tailWord_1047061 prefixEnd_1047061 159302390393313511917677 := by
  unfold tailWord_1047061
  simp only [CollatzResearch.WordTrace]
  refine ⟨38189452059684295627021037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25459634706456197084680691 38189452059684295627021037)
  ·
    refine ⟨14321044522381610860132889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38189452059684295627021037 14321044522381610860132889)
    ·
      refine ⟨10740783391786208145099667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14321044522381610860132889 10740783391786208145099667)
      ·
        refine ⟨16111175087679312217649501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740783391786208145099667 16111175087679312217649501)
        ·
          refine ⟨6041690657879742081618563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16111175087679312217649501 6041690657879742081618563)
          ·
            refine ⟨9062535986819613122427845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041690657879742081618563 9062535986819613122427845)
            ·
              refine ⟨1699225497528677460455221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9062535986819613122427845 1699225497528677460455221)
              ·
                refine ⟨159302390393313511917677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699225497528677460455221 159302390393313511917677)
                ·
                  rfl

theorem cell20_1047061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_1047061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047061 prefixEnd_1047061 := by exact prefixLift 1047061
  have htrace : WordTrace (prefixWord ++ tailWord_1047061) baseStart_1047061 baseEnd_1047061 := by
    simpa [prefixWord, tailWord_1047061, baseEnd_1047061] using wordTrace_append hprefix tailTrace_1047061
  have hstable : (prefixWord ++ tailWord_1047061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047061).length < 2 ^ (prefixWord ++ tailWord_1047061).sum := by decide
  have hdescent : baseEnd_1047061 < baseStart_1047061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047064 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 3]
def baseStart_1047064 : Nat := 118140960795 + 1047064 * 2 ^ 59
def prefixEnd_1047064 : Nat := 4983230072969 + 3 ^ 40 * 1047064 * 2
def baseEnd_1047064 : Nat := 477908540461685858653019

theorem tailTrace_1047064 : CollatzResearch.WordTrace tailWord_1047064 prefixEnd_1047064 477908540461685858653019 := by
  unfold tailWord_1047064
  simp only [CollatzResearch.WordTrace]
  refine ⟨19094780739336713569690123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25459707652448951426253497 19094780739336713569690123)
  ·
    refine ⟨28642171109005070354535185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19094780739336713569690123 28642171109005070354535185)
    ·
      refine ⟨21481628331753802765901389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28642171109005070354535185 21481628331753802765901389)
      ·
        refine ⟨8055610624407676037213021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21481628331753802765901389 8055610624407676037213021)
        ·
          refine ⟨3020853984152878513954883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8055610624407676037213021 3020853984152878513954883)
          ·
            refine ⟨4531280976229317770932325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020853984152878513954883 4531280976229317770932325)
            ·
              refine ⟨849615183042997082049811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4531280976229317770932325 849615183042997082049811)
              ·
                refine ⟨1274422774564495623074717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849615183042997082049811 1274422774564495623074717)
                ·
                  refine ⟨477908540461685858653019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274422774564495623074717 477908540461685858653019)
                  ·
                    rfl

theorem cell20_1047064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_1047064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047064 prefixEnd_1047064 := by exact prefixLift 1047064
  have htrace : WordTrace (prefixWord ++ tailWord_1047064) baseStart_1047064 baseEnd_1047064 := by
    simpa [prefixWord, tailWord_1047064, baseEnd_1047064] using wordTrace_append hprefix tailTrace_1047064
  have hstable : (prefixWord ++ tailWord_1047064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047064).length < 2 ^ (prefixWord ++ tailWord_1047064).sum := by decide
  have hdescent : baseEnd_1047064 < baseStart_1047064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047105 : List Nat := [1, 2, 5, 1, 1, 4, 2, 2, 2]
def baseStart_1047105 : Nat := 118140960795 + 1047105 * 2 ^ 59
def prefixEnd_1047105 : Nat := 4983230072969 + 3 ^ 40 * 1047105 * 2
def baseEnd_1047105 : Nat := 477927253978871938286185

theorem tailTrace_1047105 : CollatzResearch.WordTrace tailWord_1047105 prefixEnd_1047105 477927253978871938286185 := by
  unfold tailWord_1047105
  simp only [CollatzResearch.WordTrace]
  refine ⟨38191056871524891141622769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25460704581016594094415179 38191056871524891141622769)
  ·
    refine ⟨28643292653643668356217077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38191056871524891141622769 28643292653643668356217077)
    ·
      refine ⟨2685308686279093908395351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28643292653643668356217077 2685308686279093908395351)
      ·
        refine ⟨4027963029418640862593027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685308686279093908395351 4027963029418640862593027)
        ·
          refine ⟨6041944544127961293889541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027963029418640862593027 6041944544127961293889541)
          ·
            refine ⟨1132864602023992742604289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6041944544127961293889541 1132864602023992742604289)
            ·
              refine ⟨849648451517994556953217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132864602023992742604289 849648451517994556953217)
              ·
                refine ⟨637236338638495917714913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849648451517994556953217 637236338638495917714913)
                ·
                  refine ⟨477927253978871938286185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637236338638495917714913 477927253978871938286185)
                  ·
                    rfl

theorem cell20_1047105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_1047105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047105 prefixEnd_1047105 := by exact prefixLift 1047105
  have htrace : WordTrace (prefixWord ++ tailWord_1047105) baseStart_1047105 baseEnd_1047105 := by
    simpa [prefixWord, tailWord_1047105, baseEnd_1047105] using wordTrace_append hprefix tailTrace_1047105
  have hstable : (prefixWord ++ tailWord_1047105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047105).length < 2 ^ (prefixWord ++ tailWord_1047105).sum := by decide
  have hdescent : baseEnd_1047105 < baseStart_1047105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047109 : List Nat := [1, 3, 1, 1, 1, 6, 1, 4, 2]
def baseStart_1047109 : Nat := 118140960795 + 1047109 * 2 ^ 59
def prefixEnd_1047109 : Nat := 4983230072969 + 3 ^ 40 * 1047109 * 2
def baseEnd_1047109 : Nat := 477929079687865702152835

theorem tailTrace_1047109 : CollatzResearch.WordTrace tailWord_1047109 prefixEnd_1047109 477929079687865702152835 := by
  unfold tailWord_1047109
  simp only [CollatzResearch.WordTrace]
  refine ⟨38191202763510399824768381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25460801842340266549845587 38191202763510399824768381)
  ·
    refine ⟨14321701036316399934288143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38191202763510399824768381 14321701036316399934288143)
    ·
      refine ⟨21482551554474599901432215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14321701036316399934288143 21482551554474599901432215)
      ·
        refine ⟨32223827331711899852148323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21482551554474599901432215 32223827331711899852148323)
        ·
          refine ⟨48335740997567849778222485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32223827331711899852148323 48335740997567849778222485)
          ·
            refine ⟨2265737859260992958354179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48335740997567849778222485 2265737859260992958354179)
            ·
              refine ⟨3398606788891489437531269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265737859260992958354179 3398606788891489437531269)
              ·
                refine ⟨637238772917154269537113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3398606788891489437531269 637238772917154269537113)
                ·
                  refine ⟨477929079687865702152835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637238772917154269537113 477929079687865702152835)
                  ·
                    rfl

theorem cell20_1047109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_1047109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047109 prefixEnd_1047109 := by exact prefixLift 1047109
  have htrace : WordTrace (prefixWord ++ tailWord_1047109) baseStart_1047109 baseEnd_1047109 := by
    simpa [prefixWord, tailWord_1047109, baseEnd_1047109] using wordTrace_append hprefix tailTrace_1047109
  have hstable : (prefixWord ++ tailWord_1047109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047109).length < 2 ^ (prefixWord ++ tailWord_1047109).sum := by decide
  have hdescent : baseEnd_1047109 < baseStart_1047109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047120 : List Nat := [2, 1, 1, 1, 1, 3, 2, 9]
def baseStart_1047120 : Nat := 118140960795 + 1047120 * 2 ^ 59
def prefixEnd_1047120 : Nat := 4983230072969 + 3 ^ 40 * 1047120 * 2
def baseEnd_1047120 : Nat := 159311366795866184262041

theorem tailTrace_1047120 : CollatzResearch.WordTrace tailWord_1047120 prefixEnd_1047120 159311366795866184262041 := by
  unfold tailWord_1047120
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095801983235274351709407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25461069310980365802279209 19095801983235274351709407)
  ·
    refine ⟨28643702974852911527564111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19095801983235274351709407 28643702974852911527564111)
    ·
      refine ⟨42965554462279367291346167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28643702974852911527564111 42965554462279367291346167)
      ·
        refine ⟨64448331693419050937019251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42965554462279367291346167 64448331693419050937019251)
        ·
          refine ⟨96672497540128576405528877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64448331693419050937019251 96672497540128576405528877)
          ·
            refine ⟨36252186577548216152073329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96672497540128576405528877 36252186577548216152073329)
            ·
              refine ⟨27189139933161162114054997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36252186577548216152073329 27189139933161162114054997)
              ·
                refine ⟨159311366795866184262041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27189139933161162114054997 159311366795866184262041)
                ·
                  rfl

theorem cell20_1047120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_1047120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047120 prefixEnd_1047120 := by exact prefixLift 1047120
  have htrace : WordTrace (prefixWord ++ tailWord_1047120) baseStart_1047120 baseEnd_1047120 := by
    simpa [prefixWord, tailWord_1047120, baseEnd_1047120] using wordTrace_append hprefix tailTrace_1047120
  have hstable : (prefixWord ++ tailWord_1047120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047120).length < 2 ^ (prefixWord ++ tailWord_1047120).sum := by decide
  have hdescent : baseEnd_1047120 < baseStart_1047120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047157 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 3]
def baseStart_1047157 : Nat := 118140960795 + 1047157 * 2 ^ 59
def prefixEnd_1047157 : Nat := 4983230072969 + 3 ^ 40 * 1047157 * 2
def baseEnd_1047157 : Nat := 477950988195790868552639

theorem tailTrace_1047157 : CollatzResearch.WordTrace tailWord_1047157 prefixEnd_1047157 477950988195790868552639 := by
  unfold tailWord_1047157
  simp only [CollatzResearch.WordTrace]
  refine ⟨38192953467336504022515725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25461968978224336015010483 38192953467336504022515725)
  ·
    refine ⟨14322357550251189008443397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38192953467336504022515725 14322357550251189008443397)
    ·
      refine ⟨2685442040672097939083137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14322357550251189008443397 2685442040672097939083137)
      ·
        refine ⟨2014081530504073454312353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2685442040672097939083137 2014081530504073454312353)
        ·
          refine ⟨1510561147878055090734265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014081530504073454312353 1510561147878055090734265)
          ·
            refine ⟨1132920860908541318050699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510561147878055090734265 1132920860908541318050699)
            ·
              refine ⟨1699381291362811977076049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132920860908541318050699 1699381291362811977076049)
              ·
                refine ⟨1274535968522108982807037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699381291362811977076049 1274535968522108982807037)
                ·
                  refine ⟨477950988195790868552639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274535968522108982807037 477950988195790868552639)
                  ·
                    rfl

theorem cell20_1047157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_1047157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047157 prefixEnd_1047157 := by exact prefixLift 1047157
  have htrace : WordTrace (prefixWord ++ tailWord_1047157) baseStart_1047157 baseEnd_1047157 := by
    simpa [prefixWord, tailWord_1047157, baseEnd_1047157] using wordTrace_append hprefix tailTrace_1047157
  have hstable : (prefixWord ++ tailWord_1047157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047157).length < 2 ^ (prefixWord ++ tailWord_1047157).sum := by decide
  have hdescent : baseEnd_1047157 < baseStart_1047157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047161 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 3]
def baseStart_1047161 : Nat := 118140960795 + 1047161 * 2 ^ 59
def prefixEnd_1047161 : Nat := 4983230072969 + 3 ^ 40 * 1047161 * 2
def baseEnd_1047161 : Nat := 477952813904784632419289

theorem tailTrace_1047161 : CollatzResearch.WordTrace tailWord_1047161 prefixEnd_1047161 477952813904784632419289 := by
  unfold tailWord_1047161
  simp only [CollatzResearch.WordTrace]
  refine ⟨38193099359322012705661337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25462066239548008470440891 38193099359322012705661337)
  ·
    refine ⟨28644824519491509529246003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38193099359322012705661337 28644824519491509529246003)
    ·
      refine ⟨42967236779237264293869005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28644824519491509529246003 42967236779237264293869005)
      ·
        refine ⟨16112713792213974110200877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42967236779237264293869005 16112713792213974110200877)
        ·
          refine ⟨6042267672080240291325329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16112713792213974110200877 6042267672080240291325329)
          ·
            refine ⟨4531700754060180218493997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6042267672080240291325329 4531700754060180218493997)
            ·
              refine ⟨1699387782772567581935249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4531700754060180218493997 1699387782772567581935249)
              ·
                refine ⟨1274540837079425686451437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699387782772567581935249 1274540837079425686451437)
                ·
                  refine ⟨477952813904784632419289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274540837079425686451437 477952813904784632419289)
                  ·
                    rfl

theorem cell20_1047161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_1047161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047161 prefixEnd_1047161 := by exact prefixLift 1047161
  have htrace : WordTrace (prefixWord ++ tailWord_1047161) baseStart_1047161 baseEnd_1047161 := by
    simpa [prefixWord, tailWord_1047161, baseEnd_1047161] using wordTrace_append hprefix tailTrace_1047161
  have hstable : (prefixWord ++ tailWord_1047161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047161).length < 2 ^ (prefixWord ++ tailWord_1047161).sum := by decide
  have hdescent : baseEnd_1047161 < baseStart_1047161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047168 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_1047168 : Nat := 118140960795 + 1047168 * 2 ^ 59
def prefixEnd_1047168 : Nat := 4983230072969 + 3 ^ 40 * 1047168 * 2
def baseEnd_1047168 : Nat := 477956008895523719185927

theorem tailTrace_1047168 : CollatzResearch.WordTrace tailWord_1047168 prefixEnd_1047168 477956008895523719185927 := by
  unfold tailWord_1047168
  simp only [CollatzResearch.WordTrace]
  refine ⟨19096677335148326450583079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25462236446864435267444105 19096677335148326450583079)
  ·
    refine ⟨28645016002722489675874619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19096677335148326450583079 28645016002722489675874619)
    ·
      refine ⟨42967524004083734513811929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28645016002722489675874619 42967524004083734513811929)
      ·
        refine ⟨32225643003062800885358947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42967524004083734513811929 32225643003062800885358947)
        ·
          refine ⟨48338464504594201328038421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32225643003062800885358947 48338464504594201328038421)
          ·
            refine ⟨2265865523652853187251801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48338464504594201328038421 2265865523652853187251801)
            ·
              refine ⟨1699399142739639890438851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265865523652853187251801 1699399142739639890438851)
              ·
                refine ⟨2549098714109459835658277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699399142739639890438851 2549098714109459835658277)
                ·
                  refine ⟨477956008895523719185927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2549098714109459835658277 477956008895523719185927)
                  ·
                    rfl

theorem cell20_1047168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_1047168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047168 prefixEnd_1047168 := by exact prefixLift 1047168
  have htrace : WordTrace (prefixWord ++ tailWord_1047168) baseStart_1047168 baseEnd_1047168 := by
    simpa [prefixWord, tailWord_1047168, baseEnd_1047168] using wordTrace_append hprefix tailTrace_1047168
  have hstable : (prefixWord ++ tailWord_1047168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047168).length < 2 ^ (prefixWord ++ tailWord_1047168).sum := by decide
  have hdescent : baseEnd_1047168 < baseStart_1047168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047213 : List Nat := [1, 5, 2, 1, 1, 2, 8]
def baseStart_1047213 : Nat := 118140960795 + 1047213 * 2 ^ 59
def prefixEnd_1047213 : Nat := 4983230072969 + 3 ^ 40 * 1047213 * 2
def baseEnd_1047213 : Nat := 53108505346855951409527

theorem tailTrace_1047213 : CollatzResearch.WordTrace tailWord_1047213 prefixEnd_1047213 53108505346855951409527 := by
  unfold tailWord_1047213
  simp only [CollatzResearch.WordTrace]
  refine ⟨38194995955133625586554293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25463330636755750391036195 38194995955133625586554293)
  ·
    refine ⟨3580780870793777398739465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38194995955133625586554293 3580780870793777398739465)
    ·
      refine ⟨2685585653095333049054599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3580780870793777398739465 2685585653095333049054599)
      ·
        refine ⟨4028378479642999573581899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685585653095333049054599 4028378479642999573581899)
        ·
          refine ⟨6042567719464499360372849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028378479642999573581899 6042567719464499360372849)
          ·
            refine ⟨4531925789598374520279637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6042567719464499360372849 4531925789598374520279637)
            ·
              refine ⟨53108505346855951409527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4531925789598374520279637 53108505346855951409527)
              ·
                rfl

theorem cell20_1047213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_1047213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047213 prefixEnd_1047213 := by exact prefixLift 1047213
  have htrace : WordTrace (prefixWord ++ tailWord_1047213) baseStart_1047213 baseEnd_1047213 := by
    simpa [prefixWord, tailWord_1047213, baseEnd_1047213] using wordTrace_append hprefix tailTrace_1047213
  have hstable : (prefixWord ++ tailWord_1047213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047213).length < 2 ^ (prefixWord ++ tailWord_1047213).sum := by decide
  have hdescent : baseEnd_1047213 < baseStart_1047213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047223 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 4]
def baseStart_1047223 : Nat := 118140960795 + 1047223 * 2 ^ 59
def prefixEnd_1047223 : Nat := 4983230072969 + 3 ^ 40 * 1047223 * 2
def baseEnd_1047223 : Nat := 477981112394187972352369

theorem tailTrace_1047223 : CollatzResearch.WordTrace tailWord_1047223 prefixEnd_1047223 477981112394187972352369 := by
  unfold tailWord_1047223
  simp only [CollatzResearch.WordTrace]
  refine ⟨38195360685097397294418323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25463573790064931529612215 38195360685097397294418323)
  ·
    refine ⟨57293041027646095941627485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38195360685097397294418323 57293041027646095941627485)
    ·
      refine ⟨21484890385367285978110307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57293041027646095941627485 21484890385367285978110307)
      ·
        refine ⟨32227335578050928967165461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21484890385367285978110307 32227335578050928967165461)
        ·
          refine ⟨1510656355221137295335881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32227335578050928967165461 1510656355221137295335881)
          ·
            refine ⟨1132992266415852971501911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510656355221137295335881 1132992266415852971501911)
            ·
              refine ⟨1699488399623779457252867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132992266415852971501911 1699488399623779457252867)
              ·
                refine ⟨2549232599435669185879301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699488399623779457252867 2549232599435669185879301)
                ·
                  refine ⟨477981112394187972352369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2549232599435669185879301 477981112394187972352369)
                  ·
                    rfl

theorem cell20_1047223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_1047223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047223 prefixEnd_1047223 := by exact prefixLift 1047223
  have htrace : WordTrace (prefixWord ++ tailWord_1047223) baseStart_1047223 baseEnd_1047223 := by
    simpa [prefixWord, tailWord_1047223, baseEnd_1047223] using wordTrace_append hprefix tailTrace_1047223
  have hstable : (prefixWord ++ tailWord_1047223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047223).length < 2 ^ (prefixWord ++ tailWord_1047223).sum := by decide
  have hdescent : baseEnd_1047223 < baseStart_1047223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047233 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 3]
def baseStart_1047233 : Nat := 118140960795 + 1047233 * 2 ^ 59
def prefixEnd_1047233 : Nat := 4983230072969 + 3 ^ 40 * 1047233 * 2
def baseEnd_1047233 : Nat := 477985676666672382018995

theorem tailTrace_1047233 : CollatzResearch.WordTrace tailWord_1047233 prefixEnd_1047233 477985676666672382018995 := by
  unfold tailWord_1047233
  simp only [CollatzResearch.WordTrace]
  refine ⟨38195725415061169002282353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25463816943374112668188235 38195725415061169002282353)
  ·
    refine ⟨28646794061295876751711765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38195725415061169002282353 28646794061295876751711765)
    ·
      refine ⟨1342818471623244222736489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28646794061295876751711765 1342818471623244222736489)
      ·
        refine ⟨1007113853717433167052367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1342818471623244222736489 1007113853717433167052367)
        ·
          refine ⟨1510670780576149750578551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007113853717433167052367 1510670780576149750578551)
          ·
            refine ⟨2266006170864224625867827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510670780576149750578551 2266006170864224625867827)
            ·
              refine ⟨3399009256296336938801741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266006170864224625867827 3399009256296336938801741)
              ·
                refine ⟨1274628471111126352050653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3399009256296336938801741 1274628471111126352050653)
                ·
                  refine ⟨477985676666672382018995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274628471111126352050653 477985676666672382018995)
                  ·
                    rfl

theorem cell20_1047233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_1047233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047233 prefixEnd_1047233 := by exact prefixLift 1047233
  have htrace : WordTrace (prefixWord ++ tailWord_1047233) baseStart_1047233 baseEnd_1047233 := by
    simpa [prefixWord, tailWord_1047233, baseEnd_1047233] using wordTrace_append hprefix tailTrace_1047233
  have hstable : (prefixWord ++ tailWord_1047233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047233).length < 2 ^ (prefixWord ++ tailWord_1047233).sum := by decide
  have hdescent : baseEnd_1047233 < baseStart_1047233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047272 : List Nat := [2, 1, 4, 1, 12]
def baseStart_1047272 : Nat := 118140960795 + 1047272 * 2 ^ 59
def prefixEnd_1047272 : Nat := 4983230072969 + 3 ^ 40 * 1047272 * 2
def baseEnd_1047272 : Nat := 5901277497893352836035

theorem tailTrace_1047272 : CollatzResearch.WordTrace tailWord_1047272 prefixEnd_1047272 5901277497893352836035 := by
  unfold tailWord_1047272
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098573930959939331476035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25464765241279919108634713 19098573930959939331476035)
  ·
    refine ⟨28647860896439908997214053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19098573930959939331476035 28647860896439908997214053)
    ·
      refine ⟨5371473918082482936977635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28647860896439908997214053 5371473918082482936977635)
      ·
        refine ⟨8057210877123724405466453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371473918082482936977635 8057210877123724405466453)
        ·
          refine ⟨5901277497893352836035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 8057210877123724405466453 5901277497893352836035)
          ·
            rfl

theorem cell20_1047272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 12].length) (baseStart_1047272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047272 prefixEnd_1047272 := by exact prefixLift 1047272
  have htrace : WordTrace (prefixWord ++ tailWord_1047272) baseStart_1047272 baseEnd_1047272 := by
    simpa [prefixWord, tailWord_1047272, baseEnd_1047272] using wordTrace_append hprefix tailTrace_1047272
  have hstable : (prefixWord ++ tailWord_1047272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047272).length < 2 ^ (prefixWord ++ tailWord_1047272).sum := by decide
  have hdescent : baseEnd_1047272 < baseStart_1047272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047278 : List Nat := [4, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_1047278 : Nat := 118140960795 + 1047278 * 2 ^ 59
def prefixEnd_1047278 : Nat := 4983230072969 + 3 ^ 40 * 1047278 * 2
def baseEnd_1047278 : Nat := 478006215892852225518811

theorem tailTrace_1047278 : CollatzResearch.WordTrace tailWord_1047278 prefixEnd_1047278 478006215892852225518811 := by
  unfold tailWord_1047278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774670837487267710958811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25464911133265427791780325 4774670837487267710958811)
  ·
    refine ⟨7162006256230901566438217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4774670837487267710958811 7162006256230901566438217)
    ·
      refine ⟨5371504692173176174828663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7162006256230901566438217 5371504692173176174828663)
      ·
        refine ⟨8057257038259764262242995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371504692173176174828663 8057257038259764262242995)
        ·
          refine ⟨12085885557389646393364493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057257038259764262242995 12085885557389646393364493)
          ·
            refine ⟨4532207084021117397511685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12085885557389646393364493 4532207084021117397511685)
            ·
              refine ⟨849788828253959512033441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4532207084021117397511685 849788828253959512033441)
              ·
                refine ⟨637341621190469634025081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849788828253959512033441 637341621190469634025081)
                ·
                  refine ⟨478006215892852225518811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637341621190469634025081 478006215892852225518811)
                  ·
                    rfl

theorem cell20_1047278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_1047278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047278 prefixEnd_1047278 := by exact prefixLift 1047278
  have htrace : WordTrace (prefixWord ++ tailWord_1047278) baseStart_1047278 baseEnd_1047278 := by
    simpa [prefixWord, tailWord_1047278, baseEnd_1047278] using wordTrace_append hprefix tailTrace_1047278
  have hstable : (prefixWord ++ tailWord_1047278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047278).length < 2 ^ (prefixWord ++ tailWord_1047278).sum := by decide
  have hdescent : baseEnd_1047278 < baseStart_1047278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047330 : List Nat := [3, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1047330 : Nat := 118140960795 + 1047330 * 2 ^ 59
def prefixEnd_1047330 : Nat := 4983230072969 + 3 ^ 40 * 1047330 * 2
def baseEnd_1047330 : Nat := 478029950109771155785265

theorem tailTrace_1047330 : CollatzResearch.WordTrace tailWord_1047330 prefixEnd_1047330 478029950109771155785265 := by
  unfold tailWord_1047330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549815823927438642140861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25466175530473169712375629 9549815823927438642140861)
  ·
    refine ⟨3581180933972789490802823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9549815823927438642140861 3581180933972789490802823)
    ·
      refine ⟨5371771400959184236204235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581180933972789490802823 5371771400959184236204235)
      ·
        refine ⟨8057657101438776354306353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371771400959184236204235 8057657101438776354306353)
        ·
          refine ⟨6043242826079082265729765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8057657101438776354306353 6043242826079082265729765)
          ·
            refine ⟨1133108029889827924824331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6043242826079082265729765 1133108029889827924824331)
            ·
              refine ⟨1699662044834741887236497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133108029889827924824331 1699662044834741887236497)
              ·
                refine ⟨1274746533626056415427373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699662044834741887236497 1274746533626056415427373)
                ·
                  refine ⟨478029950109771155785265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274746533626056415427373 478029950109771155785265)
                  ·
                    rfl

theorem cell20_1047330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1047330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047330 prefixEnd_1047330 := by exact prefixLift 1047330
  have htrace : WordTrace (prefixWord ++ tailWord_1047330) baseStart_1047330 baseEnd_1047330 := by
    simpa [prefixWord, tailWord_1047330, baseEnd_1047330] using wordTrace_append hprefix tailTrace_1047330
  have hstable : (prefixWord ++ tailWord_1047330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047330).length < 2 ^ (prefixWord ++ tailWord_1047330).sum := by decide
  have hdescent : baseEnd_1047330 < baseStart_1047330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047351 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 3]
def baseStart_1047351 : Nat := 118140960795 + 1047351 * 2 ^ 59
def prefixEnd_1047351 : Nat := 4983230072969 + 3 ^ 40 * 1047351 * 2
def baseEnd_1047351 : Nat := 478039535081988416085179

theorem tailTrace_1047351 : CollatzResearch.WordTrace tailWord_1047351 prefixEnd_1047351 478039535081988416085179 := by
  unfold tailWord_1047351
  simp only [CollatzResearch.WordTrace]
  refine ⟨38200029228633675155077907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25466686152422450103385271 38200029228633675155077907)
  ·
    refine ⟨57300043842950512732616861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38200029228633675155077907 57300043842950512732616861)
    ·
      refine ⟨21487516441106442274731323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57300043842950512732616861 21487516441106442274731323)
      ·
        refine ⟨32231274661659663412096985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21487516441106442274731323 32231274661659663412096985)
        ·
          refine ⟨24173455996244747559072739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32231274661659663412096985 24173455996244747559072739)
          ·
            refine ⟨36260183994367121338609109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24173455996244747559072739 36260183994367121338609109)
            ·
              refine ⟨849848062367979406373651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36260183994367121338609109 849848062367979406373651)
              ·
                refine ⟨1274772093551969109560477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849848062367979406373651 1274772093551969109560477)
                ·
                  refine ⟨478039535081988416085179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274772093551969109560477 478039535081988416085179)
                  ·
                    rfl

theorem cell20_1047351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 3].length) (baseStart_1047351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047351 prefixEnd_1047351 := by exact prefixLift 1047351
  have htrace : WordTrace (prefixWord ++ tailWord_1047351) baseStart_1047351 baseEnd_1047351 := by
    simpa [prefixWord, tailWord_1047351, baseEnd_1047351] using wordTrace_append hprefix tailTrace_1047351
  have hstable : (prefixWord ++ tailWord_1047351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047351).length < 2 ^ (prefixWord ++ tailWord_1047351).sum := by decide
  have hdescent : baseEnd_1047351 < baseStart_1047351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047372 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1047372 : Nat := 118140960795 + 1047372 * 2 ^ 59
def prefixEnd_1047372 : Nat := 4983230072969 + 3 ^ 40 * 1047372 * 2
def baseEnd_1047372 : Nat := 478049120054205676385093

theorem tailTrace_1047372 : CollatzResearch.WordTrace tailWord_1047372 prefixEnd_1047372 478049120054205676385093 := by
  unfold tailWord_1047372
  simp only [CollatzResearch.WordTrace]
  refine ⟨19100397580778797870796185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25467196774371730494394913 19100397580778797870796185)
  ·
    refine ⟨14325298185584098403097139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19100397580778797870796185 14325298185584098403097139)
    ·
      refine ⟨21487947278376147604645709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14325298185584098403097139 21487947278376147604645709)
      ·
        refine ⟨8057980229391055351742141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21487947278376147604645709 8057980229391055351742141)
        ·
          refine ⟨3021742586021645756903303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8057980229391055351742141 3021742586021645756903303)
          ·
            refine ⟨4532613879032468635354955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021742586021645756903303 4532613879032468635354955)
            ·
              refine ⟨6798920818548702953032433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532613879032468635354955 6798920818548702953032433)
              ·
                refine ⟨5099190613911527214774325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798920818548702953032433 5099190613911527214774325)
                ·
                  refine ⟨478049120054205676385093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5099190613911527214774325 478049120054205676385093)
                  ·
                    rfl

theorem cell20_1047372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1047372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047372 prefixEnd_1047372 := by exact prefixLift 1047372
  have htrace : WordTrace (prefixWord ++ tailWord_1047372) baseStart_1047372 baseEnd_1047372 := by
    simpa [prefixWord, tailWord_1047372, baseEnd_1047372] using wordTrace_append hprefix tailTrace_1047372
  have hstable : (prefixWord ++ tailWord_1047372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047372).length < 2 ^ (prefixWord ++ tailWord_1047372).sum := by decide
  have hdescent : baseEnd_1047372 < baseStart_1047372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047386 : List Nat := [3, 1, 1, 2, 1, 4, 8]
def baseStart_1047386 : Nat := 118140960795 + 1047386 * 2 ^ 59
def prefixEnd_1047386 : Nat := 4983230072969 + 3 ^ 40 * 1047386 * 2
def baseEnd_1047386 : Nat := 53117278892853761102041

theorem tailTrace_1047386 : CollatzResearch.WordTrace tailWord_1047386 prefixEnd_1047386 53117278892853761102041 := by
  unfold tailWord_1047386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550326445876719033150503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25467537189004584088401341 9550326445876719033150503)
  ·
    refine ⟨14325489668815078549725755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9550326445876719033150503 14325489668815078549725755)
    ·
      refine ⟨21488234503222617824588633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14325489668815078549725755 21488234503222617824588633)
      ·
        refine ⟨16116175877416963368441475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21488234503222617824588633 16116175877416963368441475)
        ·
          refine ⟨24174263816125445052662213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16116175877416963368441475 24174263816125445052662213)
          ·
            refine ⟨4532674465523520947374165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24174263816125445052662213 4532674465523520947374165)
            ·
              refine ⟨53117278892853761102041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4532674465523520947374165 53117278892853761102041)
              ·
                rfl

theorem cell20_1047386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 8].length) (baseStart_1047386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047386 prefixEnd_1047386 := by exact prefixLift 1047386
  have htrace : WordTrace (prefixWord ++ tailWord_1047386) baseStart_1047386 baseEnd_1047386 := by
    simpa [prefixWord, tailWord_1047386, baseEnd_1047386] using wordTrace_append hprefix tailTrace_1047386
  have hstable : (prefixWord ++ tailWord_1047386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047386).length < 2 ^ (prefixWord ++ tailWord_1047386).sum := by decide
  have hdescent : baseEnd_1047386 < baseStart_1047386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047396 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1047396 : Nat := 118140960795 + 1047396 * 2 ^ 59
def prefixEnd_1047396 : Nat := 4983230072969 + 3 ^ 40 * 1047396 * 2
def baseEnd_1047396 : Nat := 478060074308168259584995

theorem tailTrace_1047396 : CollatzResearch.WordTrace tailWord_1047396 prefixEnd_1047396 478060074308168259584995 := by
  unfold tailWord_1047396
  simp only [CollatzResearch.WordTrace]
  refine ⟨19100835256735323920233021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25467780342313765226977361 19100835256735323920233021)
  ·
    refine ⟨7162813221275746470087383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19100835256735323920233021 7162813221275746470087383)
    ·
      refine ⟨10744219831913619705131075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162813221275746470087383 10744219831913619705131075)
      ·
        refine ⟨16116329747870429557696613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10744219831913619705131075 16116329747870429557696613)
        ·
          refine ⟨3021811827725705542068115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16116329747870429557696613 3021811827725705542068115)
          ·
            refine ⟨4532717741588558313102173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021811827725705542068115 4532717741588558313102173)
            ·
              refine ⟨1699769153095709367413315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4532717741588558313102173 1699769153095709367413315)
              ·
                refine ⟨2549653729643564051119973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699769153095709367413315 2549653729643564051119973)
                ·
                  refine ⟨478060074308168259584995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2549653729643564051119973 478060074308168259584995)
                  ·
                    rfl

theorem cell20_1047396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1047396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047396 prefixEnd_1047396 := by exact prefixLift 1047396
  have htrace : WordTrace (prefixWord ++ tailWord_1047396) baseStart_1047396 baseEnd_1047396 := by
    simpa [prefixWord, tailWord_1047396, baseEnd_1047396] using wordTrace_append hprefix tailTrace_1047396
  have hstable : (prefixWord ++ tailWord_1047396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047396).length < 2 ^ (prefixWord ++ tailWord_1047396).sum := by decide
  have hdescent : baseEnd_1047396 < baseStart_1047396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047406 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1047406 : Nat := 118140960795 + 1047406 * 2 ^ 59
def prefixEnd_1047406 : Nat := 4983230072969 + 3 ^ 40 * 1047406 * 2
def baseEnd_1047406 : Nat := 478064638580652669251621

theorem tailTrace_1047406 : CollatzResearch.WordTrace tailWord_1047406 prefixEnd_1047406 478064638580652669251621 := by
  unfold tailWord_1047406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4775254405429302443541259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25468023495622946365553381 4775254405429302443541259)
  ·
    refine ⟨7162881608143953665311889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4775254405429302443541259 7162881608143953665311889)
    ·
      refine ⟨5372161206107965248983917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7162881608143953665311889 5372161206107965248983917)
      ·
        refine ⟨2014560452290486968368969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5372161206107965248983917 2014560452290486968368969)
        ·
          refine ⟨1510920339217865226276727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014560452290486968368969 1510920339217865226276727)
          ·
            refine ⟨2266380508826797839415091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510920339217865226276727 2266380508826797839415091)
            ·
              refine ⟨3399570763240196759122637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266380508826797839415091 3399570763240196759122637)
              ·
                refine ⟨1274839036215073784670989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3399570763240196759122637 1274839036215073784670989)
                ·
                  refine ⟨478064638580652669251621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274839036215073784670989 478064638580652669251621)
                  ·
                    rfl

theorem cell20_1047406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1047406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047406 prefixEnd_1047406 := by exact prefixLift 1047406
  have htrace : WordTrace (prefixWord ++ tailWord_1047406) baseStart_1047406 baseEnd_1047406 := by
    simpa [prefixWord, tailWord_1047406, baseEnd_1047406] using wordTrace_append hprefix tailTrace_1047406
  have hstable : (prefixWord ++ tailWord_1047406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047406).length < 2 ^ (prefixWord ++ tailWord_1047406).sum := by decide
  have hdescent : baseEnd_1047406 < baseStart_1047406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047458 : List Nat := [3, 3, 1, 2, 2, 3, 1, 5]
def baseStart_1047458 : Nat := 118140960795 + 1047458 * 2 ^ 59
def prefixEnd_1047458 : Nat := 4983230072969 + 3 ^ 40 * 1047458 * 2
def baseEnd_1047458 : Nat := 159362790932523866506025

theorem tailTrace_1047458 : CollatzResearch.WordTrace tailWord_1047458 prefixEnd_1047458 159362790932523866506025 := by
  unfold tailWord_1047458
  simp only [CollatzResearch.WordTrace]
  refine ⟨9550982959811508107305757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25469287892830688286148685 9550982959811508107305757)
  ·
    refine ⟨3581618609929315540239659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9550982959811508107305757 3581618609929315540239659)
    ·
      refine ⟨5372427914893973310359489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581618609929315540239659 5372427914893973310359489)
      ·
        refine ⟨4029320936170479982769617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5372427914893973310359489 4029320936170479982769617)
        ·
          refine ⟨3021990702127859987077213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4029320936170479982769617 3021990702127859987077213)
          ·
            refine ⟨1133246513297947495153955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3021990702127859987077213 1133246513297947495153955)
            ·
              refine ⟨1699869769946921242730933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133246513297947495153955 1699869769946921242730933)
              ·
                refine ⟨159362790932523866506025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699869769946921242730933 159362790932523866506025)
                ·
                  rfl

theorem cell20_1047458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_1047458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047458 prefixEnd_1047458 := by exact prefixLift 1047458
  have htrace : WordTrace (prefixWord ++ tailWord_1047458) baseStart_1047458 baseEnd_1047458 := by
    simpa [prefixWord, tailWord_1047458, baseEnd_1047458] using wordTrace_append hprefix tailTrace_1047458
  have hstable : (prefixWord ++ tailWord_1047458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047458).length < 2 ^ (prefixWord ++ tailWord_1047458).sum := by decide
  have hdescent : baseEnd_1047458 < baseStart_1047458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047486 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1047486 : Nat := 118140960795 + 1047486 * 2 ^ 59
def prefixEnd_1047486 : Nat := 4983230072969 + 3 ^ 40 * 1047486 * 2
def baseEnd_1047486 : Nat := 478101152760527946584627

theorem tailTrace_1047486 : CollatzResearch.WordTrace tailWord_1047486 prefixEnd_1047486 478101152760527946584627 := by
  unfold tailWord_1047486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4775619135393074151405289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25469968722096395474161541 4775619135393074151405289)
  ·
    refine ⟨3581714351544805613553967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4775619135393074151405289 3581714351544805613553967)
    ·
      refine ⟨5372571527317208420330951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581714351544805613553967 5372571527317208420330951)
      ·
        refine ⟨8058857290975812630496427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5372571527317208420330951 8058857290975812630496427)
        ·
          refine ⟨12088285936463718945744641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8058857290975812630496427 12088285936463718945744641)
          ·
            refine ⟨9066214452347789209308481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12088285936463718945744641 9066214452347789209308481)
            ·
              refine ⟨6799660839260841906981361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9066214452347789209308481 6799660839260841906981361)
              ·
                refine ⟨5099745629445631430236021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799660839260841906981361 5099745629445631430236021)
                ·
                  refine ⟨478101152760527946584627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5099745629445631430236021 478101152760527946584627)
                  ·
                    rfl

theorem cell20_1047486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1047486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047486 prefixEnd_1047486 := by exact prefixLift 1047486
  have htrace : WordTrace (prefixWord ++ tailWord_1047486) baseStart_1047486 baseEnd_1047486 := by
    simpa [prefixWord, tailWord_1047486, baseEnd_1047486] using wordTrace_append hprefix tailTrace_1047486
  have hstable : (prefixWord ++ tailWord_1047486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047486).length < 2 ^ (prefixWord ++ tailWord_1047486).sum := by decide
  have hdescent : baseEnd_1047486 < baseStart_1047486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047500 : List Nat := [2, 2, 1, 4, 1, 1, 9]
def baseStart_1047500 : Nat := 118140960795 + 1047500 * 2 ^ 59
def prefixEnd_1047500 : Nat := 4983230072969 + 3 ^ 40 * 1047500 * 2
def baseEnd_1047500 : Nat := 53123060304667346679767

theorem tailTrace_1047500 : CollatzResearch.WordTrace tailWord_1047500 prefixEnd_1047500 53123060304667346679767 := by
  unfold tailWord_1047500
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102731852546936801125977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25470309136729249068167969 19102731852546936801125977)
  ·
    refine ⟨14327048889410202600844483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19102731852546936801125977 14327048889410202600844483)
    ·
      refine ⟨21490573334115303901266725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14327048889410202600844483 21490573334115303901266725)
      ·
        refine ⟨4029482500146619481487511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21490573334115303901266725 4029482500146619481487511)
        ·
          refine ⟨6044223750219929222231267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029482500146619481487511 6044223750219929222231267)
          ·
            refine ⟨9066335625329893833346901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044223750219929222231267 9066335625329893833346901)
            ·
              refine ⟨53123060304667346679767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9066335625329893833346901 53123060304667346679767)
              ·
                rfl

theorem cell20_1047500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 9].length) (baseStart_1047500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047500 prefixEnd_1047500 := by exact prefixLift 1047500
  have htrace : WordTrace (prefixWord ++ tailWord_1047500) baseStart_1047500 baseEnd_1047500 := by
    simpa [prefixWord, tailWord_1047500, baseEnd_1047500] using wordTrace_append hprefix tailTrace_1047500
  have hstable : (prefixWord ++ tailWord_1047500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047500).length < 2 ^ (prefixWord ++ tailWord_1047500).sum := by decide
  have hdescent : baseEnd_1047500 < baseStart_1047500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047503 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 3]
def baseStart_1047503 : Nat := 118140960795 + 1047503 * 2 ^ 59
def prefixEnd_1047503 : Nat := 4983230072969 + 3 ^ 40 * 1047503 * 2
def baseEnd_1047503 : Nat := 478108912023751443017891

theorem tailTrace_1047503 : CollatzResearch.WordTrace tailWord_1047503 prefixEnd_1047503 478108912023751443017891 := by
  unfold tailWord_1047503
  simp only [CollatzResearch.WordTrace]
  refine ⟨38205573124083005114611163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25470382082722003409740775 38205573124083005114611163)
  ·
    refine ⟨57308359686124507671916745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38205573124083005114611163 57308359686124507671916745)
    ·
      refine ⟨42981269764593380753937559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57308359686124507671916745 42981269764593380753937559)
      ·
        refine ⟨64471904646890071130906339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42981269764593380753937559 64471904646890071130906339)
        ·
          refine ⟨96707856970335106696359509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64471904646890071130906339 96707856970335106696359509)
          ·
            refine ⟨1133295198871114531597963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 96707856970335106696359509 1133295198871114531597963)
            ·
              refine ⟨1699942798306671797396945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133295198871114531597963 1699942798306671797396945)
              ·
                refine ⟨1274957098730003848047709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1699942798306671797396945 1274957098730003848047709)
                ·
                  refine ⟨478108912023751443017891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274957098730003848047709 478108912023751443017891)
                  ·
                    rfl

theorem cell20_1047503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_1047503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047503 prefixEnd_1047503 := by exact prefixLift 1047503
  have htrace : WordTrace (prefixWord ++ tailWord_1047503) baseStart_1047503 baseEnd_1047503 := by
    simpa [prefixWord, tailWord_1047503, baseEnd_1047503] using wordTrace_append hprefix tailTrace_1047503
  have hstable : (prefixWord ++ tailWord_1047503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047503).length < 2 ^ (prefixWord ++ tailWord_1047503).sum := by decide
  have hdescent : baseEnd_1047503 < baseStart_1047503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047545 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1047545 : Nat := 118140960795 + 1047545 * 2 ^ 59
def prefixEnd_1047545 : Nat := 4983230072969 + 3 ^ 40 * 1047545 * 2
def baseEnd_1047545 : Nat := 478128081968185963617719

theorem tailTrace_1047545 : CollatzResearch.WordTrace tailWord_1047545 prefixEnd_1047545 478128081968185963617719 := by
  unfold tailWord_1047545
  simp only [CollatzResearch.WordTrace]
  refine ⟨38207104989930846287640089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25471403326620564191760059 38207104989930846287640089)
  ·
    refine ⟨28655328742448134715730067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38207104989930846287640089 28655328742448134715730067)
    ·
      refine ⟨42982993113672202073595101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28655328742448134715730067 42982993113672202073595101)
      ·
        refine ⟨16118622417627075777598163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42982993113672202073595101 16118622417627075777598163)
        ·
          refine ⟨24177933626440613666397245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16118622417627075777598163 24177933626440613666397245)
          ·
            refine ⟨9066725109915230124898967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24177933626440613666397245 9066725109915230124898967)
            ·
              refine ⟨13600087664872845187348451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9066725109915230124898967 13600087664872845187348451)
              ·
                refine ⟨20400131497309267781022677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13600087664872845187348451 20400131497309267781022677)
                ·
                  refine ⟨478128081968185963617719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20400131497309267781022677 478128081968185963617719)
                  ·
                    rfl

theorem cell20_1047545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1047545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047545 prefixEnd_1047545 := by exact prefixLift 1047545
  have htrace : WordTrace (prefixWord ++ tailWord_1047545) baseStart_1047545 baseEnd_1047545 := by
    simpa [prefixWord, tailWord_1047545, baseEnd_1047545] using wordTrace_append hprefix tailTrace_1047545
  have hstable : (prefixWord ++ tailWord_1047545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047545).length < 2 ^ (prefixWord ++ tailWord_1047545).sum := by decide
  have hdescent : baseEnd_1047545 < baseStart_1047545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047562 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1047562 : Nat := 118140960795 + 1047562 * 2 ^ 59
def prefixEnd_1047562 : Nat := 4983230072969 + 3 ^ 40 * 1047562 * 2
def baseEnd_1047562 : Nat := 478135841231409460050983

theorem tailTrace_1047562 : CollatzResearch.WordTrace tailWord_1047562 prefixEnd_1047562 478135841231409460050983 := by
  unfold tailWord_1047562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9551931257717314547752235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25471816687246172127339293 9551931257717314547752235)
  ·
    refine ⟨14327896886575971821628353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9551931257717314547752235 14327896886575971821628353)
    ·
      refine ⟨10745922664931978866221265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14327896886575971821628353 10745922664931978866221265)
      ·
        refine ⟨8059441998698984149665949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10745922664931978866221265 8059441998698984149665949)
        ·
          refine ⟨3022290749512119056124731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8059441998698984149665949 3022290749512119056124731)
          ·
            refine ⟨4533436124268178584187097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022290749512119056124731 4533436124268178584187097)
            ·
              refine ⟨3400077093201133938140323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533436124268178584187097 3400077093201133938140323)
              ·
                refine ⟨5100115639801700907210485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400077093201133938140323 5100115639801700907210485)
                ·
                  refine ⟨478135841231409460050983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5100115639801700907210485 478135841231409460050983)
                  ·
                    rfl

theorem cell20_1047562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1047562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047562 prefixEnd_1047562 := by exact prefixLift 1047562
  have htrace : WordTrace (prefixWord ++ tailWord_1047562) baseStart_1047562 baseEnd_1047562 := by
    simpa [prefixWord, tailWord_1047562, baseEnd_1047562] using wordTrace_append hprefix tailTrace_1047562
  have hstable : (prefixWord ++ tailWord_1047562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047562).length < 2 ^ (prefixWord ++ tailWord_1047562).sum := by decide
  have hdescent : baseEnd_1047562 < baseStart_1047562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047576 : List Nat := [2, 1, 2, 3, 2, 2, 1, 7]
def baseStart_1047576 : Nat := 118140960795 + 1047576 * 2 ^ 59
def prefixEnd_1047576 : Nat := 4983230072969 + 3 ^ 40 * 1047576 * 2
def baseEnd_1047576 : Nat := 159380743737629211194753

theorem tailTrace_1047576 : CollatzResearch.WordTrace tailWord_1047576 prefixEnd_1047576 159380743737629211194753 := by
  unfold tailWord_1047576
  simp only [CollatzResearch.WordTrace]
  refine ⟨19104117826409269291009291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25472157101879025721345721 19104117826409269291009291)
  ·
    refine ⟨28656176739613903936513937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19104117826409269291009291 28656176739613903936513937)
    ·
      refine ⟨21492132554710427952385453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28656176739613903936513937 21492132554710427952385453)
      ·
        refine ⟨8059549708016410482144545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21492132554710427952385453 8059549708016410482144545)
        ·
          refine ⟨6044662281012307861608409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8059549708016410482144545 6044662281012307861608409)
          ·
            refine ⟨4533496710759230896206307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6044662281012307861608409 4533496710759230896206307)
            ·
              refine ⟨6800245066138846344309461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533496710759230896206307 6800245066138846344309461)
              ·
                refine ⟨159380743737629211194753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6800245066138846344309461 159380743737629211194753)
                ·
                  rfl

theorem cell20_1047576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_1047576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047576 prefixEnd_1047576 := by exact prefixLift 1047576
  have htrace : WordTrace (prefixWord ++ tailWord_1047576) baseStart_1047576 baseEnd_1047576 := by
    simpa [prefixWord, tailWord_1047576, baseEnd_1047576] using wordTrace_append hprefix tailTrace_1047576
  have hstable : (prefixWord ++ tailWord_1047576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047576).length < 2 ^ (prefixWord ++ tailWord_1047576).sum := by decide
  have hdescent : baseEnd_1047576 < baseStart_1047576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047621 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_1047621 : Nat := 118140960795 + 1047621 * 2 ^ 59
def prefixEnd_1047621 : Nat := 4983230072969 + 3 ^ 40 * 1047621 * 2
def baseEnd_1047621 : Nat := 478162770439067477084075

theorem tailTrace_1047621 : CollatzResearch.WordTrace tailWord_1047621 prefixEnd_1047621 478162770439067477084075 := by
  unfold tailWord_1047621
  simp only [CollatzResearch.WordTrace]
  refine ⟨38209876937655511267406717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25473251291770340844937811 38209876937655511267406717)
  ·
    refine ⟨14328703851620816725277519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38209876937655511267406717 14328703851620816725277519)
    ·
      refine ⟨21493055777431225087916279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14328703851620816725277519 21493055777431225087916279)
      ·
        refine ⟨32239583666146837631874419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21493055777431225087916279 32239583666146837631874419)
        ·
          refine ⟨48359375499220256447811629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32239583666146837631874419 48359375499220256447811629)
          ·
            refine ⟨18134765812207596167929361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48359375499220256447811629 18134765812207596167929361)
            ·
              refine ⟨13601074359155697125947021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18134765812207596167929361 13601074359155697125947021)
              ·
                refine ⟨5100402884683386422230133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13601074359155697125947021 5100402884683386422230133)
                ·
                  refine ⟨478162770439067477084075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5100402884683386422230133 478162770439067477084075)
                  ·
                    rfl

theorem cell20_1047621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_1047621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047621 prefixEnd_1047621 := by exact prefixLift 1047621
  have htrace : WordTrace (prefixWord ++ tailWord_1047621) baseStart_1047621 baseEnd_1047621 := by
    simpa [prefixWord, tailWord_1047621, baseEnd_1047621] using wordTrace_append hprefix tailTrace_1047621
  have hstable : (prefixWord ++ tailWord_1047621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047621).length < 2 ^ (prefixWord ++ tailWord_1047621).sum := by decide
  have hdescent : baseEnd_1047621 < baseStart_1047621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047624 : List Nat := [2, 1, 3, 1, 1, 1, 5, 4, 2]
def baseStart_1047624 : Nat := 118140960795 + 1047624 * 2 ^ 59
def prefixEnd_1047624 : Nat := 4983230072969 + 3 ^ 40 * 1047624 * 2
def baseEnd_1047624 : Nat := 478164139720812799984063

theorem tailTrace_1047624 : CollatzResearch.WordTrace tailWord_1047624 prefixEnd_1047624 478164139720812799984063 := by
  unfold tailWord_1047624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19104993178322321389882963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25473324237763095186510617 19104993178322321389882963)
  ·
    refine ⟨28657489767483482084824445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19104993178322321389882963 28657489767483482084824445)
    ·
      refine ⟨10746558662806305781809167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28657489767483482084824445 10746558662806305781809167)
      ·
        refine ⟨16119837994209458672713751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10746558662806305781809167 16119837994209458672713751)
        ·
          refine ⟨24179756991314188009070627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16119837994209458672713751 24179756991314188009070627)
          ·
            refine ⟨36269635486971282013605941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24179756991314188009070627 36269635486971282013605941)
            ·
              refine ⟨3400278326903557688775557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36269635486971282013605941 3400278326903557688775557)
              ·
                refine ⟨637552186294417066645417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3400278326903557688775557 637552186294417066645417)
                ·
                  refine ⟨478164139720812799984063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637552186294417066645417 478164139720812799984063)
                  ·
                    rfl

theorem cell20_1047624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_1047624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047624 prefixEnd_1047624 := by exact prefixLift 1047624
  have htrace : WordTrace (prefixWord ++ tailWord_1047624) baseStart_1047624 baseEnd_1047624 := by
    simpa [prefixWord, tailWord_1047624, baseEnd_1047624] using wordTrace_append hprefix tailTrace_1047624
  have hstable : (prefixWord ++ tailWord_1047624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047624).length < 2 ^ (prefixWord ++ tailWord_1047624).sum := by decide
  have hdescent : baseEnd_1047624 < baseStart_1047624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047683 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_1047683 : Nat := 118140960795 + 1047683 * 2 ^ 59
def prefixEnd_1047683 : Nat := 4983230072969 + 3 ^ 40 * 1047683 * 2
def baseEnd_1047683 : Nat := 478191068928470817017155

theorem tailTrace_1047683 : CollatzResearch.WordTrace tailWord_1047683 prefixEnd_1047683 478191068928470817017155 := by
  unfold tailWord_1047683
  simp only [CollatzResearch.WordTrace]
  refine ⟨38212138263430895856163703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25474758842287263904109135 38212138263430895856163703)
  ·
    refine ⟨57318207395146343784245555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38212138263430895856163703 57318207395146343784245555)
    ·
      refine ⟨85977311092719515676368333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57318207395146343784245555 85977311092719515676368333)
      ·
        refine ⟨32241491659769818378638125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85977311092719515676368333 32241491659769818378638125)
        ·
          refine ⟨12090559372413681891989297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32241491659769818378638125 12090559372413681891989297)
          ·
            refine ⟨9067919529310261418991973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12090559372413681891989297 9067919529310261418991973)
            ·
              refine ⟨1700234911745674016060995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9067919529310261418991973 1700234911745674016060995)
              ·
                refine ⟨2550352367618511024091493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700234911745674016060995 2550352367618511024091493)
                ·
                  refine ⟨478191068928470817017155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550352367618511024091493 478191068928470817017155)
                  ·
                    rfl

theorem cell20_1047683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_1047683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047683 prefixEnd_1047683 := by exact prefixLift 1047683
  have htrace : WordTrace (prefixWord ++ tailWord_1047683) baseStart_1047683 baseEnd_1047683 := by
    simpa [prefixWord, tailWord_1047683, baseEnd_1047683] using wordTrace_append hprefix tailTrace_1047683
  have hstable : (prefixWord ++ tailWord_1047683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047683).length < 2 ^ (prefixWord ++ tailWord_1047683).sum := by decide
  have hdescent : baseEnd_1047683 < baseStart_1047683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047690 : List Nat := [3, 1, 2, 3, 1, 1, 2, 7]
def baseStart_1047690 : Nat := 118140960795 + 1047690 * 2 ^ 59
def prefixEnd_1047690 : Nat := 4983230072969 + 3 ^ 40 * 1047690 * 2
def baseEnd_1047690 : Nat := 159398087973069967927931

theorem tailTrace_1047690 : CollatzResearch.WordTrace tailWord_1047690 prefixEnd_1047690 159398087973069967927931 := by
  unfold tailWord_1047690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9553098393601384012917131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25474929049603690701112349 9553098393601384012917131)
  ·
    refine ⟨14329647590402076019375697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9553098393601384012917131 14329647590402076019375697)
    ·
      refine ⟨10747235692801557014531773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14329647590402076019375697 10747235692801557014531773)
      ·
        refine ⟨4030213384800583880449415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10747235692801557014531773 4030213384800583880449415)
        ·
          refine ⟨6045320077200875820674123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030213384800583880449415 6045320077200875820674123)
          ·
            refine ⟨9067980115801313731011185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045320077200875820674123 9067980115801313731011185)
            ·
              refine ⟨6800985086850985298258389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067980115801313731011185 6800985086850985298258389)
              ·
                refine ⟨159398087973069967927931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6800985086850985298258389 159398087973069967927931)
                ·
                  rfl

theorem cell20_1047690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_1047690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047690 prefixEnd_1047690 := by exact prefixLift 1047690
  have htrace : WordTrace (prefixWord ++ tailWord_1047690) baseStart_1047690 baseEnd_1047690 := by
    simpa [prefixWord, tailWord_1047690, baseEnd_1047690] using wordTrace_append hprefix tailTrace_1047690
  have hstable : (prefixWord ++ tailWord_1047690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047690).length < 2 ^ (prefixWord ++ tailWord_1047690).sum := by decide
  have hdescent : baseEnd_1047690 < baseStart_1047690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047717 : List Nat := [1, 3, 1, 2, 1, 6, 1, 3, 2]
def baseStart_1047717 : Nat := 118140960795 + 1047717 * 2 ^ 59
def prefixEnd_1047717 : Nat := 4983230072969 + 3 ^ 40 * 1047717 * 2
def baseEnd_1047717 : Nat := 478206587454917809883683

theorem tailTrace_1047717 : CollatzResearch.WordTrace tailWord_1047717 prefixEnd_1047717 478206587454917809883683 := by
  unfold tailWord_1047717
  simp only [CollatzResearch.WordTrace]
  refine ⟨38213378345307719662901405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25475585563538479775267603 38213378345307719662901405)
  ·
    refine ⟨14330016879490394873588027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38213378345307719662901405 14330016879490394873588027)
    ·
      refine ⟨21495025319235592310382041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14330016879490394873588027 21495025319235592310382041)
      ·
        refine ⟨16121268989426694232786531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21495025319235592310382041 16121268989426694232786531)
        ·
          refine ⟨24181903484140041349179797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16121268989426694232786531 24181903484140041349179797)
          ·
            refine ⟨1133526725819064438242803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24181903484140041349179797 1133526725819064438242803)
            ·
              refine ⟨1700290088728596657364205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133526725819064438242803 1700290088728596657364205)
              ·
                refine ⟨637608783273223746511577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1700290088728596657364205 637608783273223746511577)
                ·
                  refine ⟨478206587454917809883683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637608783273223746511577 478206587454917809883683)
                  ·
                    rfl

theorem cell20_1047717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_1047717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047717 prefixEnd_1047717 := by exact prefixLift 1047717
  have htrace : WordTrace (prefixWord ++ tailWord_1047717) baseStart_1047717 baseEnd_1047717 := by
    simpa [prefixWord, tailWord_1047717, baseEnd_1047717] using wordTrace_append hprefix tailTrace_1047717
  have hstable : (prefixWord ++ tailWord_1047717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047717).length < 2 ^ (prefixWord ++ tailWord_1047717).sum := by decide
  have hdescent : baseEnd_1047717 < baseStart_1047717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
