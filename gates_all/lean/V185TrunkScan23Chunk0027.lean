import V185TrunkScan23Chunk0026

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_159847 : List Nat := [1, 1, 5, 1, 1, 2, 2, 5, 5]
def baseStart_159847 : Nat := 118140960795 + 159847 * 2 ^ 59
def prefixEnd_159847 : Nat := 4983230072969 + 3 ^ 40 * 159847 * 2
def baseEnd_159847 : Nat := 9119815797704592397487

theorem tailTrace_159847 : CollatzResearch.WordTrace tailWord_159847 prefixEnd_159847 9119815797704592397487 := by
  unfold tailWord_159847
  simp only [CollatzResearch.WordTrace]
  refine ⟨5830099051909093539269795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3886732701272729026179863 5830099051909093539269795)
  ·
    refine ⟨8745148577863640308904693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5830099051909093539269795 8745148577863640308904693)
    ·
      refine ⟨819857679174716278959815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8745148577863640308904693 819857679174716278959815)
      ·
        refine ⟨1229786518762074418439723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819857679174716278959815 1229786518762074418439723)
        ·
          refine ⟨1844679778143111627659585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229786518762074418439723 1844679778143111627659585)
          ·
            refine ⟨1383509833607333720744689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844679778143111627659585 1383509833607333720744689)
            ·
              refine ⟨1037632375205500290558517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383509833607333720744689 1037632375205500290558517)
              ·
                refine ⟨97278035175515652239861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1037632375205500290558517 97278035175515652239861)
                ·
                  refine ⟨9119815797704592397487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97278035175515652239861 9119815797704592397487)
                  ·
                    rfl

theorem cell23_159847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 5].length) (baseStart_159847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159847 prefixEnd_159847 := by exact prefixLift 159847
  have htrace : WordTrace (prefixWord ++ tailWord_159847) baseStart_159847 baseEnd_159847 := by
    simpa [prefixWord, tailWord_159847, baseEnd_159847] using wordTrace_append hprefix tailTrace_159847
  have hstable : (prefixWord ++ tailWord_159847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159847).length < 2 ^ (prefixWord ++ tailWord_159847).sum := by decide
  have hdescent : baseEnd_159847 < baseStart_159847 := by decide
  rcases family_descends (prefixWord ++ tailWord_159847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159987 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 4]
def baseStart_159987 : Nat := 118140960795 + 159987 * 2 ^ 59
def prefixEnd_159987 : Nat := 4983230072969 + 3 ^ 40 * 159987 * 2
def baseEnd_159987 : Nat := 82150229470970783826739

theorem tailTrace_159987 : CollatzResearch.WordTrace tailWord_159987 prefixEnd_159987 82150229470970783826739 := by
  unfold tailWord_159987
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835205271401897449366215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3890136847601264966244143 5835205271401897449366215)
  ·
    refine ⟨8752807907102846174049323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5835205271401897449366215 8752807907102846174049323)
    ·
      refine ⟨13129211860654269261073985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8752807907102846174049323 13129211860654269261073985)
      ·
        refine ⟨9846908895490701945805489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13129211860654269261073985 9846908895490701945805489)
        ·
          refine ⟨7385181671618026459354117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9846908895490701945805489 7385181671618026459354117)
          ·
            refine ⟨1384721563428379961128897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7385181671618026459354117 1384721563428379961128897)
            ·
              refine ⟨1038541172571284970846673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384721563428379961128897 1038541172571284970846673)
              ·
                refine ⟨778905879428463728135005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038541172571284970846673 778905879428463728135005)
                ·
                  refine ⟨292089704785673898050627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 778905879428463728135005 292089704785673898050627)
                  ·
                    refine ⟨438134557178510847075941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 292089704785673898050627 438134557178510847075941)
                    ·
                      refine ⟨82150229470970783826739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 438134557178510847075941 82150229470970783826739)
                      ·
                        rfl

theorem cell23_159987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_159987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_159987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_159987 prefixEnd_159987 := by exact prefixLift 159987
  have htrace : WordTrace (prefixWord ++ tailWord_159987) baseStart_159987 baseEnd_159987 := by
    simpa [prefixWord, tailWord_159987, baseEnd_159987] using wordTrace_append hprefix tailTrace_159987
  have hstable : (prefixWord ++ tailWord_159987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159987).length < 2 ^ (prefixWord ++ tailWord_159987).sum := by decide
  have hdescent : baseEnd_159987 < baseStart_159987 := by decide
  rcases family_descends (prefixWord ++ tailWord_159987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160017 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_160017 : Nat := 118140960795 + 160017 * 2 ^ 59
def prefixEnd_160017 : Nat := 4983230072969 + 3 ^ 40 * 160017 * 2
def baseEnd_160017 : Nat := 82165633890605666451601

theorem tailTrace_160017 : CollatzResearch.WordTrace tailWord_160017 prefixEnd_160017 82165633890605666451601 := by
  unfold tailWord_160017
  simp only [CollatzResearch.WordTrace]
  refine ⟨5836299461293212572958305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3890866307528808381972203 5836299461293212572958305)
  ·
    refine ⟨4377224595969909429718729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5836299461293212572958305 4377224595969909429718729)
    ·
      refine ⟨3282918446977432072289047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4377224595969909429718729 3282918446977432072289047)
      ·
        refine ⟨4924377670466148108433571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282918446977432072289047 4924377670466148108433571)
        ·
          refine ⟨7386566505699222162650357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4924377670466148108433571 7386566505699222162650357)
          ·
            refine ⟨692490609909302077748471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7386566505699222162650357 692490609909302077748471)
            ·
              refine ⟨1038735914863953116622707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692490609909302077748471 1038735914863953116622707)
              ·
                refine ⟨1558103872295929674934061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038735914863953116622707 1558103872295929674934061)
                ·
                  refine ⟨584288952110973628100273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1558103872295929674934061 584288952110973628100273)
                  ·
                    refine ⟨438216714083230221075205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584288952110973628100273 438216714083230221075205)
                    ·
                      refine ⟨82165633890605666451601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 438216714083230221075205 82165633890605666451601)
                      ·
                        rfl

theorem cell23_160017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_160017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160017 prefixEnd_160017 := by exact prefixLift 160017
  have htrace : WordTrace (prefixWord ++ tailWord_160017) baseStart_160017 baseEnd_160017 := by
    simpa [prefixWord, tailWord_160017, baseEnd_160017] using wordTrace_append hprefix tailTrace_160017
  have hstable : (prefixWord ++ tailWord_160017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160017).length < 2 ^ (prefixWord ++ tailWord_160017).sum := by decide
  have hdescent : baseEnd_160017 < baseStart_160017 := by decide
  rcases family_descends (prefixWord ++ tailWord_160017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160031 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 2, 4]
def baseStart_160031 : Nat := 118140960795 + 160031 * 2 ^ 59
def prefixEnd_160031 : Nat := 4983230072969 + 3 ^ 40 * 160031 * 2
def baseEnd_160031 : Nat := 27390940873256203892179

theorem tailTrace_160031 : CollatzResearch.WordTrace tailWord_160031 prefixEnd_160031 27390940873256203892179 := by
  unfold tailWord_160031
  simp only [CollatzResearch.WordTrace]
  refine ⟨5836810083242492963967947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3891206722161661975978631 5836810083242492963967947)
  ·
    refine ⟨8755215124863739445951921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5836810083242492963967947 8755215124863739445951921)
    ·
      refine ⟨6566411343647804584463941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8755215124863739445951921 6566411343647804584463941)
      ·
        refine ⟨1231202126933963359586989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6566411343647804584463941 1231202126933963359586989)
        ·
          refine ⟨461700797600236259845121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1231202126933963359586989 461700797600236259845121)
          ·
            refine ⟨346275598200177194883841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461700797600236259845121 346275598200177194883841)
            ·
              refine ⟨259706698650132896162881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346275598200177194883841 259706698650132896162881)
              ·
                refine ⟨194780023987599672122161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259706698650132896162881 194780023987599672122161)
                ·
                  refine ⟨146085017990699754091621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194780023987599672122161 146085017990699754091621)
                  ·
                    refine ⟨27390940873256203892179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146085017990699754091621 27390940873256203892179)
                    ·
                      rfl

theorem cell23_160031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_160031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160031 prefixEnd_160031 := by exact prefixLift 160031
  have htrace : WordTrace (prefixWord ++ tailWord_160031) baseStart_160031 baseEnd_160031 := by
    simpa [prefixWord, tailWord_160031, baseEnd_160031] using wordTrace_append hprefix tailTrace_160031
  have hstable : (prefixWord ++ tailWord_160031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160031).length < 2 ^ (prefixWord ++ tailWord_160031).sum := by decide
  have hdescent : baseEnd_160031 < baseStart_160031 := by decide
  rcases family_descends (prefixWord ++ tailWord_160031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160087 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 4, 6]
def baseStart_160087 : Nat := 118140960795 + 160087 * 2 ^ 59
def prefixEnd_160087 : Nat := 4983230072969 + 3 ^ 40 * 160087 * 2
def baseEnd_160087 : Nat := 27400525845473464192093

theorem tailTrace_160087 : CollatzResearch.WordTrace tailWord_160087 prefixEnd_160087 27400525845473464192093 := by
  unfold tailWord_160087
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838852571039614528006515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3892568380693076352004343 5838852571039614528006515)
  ·
    refine ⟨8758278856559421792009773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5838852571039614528006515 8758278856559421792009773)
    ·
      refine ⟨3284354571209783172003665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8758278856559421792009773 3284354571209783172003665)
      ·
        refine ⟨2463265928407337379002749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3284354571209783172003665 2463265928407337379002749)
        ·
          refine ⟨923724723152751517126031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2463265928407337379002749 923724723152751517126031)
          ·
            refine ⟨1385587084729127275689047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923724723152751517126031 1385587084729127275689047)
            ·
              refine ⟨2078380627093690913533571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385587084729127275689047 2078380627093690913533571)
              ·
                refine ⟨3117570940640536370300357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078380627093690913533571 3117570940640536370300357)
                ·
                  refine ⟨584544551370100569431317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3117570940640536370300357 584544551370100569431317)
                  ·
                    refine ⟨27400525845473464192093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 584544551370100569431317 27400525845473464192093)
                    ·
                      rfl

theorem cell23_160087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_160087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160087 prefixEnd_160087 := by exact prefixLift 160087
  have htrace : WordTrace (prefixWord ++ tailWord_160087) baseStart_160087 baseEnd_160087 := by
    simpa [prefixWord, tailWord_160087, baseEnd_160087] using wordTrace_append hprefix tailTrace_160087
  have hstable : (prefixWord ++ tailWord_160087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160087).length < 2 ^ (prefixWord ++ tailWord_160087).sum := by decide
  have hdescent : baseEnd_160087 < baseStart_160087 := by decide
  rcases family_descends (prefixWord ++ tailWord_160087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160097 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_160097 : Nat := 118140960795 + 160097 * 2 ^ 59
def prefixEnd_160097 : Nat := 4983230072969 + 3 ^ 40 * 160097 * 2
def baseEnd_160097 : Nat := 82206712342965353451233

theorem tailTrace_160097 : CollatzResearch.WordTrace tailWord_160097 prefixEnd_160097 82206712342965353451233 := by
  unfold tailWord_160097
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839217301003386235870545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3892811534002257490580363 5839217301003386235870545)
  ·
    refine ⟨4379412975752539676902909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5839217301003386235870545 4379412975752539676902909)
    ·
      refine ⟨1642279865907202378838591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4379412975752539676902909 1642279865907202378838591)
      ·
        refine ⟨2463419798860803568257887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642279865907202378838591 2463419798860803568257887)
        ·
          refine ⟨3695129698291205352386831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463419798860803568257887 3695129698291205352386831)
          ·
            refine ⟨5542694547436808028580247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695129698291205352386831 5542694547436808028580247)
            ·
              refine ⟨8314041821155212042870371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5542694547436808028580247 8314041821155212042870371)
              ·
                refine ⟨12471062731732818064305557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8314041821155212042870371 12471062731732818064305557)
                ·
                  refine ⟨584581065549975846764323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12471062731732818064305557 584581065549975846764323)
                  ·
                    refine ⟨876871598324963770146485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 584581065549975846764323 876871598324963770146485)
                    ·
                      refine ⟨82206712342965353451233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 876871598324963770146485 82206712342965353451233)
                      ·
                        rfl

theorem cell23_160097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_160097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160097 prefixEnd_160097 := by exact prefixLift 160097
  have htrace : WordTrace (prefixWord ++ tailWord_160097) baseStart_160097 baseEnd_160097 := by
    simpa [prefixWord, tailWord_160097, baseEnd_160097] using wordTrace_append hprefix tailTrace_160097
  have hstable : (prefixWord ++ tailWord_160097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160097).length < 2 ^ (prefixWord ++ tailWord_160097).sum := by decide
  have hdescent : baseEnd_160097 < baseStart_160097 := by decide
  rcases family_descends (prefixWord ++ tailWord_160097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160104 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 2, 6]
def baseStart_160104 : Nat := 118140960795 + 160104 * 2 ^ 59
def prefixEnd_160104 : Nat := 4983230072969 + 3 ^ 40 * 160104 * 2
def baseEnd_160104 : Nat := 27403435569182275354567

theorem tailTrace_160104 : CollatzResearch.WordTrace tailWord_160104 prefixEnd_160104 27403435569182275354567 := by
  unfold tailWord_160104
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919736305989013215687683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3892981741318684287583577 2919736305989013215687683)
  ·
    refine ⟨4379604458983519823531525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2919736305989013215687683 4379604458983519823531525)
    ·
      refine ⟨821175836059409966912161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4379604458983519823531525 821175836059409966912161)
      ·
        refine ⟨615881877044557475184121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 821175836059409966912161 615881877044557475184121)
        ·
          refine ⟨461911407783418106388091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615881877044557475184121 461911407783418106388091)
          ·
            refine ⟨692867111675127159582137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461911407783418106388091 692867111675127159582137)
            ·
              refine ⟨519650333756345369686603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692867111675127159582137 519650333756345369686603)
              ·
                refine ⟨779475500634518054529905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519650333756345369686603 779475500634518054529905)
                ·
                  refine ⟨584606625475888540897429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 779475500634518054529905 584606625475888540897429)
                  ·
                    refine ⟨27403435569182275354567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 584606625475888540897429 27403435569182275354567)
                    ·
                      rfl

theorem cell23_160104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_160104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160104 prefixEnd_160104 := by exact prefixLift 160104
  have htrace : WordTrace (prefixWord ++ tailWord_160104) baseStart_160104 baseEnd_160104 := by
    simpa [prefixWord, tailWord_160104, baseEnd_160104] using wordTrace_append hprefix tailTrace_160104
  have hstable : (prefixWord ++ tailWord_160104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160104).length < 2 ^ (prefixWord ++ tailWord_160104).sum := by decide
  have hdescent : baseEnd_160104 < baseStart_160104 := by decide
  rcases family_descends (prefixWord ++ tailWord_160104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160221 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_160221 : Nat := 118140960795 + 160221 * 2 ^ 59
def prefixEnd_160221 : Nat := 4983230072969 + 3 ^ 40 * 160221 * 2
def baseEnd_160221 : Nat := 82270383944122868300663

theorem tailTrace_160221 : CollatzResearch.WordTrace tailWord_160221 prefixEnd_160221 82270383944122868300663 := by
  unfold tailWord_160221
  simp only [CollatzResearch.WordTrace]
  refine ⟨5843739952554155413384517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3895826635036103608923011 5843739952554155413384517)
  ·
    refine ⟨1095701241103904140009597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5843739952554155413384517 1095701241103904140009597)
    ·
      refine ⟨410887965413964052503599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1095701241103904140009597 410887965413964052503599)
      ·
        refine ⟨616331948120946078755399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410887965413964052503599 616331948120946078755399)
        ·
          refine ⟨924497922181419118133099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616331948120946078755399 924497922181419118133099)
          ·
            refine ⟨1386746883272128677199649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924497922181419118133099 1386746883272128677199649)
            ·
              refine ⟨1040060162454096507899737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386746883272128677199649 1040060162454096507899737)
              ·
                refine ⟨780045121840572380924803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040060162454096507899737 780045121840572380924803)
                ·
                  refine ⟨1170067682760858571387205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780045121840572380924803 1170067682760858571387205)
                  ·
                    refine ⟨219387690517660982135101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1170067682760858571387205 219387690517660982135101)
                    ·
                      refine ⟨82270383944122868300663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 219387690517660982135101 82270383944122868300663)
                      ·
                        rfl

theorem cell23_160221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_160221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160221 prefixEnd_160221 := by exact prefixLift 160221
  have htrace : WordTrace (prefixWord ++ tailWord_160221) baseStart_160221 baseEnd_160221 := by
    simpa [prefixWord, tailWord_160221, baseEnd_160221] using wordTrace_append hprefix tailTrace_160221
  have hstable : (prefixWord ++ tailWord_160221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160221).length < 2 ^ (prefixWord ++ tailWord_160221).sum := by decide
  have hdescent : baseEnd_160221 < baseStart_160221 := by decide
  rcases family_descends (prefixWord ++ tailWord_160221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160224 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 6]
def baseStart_160224 : Nat := 118140960795 + 160224 * 2 ^ 59
def prefixEnd_160224 : Nat := 4983230072969 + 3 ^ 40 * 160224 * 2
def baseEnd_160224 : Nat := 9141324931787372951461

theorem tailTrace_160224 : CollatzResearch.WordTrace tailWord_160224 prefixEnd_160224 9141324931787372951461 := by
  unfold tailWord_160224
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921924685771643462871863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3895899581028857950495817 2921924685771643462871863)
  ·
    refine ⟨4382887028657465194307795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2921924685771643462871863 4382887028657465194307795)
    ·
      refine ⟨6574330542986197791461693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382887028657465194307795 6574330542986197791461693)
      ·
        refine ⟨2465373953619824171798135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6574330542986197791461693 2465373953619824171798135)
        ·
          refine ⟨3698060930429736257697203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465373953619824171798135 3698060930429736257697203)
          ·
            refine ⟨5547091395644604386545805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698060930429736257697203 5547091395644604386545805)
            ·
              refine ⟨2080159273366726644954677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5547091395644604386545805 2080159273366726644954677)
              ·
                refine ⟨195014931878130622964501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2080159273366726644954677 195014931878130622964501)
                ·
                  refine ⟨9141324931787372951461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 195014931878130622964501 9141324931787372951461)
                  ·
                    rfl

theorem cell23_160224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 6].length) (baseStart_160224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160224 prefixEnd_160224 := by exact prefixLift 160224
  have htrace : WordTrace (prefixWord ++ tailWord_160224) baseStart_160224 baseEnd_160224 := by
    simpa [prefixWord, tailWord_160224, baseEnd_160224] using wordTrace_append hprefix tailTrace_160224
  have hstable : (prefixWord ++ tailWord_160224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160224).length < 2 ^ (prefixWord ++ tailWord_160224).sum := by decide
  have hdescent : baseEnd_160224 < baseStart_160224 := by decide
  rcases family_descends (prefixWord ++ tailWord_160224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160238 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_160238 : Nat := 118140960795 + 160238 * 2 ^ 59
def prefixEnd_160238 : Nat := 4983230072969 + 3 ^ 40 * 160238 * 2
def baseEnd_160238 : Nat := 82279113115249301788085

theorem tailTrace_160238 : CollatzResearch.WordTrace tailWord_160238 prefixEnd_160238 82279113115249301788085 := by
  unfold tailWord_160238
  simp only [CollatzResearch.WordTrace]
  refine ⟨730544999186570914594171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3896239995661711544502245 730544999186570914594171)
  ·
    refine ⟨1095817498779856371891257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 730544999186570914594171 1095817498779856371891257)
    ·
      refine ⟨821863124084892278918443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1095817498779856371891257 821863124084892278918443)
      ·
        refine ⟨1232794686127338418377665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821863124084892278918443 1232794686127338418377665)
        ·
          refine ⟨924596014595503813783249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1232794686127338418377665 924596014595503813783249)
          ·
            refine ⟨693447010946627860337437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 924596014595503813783249 693447010946627860337437)
            ·
              refine ⟨260042629104985447626539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 693447010946627860337437 260042629104985447626539)
              ·
                refine ⟨390063943657478171439809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260042629104985447626539 390063943657478171439809)
                ·
                  refine ⟨292547957743108628579857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390063943657478171439809 292547957743108628579857)
                  ·
                    refine ⟨219410968307331471434893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 292547957743108628579857 219410968307331471434893)
                    ·
                      refine ⟨82279113115249301788085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 219410968307331471434893 82279113115249301788085)
                      ·
                        rfl

theorem cell23_160238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_160238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160238 prefixEnd_160238 := by exact prefixLift 160238
  have htrace : WordTrace (prefixWord ++ tailWord_160238) baseStart_160238 baseEnd_160238 := by
    simpa [prefixWord, tailWord_160238, baseEnd_160238] using wordTrace_append hprefix tailTrace_160238
  have hstable : (prefixWord ++ tailWord_160238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160238).length < 2 ^ (prefixWord ++ tailWord_160238).sum := by decide
  have hdescent : baseEnd_160238 < baseStart_160238 := by decide
  rcases family_descends (prefixWord ++ tailWord_160238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160258 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 8]
def baseStart_160258 : Nat := 118140960795 + 160258 * 2 ^ 59
def prefixEnd_160258 : Nat := 4983230072969 + 3 ^ 40 * 160258 * 2
def baseEnd_160258 : Nat := 9143264747593247059777

theorem tailTrace_160258 : CollatzResearch.WordTrace tailWord_160258 prefixEnd_160258 9143264747593247059777 := by
  unfold tailWord_160258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461272363355027683120357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3896726302280073821654285 1461272363355027683120357)
  ·
    refine ⟨273988568129067690585067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1461272363355027683120357 273988568129067690585067)
    ·
      refine ⟨410982852193601535877601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273988568129067690585067 410982852193601535877601)
      ·
        refine ⟨308237139145201151908201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410982852193601535877601 308237139145201151908201)
        ·
          refine ⟨231177854358900863931151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308237139145201151908201 231177854358900863931151)
          ·
            refine ⟨346766781538351295896727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231177854358900863931151 346766781538351295896727)
            ·
              refine ⟨520150172307526943845091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346766781538351295896727 520150172307526943845091)
              ·
                refine ⟨780225258461290415767637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520150172307526943845091 780225258461290415767637)
                ·
                  refine ⟨9143264747593247059777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 780225258461290415767637 9143264747593247059777)
                  ·
                    rfl

theorem cell23_160258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_160258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160258 prefixEnd_160258 := by exact prefixLift 160258
  have htrace : WordTrace (prefixWord ++ tailWord_160258) baseStart_160258 baseEnd_160258 := by
    simpa [prefixWord, tailWord_160258, baseEnd_160258] using wordTrace_append hprefix tailTrace_160258
  have hstable : (prefixWord ++ tailWord_160258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160258).length < 2 ^ (prefixWord ++ tailWord_160258).sum := by decide
  have hdescent : baseEnd_160258 < baseStart_160258 := by decide
  rcases family_descends (prefixWord ++ tailWord_160258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160262 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_160262 : Nat := 118140960795 + 160262 * 2 ^ 59
def prefixEnd_160262 : Nat := 4983230072969 + 3 ^ 40 * 160262 * 2
def baseEnd_160262 : Nat := 27430478883652402629325

theorem tailTrace_160262 : CollatzResearch.WordTrace tailWord_160262 prefixEnd_160262 27430478883652402629325 := by
  unfold tailWord_160262
  simp only [CollatzResearch.WordTrace]
  refine ⟨182663604543925606738345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3896823563603746277084693 182663604543925606738345)
  ·
    refine ⟨136997703407944205053759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182663604543925606738345 136997703407944205053759)
    ·
      refine ⟨205496555111916307580639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136997703407944205053759 205496555111916307580639)
      ·
        refine ⟨308244832667874461370959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205496555111916307580639 308244832667874461370959)
        ·
          refine ⟨462367249001811692056439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308244832667874461370959 462367249001811692056439)
          ·
            refine ⟨693550873502717538084659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462367249001811692056439 693550873502717538084659)
            ·
              refine ⟨1040326310254076307126989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693550873502717538084659 1040326310254076307126989)
              ·
                refine ⟨390122366345278615172621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1040326310254076307126989 390122366345278615172621)
                ·
                  refine ⟨146295887379479480689733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390122366345278615172621 146295887379479480689733)
                  ·
                    refine ⟨27430478883652402629325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146295887379479480689733 27430478883652402629325)
                    ·
                      rfl

theorem cell23_160262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_160262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160262 prefixEnd_160262 := by exact prefixLift 160262
  have htrace : WordTrace (prefixWord ++ tailWord_160262) baseStart_160262 baseEnd_160262 := by
    simpa [prefixWord, tailWord_160262, baseEnd_160262] using wordTrace_append hprefix tailTrace_160262
  have hstable : (prefixWord ++ tailWord_160262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160262).length < 2 ^ (prefixWord ++ tailWord_160262).sum := by decide
  have hdescent : baseEnd_160262 < baseStart_160262 := by decide
  rcases family_descends (prefixWord ++ tailWord_160262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160268 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_160268 : Nat := 118140960795 + 160268 * 2 ^ 59
def prefixEnd_160268 : Nat := 4983230072969 + 3 ^ 40 * 160268 * 2
def baseEnd_160268 : Nat := 82294517534884184412947

theorem tailTrace_160268 : CollatzResearch.WordTrace tailWord_160268 prefixEnd_160268 82294517534884184412947 := by
  unfold tailWord_160268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922727091691941220172729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3896969455589254960230305 2922727091691941220172729)
  ·
    refine ⟨2192045318768955915129547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2922727091691941220172729 2192045318768955915129547)
    ·
      refine ⟨3288067978153433872694321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192045318768955915129547 3288067978153433872694321)
      ·
        refine ⟨2466050983615075404520741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288067978153433872694321 2466050983615075404520741)
        ·
          refine ⟨462384559427826638347639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2466050983615075404520741 462384559427826638347639)
          ·
            refine ⟨693576839141739957521459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462384559427826638347639 693576839141739957521459)
            ·
              refine ⟨1040365258712609936282189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693576839141739957521459 1040365258712609936282189)
              ·
                refine ⟨390136972017228726105821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1040365258712609936282189 390136972017228726105821)
                ·
                  refine ⟨146301364506460772289683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390136972017228726105821 146301364506460772289683)
                  ·
                    refine ⟨219452046759691158434525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146301364506460772289683 219452046759691158434525)
                    ·
                      refine ⟨82294517534884184412947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 219452046759691158434525 82294517534884184412947)
                      ·
                        rfl

theorem cell23_160268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_160268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160268 prefixEnd_160268 := by exact prefixLift 160268
  have htrace : WordTrace (prefixWord ++ tailWord_160268) baseStart_160268 baseEnd_160268 := by
    simpa [prefixWord, tailWord_160268, baseEnd_160268] using wordTrace_append hprefix tailTrace_160268
  have hstable : (prefixWord ++ tailWord_160268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160268).length < 2 ^ (prefixWord ++ tailWord_160268).sum := by decide
  have hdescent : baseEnd_160268 < baseStart_160268 := by decide
  rcases family_descends (prefixWord ++ tailWord_160268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160311 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_160311 : Nat := 118140960795 + 160311 * 2 ^ 59
def prefixEnd_160311 : Nat := 4983230072969 + 3 ^ 40 * 160311 * 2
def baseEnd_160311 : Nat := 82316597203027516175249

theorem tailTrace_160311 : CollatzResearch.WordTrace tailWord_160311 prefixEnd_160311 82316597203027516175249 := by
  unfold tailWord_160311
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847022522228100784160787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3898015014818733856107191 5847022522228100784160787)
  ·
    refine ⟨8770533783342151176241181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5847022522228100784160787 8770533783342151176241181)
    ·
      refine ⟨3288950168753306691090443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8770533783342151176241181 3288950168753306691090443)
      ·
        refine ⟨4933425253129960036635665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3288950168753306691090443 4933425253129960036635665)
        ·
          refine ⟨3700068939847470027476749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4933425253129960036635665 3700068939847470027476749)
          ·
            refine ⟨1387525852442801260303781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3700068939847470027476749 1387525852442801260303781)
            ·
              refine ⟨260161097333025236306959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1387525852442801260303781 260161097333025236306959)
              ·
                refine ⟨390241645999537854460439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260161097333025236306959 390241645999537854460439)
                ·
                  refine ⟨585362468999306781690659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390241645999537854460439 585362468999306781690659)
                  ·
                    refine ⟨878043703498960172535989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 585362468999306781690659 878043703498960172535989)
                    ·
                      refine ⟨82316597203027516175249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 878043703498960172535989 82316597203027516175249)
                      ·
                        rfl

theorem cell23_160311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_160311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160311 prefixEnd_160311 := by exact prefixLift 160311
  have htrace : WordTrace (prefixWord ++ tailWord_160311) baseStart_160311 baseEnd_160311 := by
    simpa [prefixWord, tailWord_160311, baseEnd_160311] using wordTrace_append hprefix tailTrace_160311
  have hstable : (prefixWord ++ tailWord_160311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160311).length < 2 ^ (prefixWord ++ tailWord_160311).sum := by decide
  have hdescent : baseEnd_160311 < baseStart_160311 := by decide
  rcases family_descends (prefixWord ++ tailWord_160311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160314 : List Nat := [3, 1, 1, 1, 3, 3, 11]
def baseStart_160314 : Nat := 118140960795 + 160314 * 2 ^ 59
def prefixEnd_160314 : Nat := 4983230072969 + 3 ^ 40 * 160314 * 2
def baseEnd_160314 : Nat := 1016273304259148202935

theorem tailTrace_160314 : CollatzResearch.WordTrace tailWord_160314 prefixEnd_160314 1016273304259148202935 := by
  unfold tailWord_160314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461782985304308074129999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3898087960811488197679997 1461782985304308074129999)
  ·
    refine ⟨2192674477956462111194999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1461782985304308074129999 2192674477956462111194999)
    ·
      refine ⟨3289011716934693166792499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192674477956462111194999 3289011716934693166792499)
      ·
        refine ⟨4933517575402039750188749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289011716934693166792499 4933517575402039750188749)
        ·
          refine ⟨1850069090775764906320781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4933517575402039750188749 1850069090775764906320781)
          ·
            refine ⟨693775909040911839870293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1850069090775764906320781 693775909040911839870293)
            ·
              refine ⟨1016273304259148202935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 693775909040911839870293 1016273304259148202935)
              ·
                rfl

theorem cell23_160314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 11].length) (baseStart_160314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160314 prefixEnd_160314 := by exact prefixLift 160314
  have htrace : WordTrace (prefixWord ++ tailWord_160314) baseStart_160314 baseEnd_160314 := by
    simpa [prefixWord, tailWord_160314, baseEnd_160314] using wordTrace_append hprefix tailTrace_160314
  have hstable : (prefixWord ++ tailWord_160314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160314).length < 2 ^ (prefixWord ++ tailWord_160314).sum := by decide
  have hdescent : baseEnd_160314 < baseStart_160314 := by decide
  rcases family_descends (prefixWord ++ tailWord_160314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160321 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_160321 : Nat := 118140960795 + 160321 * 2 ^ 59
def prefixEnd_160321 : Nat := 4983230072969 + 3 ^ 40 * 160321 * 2
def baseEnd_160321 : Nat := 82321732009572477050203

theorem tailTrace_160321 : CollatzResearch.WordTrace tailWord_160321 prefixEnd_160321 82321732009572477050203 := by
  unfold tailWord_160321
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847387252191872492024817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3898258168127914994683211 5847387252191872492024817)
  ·
    refine ⟨4385540439143904369018613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5847387252191872492024817 4385540439143904369018613)
    ·
      refine ⟨411144416169741034595495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4385540439143904369018613 411144416169741034595495)
      ·
        refine ⟨616716624254611551893243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411144416169741034595495 616716624254611551893243)
        ·
          refine ⟨925074936381917327839865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616716624254611551893243 925074936381917327839865)
          ·
            refine ⟨693806202286437995879899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 925074936381917327839865 693806202286437995879899)
            ·
              refine ⟨1040709303429656993819849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693806202286437995879899 1040709303429656993819849)
              ·
                refine ⟨780531977572242745364887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040709303429656993819849 780531977572242745364887)
                ·
                  refine ⟨1170797966358364118047331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780531977572242745364887 1170797966358364118047331)
                  ·
                    refine ⟨1756196949537546177070997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1170797966358364118047331 1756196949537546177070997)
                    ·
                      refine ⟨82321732009572477050203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1756196949537546177070997 82321732009572477050203)
                      ·
                        rfl

theorem cell23_160321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_160321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160321 prefixEnd_160321 := by exact prefixLift 160321
  have htrace : WordTrace (prefixWord ++ tailWord_160321) baseStart_160321 baseEnd_160321 := by
    simpa [prefixWord, tailWord_160321, baseEnd_160321] using wordTrace_append hprefix tailTrace_160321
  have hstable : (prefixWord ++ tailWord_160321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160321).length < 2 ^ (prefixWord ++ tailWord_160321).sum := by decide
  have hdescent : baseEnd_160321 < baseStart_160321 := by decide
  rcases family_descends (prefixWord ++ tailWord_160321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160325 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 3, 2, 2]
def baseStart_160325 : Nat := 118140960795 + 160325 * 2 ^ 59
def prefixEnd_160325 : Nat := 4983230072969 + 3 ^ 40 * 160325 * 2
def baseEnd_160325 : Nat := 82323785932190461400185

theorem tailTrace_160325 : CollatzResearch.WordTrace tailWord_160325 prefixEnd_160325 82323785932190461400185 := by
  unfold tailWord_160325
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847533144177381175170429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3898355429451587450113619 5847533144177381175170429)
  ·
    refine ⟨2192824929066517940688911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5847533144177381175170429 2192824929066517940688911)
    ·
      refine ⟨3289237393599776911033367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192824929066517940688911 3289237393599776911033367)
      ·
        refine ⟨4933856090399665366550051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3289237393599776911033367 4933856090399665366550051)
        ·
          refine ⟨7400784135599498049825077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4933856090399665366550051 7400784135599498049825077)
          ·
            refine ⟨693823512712452942171101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7400784135599498049825077 693823512712452942171101)
            ·
              refine ⟨260183817267169853314163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 693823512712452942171101 260183817267169853314163)
              ·
                refine ⟨390275725900754779971245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260183817267169853314163 390275725900754779971245)
                ·
                  refine ⟨146353397212783042489217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 390275725900754779971245 146353397212783042489217)
                  ·
                    refine ⟨109765047909587281866913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146353397212783042489217 109765047909587281866913)
                    ·
                      refine ⟨82323785932190461400185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109765047909587281866913 82323785932190461400185)
                      ·
                        rfl

theorem cell23_160325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_160325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160325 prefixEnd_160325 := by exact prefixLift 160325
  have htrace : WordTrace (prefixWord ++ tailWord_160325) baseStart_160325 baseEnd_160325 := by
    simpa [prefixWord, tailWord_160325, baseEnd_160325] using wordTrace_append hprefix tailTrace_160325
  have hstable : (prefixWord ++ tailWord_160325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160325).length < 2 ^ (prefixWord ++ tailWord_160325).sum := by decide
  have hdescent : baseEnd_160325 < baseStart_160325 := by decide
  rcases family_descends (prefixWord ++ tailWord_160325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160391 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 2, 6]
def baseStart_160391 : Nat := 118140960795 + 160391 * 2 ^ 59
def prefixEnd_160391 : Nat := 4983230072969 + 3 ^ 40 * 160391 * 2
def baseEnd_160391 : Nat := 27452558551795734391627

theorem tailTrace_160391 : CollatzResearch.WordTrace tailWord_160391 prefixEnd_160391 27452558551795734391627 := by
  unfold tailWord_160391
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849940361938274447073027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3899960241292182964715351 5849940361938274447073027)
  ·
    refine ⟨8774910542907411670609541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5849940361938274447073027 8774910542907411670609541)
    ·
      refine ⟨1645295726795139688239289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8774910542907411670609541 1645295726795139688239289)
      ·
        refine ⟨1233971795096354766179467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1645295726795139688239289 1233971795096354766179467)
        ·
          refine ⟨1850957692644532149269201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233971795096354766179467 1850957692644532149269201)
          ·
            refine ⟨1388218269483399111951901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850957692644532149269201 1388218269483399111951901)
            ·
              refine ⟨520581851056274666981963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1388218269483399111951901 520581851056274666981963)
              ·
                refine ⟨780872776584412000472945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520581851056274666981963 780872776584412000472945)
                ·
                  refine ⟨585654582438309000354709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780872776584412000472945 585654582438309000354709)
                  ·
                    refine ⟨27452558551795734391627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 585654582438309000354709 27452558551795734391627)
                    ·
                      rfl

theorem cell23_160391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_160391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160391 prefixEnd_160391 := by exact prefixLift 160391
  have htrace : WordTrace (prefixWord ++ tailWord_160391) baseStart_160391 baseEnd_160391 := by
    simpa [prefixWord, tailWord_160391, baseEnd_160391] using wordTrace_append hprefix tailTrace_160391
  have hstable : (prefixWord ++ tailWord_160391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160391).length < 2 ^ (prefixWord ++ tailWord_160391).sum := by decide
  have hdescent : baseEnd_160391 < baseStart_160391 := by decide
  rcases family_descends (prefixWord ++ tailWord_160391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160426 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_160426 : Nat := 118140960795 + 160426 * 2 ^ 59
def prefixEnd_160426 : Nat := 4983230072969 + 3 ^ 40 * 160426 * 2
def baseEnd_160426 : Nat := 82375647478294566237221

theorem tailTrace_160426 : CollatzResearch.WordTrace tailWord_160426 prefixEnd_160426 82375647478294566237221 := by
  unfold tailWord_160426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462804229202868856149283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3900811277874316949731421 1462804229202868856149283)
  ·
    refine ⟨2194206343804303284223925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1462804229202868856149283 2194206343804303284223925)
    ·
      refine ⟨205706844731653432895993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2194206343804303284223925 205706844731653432895993)
      ·
        refine ⟨154280133548740074671995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205706844731653432895993 154280133548740074671995)
        ·
          refine ⟨231420200323110112007993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154280133548740074671995 231420200323110112007993)
          ·
            refine ⟨173565150242332584005995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231420200323110112007993 173565150242332584005995)
            ·
              refine ⟨260347725363498876008993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173565150242332584005995 260347725363498876008993)
              ·
                refine ⟨195260794022624157006745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260347725363498876008993 195260794022624157006745)
                ·
                  refine ⟨146445595516968117755059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195260794022624157006745 146445595516968117755059)
                  ·
                    refine ⟨219668393275452176632589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146445595516968117755059 219668393275452176632589)
                    ·
                      refine ⟨82375647478294566237221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 219668393275452176632589 82375647478294566237221)
                      ·
                        rfl

theorem cell23_160426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_160426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160426 prefixEnd_160426 := by exact prefixLift 160426
  have htrace : WordTrace (prefixWord ++ tailWord_160426) baseStart_160426 baseEnd_160426 := by
    simpa [prefixWord, tailWord_160426, baseEnd_160426] using wordTrace_append hprefix tailTrace_160426
  have hstable : (prefixWord ++ tailWord_160426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160426).length < 2 ^ (prefixWord ++ tailWord_160426).sum := by decide
  have hdescent : baseEnd_160426 < baseStart_160426 := by decide
  rcases family_descends (prefixWord ++ tailWord_160426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160448 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3]
def baseStart_160448 : Nat := 118140960795 + 160448 * 2 ^ 59
def prefixEnd_160448 : Nat := 4983230072969 + 3 ^ 40 * 160448 * 2
def baseEnd_160448 : Nat := 82386944052693480162119

theorem tailTrace_160448 : CollatzResearch.WordTrace tailWord_160448 prefixEnd_160448 82386944052693480162119 := by
  unfold tailWord_160448
  simp only [CollatzResearch.WordTrace]
  refine ⟨2926009661365886590948999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3901346215154515454598665 2926009661365886590948999)
  ·
    refine ⟨4389014492048829886423499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2926009661365886590948999 4389014492048829886423499)
    ·
      refine ⟨6583521738073244829635249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4389014492048829886423499 6583521738073244829635249)
      ·
        refine ⟨4937641303554933622226437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6583521738073244829635249 4937641303554933622226437)
        ·
          refine ⟨925807744416550054167457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4937641303554933622226437 925807744416550054167457)
          ·
            refine ⟨694355808312412540625593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 925807744416550054167457 694355808312412540625593)
            ·
              refine ⟨520766856234309405469195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694355808312412540625593 520766856234309405469195)
              ·
                refine ⟨781150284351464108203793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520766856234309405469195 781150284351464108203793)
                ·
                  refine ⟨585862713263598081152845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 781150284351464108203793 585862713263598081152845)
                  ·
                    refine ⟨219698517473849280432317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 585862713263598081152845 219698517473849280432317)
                    ·
                      refine ⟨82386944052693480162119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 219698517473849280432317 82386944052693480162119)
                      ·
                        rfl

theorem cell23_160448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_160448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160448 prefixEnd_160448 := by exact prefixLift 160448
  have htrace : WordTrace (prefixWord ++ tailWord_160448) baseStart_160448 baseEnd_160448 := by
    simpa [prefixWord, tailWord_160448, baseEnd_160448] using wordTrace_append hprefix tailTrace_160448
  have hstable : (prefixWord ++ tailWord_160448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160448).length < 2 ^ (prefixWord ++ tailWord_160448).sum := by decide
  have hdescent : baseEnd_160448 < baseStart_160448 := by decide
  rcases family_descends (prefixWord ++ tailWord_160448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160500 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_160500 : Nat := 118140960795 + 160500 * 2 ^ 59
def prefixEnd_160500 : Nat := 4983230072969 + 3 ^ 40 * 160500 * 2
def baseEnd_160500 : Nat := 82413645046727276711881

theorem tailTrace_160500 : CollatzResearch.WordTrace tailWord_160500 prefixEnd_160500 82413645046727276711881 := by
  unfold tailWord_160500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2926957959271693031395477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3902610612362257375193969 2926957959271693031395477)
  ·
    refine ⟨137201154340860610846663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2926957959271693031395477 137201154340860610846663)
    ·
      refine ⟨205801731511290916269995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137201154340860610846663 205801731511290916269995)
      ·
        refine ⟨308702597266936374404993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205801731511290916269995 308702597266936374404993)
        ·
          refine ⟨231526947950202280803745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308702597266936374404993 231526947950202280803745)
          ·
            refine ⟨173645210962651710602809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231526947950202280803745 173645210962651710602809)
            ·
              refine ⟨130233908221988782952107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173645210962651710602809 130233908221988782952107)
              ·
                refine ⟨195350862332983174428161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130233908221988782952107 195350862332983174428161)
                ·
                  refine ⟨146513146749737380821121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195350862332983174428161 146513146749737380821121)
                  ·
                    refine ⟨109884860062303035615841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146513146749737380821121 109884860062303035615841)
                    ·
                      refine ⟨82413645046727276711881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109884860062303035615841 82413645046727276711881)
                      ·
                        rfl

theorem cell23_160500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_160500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160500 prefixEnd_160500 := by exact prefixLift 160500
  have htrace : WordTrace (prefixWord ++ tailWord_160500) baseStart_160500 baseEnd_160500 := by
    simpa [prefixWord, tailWord_160500, baseEnd_160500] using wordTrace_append hprefix tailTrace_160500
  have hstable : (prefixWord ++ tailWord_160500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160500).length < 2 ^ (prefixWord ++ tailWord_160500).sum := by decide
  have hdescent : baseEnd_160500 < baseStart_160500 := by decide
  rcases family_descends (prefixWord ++ tailWord_160500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160608 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_160608 : Nat := 118140960795 + 160608 * 2 ^ 59
def prefixEnd_160608 : Nat := 4983230072969 + 3 ^ 40 * 160608 * 2
def baseEnd_160608 : Nat := 82469100957412854161383

theorem tailTrace_160608 : CollatzResearch.WordTrace tailWord_160608 prefixEnd_160608 82469100957412854161383 := by
  unfold tailWord_160608
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928927501076060253861239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3905236668101413671814985 2928927501076060253861239)
  ·
    refine ⟨4393391251614090380791859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2928927501076060253861239 4393391251614090380791859)
    ·
      refine ⟨6590086877421135571187789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4393391251614090380791859 6590086877421135571187789)
      ·
        refine ⟨2471282579032925839195421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6590086877421135571187789 2471282579032925839195421)
        ·
          refine ⟨926730967137347189698283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2471282579032925839195421 926730967137347189698283)
          ·
            refine ⟨1390096450706020784547425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926730967137347189698283 1390096450706020784547425)
            ·
              refine ⟨1042572338029515588410569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390096450706020784547425 1042572338029515588410569)
              ·
                refine ⟨781929253522136691307927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042572338029515588410569 781929253522136691307927)
                ·
                  refine ⟨1172893880283205036961891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781929253522136691307927 1172893880283205036961891)
                  ·
                    refine ⟨1759340820424807555442837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172893880283205036961891 1759340820424807555442837)
                    ·
                      refine ⟨82469100957412854161383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1759340820424807555442837 82469100957412854161383)
                      ·
                        rfl

theorem cell23_160608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_160608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160608 prefixEnd_160608 := by exact prefixLift 160608
  have htrace : WordTrace (prefixWord ++ tailWord_160608) baseStart_160608 baseEnd_160608 := by
    simpa [prefixWord, tailWord_160608, baseEnd_160608] using wordTrace_append hprefix tailTrace_160608
  have hstable : (prefixWord ++ tailWord_160608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160608).length < 2 ^ (prefixWord ++ tailWord_160608).sum := by decide
  have hdescent : baseEnd_160608 < baseStart_160608 := by decide
  rcases family_descends (prefixWord ++ tailWord_160608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160615 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_160615 : Nat := 118140960795 + 160615 * 2 ^ 59
def prefixEnd_160615 : Nat := 4983230072969 + 3 ^ 40 * 160615 * 2
def baseEnd_160615 : Nat := 82472695321994326773851

theorem tailTrace_160615 : CollatzResearch.WordTrace tailWord_160615 prefixEnd_160615 82472695321994326773851 := by
  unfold tailWord_160615
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858110313126760703227299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3905406875417840468818199 5858110313126760703227299)
  ·
    refine ⟨8787165469690141054840949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5858110313126760703227299 8787165469690141054840949)
    ·
      refine ⟨823796762783450723891339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8787165469690141054840949 823796762783450723891339)
      ·
        refine ⟨1235695144175176085837009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823796762783450723891339 1235695144175176085837009)
        ·
          refine ⟨926771358131382064377757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235695144175176085837009 926771358131382064377757)
          ·
            refine ⟨347539259299268274141659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 926771358131382064377757 347539259299268274141659)
            ·
              refine ⟨521308888948902411212489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347539259299268274141659 521308888948902411212489)
              ·
                refine ⟨390981666711676808409367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521308888948902411212489 390981666711676808409367)
                ·
                  refine ⟨586472500067515212614051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390981666711676808409367 586472500067515212614051)
                  ·
                    refine ⟨879708750101272818921077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586472500067515212614051 879708750101272818921077)
                    ·
                      refine ⟨82472695321994326773851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 879708750101272818921077 82472695321994326773851)
                      ·
                        rfl

theorem cell23_160615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_160615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160615 prefixEnd_160615 := by exact prefixLift 160615
  have htrace : WordTrace (prefixWord ++ tailWord_160615) baseStart_160615 baseEnd_160615 := by
    simpa [prefixWord, tailWord_160615, baseEnd_160615] using wordTrace_append hprefix tailTrace_160615
  have hstable : (prefixWord ++ tailWord_160615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160615).length < 2 ^ (prefixWord ++ tailWord_160615).sum := by decide
  have hdescent : baseEnd_160615 < baseStart_160615 := by decide
  rcases family_descends (prefixWord ++ tailWord_160615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160625 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_160625 : Nat := 118140960795 + 160625 * 2 ^ 59
def prefixEnd_160625 : Nat := 4983230072969 + 3 ^ 40 * 160625 * 2
def baseEnd_160625 : Nat := 82477830128539287648805

theorem tailTrace_160625 : CollatzResearch.WordTrace tailWord_160625 prefixEnd_160625 82477830128539287648805 := by
  unfold tailWord_160625
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858475043090532411091329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3905650028727021607394219 5858475043090532411091329)
  ·
    refine ⟨4393856282317899308318497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5858475043090532411091329 4393856282317899308318497)
    ·
      refine ⟨3295392211738424481238873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4393856282317899308318497 3295392211738424481238873)
      ·
        refine ⟨2471544158803818360929155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3295392211738424481238873 2471544158803818360929155)
        ·
          refine ⟨3707316238205727541393733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471544158803818360929155 3707316238205727541393733)
          ·
            refine ⟨695121794663573914011325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3707316238205727541393733 695121794663573914011325)
            ·
              refine ⟨260670672998840217754247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 695121794663573914011325 260670672998840217754247)
              ·
                refine ⟨391006009498260326631371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260670672998840217754247 391006009498260326631371)
                ·
                  refine ⟨586509014247390489947057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391006009498260326631371 586509014247390489947057)
                  ·
                    refine ⟨439881760685542867460293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586509014247390489947057 439881760685542867460293)
                    ·
                      refine ⟨82477830128539287648805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 439881760685542867460293 82477830128539287648805)
                      ·
                        rfl

theorem cell23_160625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_160625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160625 prefixEnd_160625 := by exact prefixLift 160625
  have htrace : WordTrace (prefixWord ++ tailWord_160625) baseStart_160625 baseEnd_160625 := by
    simpa [prefixWord, tailWord_160625, baseEnd_160625] using wordTrace_append hprefix tailTrace_160625
  have hstable : (prefixWord ++ tailWord_160625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160625).length < 2 ^ (prefixWord ++ tailWord_160625).sum := by decide
  have hdescent : baseEnd_160625 < baseStart_160625 := by decide
  rcases family_descends (prefixWord ++ tailWord_160625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160629 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_160629 : Nat := 118140960795 + 160629 * 2 ^ 59
def prefixEnd_160629 : Nat := 4983230072969 + 3 ^ 40 * 160629 * 2
def baseEnd_160629 : Nat := 82479884051157271998787

theorem tailTrace_160629 : CollatzResearch.WordTrace tailWord_160629 prefixEnd_160629 82479884051157271998787 := by
  unfold tailWord_160629
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858620935076041094236941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3905747290050694062824627 5858620935076041094236941)
  ·
    refine ⟨2196982850653515410338853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5858620935076041094236941 2196982850653515410338853)
    ·
      refine ⟨411934284497534139438535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2196982850653515410338853 411934284497534139438535)
      ·
        refine ⟨617901426746301209157803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411934284497534139438535 617901426746301209157803)
        ·
          refine ⟨926852140119451813736705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617901426746301209157803 926852140119451813736705)
          ·
            refine ⟨695139105089588860302529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926852140119451813736705 695139105089588860302529)
            ·
              refine ⟨521354328817191645226897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695139105089588860302529 521354328817191645226897)
              ·
                refine ⟨391015746612893733920173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521354328817191645226897 391015746612893733920173)
                ·
                  refine ⟨146630904979835150220065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391015746612893733920173 146630904979835150220065)
                  ·
                    refine ⟨109973178734876362665049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146630904979835150220065 109973178734876362665049)
                    ·
                      refine ⟨82479884051157271998787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 109973178734876362665049 82479884051157271998787)
                      ·
                        rfl

theorem cell23_160629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_160629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160629 prefixEnd_160629 := by exact prefixLift 160629
  have htrace : WordTrace (prefixWord ++ tailWord_160629) baseStart_160629 baseEnd_160629 := by
    simpa [prefixWord, tailWord_160629, baseEnd_160629] using wordTrace_append hprefix tailTrace_160629
  have hstable : (prefixWord ++ tailWord_160629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160629).length < 2 ^ (prefixWord ++ tailWord_160629).sum := by decide
  have hdescent : baseEnd_160629 < baseStart_160629 := by decide
  rcases family_descends (prefixWord ++ tailWord_160629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160689 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 3, 3, 2]
def baseStart_160689 : Nat := 118140960795 + 160689 * 2 ^ 59
def prefixEnd_160689 : Nat := 4983230072969 + 3 ^ 40 * 160689 * 2
def baseEnd_160689 : Nat := 82510692890427037248511

theorem tailTrace_160689 : CollatzResearch.WordTrace tailWord_160689 prefixEnd_160689 82510692890427037248511 := by
  unfold tailWord_160689
  simp only [CollatzResearch.WordTrace]
  refine ⟨5860809314858671341421121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3907206209905780894280747 5860809314858671341421121)
  ·
    refine ⟨4395606986144003506065841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5860809314858671341421121 4395606986144003506065841)
    ·
      refine ⟨3296705239608002629549381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4395606986144003506065841 3296705239608002629549381)
      ·
        refine ⟨618132232426500493040509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3296705239608002629549381 618132232426500493040509)
        ·
          refine ⟨231799587159937684890191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 618132232426500493040509 231799587159937684890191)
          ·
            refine ⟨347699380739906527335287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231799587159937684890191 347699380739906527335287)
            ·
              refine ⟨521549071109859791002931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347699380739906527335287 521549071109859791002931)
              ·
                refine ⟨782323606664789686504397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521549071109859791002931 782323606664789686504397)
                ·
                  refine ⟨293371352499296132439149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782323606664789686504397 293371352499296132439149)
                  ·
                    refine ⟨110014257187236049664681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293371352499296132439149 110014257187236049664681)
                    ·
                      refine ⟨82510692890427037248511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110014257187236049664681 82510692890427037248511)
                      ·
                        rfl

theorem cell23_160689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_160689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160689 prefixEnd_160689 := by exact prefixLift 160689
  have htrace : WordTrace (prefixWord ++ tailWord_160689) baseStart_160689 baseEnd_160689 := by
    simpa [prefixWord, tailWord_160689, baseEnd_160689] using wordTrace_append hprefix tailTrace_160689
  have hstable : (prefixWord ++ tailWord_160689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160689).length < 2 ^ (prefixWord ++ tailWord_160689).sum := by decide
  have hdescent : baseEnd_160689 < baseStart_160689 := by decide
  rcases family_descends (prefixWord ++ tailWord_160689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160719 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 2, 2, 2]
def baseStart_160719 : Nat := 118140960795 + 160719 * 2 ^ 59
def prefixEnd_160719 : Nat := 4983230072969 + 3 ^ 40 * 160719 * 2
def baseEnd_160719 : Nat := 82526097310061919873373

theorem tailTrace_160719 : CollatzResearch.WordTrace tailWord_160719 prefixEnd_160719 82526097310061919873373 := by
  unfold tailWord_160719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861903504749986465013211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3907935669833324310008807 5861903504749986465013211)
  ·
    refine ⟨8792855257124979697519817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5861903504749986465013211 8792855257124979697519817)
    ·
      refine ⟨6594641442843734773139863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8792855257124979697519817 6594641442843734773139863)
      ·
        refine ⟨9891962164265602159709795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594641442843734773139863 9891962164265602159709795)
        ·
          refine ⟨14837943246398403239564693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9891962164265602159709795 14837943246398403239564693)
          ·
            refine ⟨695528589674925151854595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14837943246398403239564693 695528589674925151854595)
            ·
              refine ⟨1043292884512387727781893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695528589674925151854595 1043292884512387727781893)
              ·
                refine ⟨195617415846072698959105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1043292884512387727781893 195617415846072698959105)
                ·
                  refine ⟨146713061884554524219329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195617415846072698959105 146713061884554524219329)
                  ·
                    refine ⟨110034796413415893164497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146713061884554524219329 110034796413415893164497)
                    ·
                      refine ⟨82526097310061919873373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110034796413415893164497 82526097310061919873373)
                      ·
                        rfl

theorem cell23_160719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 2, 2].length) (baseStart_160719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160719 prefixEnd_160719 := by exact prefixLift 160719
  have htrace : WordTrace (prefixWord ++ tailWord_160719) baseStart_160719 baseEnd_160719 := by
    simpa [prefixWord, tailWord_160719, baseEnd_160719] using wordTrace_append hprefix tailTrace_160719
  have hstable : (prefixWord ++ tailWord_160719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160719).length < 2 ^ (prefixWord ++ tailWord_160719).sum := by decide
  have hdescent : baseEnd_160719 < baseStart_160719 := by decide
  rcases family_descends (prefixWord ++ tailWord_160719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160722 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_160722 : Nat := 118140960795 + 160722 * 2 ^ 59
def prefixEnd_160722 : Nat := 4983230072969 + 3 ^ 40 * 160722 * 2
def baseEnd_160722 : Nat := 82527637752025408135859

theorem tailTrace_160722 : CollatzResearch.WordTrace tailWord_160722 prefixEnd_160722 82527637752025408135859 := by
  unfold tailWord_160722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1465503230934779494343105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3908008615826078651581613 1465503230934779494343105)
  ·
    refine ⟨1099127423201084620757329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1465503230934779494343105 1099127423201084620757329)
    ·
      refine ⟨824345567400813465567997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1099127423201084620757329 824345567400813465567997)
      ·
        refine ⟨309129587775305049587999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 824345567400813465567997 309129587775305049587999)
        ·
          refine ⟨463694381662957574381999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309129587775305049587999 463694381662957574381999)
          ·
            refine ⟨695541572494436361572999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463694381662957574381999 695541572494436361572999)
            ·
              refine ⟨1043312358741654542359499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695541572494436361572999 1043312358741654542359499)
              ·
                refine ⟨1564968538112481813539249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043312358741654542359499 1564968538112481813539249)
                ·
                  refine ⟨1173726403584361360154437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1564968538112481813539249 1173726403584361360154437)
                  ·
                    refine ⟨220073700672067755028957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173726403584361360154437 220073700672067755028957)
                    ·
                      refine ⟨82527637752025408135859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 220073700672067755028957 82527637752025408135859)
                      ·
                        rfl

theorem cell23_160722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_160722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160722 prefixEnd_160722 := by exact prefixLift 160722
  have htrace : WordTrace (prefixWord ++ tailWord_160722) baseStart_160722 baseEnd_160722 := by
    simpa [prefixWord, tailWord_160722, baseEnd_160722] using wordTrace_append hprefix tailTrace_160722
  have hstable : (prefixWord ++ tailWord_160722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160722).length < 2 ^ (prefixWord ++ tailWord_160722).sum := by decide
  have hdescent : baseEnd_160722 < baseStart_160722 := by decide
  rcases family_descends (prefixWord ++ tailWord_160722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160757 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_160757 : Nat := 118140960795 + 160757 * 2 ^ 59
def prefixEnd_160757 : Nat := 4983230072969 + 3 ^ 40 * 160757 * 2
def baseEnd_160757 : Nat := 82545609574932771198199

theorem tailTrace_160757 : CollatzResearch.WordTrace tailWord_160757 prefixEnd_160757 82545609574932771198199 := by
  unfold tailWord_160757
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863289478612318954896525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3908859652408212636597683 5863289478612318954896525)
  ·
    refine ⟨2198733554479619608086197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5863289478612318954896525 2198733554479619608086197)
    ·
      refine ⟨206131270732464338258081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2198733554479619608086197 206131270732464338258081)
      ·
        refine ⟨154598453049348253693561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206131270732464338258081 154598453049348253693561)
        ·
          refine ⟨115948839787011190270171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154598453049348253693561 115948839787011190270171)
          ·
            refine ⟨173923259680516785405257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115948839787011190270171 173923259680516785405257)
            ·
              refine ⟨130442444760387589053943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173923259680516785405257 130442444760387589053943)
              ·
                refine ⟨195663667140581383580915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130442444760387589053943 195663667140581383580915)
                ·
                  refine ⟨293495500710872075371373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195663667140581383580915 293495500710872075371373)
                  ·
                    refine ⟨110060812766577028264265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293495500710872075371373 110060812766577028264265)
                    ·
                      refine ⟨82545609574932771198199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110060812766577028264265 82545609574932771198199)
                      ·
                        rfl

theorem cell23_160757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_160757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160757 prefixEnd_160757 := by exact prefixLift 160757
  have htrace : WordTrace (prefixWord ++ tailWord_160757) baseStart_160757 baseEnd_160757 := by
    simpa [prefixWord, tailWord_160757, baseEnd_160757] using wordTrace_append hprefix tailTrace_160757
  have hstable : (prefixWord ++ tailWord_160757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160757).length < 2 ^ (prefixWord ++ tailWord_160757).sum := by decide
  have hdescent : baseEnd_160757 < baseStart_160757 := by decide
  rcases family_descends (prefixWord ++ tailWord_160757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160805 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_160805 : Nat := 118140960795 + 160805 * 2 ^ 59
def prefixEnd_160805 : Nat := 4983230072969 + 3 ^ 40 * 160805 * 2
def baseEnd_160805 : Nat := 82570256646348583397977

theorem tailTrace_160805 : CollatzResearch.WordTrace tailWord_160805 prefixEnd_160805 82570256646348583397977 := by
  unfold tailWord_160805
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865040182438423152643869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3910026788292282101762579 5865040182438423152643869)
  ·
    refine ⟨2199390068414408682241451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5865040182438423152643869 2199390068414408682241451)
    ·
      refine ⟨3299085102621613023362177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199390068414408682241451 3299085102621613023362177)
      ·
        refine ⟨2474313826966209767521633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3299085102621613023362177 2474313826966209767521633)
        ·
          refine ⟨1855735370224657325641225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2474313826966209767521633 1855735370224657325641225)
          ·
            refine ⟨1391801527668492994230919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1855735370224657325641225 1391801527668492994230919)
            ·
              refine ⟨2087702291502739491346379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391801527668492994230919 2087702291502739491346379)
              ·
                refine ⟨3131553437254109237019569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087702291502739491346379 3131553437254109237019569)
                ·
                  refine ⟨2348665077940581927764677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3131553437254109237019569 2348665077940581927764677)
                  ·
                    refine ⟨440374702113859111455877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2348665077940581927764677 440374702113859111455877)
                    ·
                      refine ⟨82570256646348583397977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 440374702113859111455877 82570256646348583397977)
                      ·
                        rfl

theorem cell23_160805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_160805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160805 prefixEnd_160805 := by exact prefixLift 160805
  have htrace : WordTrace (prefixWord ++ tailWord_160805) baseStart_160805 baseEnd_160805 := by
    simpa [prefixWord, tailWord_160805, baseEnd_160805] using wordTrace_append hprefix tailTrace_160805
  have hstable : (prefixWord ++ tailWord_160805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160805).length < 2 ^ (prefixWord ++ tailWord_160805).sum := by decide
  have hdescent : baseEnd_160805 < baseStart_160805 := by decide
  rcases family_descends (prefixWord ++ tailWord_160805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160812 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_160812 : Nat := 118140960795 + 160812 * 2 ^ 59
def prefixEnd_160812 : Nat := 4983230072969 + 3 ^ 40 * 160812 * 2
def baseEnd_160812 : Nat := 82573851010930056010445

theorem tailTrace_160812 : CollatzResearch.WordTrace tailWord_160812 prefixEnd_160812 82573851010930056010445 := by
  unfold tailWord_160812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932647746706531674074345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3910196995608708898765793 2932647746706531674074345)
  ·
    refine ⟨2199485810029898755555759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2932647746706531674074345 2199485810029898755555759)
    ·
      refine ⟨3299228715044848133333639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199485810029898755555759 3299228715044848133333639)
      ·
        refine ⟨4948843072567272200000459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299228715044848133333639 4948843072567272200000459)
        ·
          refine ⟨7423264608850908300000689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4948843072567272200000459 7423264608850908300000689)
          ·
            refine ⟨5567448456638181225000517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7423264608850908300000689 5567448456638181225000517)
            ·
              refine ⟨1043896585619658979687597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5567448456638181225000517 1043896585619658979687597)
              ·
                refine ⟨391461219607372117382849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1043896585619658979687597 391461219607372117382849)
                ·
                  refine ⟨293595914705529088037137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391461219607372117382849 293595914705529088037137)
                  ·
                    refine ⟨220196936029146816027853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 293595914705529088037137 220196936029146816027853)
                    ·
                      refine ⟨82573851010930056010445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 220196936029146816027853 82573851010930056010445)
                      ·
                        rfl

theorem cell23_160812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_160812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160812 prefixEnd_160812 := by exact prefixLift 160812
  have htrace : WordTrace (prefixWord ++ tailWord_160812) baseStart_160812 baseEnd_160812 := by
    simpa [prefixWord, tailWord_160812, baseEnd_160812] using wordTrace_append hprefix tailTrace_160812
  have hstable : (prefixWord ++ tailWord_160812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160812).length < 2 ^ (prefixWord ++ tailWord_160812).sum := by decide
  have hdescent : baseEnd_160812 < baseStart_160812 := by decide
  rcases family_descends (prefixWord ++ tailWord_160812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160829 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_160829 : Nat := 118140960795 + 160829 * 2 ^ 59
def prefixEnd_160829 : Nat := 4983230072969 + 3 ^ 40 * 160829 * 2
def baseEnd_160829 : Nat := 82582580182056489497867

theorem tailTrace_160829 : CollatzResearch.WordTrace tailWord_160829 prefixEnd_160829 82582580182056489497867 := by
  unfold tailWord_160829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865915534351475251517541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3910610356234316834345027 5865915534351475251517541)
  ·
    refine ⟨1099859162690901609659539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5865915534351475251517541 1099859162690901609659539)
    ·
      refine ⟨1649788744036352414489309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099859162690901609659539 1649788744036352414489309)
      ·
        refine ⟨618670779013632155433491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1649788744036352414489309 618670779013632155433491)
        ·
          refine ⟨928006168520448233150237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618670779013632155433491 928006168520448233150237)
          ·
            refine ⟨348002313195168087431339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 928006168520448233150237 348002313195168087431339)
            ·
              refine ⟨522003469792752131147009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348002313195168087431339 522003469792752131147009)
              ·
                refine ⟨391502602344564098360257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522003469792752131147009 391502602344564098360257)
                ·
                  refine ⟨293626951758423073770193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391502602344564098360257 293626951758423073770193)
                  ·
                    refine ⟨220220213818817305327645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 293626951758423073770193 220220213818817305327645)
                    ·
                      refine ⟨82582580182056489497867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 220220213818817305327645 82582580182056489497867)
                      ·
                        rfl

theorem cell23_160829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_160829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160829 prefixEnd_160829 := by exact prefixLift 160829
  have htrace : WordTrace (prefixWord ++ tailWord_160829) baseStart_160829 baseEnd_160829 := by
    simpa [prefixWord, tailWord_160829, baseEnd_160829] using wordTrace_append hprefix tailTrace_160829
  have hstable : (prefixWord ++ tailWord_160829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160829).length < 2 ^ (prefixWord ++ tailWord_160829).sum := by decide
  have hdescent : baseEnd_160829 < baseStart_160829 := by decide
  rcases family_descends (prefixWord ++ tailWord_160829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160876 : List Nat := [2, 2, 1, 1, 3, 2, 2, 5, 1, 1, 3]
def baseStart_160876 : Nat := 118140960795 + 160876 * 2 ^ 59
def prefixEnd_160876 : Nat := 4983230072969 + 3 ^ 40 * 160876 * 2
def baseEnd_160876 : Nat := 82606713772817805610151

theorem tailTrace_160876 : CollatzResearch.WordTrace tailWord_160876 prefixEnd_160876 82606713772817805610151 := by
  unfold tailWord_160876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933814882590601139239241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3911753176787468185652321 2933814882590601139239241)
  ·
    refine ⟨2200361161942950854429431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2933814882590601139239241 2200361161942950854429431)
    ·
      refine ⟨3300541742914426281644147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200361161942950854429431 3300541742914426281644147)
      ·
        refine ⟨4950812614371639422466221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300541742914426281644147 4950812614371639422466221)
        ·
          refine ⟨1856554730389364783424833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4950812614371639422466221 1856554730389364783424833)
          ·
            refine ⟨1392416047792023587568625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1856554730389364783424833 1392416047792023587568625)
            ·
              refine ⟨1044312035844017690676469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392416047792023587568625 1044312035844017690676469)
              ·
                refine ⟨97904253360376658500919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1044312035844017690676469 97904253360376658500919)
                ·
                  refine ⟨146856380040564987751379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97904253360376658500919 146856380040564987751379)
                  ·
                    refine ⟨220284570060847481627069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146856380040564987751379 220284570060847481627069)
                    ·
                      refine ⟨82606713772817805610151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 220284570060847481627069 82606713772817805610151)
                      ·
                        rfl

theorem cell23_160876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_160876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160876 prefixEnd_160876 := by exact prefixLift 160876
  have htrace : WordTrace (prefixWord ++ tailWord_160876) baseStart_160876 baseEnd_160876 := by
    simpa [prefixWord, tailWord_160876, baseEnd_160876] using wordTrace_append hprefix tailTrace_160876
  have hstable : (prefixWord ++ tailWord_160876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160876).length < 2 ^ (prefixWord ++ tailWord_160876).sum := by decide
  have hdescent : baseEnd_160876 < baseStart_160876 := by decide
  rcases family_descends (prefixWord ++ tailWord_160876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160879 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 1, 5]
def baseStart_160879 : Nat := 118140960795 + 160879 * 2 ^ 59
def prefixEnd_160879 : Nat := 4983230072969 + 3 ^ 40 * 160879 * 2
def baseEnd_160879 : Nat := 27536084738260431290879

theorem tailTrace_160879 : CollatzResearch.WordTrace tailWord_160879 prefixEnd_160879 27536084738260431290879 := by
  unfold tailWord_160879
  simp only [CollatzResearch.WordTrace]
  refine ⟨5867739184170333790837691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3911826122780222527225127 5867739184170333790837691)
  ·
    refine ⟨8801608776255500686256537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5867739184170333790837691 8801608776255500686256537)
    ·
      refine ⟨6601206582191625514692403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8801608776255500686256537 6601206582191625514692403)
      ·
        refine ⟨9901809873287438272038605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601206582191625514692403 9901809873287438272038605)
        ·
          refine ⟨3713178702482789352014477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9901809873287438272038605 3713178702482789352014477)
          ·
            refine ⟨1392442013431046007005429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3713178702482789352014477 1392442013431046007005429)
            ·
              refine ⟨130541438759160563156759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1392442013431046007005429 130541438759160563156759)
              ·
                refine ⟨195812158138740844735139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130541438759160563156759 195812158138740844735139)
                ·
                  refine ⟨293718237208111267102709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195812158138740844735139 293718237208111267102709)
                  ·
                    refine ⟨27536084738260431290879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 293718237208111267102709 27536084738260431290879)
                    ·
                      rfl

theorem cell23_160879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 5].length) (baseStart_160879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160879 prefixEnd_160879 := by exact prefixLift 160879
  have htrace : WordTrace (prefixWord ++ tailWord_160879) baseStart_160879 baseEnd_160879 := by
    simpa [prefixWord, tailWord_160879, baseEnd_160879] using wordTrace_append hprefix tailTrace_160879
  have hstable : (prefixWord ++ tailWord_160879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160879).length < 2 ^ (prefixWord ++ tailWord_160879).sum := by decide
  have hdescent : baseEnd_160879 < baseStart_160879 := by decide
  rcases family_descends (prefixWord ++ tailWord_160879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160886 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_160886 : Nat := 118140960795 + 160886 * 2 ^ 59
def prefixEnd_160886 : Nat := 4983230072969 + 3 ^ 40 * 160886 * 2
def baseEnd_160886 : Nat := 82611848579362766485105

theorem tailTrace_160886 : CollatzResearch.WordTrace tailWord_160886 prefixEnd_160886 82611848579362766485105 := by
  unfold tailWord_160886
  simp only [CollatzResearch.WordTrace]
  refine ⟨366749655946560874146407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3911996330096649324228341 366749655946560874146407)
  ·
    refine ⟨550124483919841311219611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 366749655946560874146407 550124483919841311219611)
    ·
      refine ⟨825186725879761966829417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550124483919841311219611 825186725879761966829417)
      ·
        refine ⟨618890044409821475122063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 825186725879761966829417 618890044409821475122063)
        ·
          refine ⟨928335066614732212683095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618890044409821475122063 928335066614732212683095)
          ·
            refine ⟨1392502599922098319024643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928335066614732212683095 1392502599922098319024643)
            ·
              refine ⟨2088753899883147478536965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392502599922098319024643 2088753899883147478536965)
              ·
                refine ⟨391641356228090152225681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2088753899883147478536965 391641356228090152225681)
                ·
                  refine ⟨293731017171067614169261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391641356228090152225681 293731017171067614169261)
                  ·
                    refine ⟨110149131439150355313473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293731017171067614169261 110149131439150355313473)
                    ·
                      refine ⟨82611848579362766485105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110149131439150355313473 82611848579362766485105)
                      ·
                        rfl

theorem cell23_160886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_160886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160886 prefixEnd_160886 := by exact prefixLift 160886
  have htrace : WordTrace (prefixWord ++ tailWord_160886) baseStart_160886 baseEnd_160886 := by
    simpa [prefixWord, tailWord_160886, baseEnd_160886] using wordTrace_append hprefix tailTrace_160886
  have hstable : (prefixWord ++ tailWord_160886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160886).length < 2 ^ (prefixWord ++ tailWord_160886).sum := by decide
  have hdescent : baseEnd_160886 < baseStart_160886 := by decide
  rcases family_descends (prefixWord ++ tailWord_160886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160919 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_160919 : Nat := 118140960795 + 160919 * 2 ^ 59
def prefixEnd_160919 : Nat := 4983230072969 + 3 ^ 40 * 160919 * 2
def baseEnd_160919 : Nat := 82628793440961137372453

theorem tailTrace_160919 : CollatzResearch.WordTrace tailWord_160919 prefixEnd_160919 82628793440961137372453 := by
  unfold tailWord_160919
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869198104025420622293811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3912798736016947081529207 5869198104025420622293811)
  ·
    refine ⟨8803797156038130933440717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5869198104025420622293811 8803797156038130933440717)
    ·
      refine ⟨3301423933514299100040269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8803797156038130933440717 3301423933514299100040269)
      ·
        refine ⟨1238033975067862162515101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3301423933514299100040269 1238033975067862162515101)
        ·
          refine ⟨464262740650448310943163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1238033975067862162515101 464262740650448310943163)
          ·
            refine ⟨696394110975672466414745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464262740650448310943163 696394110975672466414745)
            ·
              refine ⟨522295583231754349811059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696394110975672466414745 522295583231754349811059)
              ·
                refine ⟨783443374847631524716589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522295583231754349811059 783443374847631524716589)
                ·
                  refine ⟨293791265567861821768721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783443374847631524716589 293791265567861821768721)
                  ·
                    refine ⟨220343449175896366326541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 293791265567861821768721 220343449175896366326541)
                    ·
                      refine ⟨82628793440961137372453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 220343449175896366326541 82628793440961137372453)
                      ·
                        rfl

theorem cell23_160919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_160919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160919 prefixEnd_160919 := by exact prefixLift 160919
  have htrace : WordTrace (prefixWord ++ tailWord_160919) baseStart_160919 baseEnd_160919 := by
    simpa [prefixWord, tailWord_160919, baseEnd_160919] using wordTrace_append hprefix tailTrace_160919
  have hstable : (prefixWord ++ tailWord_160919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160919).length < 2 ^ (prefixWord ++ tailWord_160919).sum := by decide
  have hdescent : baseEnd_160919 < baseStart_160919 := by decide
  rcases family_descends (prefixWord ++ tailWord_160919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160930 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_160930 : Nat := 118140960795 + 160930 * 2 ^ 59
def prefixEnd_160930 : Nat := 4983230072969 + 3 ^ 40 * 160930 * 2
def baseEnd_160930 : Nat := 27544813909386864778301

theorem tailTrace_160930 : CollatzResearch.WordTrace tailWord_160930 prefixEnd_160930 27544813909386864778301 := by
  unfold tailWord_160930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467399826746392375236061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3913066204657046333962829 1467399826746392375236061)
  ·
    refine ⟨550274935029897140713523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1467399826746392375236061 550274935029897140713523)
    ·
      refine ⟨825412402544845711070285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550274935029897140713523 825412402544845711070285)
      ·
        refine ⟨309529650954317141651357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 825412402544845711070285 309529650954317141651357)
        ·
          refine ⟨116073619107868928119259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309529650954317141651357 116073619107868928119259)
          ·
            refine ⟨174110428661803392178889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116073619107868928119259 174110428661803392178889)
            ·
              refine ⟨130582821496352544134167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174110428661803392178889 130582821496352544134167)
              ·
                refine ⟨195874232244528816201251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130582821496352544134167 195874232244528816201251)
                ·
                  refine ⟨293811348366793224301877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195874232244528816201251 293811348366793224301877)
                  ·
                    refine ⟨27544813909386864778301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 293811348366793224301877 27544813909386864778301)
                    ·
                      rfl

theorem cell23_160930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_160930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160930 prefixEnd_160930 := by exact prefixLift 160930
  have htrace : WordTrace (prefixWord ++ tailWord_160930) baseStart_160930 baseEnd_160930 := by
    simpa [prefixWord, tailWord_160930, baseEnd_160930] using wordTrace_append hprefix tailTrace_160930
  have hstable : (prefixWord ++ tailWord_160930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160930).length < 2 ^ (prefixWord ++ tailWord_160930).sum := by decide
  have hdescent : baseEnd_160930 < baseStart_160930 := by decide
  rcases family_descends (prefixWord ++ tailWord_160930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160933 : List Nat := [1, 3, 1, 2, 1, 4, 1, 5, 1, 2, 2]
def baseStart_160933 : Nat := 118140960795 + 160933 * 2 ^ 59
def prefixEnd_160933 : Nat := 4983230072969 + 3 ^ 40 * 160933 * 2
def baseEnd_160933 : Nat := 82635982170124082597389

theorem tailTrace_160933 : CollatzResearch.WordTrace tailWord_160933 prefixEnd_160933 82635982170124082597389 := by
  unfold tailWord_160933
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869708725974701013303453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3913139150649800675535635 5869708725974701013303453)
  ·
    refine ⟨2201140772240512879988795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5869708725974701013303453 2201140772240512879988795)
    ·
      refine ⟨3301711158360769319983193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201140772240512879988795 3301711158360769319983193)
      ·
        refine ⟨2476283368770576989987395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3301711158360769319983193 2476283368770576989987395)
        ·
          refine ⟨3714425053155865484981093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476283368770576989987395 3714425053155865484981093)
          ·
            refine ⟨696454697466724778433955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3714425053155865484981093 696454697466724778433955)
            ·
              refine ⟨1044682046200087167650933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696454697466724778433955 1044682046200087167650933)
              ·
                refine ⟨97938941831258171967275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1044682046200087167650933 97938941831258171967275)
                ·
                  refine ⟨146908412746887257950913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97938941831258171967275 146908412746887257950913)
                  ·
                    refine ⟨110181309560165443463185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146908412746887257950913 110181309560165443463185)
                    ·
                      refine ⟨82635982170124082597389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110181309560165443463185 82635982170124082597389)
                      ·
                        rfl

theorem cell23_160933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_160933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160933 prefixEnd_160933 := by exact prefixLift 160933
  have htrace : WordTrace (prefixWord ++ tailWord_160933) baseStart_160933 baseEnd_160933 := by
    simpa [prefixWord, tailWord_160933, baseEnd_160933] using wordTrace_append hprefix tailTrace_160933
  have hstable : (prefixWord ++ tailWord_160933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160933).length < 2 ^ (prefixWord ++ tailWord_160933).sum := by decide
  have hdescent : baseEnd_160933 < baseStart_160933 := by decide
  rcases family_descends (prefixWord ++ tailWord_160933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160959 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 5, 3, 2]
def baseStart_160959 : Nat := 118140960795 + 160959 * 2 ^ 59
def prefixEnd_160959 : Nat := 4983230072969 + 3 ^ 40 * 160959 * 2
def baseEnd_160959 : Nat := 82649332667140980872269

theorem tailTrace_160959 : CollatzResearch.WordTrace tailWord_160959 prefixEnd_160959 82649332667140980872269 := by
  unfold tailWord_160959
  simp only [CollatzResearch.WordTrace]
  refine ⟨5870657023880507453749931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3913771349253671635833287 5870657023880507453749931)
  ·
    refine ⟨8805985535820761180624897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5870657023880507453749931 8805985535820761180624897)
    ·
      refine ⟨6604489151865570885468673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8805985535820761180624897 6604489151865570885468673)
      ·
        refine ⟨4953366863899178164101505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6604489151865570885468673 4953366863899178164101505)
        ·
          refine ⟨3715025147924383623076129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4953366863899178164101505 3715025147924383623076129)
          ·
            refine ⟨2786268860943287717307097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3715025147924383623076129 2786268860943287717307097)
            ·
              refine ⟨2089701645707465787980323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786268860943287717307097 2089701645707465787980323)
              ·
                refine ⟨3134552468561198681970485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089701645707465787980323 3134552468561198681970485)
                ·
                  refine ⟨293864293927612376434733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3134552468561198681970485 293864293927612376434733)
                  ·
                    refine ⟨110199110222854641163025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 293864293927612376434733 110199110222854641163025)
                    ·
                      refine ⟨82649332667140980872269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110199110222854641163025 82649332667140980872269)
                      ·
                        rfl

theorem cell23_160959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_160959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160959 prefixEnd_160959 := by exact prefixLift 160959
  have htrace : WordTrace (prefixWord ++ tailWord_160959) baseStart_160959 baseEnd_160959 := by
    simpa [prefixWord, tailWord_160959, baseEnd_160959] using wordTrace_append hprefix tailTrace_160959
  have hstable : (prefixWord ++ tailWord_160959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160959).length < 2 ^ (prefixWord ++ tailWord_160959).sum := by decide
  have hdescent : baseEnd_160959 < baseStart_160959 := by decide
  rcases family_descends (prefixWord ++ tailWord_160959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160992 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_160992 : Nat := 118140960795 + 160992 * 2 ^ 59
def prefixEnd_160992 : Nat := 4983230072969 + 3 ^ 40 * 160992 * 2
def baseEnd_160992 : Nat := 82666277528739351759617

theorem tailTrace_160992 : CollatzResearch.WordTrace tailWord_160992 prefixEnd_160992 82666277528739351759617 := by
  unfold tailWord_160992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935930316380477044850615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3914573755173969393134153 2935930316380477044850615)
  ·
    refine ⟨4403895474570715567275923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2935930316380477044850615 4403895474570715567275923)
    ·
      refine ⟨6605843211856073350913885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4403895474570715567275923 6605843211856073350913885)
      ·
        refine ⟨2477191204446027506592707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6605843211856073350913885 2477191204446027506592707)
        ·
          refine ⟨3715786806669041259889061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477191204446027506592707 3715786806669041259889061)
          ·
            refine ⟨696710026250445236229199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3715786806669041259889061 696710026250445236229199)
            ·
              refine ⟨1045065039375667854343799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696710026250445236229199 1045065039375667854343799)
              ·
                refine ⟨1567597559063501781515699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045065039375667854343799 1567597559063501781515699)
                ·
                  refine ⟨2351396338595252672273549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567597559063501781515699 2351396338595252672273549)
                  ·
                    refine ⟨881773626973219752102581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351396338595252672273549 881773626973219752102581)
                    ·
                      refine ⟨82666277528739351759617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 881773626973219752102581 82666277528739351759617)
                      ·
                        rfl

theorem cell23_160992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_160992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_160992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_160992 prefixEnd_160992 := by exact prefixLift 160992
  have htrace : WordTrace (prefixWord ++ tailWord_160992) baseStart_160992 baseEnd_160992 := by
    simpa [prefixWord, tailWord_160992, baseEnd_160992] using wordTrace_append hprefix tailTrace_160992
  have hstable : (prefixWord ++ tailWord_160992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160992).length < 2 ^ (prefixWord ++ tailWord_160992).sum := by decide
  have hdescent : baseEnd_160992 < baseStart_160992 := by decide
  rcases family_descends (prefixWord ++ tailWord_160992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161023 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 2, 2, 2]
def baseStart_161023 : Nat := 118140960795 + 161023 * 2 ^ 59
def prefixEnd_161023 : Nat := 4983230072969 + 3 ^ 40 * 161023 * 2
def baseEnd_161023 : Nat := 82682195429028730471975

theorem tailTrace_161023 : CollatzResearch.WordTrace tailWord_161023 prefixEnd_161023 82682195429028730471975 := by
  unfold tailWord_161023
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872991295648646384079723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3915327530432430922719815 5872991295648646384079723)
  ·
    refine ⟨8809486943472969576119585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5872991295648646384079723 8809486943472969576119585)
    ·
      refine ⟨6607115207604727182089689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8809486943472969576119585 6607115207604727182089689)
      ·
        refine ⟨4955336405703545386567267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6607115207604727182089689 4955336405703545386567267)
        ·
          refine ⟨7433004608555318079850901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955336405703545386567267 7433004608555318079850901)
          ·
            refine ⟨348422091026030534993011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7433004608555318079850901 348422091026030534993011)
            ·
              refine ⟨522633136539045802489517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348422091026030534993011 522633136539045802489517)
              ·
                refine ⟨195987426202142175933569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 522633136539045802489517 195987426202142175933569)
                ·
                  refine ⟨146990569651606631950177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195987426202142175933569 146990569651606631950177)
                  ·
                    refine ⟨110242927238704973962633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146990569651606631950177 110242927238704973962633)
                    ·
                      refine ⟨82682195429028730471975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110242927238704973962633 82682195429028730471975)
                      ·
                        rfl

theorem cell23_161023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_161023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161023 prefixEnd_161023 := by exact prefixLift 161023
  have htrace : WordTrace (prefixWord ++ tailWord_161023) baseStart_161023 baseEnd_161023 := by
    simpa [prefixWord, tailWord_161023, baseEnd_161023] using wordTrace_append hprefix tailTrace_161023
  have hstable : (prefixWord ++ tailWord_161023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161023).length < 2 ^ (prefixWord ++ tailWord_161023).sum := by decide
  have hdescent : baseEnd_161023 < baseStart_161023 := by decide
  rcases family_descends (prefixWord ++ tailWord_161023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161049 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 6, 5, 2]
def baseStart_161049 : Nat := 118140960795 + 161049 * 2 ^ 59
def prefixEnd_161049 : Nat := 4983230072969 + 3 ^ 40 * 161049 * 2
def baseEnd_161049 : Nat := 82695545926045628746855

theorem tailTrace_161049 : CollatzResearch.WordTrace tailWord_161049 prefixEnd_161049 82695545926045628746855 := by
  unfold tailWord_161049
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873939593554452824526201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3915959729036301883017467 5873939593554452824526201)
  ·
    refine ⟨4405454695165839618394651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5873939593554452824526201 4405454695165839618394651)
    ·
      refine ⟨6608182042748759427591977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4405454695165839618394651 6608182042748759427591977)
      ·
        refine ⟨4956136532061569570693983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6608182042748759427591977 4956136532061569570693983)
        ·
          refine ⟨7434204798092354356040975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956136532061569570693983 7434204798092354356040975)
          ·
            refine ⟨11151307197138531534061463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434204798092354356040975 11151307197138531534061463)
            ·
              refine ⟨16726960795707797301092195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11151307197138531534061463 16726960795707797301092195)
              ·
                refine ⟨25090441193561695951638293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16726960795707797301092195 25090441193561695951638293)
                ·
                  refine ⟨1176114430948204497733045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25090441193561695951638293 1176114430948204497733045)
                  ·
                    refine ⟨110260727901394171662473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1176114430948204497733045 110260727901394171662473)
                    ·
                      refine ⟨82695545926045628746855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110260727901394171662473 82695545926045628746855)
                      ·
                        rfl

theorem cell23_161049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_161049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161049 prefixEnd_161049 := by exact prefixLift 161049
  have htrace : WordTrace (prefixWord ++ tailWord_161049) baseStart_161049 baseEnd_161049 := by
    simpa [prefixWord, tailWord_161049, baseEnd_161049] using wordTrace_append hprefix tailTrace_161049
  have hstable : (prefixWord ++ tailWord_161049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161049).length < 2 ^ (prefixWord ++ tailWord_161049).sum := by decide
  have hdescent : baseEnd_161049 < baseStart_161049 := by decide
  rcases family_descends (prefixWord ++ tailWord_161049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161059 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 2, 5]
def baseStart_161059 : Nat := 118140960795 + 161059 * 2 ^ 59
def prefixEnd_161059 : Nat := 4983230072969 + 3 ^ 40 * 161059 * 2
def baseEnd_161059 : Nat := 27566893577530196540603

theorem tailTrace_161059 : CollatzResearch.WordTrace tailWord_161059 prefixEnd_161059 27566893577530196540603 := by
  unfold tailWord_161059
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874304323518224532390231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3916202882345483021593487 5874304323518224532390231)
  ·
    refine ⟨8811456485277336798585347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5874304323518224532390231 8811456485277336798585347)
    ·
      refine ⟨13217184727916005197878021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8811456485277336798585347 13217184727916005197878021)
      ·
        refine ⟨2478222136484250974602129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13217184727916005197878021 2478222136484250974602129)
        ·
          refine ⟨1858666602363188230951597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2478222136484250974602129 1858666602363188230951597)
          ·
            refine ⟨696999975886195586606849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1858666602363188230951597 696999975886195586606849)
            ·
              refine ⟨522749981914646689955137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696999975886195586606849 522749981914646689955137)
              ·
                refine ⟨392062486435985017466353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522749981914646689955137 392062486435985017466353)
                ·
                  refine ⟨294046864826988763099765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392062486435985017466353 294046864826988763099765)
                  ·
                    refine ⟨27566893577530196540603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 294046864826988763099765 27566893577530196540603)
                    ·
                      rfl

theorem cell23_161059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 5].length) (baseStart_161059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161059 prefixEnd_161059 := by exact prefixLift 161059
  have htrace : WordTrace (prefixWord ++ tailWord_161059) baseStart_161059 baseEnd_161059 := by
    simpa [prefixWord, tailWord_161059, baseEnd_161059] using wordTrace_append hprefix tailTrace_161059
  have hstable : (prefixWord ++ tailWord_161059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161059).length < 2 ^ (prefixWord ++ tailWord_161059).sum := by decide
  have hdescent : baseEnd_161059 < baseStart_161059 := by decide
  rcases family_descends (prefixWord ++ tailWord_161059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161109 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_161109 : Nat := 118140960795 + 161109 * 2 ^ 59
def prefixEnd_161109 : Nat := 4983230072969 + 3 ^ 40 * 161109 * 2
def baseEnd_161109 : Nat := 82726354765315393996579

theorem tailTrace_161109 : CollatzResearch.WordTrace tailWord_161109 prefixEnd_161109 82726354765315393996579 := by
  unfold tailWord_161109
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876127973337083071710381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3917418648891388714473587 5876127973337083071710381)
  ·
    refine ⟨2203547990001406151891393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5876127973337083071710381 2203547990001406151891393)
    ·
      refine ⟨1652660992501054613918545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2203547990001406151891393 1652660992501054613918545)
      ·
        refine ⟨1239495744375790960438909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652660992501054613918545 1239495744375790960438909)
        ·
          refine ⟨464810904140921610164591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1239495744375790960438909 464810904140921610164591)
          ·
            refine ⟨697216356211382415246887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464810904140921610164591 697216356211382415246887)
            ·
              refine ⟨1045824534317073622870331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697216356211382415246887 1045824534317073622870331)
              ·
                refine ⟨1568736801475610434305497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045824534317073622870331 1568736801475610434305497)
                ·
                  refine ⟨1176552601106707825729123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1568736801475610434305497 1176552601106707825729123)
                  ·
                    refine ⟨1764828901660061738593685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1176552601106707825729123 1764828901660061738593685)
                    ·
                      refine ⟨82726354765315393996579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1764828901660061738593685 82726354765315393996579)
                      ·
                        rfl

theorem cell23_161109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_161109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161109 prefixEnd_161109 := by exact prefixLift 161109
  have htrace : WordTrace (prefixWord ++ tailWord_161109) baseStart_161109 baseEnd_161109 := by
    simpa [prefixWord, tailWord_161109, baseEnd_161109] using wordTrace_append hprefix tailTrace_161109
  have hstable : (prefixWord ++ tailWord_161109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161109).length < 2 ^ (prefixWord ++ tailWord_161109).sum := by decide
  have hdescent : baseEnd_161109 < baseStart_161109 := by decide
  rcases family_descends (prefixWord ++ tailWord_161109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161123 : List Nat := [1, 1, 1, 5, 2, 2, 2, 4, 1, 4]
def baseStart_161123 : Nat := 118140960795 + 161123 * 2 ^ 59
def prefixEnd_161123 : Nat := 4983230072969 + 3 ^ 40 * 161123 * 2
def baseEnd_161123 : Nat := 27577847831492779740505

theorem tailTrace_161123 : CollatzResearch.WordTrace tailWord_161123 prefixEnd_161123 27577847831492779740505 := by
  unfold tailWord_161123
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876638595286363462720023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3917759063524242308480015 5876638595286363462720023)
  ·
    refine ⟨8814957892929545194080035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5876638595286363462720023 8814957892929545194080035)
    ·
      refine ⟨13222436839394317791120053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8814957892929545194080035 13222436839394317791120053)
      ·
        refine ⟨1239603453693217292917505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13222436839394317791120053 1239603453693217292917505)
        ·
          refine ⟨929702590269912969688129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239603453693217292917505 929702590269912969688129)
          ·
            refine ⟨697276942702434727266097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929702590269912969688129 697276942702434727266097)
            ·
              refine ⟨522957707026826045449573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697276942702434727266097 522957707026826045449573)
              ·
                refine ⟨98054570067529883521795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 522957707026826045449573 98054570067529883521795)
                ·
                  refine ⟨147081855101294825282693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98054570067529883521795 147081855101294825282693)
                  ·
                    refine ⟨27577847831492779740505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147081855101294825282693 27577847831492779740505)
                    ·
                      rfl

theorem cell23_161123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 4].length) (baseStart_161123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161123 prefixEnd_161123 := by exact prefixLift 161123
  have htrace : WordTrace (prefixWord ++ tailWord_161123) baseStart_161123 baseEnd_161123 := by
    simpa [prefixWord, tailWord_161123, baseEnd_161123] using wordTrace_append hprefix tailTrace_161123
  have hstable : (prefixWord ++ tailWord_161123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161123).length < 2 ^ (prefixWord ++ tailWord_161123).sum := by decide
  have hdescent : baseEnd_161123 < baseStart_161123 := by decide
  rcases family_descends (prefixWord ++ tailWord_161123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161136 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 6]
def baseStart_161136 : Nat := 118140960795 + 161136 * 2 ^ 59
def prefixEnd_161136 : Nat := 4983230072969 + 3 ^ 40 * 161136 * 2
def baseEnd_161136 : Nat := 9193357638109643150995

theorem tailTrace_161136 : CollatzResearch.WordTrace tailWord_161136 prefixEnd_161136 9193357638109643150995 := by
  unfold tailWord_161136
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938556372119633341471631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3918075162826177788628841 2938556372119633341471631)
  ·
    refine ⟨4407834558179450012207447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2938556372119633341471631 4407834558179450012207447)
    ·
      refine ⟨6611751837269175018311171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407834558179450012207447 6611751837269175018311171)
      ·
        refine ⟨9917627755903762527466757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6611751837269175018311171 9917627755903762527466757)
        ·
          refine ⟨1859555204231955473900017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9917627755903762527466757 1859555204231955473900017)
          ·
            refine ⟨1394666403173966605425013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1859555204231955473900017 1394666403173966605425013)
            ·
              refine ⟨130749975297559369258595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1394666403173966605425013 130749975297559369258595)
              ·
                refine ⟨196124962946339053887893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130749975297559369258595 196124962946339053887893)
                ·
                  refine ⟨9193357638109643150995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 196124962946339053887893 9193357638109643150995)
                  ·
                    rfl

theorem cell23_161136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 6].length) (baseStart_161136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161136 prefixEnd_161136 := by exact prefixLift 161136
  have htrace : WordTrace (prefixWord ++ tailWord_161136) baseStart_161136 baseEnd_161136 := by
    simpa [prefixWord, tailWord_161136, baseEnd_161136] using wordTrace_append hprefix tailTrace_161136
  have hstable : (prefixWord ++ tailWord_161136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161136).length < 2 ^ (prefixWord ++ tailWord_161136).sum := by decide
  have hdescent : baseEnd_161136 < baseStart_161136 := by decide
  rcases family_descends (prefixWord ++ tailWord_161136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161189 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_161189 : Nat := 118140960795 + 161189 * 2 ^ 59
def prefixEnd_161189 : Nat := 4983230072969 + 3 ^ 40 * 161189 * 2
def baseEnd_161189 : Nat := 82767433217675080996211

theorem tailTrace_161189 : CollatzResearch.WordTrace tailWord_161189 prefixEnd_161189 82767433217675080996211 := by
  unfold tailWord_161189
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879045813047256734622621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3919363875364837823081747 5879045813047256734622621)
  ·
    refine ⟨2204642179892721275483483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5879045813047256734622621 2204642179892721275483483)
    ·
      refine ⟨3306963269839081913225225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2204642179892721275483483 3306963269839081913225225)
      ·
        refine ⟨2480222452379311434918919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3306963269839081913225225 2480222452379311434918919)
        ·
          refine ⟨3720333678568967152378379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480222452379311434918919 3720333678568967152378379)
          ·
            refine ⟨5580500517853450728567569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720333678568967152378379 5580500517853450728567569)
            ·
              refine ⟨4185375388390088046425677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5580500517853450728567569 4185375388390088046425677)
              ·
                refine ⟨1569515770646283017409629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4185375388390088046425677 1569515770646283017409629)
                ·
                  refine ⟨588568413992356131528611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1569515770646283017409629 588568413992356131528611)
                  ·
                    refine ⟨882852620988534197292917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 588568413992356131528611 882852620988534197292917)
                    ·
                      refine ⟨82767433217675080996211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 882852620988534197292917 82767433217675080996211)
                      ·
                        rfl

theorem cell23_161189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_161189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161189 prefixEnd_161189 := by exact prefixLift 161189
  have htrace : WordTrace (prefixWord ++ tailWord_161189) baseStart_161189 baseEnd_161189 := by
    simpa [prefixWord, tailWord_161189, baseEnd_161189] using wordTrace_append hprefix tailTrace_161189
  have hstable : (prefixWord ++ tailWord_161189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161189).length < 2 ^ (prefixWord ++ tailWord_161189).sum := by decide
  have hdescent : baseEnd_161189 < baseStart_161189 := by decide
  rcases family_descends (prefixWord ++ tailWord_161189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161199 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_161199 : Nat := 118140960795 + 161199 * 2 ^ 59
def prefixEnd_161199 : Nat := 4983230072969 + 3 ^ 40 * 161199 * 2
def baseEnd_161199 : Nat := 82772568024220041871165

theorem tailTrace_161199 : CollatzResearch.WordTrace tailWord_161199 prefixEnd_161199 82772568024220041871165 := by
  unfold tailWord_161199
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879410543011028442486651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3919607028674018961657767 5879410543011028442486651)
  ·
    refine ⟨8819115814516542663729977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5879410543011028442486651 8819115814516542663729977)
    ·
      refine ⟨6614336860887406997797483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8819115814516542663729977 6614336860887406997797483)
      ·
        refine ⟨9921505291331110496696225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614336860887406997797483 9921505291331110496696225)
        ·
          refine ⟨7441128968498332872522169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9921505291331110496696225 7441128968498332872522169)
          ·
            refine ⟨5580846726373749654391627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7441128968498332872522169 5580846726373749654391627)
            ·
              refine ⟨8371270089560624481587441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580846726373749654391627 8371270089560624481587441)
              ·
                refine ⟨6278452567170468361190581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8371270089560624481587441 6278452567170468361190581)
                ·
                  refine ⟨588604928172231408861617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6278452567170468361190581 588604928172231408861617)
                  ·
                    refine ⟨441453696129173556646213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 588604928172231408861617 441453696129173556646213)
                    ·
                      refine ⟨82772568024220041871165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 441453696129173556646213 82772568024220041871165)
                      ·
                        rfl

theorem cell23_161199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_161199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161199 prefixEnd_161199 := by exact prefixLift 161199
  have htrace : WordTrace (prefixWord ++ tailWord_161199) baseStart_161199 baseEnd_161199 := by
    simpa [prefixWord, tailWord_161199, baseEnd_161199] using wordTrace_append hprefix tailTrace_161199
  have hstable : (prefixWord ++ tailWord_161199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161199).length < 2 ^ (prefixWord ++ tailWord_161199).sum := by decide
  have hdescent : baseEnd_161199 < baseStart_161199 := by decide
  rcases family_descends (prefixWord ++ tailWord_161199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161203 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 3, 2, 2]
def baseStart_161203 : Nat := 118140960795 + 161203 * 2 ^ 59
def prefixEnd_161203 : Nat := 4983230072969 + 3 ^ 40 * 161203 * 2
def baseEnd_161203 : Nat := 82774621946838026221147

theorem tailTrace_161203 : CollatzResearch.WordTrace tailWord_161203 prefixEnd_161203 82774621946838026221147 := by
  unfold tailWord_161203
  simp only [CollatzResearch.WordTrace]
  refine ⟨5879556434996537125632263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3919704289997691417088175 5879556434996537125632263)
  ·
    refine ⟨8819334652494805688448395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5879556434996537125632263 8819334652494805688448395)
    ·
      refine ⟨13229001978742208532672593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8819334652494805688448395 13229001978742208532672593)
      ·
        refine ⟨9921751484056656399504445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13229001978742208532672593 9921751484056656399504445)
        ·
          refine ⟨3720656806521246149814167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9921751484056656399504445 3720656806521246149814167)
          ·
            refine ⟨5580985209781869224721251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3720656806521246149814167 5580985209781869224721251)
            ·
              refine ⟨8371477814672803837081877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5580985209781869224721251 8371477814672803837081877)
              ·
                refine ⟨392413022562787679863213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8371477814672803837081877 392413022562787679863213)
                ·
                  refine ⟨147154883461045379948705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392413022562787679863213 147154883461045379948705)
                  ·
                    refine ⟨110366162595784034961529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147154883461045379948705 110366162595784034961529)
                    ·
                      refine ⟨82774621946838026221147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110366162595784034961529 82774621946838026221147)
                      ·
                        rfl

theorem cell23_161203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 2, 2].length) (baseStart_161203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161203 prefixEnd_161203 := by exact prefixLift 161203
  have htrace : WordTrace (prefixWord ++ tailWord_161203) baseStart_161203 baseEnd_161203 := by
    simpa [prefixWord, tailWord_161203, baseEnd_161203] using wordTrace_append hprefix tailTrace_161203
  have hstable : (prefixWord ++ tailWord_161203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161203).length < 2 ^ (prefixWord ++ tailWord_161203).sum := by decide
  have hdescent : baseEnd_161203 < baseStart_161203 := by decide
  rcases family_descends (prefixWord ++ tailWord_161203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161237 : List Nat := [1, 3, 2, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_161237 : Nat := 118140960795 + 161237 * 2 ^ 59
def prefixEnd_161237 : Nat := 4983230072969 + 3 ^ 40 * 161237 * 2
def baseEnd_161237 : Nat := 82792080289090893195991

theorem tailTrace_161237 : CollatzResearch.WordTrace tailWord_161237 prefixEnd_161237 82792080289090893195991 := by
  unfold tailWord_161237
  simp only [CollatzResearch.WordTrace]
  refine ⟨5880796516873360932369965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3920531011248907288246643 5880796516873360932369965)
  ·
    refine ⟨2205298693827510349638737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5880796516873360932369965 2205298693827510349638737)
    ·
      refine ⟨1653974020370632762229053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2205298693827510349638737 1653974020370632762229053)
      ·
        refine ⟨620240257638987285835895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1653974020370632762229053 620240257638987285835895)
        ·
          refine ⟨930360386458480928753843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620240257638987285835895 930360386458480928753843)
          ·
            refine ⟨1395540579687721393130765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930360386458480928753843 1395540579687721393130765)
            ·
              refine ⟨523327717382895522424037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1395540579687721393130765 523327717382895522424037)
              ·
                refine ⟨98123947009292910454507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 523327717382895522424037 98123947009292910454507)
                ·
                  refine ⟨147185920513939365681761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98123947009292910454507 147185920513939365681761)
                  ·
                    refine ⟨110389440385454524261321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147185920513939365681761 110389440385454524261321)
                    ·
                      refine ⟨82792080289090893195991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110389440385454524261321 82792080289090893195991)
                      ·
                        rfl

theorem cell23_161237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_161237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161237 prefixEnd_161237 := by exact prefixLift 161237
  have htrace : WordTrace (prefixWord ++ tailWord_161237) baseStart_161237 baseEnd_161237 := by
    simpa [prefixWord, tailWord_161237, baseEnd_161237] using wordTrace_append hprefix tailTrace_161237
  have hstable : (prefixWord ++ tailWord_161237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161237).length < 2 ^ (prefixWord ++ tailWord_161237).sum := by decide
  have hdescent : baseEnd_161237 < baseStart_161237 := by decide
  rcases family_descends (prefixWord ++ tailWord_161237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161253 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_161253 : Nat := 118140960795 + 161253 * 2 ^ 59
def prefixEnd_161253 : Nat := 4983230072969 + 3 ^ 40 * 161253 * 2
def baseEnd_161253 : Nat := 82800295979562830595917

theorem tailTrace_161253 : CollatzResearch.WordTrace tailWord_161253 prefixEnd_161253 82800295979562830595917 := by
  unfold tailWord_161253
  simp only [CollatzResearch.WordTrace]
  refine ⟨5881380084815395664952413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3920920056543597109968275 5881380084815395664952413)
  ·
    refine ⟨2205517531805773374357155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5881380084815395664952413 2205517531805773374357155)
    ·
      refine ⟨3308276297708660061535733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205517531805773374357155 3308276297708660061535733)
      ·
        refine ⟨310150902910186880768975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3308276297708660061535733 310150902910186880768975)
        ·
          refine ⟨465226354365280321153463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310150902910186880768975 465226354365280321153463)
          ·
            refine ⟨697839531547920481730195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465226354365280321153463 697839531547920481730195)
            ·
              refine ⟨1046759297321880722595293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 697839531547920481730195 1046759297321880722595293)
              ·
                refine ⟨392534736495705270973235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1046759297321880722595293 392534736495705270973235)
                ·
                  refine ⟨588802104743557906459853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392534736495705270973235 588802104743557906459853)
                  ·
                    refine ⟨220800789278834214922445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 588802104743557906459853 220800789278834214922445)
                    ·
                      refine ⟨82800295979562830595917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 220800789278834214922445 82800295979562830595917)
                      ·
                        rfl

theorem cell23_161253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_161253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161253 prefixEnd_161253 := by exact prefixLift 161253
  have htrace : WordTrace (prefixWord ++ tailWord_161253) baseStart_161253 baseEnd_161253 := by
    simpa [prefixWord, tailWord_161253, baseEnd_161253] using wordTrace_append hprefix tailTrace_161253
  have hstable : (prefixWord ++ tailWord_161253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161253).length < 2 ^ (prefixWord ++ tailWord_161253).sum := by decide
  have hdescent : baseEnd_161253 < baseStart_161253 := by decide
  rcases family_descends (prefixWord ++ tailWord_161253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161263 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 3, 3, 2]
def baseStart_161263 : Nat := 118140960795 + 161263 * 2 ^ 59
def prefixEnd_161263 : Nat := 4983230072969 + 3 ^ 40 * 161263 * 2
def baseEnd_161263 : Nat := 82805430786107791470871

theorem tailTrace_161263 : CollatzResearch.WordTrace tailWord_161263 prefixEnd_161263 82805430786107791470871 := by
  unfold tailWord_161263
  simp only [CollatzResearch.WordTrace]
  refine ⟨5881744814779167372816443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3921163209852778248544295 5881744814779167372816443)
  ·
    refine ⟨8822617222168751059224665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5881744814779167372816443 8822617222168751059224665)
    ·
      refine ⟨6616962916626563294418499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8822617222168751059224665 6616962916626563294418499)
      ·
        refine ⟨9925444374939844941627749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6616962916626563294418499 9925444374939844941627749)
        ·
          refine ⟨1861020820301220926555203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9925444374939844941627749 1861020820301220926555203)
          ·
            refine ⟨2791531230451831389832805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861020820301220926555203 2791531230451831389832805)
            ·
              refine ⟨523412105709718385593651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2791531230451831389832805 523412105709718385593651)
              ·
                refine ⟨785118158564577578390477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523412105709718385593651 785118158564577578390477)
                ·
                  refine ⟨294419309461716591896429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785118158564577578390477 294419309461716591896429)
                  ·
                    refine ⟨110407241048143721961161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 294419309461716591896429 110407241048143721961161)
                    ·
                      refine ⟨82805430786107791470871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110407241048143721961161 82805430786107791470871)
                      ·
                        rfl

theorem cell23_161263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3, 2].length) (baseStart_161263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161263 prefixEnd_161263 := by exact prefixLift 161263
  have htrace : WordTrace (prefixWord ++ tailWord_161263) baseStart_161263 baseEnd_161263 := by
    simpa [prefixWord, tailWord_161263, baseEnd_161263] using wordTrace_append hprefix tailTrace_161263
  have hstable : (prefixWord ++ tailWord_161263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161263).length < 2 ^ (prefixWord ++ tailWord_161263).sum := by decide
  have hdescent : baseEnd_161263 < baseStart_161263 := by decide
  rcases family_descends (prefixWord ++ tailWord_161263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161287 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_161287 : Nat := 118140960795 + 161287 * 2 ^ 59
def prefixEnd_161287 : Nat := 4983230072969 + 3 ^ 40 * 161287 * 2
def baseEnd_161287 : Nat := 82817754321815697570761

theorem tailTrace_161287 : CollatzResearch.WordTrace tailWord_161287 prefixEnd_161287 82817754321815697570761 := by
  unfold tailWord_161287
  simp only [CollatzResearch.WordTrace]
  refine ⟨5882620166692219471690115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3921746777794812981126743 5882620166692219471690115)
  ·
    refine ⟨8823930250038329207535173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5882620166692219471690115 8823930250038329207535173)
    ·
      refine ⟨1654486921882186726412845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8823930250038329207535173 1654486921882186726412845)
      ·
        refine ⟨620432595705820022404817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1654486921882186726412845 620432595705820022404817)
        ·
          refine ⟨465324446779365016803613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620432595705820022404817 465324446779365016803613)
          ·
            refine ⟨174496667542261881301355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465324446779365016803613 174496667542261881301355)
            ·
              refine ⟨261745001313392821952033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174496667542261881301355 261745001313392821952033)
              ·
                refine ⟨196308750985044616464025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261745001313392821952033 196308750985044616464025)
                ·
                  refine ⟨147231563238783462348019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196308750985044616464025 147231563238783462348019)
                  ·
                    refine ⟨220847344858175193522029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147231563238783462348019 220847344858175193522029)
                    ·
                      refine ⟨82817754321815697570761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 220847344858175193522029 82817754321815697570761)
                      ·
                        rfl

theorem cell23_161287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_161287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161287 prefixEnd_161287 := by exact prefixLift 161287
  have htrace : WordTrace (prefixWord ++ tailWord_161287) baseStart_161287 baseEnd_161287 := by
    simpa [prefixWord, tailWord_161287, baseEnd_161287] using wordTrace_append hprefix tailTrace_161287
  have hstable : (prefixWord ++ tailWord_161287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161287).length < 2 ^ (prefixWord ++ tailWord_161287).sum := by decide
  have hdescent : baseEnd_161287 < baseStart_161287 := by decide
  rcases family_descends (prefixWord ++ tailWord_161287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161356 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_161356 : Nat := 118140960795 + 161356 * 2 ^ 59
def prefixEnd_161356 : Nat := 4983230072969 + 3 ^ 40 * 161356 * 2
def baseEnd_161356 : Nat := 82853184486975927607943

theorem tailTrace_161356 : CollatzResearch.WordTrace tailWord_161356 prefixEnd_161356 82853184486975927607943 := by
  unfold tailWord_161356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942568401721122127975961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3923424535628162837301281 2942568401721122127975961)
  ·
    refine ⟨2206926301290841595981971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2942568401721122127975961 2206926301290841595981971)
    ·
      refine ⟨3310389451936262393972957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206926301290841595981971 3310389451936262393972957)
      ·
        refine ⟨1241396044476098397739859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3310389451936262393972957 1241396044476098397739859)
        ·
          refine ⟨1862094066714147596609789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241396044476098397739859 1862094066714147596609789)
          ·
            refine ⟨698285275017805348728671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1862094066714147596609789 698285275017805348728671)
            ·
              refine ⟨1047427912526708023093007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698285275017805348728671 1047427912526708023093007)
              ·
                refine ⟨1571141868790062034639511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1047427912526708023093007 1571141868790062034639511)
                ·
                  refine ⟨2356712803185093051959267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1571141868790062034639511 2356712803185093051959267)
                  ·
                    refine ⟨3535069204777639577938901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2356712803185093051959267 3535069204777639577938901)
                    ·
                      refine ⟨82853184486975927607943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3535069204777639577938901 82853184486975927607943)
                      ·
                        rfl

theorem cell23_161356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_161356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161356 prefixEnd_161356 := by exact prefixLift 161356
  have htrace : WordTrace (prefixWord ++ tailWord_161356) baseStart_161356 baseEnd_161356 := by
    simpa [prefixWord, tailWord_161356, baseEnd_161356] using wordTrace_append hprefix tailTrace_161356
  have hstable : (prefixWord ++ tailWord_161356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161356).length < 2 ^ (prefixWord ++ tailWord_161356).sum := by decide
  have hdescent : baseEnd_161356 < baseStart_161356 := by decide
  rcases family_descends (prefixWord ++ tailWord_161356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161383 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_161383 : Nat := 118140960795 + 161383 * 2 ^ 59
def prefixEnd_161383 : Nat := 4983230072969 + 3 ^ 40 * 161383 * 2
def baseEnd_161383 : Nat := 82867048464647321970319

theorem tailTrace_161383 : CollatzResearch.WordTrace tailWord_161383 prefixEnd_161383 82867048464647321970319 := by
  unfold tailWord_161383
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886121574344427867184803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3924081049562951911456535 5886121574344427867184803)
  ·
    refine ⟨8829182361516641800777205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5886121574344427867184803 8829182361516641800777205)
    ·
      refine ⟨827735846392185168822863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8829182361516641800777205 827735846392185168822863)
      ·
        refine ⟨1241603769588277753234295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827735846392185168822863 1241603769588277753234295)
        ·
          refine ⟨1862405654382416629851443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241603769588277753234295 1862405654382416629851443)
          ·
            refine ⟨2793608481573624944777165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862405654382416629851443 2793608481573624944777165)
            ·
              refine ⟨1047603180590109354291437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2793608481573624944777165 1047603180590109354291437)
              ·
                refine ⟨392851192721291007859289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047603180590109354291437 392851192721291007859289)
                ·
                  refine ⟨294638394540968255894467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392851192721291007859289 294638394540968255894467)
                  ·
                    refine ⟨441957591811452383841701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 294638394540968255894467 441957591811452383841701)
                    ·
                      refine ⟨82867048464647321970319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 441957591811452383841701 82867048464647321970319)
                      ·
                        rfl

theorem cell23_161383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_161383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161383 prefixEnd_161383 := by exact prefixLift 161383
  have htrace : WordTrace (prefixWord ++ tailWord_161383) baseStart_161383 baseEnd_161383 := by
    simpa [prefixWord, tailWord_161383, baseEnd_161383] using wordTrace_append hprefix tailTrace_161383
  have hstable : (prefixWord ++ tailWord_161383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161383).length < 2 ^ (prefixWord ++ tailWord_161383).sum := by decide
  have hdescent : baseEnd_161383 < baseStart_161383 := by decide
  rcases family_descends (prefixWord ++ tailWord_161383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161403 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 3]
def baseStart_161403 : Nat := 118140960795 + 161403 * 2 ^ 59
def prefixEnd_161403 : Nat := 4983230072969 + 3 ^ 40 * 161403 * 2
def baseEnd_161403 : Nat := 82877318077737243720227

theorem tailTrace_161403 : CollatzResearch.WordTrace tailWord_161403 prefixEnd_161403 82877318077737243720227 := by
  unfold tailWord_161403
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886851034271971282912863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3924567356181314188608575 5886851034271971282912863)
  ·
    refine ⟨8830276551407956924369295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5886851034271971282912863 8830276551407956924369295)
    ·
      refine ⟨13245414827111935386553943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8830276551407956924369295 13245414827111935386553943)
      ·
        refine ⟨19868122240667903079830915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13245414827111935386553943 19868122240667903079830915)
        ·
          refine ⟨29802183361001854619746373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19868122240667903079830915 29802183361001854619746373)
          ·
            refine ⟨5587909380187847741202445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29802183361001854619746373 5587909380187847741202445)
            ·
              refine ⟨2095466017570442902950917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5587909380187847741202445 2095466017570442902950917)
              ·
                refine ⟨392899878294458044303297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2095466017570442902950917 392899878294458044303297)
                ·
                  refine ⟨294674908720843533227473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392899878294458044303297 294674908720843533227473)
                  ·
                    refine ⟨221006181540632649920605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294674908720843533227473 221006181540632649920605)
                    ·
                      refine ⟨82877318077737243720227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 221006181540632649920605 82877318077737243720227)
                      ·
                        rfl

theorem cell23_161403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 3].length) (baseStart_161403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161403 prefixEnd_161403 := by exact prefixLift 161403
  have htrace : WordTrace (prefixWord ++ tailWord_161403) baseStart_161403 baseEnd_161403 := by
    simpa [prefixWord, tailWord_161403, baseEnd_161403] using wordTrace_append hprefix tailTrace_161403
  have hstable : (prefixWord ++ tailWord_161403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161403).length < 2 ^ (prefixWord ++ tailWord_161403).sum := by decide
  have hdescent : baseEnd_161403 < baseStart_161403 := by decide
  rcases family_descends (prefixWord ++ tailWord_161403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161503 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_161503 : Nat := 118140960795 + 161503 * 2 ^ 59
def prefixEnd_161503 : Nat := 4983230072969 + 3 ^ 40 * 161503 * 2
def baseEnd_161503 : Nat := 82928666143186852469767

theorem tailTrace_161503 : CollatzResearch.WordTrace tailWord_161503 prefixEnd_161503 82928666143186852469767 := by
  unfold tailWord_161503
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890498333909688361553163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3926998889273125574368775 5890498333909688361553163)
  ·
    refine ⟨8835747500864532542329745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5890498333909688361553163 8835747500864532542329745)
    ·
      refine ⟨6626810625648399406747309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8835747500864532542329745 6626810625648399406747309)
      ·
        refine ⟨2485053984618149777530241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6626810625648399406747309 2485053984618149777530241)
        ·
          refine ⟨1863790488463612333147681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2485053984618149777530241 1863790488463612333147681)
          ·
            refine ⟨1397842866347709249860761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863790488463612333147681 1397842866347709249860761)
            ·
              refine ⟨1048382149760781937395571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397842866347709249860761 1048382149760781937395571)
              ·
                refine ⟨1572573224641172906093357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048382149760781937395571 1572573224641172906093357)
                ·
                  refine ⟨589714959240439839785009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1572573224641172906093357 589714959240439839785009)
                  ·
                    refine ⟨442286219430329879838757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 589714959240439839785009 442286219430329879838757)
                    ·
                      refine ⟨82928666143186852469767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 442286219430329879838757 82928666143186852469767)
                      ·
                        rfl

theorem cell23_161503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_161503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161503 prefixEnd_161503 := by exact prefixLift 161503
  have htrace : WordTrace (prefixWord ++ tailWord_161503) baseStart_161503 baseEnd_161503 := by
    simpa [prefixWord, tailWord_161503, baseEnd_161503] using wordTrace_append hprefix tailTrace_161503
  have hstable : (prefixWord ++ tailWord_161503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161503).length < 2 ^ (prefixWord ++ tailWord_161503).sum := by decide
  have hdescent : baseEnd_161503 < baseStart_161503 := by decide
  rcases family_descends (prefixWord ++ tailWord_161503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161534 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_161534 : Nat := 118140960795 + 161534 * 2 ^ 59
def prefixEnd_161534 : Nat := 4983230072969 + 3 ^ 40 * 161534 * 2
def baseEnd_161534 : Nat := 27648194681158743727375

theorem tailTrace_161534 : CollatzResearch.WordTrace tailWord_161534 prefixEnd_161534 27648194681158743727375 := by
  unfold tailWord_161534
  simp only [CollatzResearch.WordTrace]
  refine ⟨736453624599672581991457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3927752664531587103954437 736453624599672581991457)
  ·
    refine ⟨552340218449754436493593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 736453624599672581991457 552340218449754436493593)
    ·
      refine ⟨414255163837315827370195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 552340218449754436493593 414255163837315827370195)
      ·
        refine ⟨621382745755973741055293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414255163837315827370195 621382745755973741055293)
        ·
          refine ⟨233018529658490152895735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 621382745755973741055293 233018529658490152895735)
          ·
            refine ⟨349527794487735229343603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233018529658490152895735 349527794487735229343603)
            ·
              refine ⟨524291691731602844015405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349527794487735229343603 524291691731602844015405)
              ·
                refine ⟨196609384399351066505777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524291691731602844015405 196609384399351066505777)
                ·
                  refine ⟨147457038299513299879333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196609384399351066505777 147457038299513299879333)
                  ·
                    refine ⟨27648194681158743727375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147457038299513299879333 27648194681158743727375)
                    ·
                      rfl

theorem cell23_161534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_161534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161534 prefixEnd_161534 := by exact prefixLift 161534
  have htrace : WordTrace (prefixWord ++ tailWord_161534) baseStart_161534 baseEnd_161534 := by
    simpa [prefixWord, tailWord_161534, baseEnd_161534] using wordTrace_append hprefix tailTrace_161534
  have hstable : (prefixWord ++ tailWord_161534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161534).length < 2 ^ (prefixWord ++ tailWord_161534).sum := by decide
  have hdescent : baseEnd_161534 < baseStart_161534 := by decide
  rcases family_descends (prefixWord ++ tailWord_161534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161603 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 9]
def baseStart_161603 : Nat := 118140960795 + 161603 * 2 ^ 59
def prefixEnd_161603 : Nat := 4983230072969 + 3 ^ 40 * 161603 * 2
def baseEnd_161603 : Nat := 9220001578737384579923

theorem tailTrace_161603 : CollatzResearch.WordTrace tailWord_161603 prefixEnd_161603 9220001578737384579923 := by
  unfold tailWord_161603
  simp only [CollatzResearch.WordTrace]
  refine ⟨5894145633547405440193463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3929430422364936960128975 5894145633547405440193463)
  ·
    refine ⟨8841218450321108160290195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5894145633547405440193463 8841218450321108160290195)
    ·
      refine ⟨13261827675481662240435293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8841218450321108160290195 13261827675481662240435293)
      ·
        refine ⟨4973185378305623340163235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13261827675481662240435293 4973185378305623340163235)
        ·
          refine ⟨7459778067458435010244853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4973185378305623340163235 7459778067458435010244853)
          ·
            refine ⟨699354193824228282210455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7459778067458435010244853 699354193824228282210455)
            ·
              refine ⟨1049031290736342423315683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699354193824228282210455 1049031290736342423315683)
              ·
                refine ⟨1573546936104513634973525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049031290736342423315683 1573546936104513634973525)
                ·
                  refine ⟨9220001578737384579923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1573546936104513634973525 9220001578737384579923)
                  ·
                    rfl

theorem cell23_161603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 9].length) (baseStart_161603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161603 prefixEnd_161603 := by exact prefixLift 161603
  have htrace : WordTrace (prefixWord ++ tailWord_161603) baseStart_161603 baseEnd_161603 := by
    simpa [prefixWord, tailWord_161603, baseEnd_161603] using wordTrace_append hprefix tailTrace_161603
  have hstable : (prefixWord ++ tailWord_161603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161603).length < 2 ^ (prefixWord ++ tailWord_161603).sum := by decide
  have hdescent : baseEnd_161603 < baseStart_161603 := by decide
  rcases family_descends (prefixWord ++ tailWord_161603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161631 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 2, 2, 2]
def baseStart_161631 : Nat := 118140960795 + 161631 * 2 ^ 59
def prefixEnd_161631 : Nat := 4983230072969 + 3 ^ 40 * 161631 * 2
def baseEnd_161631 : Nat := 82994391666962351669179

theorem tailTrace_161631 : CollatzResearch.WordTrace tailWord_161631 prefixEnd_161631 82994391666962351669179 := by
  unfold tailWord_161631
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895166877445966222212747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3930111251630644148141831 5895166877445966222212747)
  ·
    refine ⟨8842750316168949333319121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5895166877445966222212747 8842750316168949333319121)
    ·
      refine ⟨6632062737126711999989341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8842750316168949333319121 6632062737126711999989341)
      ·
        refine ⟨2487023526422516999996003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6632062737126711999989341 2487023526422516999996003)
        ·
          refine ⟨3730535289633775499994005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487023526422516999996003 3730535289633775499994005)
          ·
            refine ⟨174868841701583226562219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3730535289633775499994005 174868841701583226562219)
            ·
              refine ⟨262303262552374839843329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174868841701583226562219 262303262552374839843329)
              ·
                refine ⟨196727446914281129882497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262303262552374839843329 196727446914281129882497)
                ·
                  refine ⟨147545585185710847411873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196727446914281129882497 147545585185710847411873)
                  ·
                    refine ⟨110659188889283135558905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 147545585185710847411873 110659188889283135558905)
                    ·
                      refine ⟨82994391666962351669179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110659188889283135558905 82994391666962351669179)
                      ·
                        rfl

theorem cell23_161631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_161631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161631 prefixEnd_161631 := by exact prefixLift 161631
  have htrace : WordTrace (prefixWord ++ tailWord_161631) baseStart_161631 baseEnd_161631 := by
    simpa [prefixWord, tailWord_161631, baseEnd_161631] using wordTrace_append hprefix tailTrace_161631
  have hstable : (prefixWord ++ tailWord_161631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161631).length < 2 ^ (prefixWord ++ tailWord_161631).sum := by decide
  have hdescent : baseEnd_161631 < baseStart_161631 := by decide
  rcases family_descends (prefixWord ++ tailWord_161631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161643 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7]
def baseStart_161643 : Nat := 118140960795 + 161643 * 2 ^ 59
def prefixEnd_161643 : Nat := 4983230072969 + 3 ^ 40 * 161643 * 2
def baseEnd_161643 : Nat := 83000553434816304719123

theorem tailTrace_161643 : CollatzResearch.WordTrace tailWord_161643 prefixEnd_161643 83000553434816304719123 := by
  unfold tailWord_161643
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895604553402492271649583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3930403035601661514433055 5895604553402492271649583)
  ·
    refine ⟨8843406830103738407474375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5895604553402492271649583 8843406830103738407474375)
    ·
      refine ⟨13265110245155607611211563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8843406830103738407474375 13265110245155607611211563)
      ·
        refine ⟨19897665367733411416817345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13265110245155607611211563 19897665367733411416817345)
        ·
          refine ⟨14923249025800058562613009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19897665367733411416817345 14923249025800058562613009)
          ·
            refine ⟨11192436769350043921959757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14923249025800058562613009 11192436769350043921959757)
            ·
              refine ⟨4197163788506266470734909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11192436769350043921959757 4197163788506266470734909)
              ·
                refine ⟨1573936420689849926525591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4197163788506266470734909 1573936420689849926525591)
                ·
                  refine ⟨2360904631034774889788387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1573936420689849926525591 2360904631034774889788387)
                  ·
                    refine ⟨3541356946552162334682581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2360904631034774889788387 3541356946552162334682581)
                    ·
                      refine ⟨83000553434816304719123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3541356946552162334682581 83000553434816304719123)
                      ·
                        rfl

theorem cell23_161643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_161643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161643 prefixEnd_161643 := by exact prefixLift 161643
  have htrace : WordTrace (prefixWord ++ tailWord_161643) baseStart_161643 baseEnd_161643 := by
    simpa [prefixWord, tailWord_161643, baseEnd_161643] using wordTrace_append hprefix tailTrace_161643
  have hstable : (prefixWord ++ tailWord_161643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161643).length < 2 ^ (prefixWord ++ tailWord_161643).sum := by decide
  have hdescent : baseEnd_161643 < baseStart_161643 := by decide
  rcases family_descends (prefixWord ++ tailWord_161643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161663 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 10]
def baseStart_161663 : Nat := 118140960795 + 161663 * 2 ^ 59
def prefixEnd_161663 : Nat := 4983230072969 + 3 ^ 40 * 161663 * 2
def baseEnd_161663 : Nat := 27670274349302075489677

theorem tailTrace_161663 : CollatzResearch.WordTrace tailWord_161663 prefixEnd_161663 27670274349302075489677 := by
  unfold tailWord_161663
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896334013330035687377643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3930889342220023791585095 5896334013330035687377643)
  ·
    refine ⟨8844501019995053531066465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5896334013330035687377643 8844501019995053531066465)
    ·
      refine ⟨6633375764996290148299849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8844501019995053531066465 6633375764996290148299849)
      ·
        refine ⟨4975031823747217611224887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6633375764996290148299849 4975031823747217611224887)
        ·
          refine ⟨7462547735620826416837331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975031823747217611224887 7462547735620826416837331)
          ·
            refine ⟨11193821603431239625255997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7462547735620826416837331 11193821603431239625255997)
            ·
              refine ⟨4197683101286714859470999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11193821603431239625255997 4197683101286714859470999)
              ·
                refine ⟨6296524651930072289206499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4197683101286714859470999 6296524651930072289206499)
                ·
                  refine ⟨9444786977895108433809749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296524651930072289206499 9444786977895108433809749)
                  ·
                    refine ⟨27670274349302075489677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 9444786977895108433809749 27670274349302075489677)
                    ·
                      rfl

theorem cell23_161663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_161663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161663 prefixEnd_161663 := by exact prefixLift 161663
  have htrace : WordTrace (prefixWord ++ tailWord_161663) baseStart_161663 baseEnd_161663 := by
    simpa [prefixWord, tailWord_161663, baseEnd_161663] using wordTrace_append hprefix tailTrace_161663
  have hstable : (prefixWord ++ tailWord_161663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161663).length < 2 ^ (prefixWord ++ tailWord_161663).sum := by decide
  have hdescent : baseEnd_161663 < baseStart_161663 := by decide
  rcases family_descends (prefixWord ++ tailWord_161663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161671 : List Nat := [1, 1, 4, 2, 5, 1, 1, 3, 5]
def baseStart_161671 : Nat := 118140960795 + 161671 * 2 ^ 59
def prefixEnd_161671 : Nat := 4983230072969 + 3 ^ 40 * 161671 * 2
def baseEnd_161671 : Nat := 9223881210349132796555

theorem tailTrace_161671 : CollatzResearch.WordTrace tailWord_161671 prefixEnd_161671 9223881210349132796555 := by
  unfold tailWord_161671
  simp only [CollatzResearch.WordTrace]
  refine ⟨5896625797301053053668867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3931083864867368702445911 5896625797301053053668867)
  ·
    refine ⟨8844938695951579580503301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5896625797301053053668867 8844938695951579580503301)
    ·
      refine ⟨1658426005490921171344369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8844938695951579580503301 1658426005490921171344369)
      ·
        refine ⟨1243819504118190878508277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1658426005490921171344369 1243819504118190878508277)
        ·
          refine ⟨116608078511080394860151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1243819504118190878508277 116608078511080394860151)
          ·
            refine ⟨174912117766620592290227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116608078511080394860151 174912117766620592290227)
            ·
              refine ⟨262368176649930888435341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174912117766620592290227 262368176649930888435341)
              ·
                refine ⟨98388066243724083163253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262368176649930888435341 98388066243724083163253)
                ·
                  refine ⟨9223881210349132796555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98388066243724083163253 9223881210349132796555)
                  ·
                    rfl

theorem cell23_161671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 5].length) (baseStart_161671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161671 prefixEnd_161671 := by exact prefixLift 161671
  have htrace : WordTrace (prefixWord ++ tailWord_161671) baseStart_161671 baseEnd_161671 := by
    simpa [prefixWord, tailWord_161671, baseEnd_161671] using wordTrace_append hprefix tailTrace_161671
  have hstable : (prefixWord ++ tailWord_161671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161671).length < 2 ^ (prefixWord ++ tailWord_161671).sum := by decide
  have hdescent : baseEnd_161671 < baseStart_161671 := by decide
  rcases family_descends (prefixWord ++ tailWord_161671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161680 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 7, 4]
def baseStart_161680 : Nat := 118140960795 + 161680 * 2 ^ 59
def prefixEnd_161680 : Nat := 4983230072969 + 3 ^ 40 * 161680 * 2
def baseEnd_161680 : Nat := 27673184073010886652151

theorem tailTrace_161680 : CollatzResearch.WordTrace tailWord_161680 prefixEnd_161680 27673184073010886652151 := by
  unfold tailWord_161680
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948477027134223795373247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3931302702845631727164329 2948477027134223795373247)
  ·
    refine ⟨4422715540701335693059871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2948477027134223795373247 4422715540701335693059871)
    ·
      refine ⟨6634073311052003539589807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4422715540701335693059871 6634073311052003539589807)
      ·
        refine ⟨9951109966578005309384711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6634073311052003539589807 9951109966578005309384711)
        ·
          refine ⟨14926664949867007964077067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9951109966578005309384711 14926664949867007964077067)
          ·
            refine ⟨22389997424800511946115601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14926664949867007964077067 22389997424800511946115601)
            ·
              refine ⟨16792498068600383959586701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22389997424800511946115601 16792498068600383959586701)
              ·
                refine ⟨6297186775725143984845013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16792498068600383959586701 6297186775725143984845013)
                ·
                  refine ⟨147590315056058062144805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6297186775725143984845013 147590315056058062144805)
                  ·
                    refine ⟨27673184073010886652151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147590315056058062144805 27673184073010886652151)
                    ·
                      rfl

theorem cell23_161680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_161680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161680 prefixEnd_161680 := by exact prefixLift 161680
  have htrace : WordTrace (prefixWord ++ tailWord_161680) baseStart_161680 baseEnd_161680 := by
    simpa [prefixWord, tailWord_161680, baseEnd_161680] using wordTrace_append hprefix tailTrace_161680
  have hstable : (prefixWord ++ tailWord_161680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161680).length < 2 ^ (prefixWord ++ tailWord_161680).sum := by decide
  have hdescent : baseEnd_161680 < baseStart_161680 := by decide
  rcases family_descends (prefixWord ++ tailWord_161680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161687 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_161687 : Nat := 118140960795 + 161687 * 2 ^ 59
def prefixEnd_161687 : Nat := 4983230072969 + 3 ^ 40 * 161687 * 2
def baseEnd_161687 : Nat := 83023146583614132568921

theorem tailTrace_161687 : CollatzResearch.WordTrace tailWord_161687 prefixEnd_161687 83023146583614132568921 := by
  unfold tailWord_161687
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897209365243087786251315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3931472910162058524167543 5897209365243087786251315)
  ·
    refine ⟨8845814047864631679376973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5897209365243087786251315 8845814047864631679376973)
    ·
      refine ⟨3317180267949236879766365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8845814047864631679376973 3317180267949236879766365)
      ·
        refine ⟨1243942600480963829912387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3317180267949236879766365 1243942600480963829912387)
        ·
          refine ⟨1865913900721445744868581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243942600480963829912387 1865913900721445744868581)
          ·
            refine ⟨349858856385271077162859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1865913900721445744868581 349858856385271077162859)
            ·
              refine ⟨524788284577906615744289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349858856385271077162859 524788284577906615744289)
              ·
                refine ⟨393591213433429961808217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524788284577906615744289 393591213433429961808217)
                ·
                  refine ⟨295193410075072471356163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 393591213433429961808217 295193410075072471356163)
                  ·
                    refine ⟨442790115112608707034245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295193410075072471356163 442790115112608707034245)
                    ·
                      refine ⟨83023146583614132568921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 442790115112608707034245 83023146583614132568921)
                      ·
                        rfl

theorem cell23_161687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_161687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161687 prefixEnd_161687 := by exact prefixLift 161687
  have htrace : WordTrace (prefixWord ++ tailWord_161687) baseStart_161687 baseEnd_161687 := by
    simpa [prefixWord, tailWord_161687, baseEnd_161687] using wordTrace_append hprefix tailTrace_161687
  have hstable : (prefixWord ++ tailWord_161687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161687).length < 2 ^ (prefixWord ++ tailWord_161687).sum := by decide
  have hdescent : baseEnd_161687 < baseStart_161687 := by decide
  rcases family_descends (prefixWord ++ tailWord_161687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161737 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 3]
def baseStart_161737 : Nat := 118140960795 + 161737 * 2 ^ 59
def prefixEnd_161737 : Nat := 4983230072969 + 3 ^ 40 * 161737 * 2
def baseEnd_161737 : Nat := 83048820616338936943691

theorem tailTrace_161737 : CollatzResearch.WordTrace tailWord_161737 prefixEnd_161737 83048820616338936943691 := by
  unfold tailWord_161737
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899033015061946325571465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3932688676707964217047643 5899033015061946325571465)
  ·
    refine ⟨4424274761296459744178599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5899033015061946325571465 4424274761296459744178599)
    ·
      refine ⟨6636412141944689616267899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4424274761296459744178599 6636412141944689616267899)
      ·
        refine ⟨9954618212917034424401849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6636412141944689616267899 9954618212917034424401849)
        ·
          refine ⟨7465963659687775818301387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954618212917034424401849 7465963659687775818301387)
          ·
            refine ⟨11198945489531663727452081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7465963659687775818301387 11198945489531663727452081)
            ·
              refine ⟨8399209117148747795589061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11198945489531663727452081 8399209117148747795589061)
              ·
                refine ⟨1574851709465390211672949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8399209117148747795589061 1574851709465390211672949)
                ·
                  refine ⟨147642347762380332344339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1574851709465390211672949 147642347762380332344339)
                  ·
                    refine ⟨221463521643570498516509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147642347762380332344339 221463521643570498516509)
                    ·
                      refine ⟨83048820616338936943691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 221463521643570498516509 83048820616338936943691)
                      ·
                        rfl

theorem cell23_161737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 3].length) (baseStart_161737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161737 prefixEnd_161737 := by exact prefixLift 161737
  have htrace : WordTrace (prefixWord ++ tailWord_161737) baseStart_161737 baseEnd_161737 := by
    simpa [prefixWord, tailWord_161737, baseEnd_161737] using wordTrace_append hprefix tailTrace_161737
  have hstable : (prefixWord ++ tailWord_161737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161737).length < 2 ^ (prefixWord ++ tailWord_161737).sum := by decide
  have hdescent : baseEnd_161737 < baseStart_161737 := by decide
  rcases family_descends (prefixWord ++ tailWord_161737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161800 : List Nat := [2, 1, 3, 2, 1, 2, 12]
def baseStart_161800 : Nat := 118140960795 + 161800 * 2 ^ 59
def prefixEnd_161800 : Nat := 4983230072969 + 3 ^ 40 * 161800 * 2
def baseEnd_161800 : Nat := 1025693455525582598221

theorem tailTrace_161800 : CollatzResearch.WordTrace tailWord_161800 prefixEnd_161800 1025693455525582598221 := by
  unfold tailWord_161800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2950665406916854042557427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3934220542555805390076569 2950665406916854042557427)
  ·
    refine ⟨4425998110375281063836141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2950665406916854042557427 4425998110375281063836141)
    ·
      refine ⟨1659749291390730398938553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4425998110375281063836141 1659749291390730398938553)
      ·
        refine ⟨1244811968543047799203915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1659749291390730398938553 1244811968543047799203915)
        ·
          refine ⟨1867217952814571698805873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244811968543047799203915 1867217952814571698805873)
          ·
            refine ⟨1400413464610928774104405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1867217952814571698805873 1400413464610928774104405)
            ·
              refine ⟨1025693455525582598221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 1400413464610928774104405 1025693455525582598221)
              ·
                rfl

theorem cell23_161800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 12].length) (baseStart_161800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161800 prefixEnd_161800 := by exact prefixLift 161800
  have htrace : WordTrace (prefixWord ++ tailWord_161800) baseStart_161800 baseEnd_161800 := by
    simpa [prefixWord, tailWord_161800, baseEnd_161800] using wordTrace_append hprefix tailTrace_161800
  have hstable : (prefixWord ++ tailWord_161800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161800).length < 2 ^ (prefixWord ++ tailWord_161800).sum := by decide
  have hdescent : baseEnd_161800 < baseStart_161800 := by decide
  rcases family_descends (prefixWord ++ tailWord_161800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161834 : List Nat := [3, 1, 4, 1, 2, 1, 4, 7]
def baseStart_161834 : Nat := 118140960795 + 161834 * 2 ^ 59
def prefixEnd_161834 : Nat := 4983230072969 + 3 ^ 40 * 161834 * 2
def baseEnd_161834 : Nat := 3077726971845372497435

theorem tailTrace_161834 : CollatzResearch.WordTrace tailWord_161834 prefixEnd_161834 3077726971845372497435 := by
  unfold tailWord_161834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475642723927632972963139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3935047263807021261235037 1475642723927632972963139)
  ·
    refine ⟨2213464085891449459444709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1475642723927632972963139 2213464085891449459444709)
    ·
      refine ⟨415024516104646773645883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2213464085891449459444709 415024516104646773645883)
      ·
        refine ⟨622536774156970160468825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415024516104646773645883 622536774156970160468825)
        ·
          refine ⟨466902580617727620351619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622536774156970160468825 466902580617727620351619)
          ·
            refine ⟨700353870926591430527429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466902580617727620351619 700353870926591430527429)
            ·
              refine ⟨131316350798735893223893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 700353870926591430527429 131316350798735893223893)
              ·
                refine ⟨3077726971845372497435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131316350798735893223893 3077726971845372497435)
                ·
                  rfl

theorem cell23_161834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_161834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161834 prefixEnd_161834 := by exact prefixLift 161834
  have htrace : WordTrace (prefixWord ++ tailWord_161834) baseStart_161834 baseEnd_161834 := by
    simpa [prefixWord, tailWord_161834, baseEnd_161834] using wordTrace_append hprefix tailTrace_161834
  have hstable : (prefixWord ++ tailWord_161834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161834).length < 2 ^ (prefixWord ++ tailWord_161834).sum := by decide
  have hdescent : baseEnd_161834 < baseStart_161834 := by decide
  rcases family_descends (prefixWord ++ tailWord_161834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161887 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 3]
def baseStart_161887 : Nat := 118140960795 + 161887 * 2 ^ 59
def prefixEnd_161887 : Nat := 4983230072969 + 3 ^ 40 * 161887 * 2
def baseEnd_161887 : Nat := 83125842714513350068001

theorem tailTrace_161887 : CollatzResearch.WordTrace tailWord_161887 prefixEnd_161887 83125842714513350068001 := by
  unfold tailWord_161887
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904503964518521943531915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3936335976345681295687943 5904503964518521943531915)
  ·
    refine ⟨8856755946777782915297873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5904503964518521943531915 8856755946777782915297873)
    ·
      refine ⟨6642566960083337186473405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8856755946777782915297873 6642566960083337186473405)
      ·
        refine ⟨2490962610031251444927527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6642566960083337186473405 2490962610031251444927527)
        ·
          refine ⟨3736443915046877167391291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490962610031251444927527 3736443915046877167391291)
          ·
            refine ⟨5604665872570315751086937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736443915046877167391291 5604665872570315751086937)
            ·
              refine ⟨4203499404427736813315203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5604665872570315751086937 4203499404427736813315203)
              ·
                refine ⟨6305249106641605219972805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4203499404427736813315203 6305249106641605219972805)
                ·
                  refine ⟨1182234207495300978744901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6305249106641605219972805 1182234207495300978744901)
                  ·
                    refine ⟨221668913905368933514669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1182234207495300978744901 221668913905368933514669)
                    ·
                      refine ⟨83125842714513350068001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 221668913905368933514669 83125842714513350068001)
                      ·
                        rfl

theorem cell23_161887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_161887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161887 prefixEnd_161887 := by exact prefixLift 161887
  have htrace : WordTrace (prefixWord ++ tailWord_161887) baseStart_161887 baseEnd_161887 := by
    simpa [prefixWord, tailWord_161887, baseEnd_161887] using wordTrace_append hprefix tailTrace_161887
  have hstable : (prefixWord ++ tailWord_161887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161887).length < 2 ^ (prefixWord ++ tailWord_161887).sum := by decide
  have hdescent : baseEnd_161887 < baseStart_161887 := by decide
  rcases family_descends (prefixWord ++ tailWord_161887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161888 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 1, 3, 2]
def baseStart_161888 : Nat := 118140960795 + 161888 * 2 ^ 59
def prefixEnd_161888 : Nat := 4983230072969 + 3 ^ 40 * 161888 * 2
def baseEnd_161888 : Nat := 83126356195167846155497

theorem tailTrace_161888 : CollatzResearch.WordTrace tailWord_161888 prefixEnd_161888 83126356195167846155497 := by
  unfold tailWord_161888
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952270218757449557159159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3936360291676599409545545 2952270218757449557159159)
  ·
    refine ⟨4428405328136174335738739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2952270218757449557159159 4428405328136174335738739)
    ·
      refine ⟨6642607992204261503608109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4428405328136174335738739 6642607992204261503608109)
      ·
        refine ⟨2490977997076598063853041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6642607992204261503608109 2490977997076598063853041)
        ·
          refine ⟨1868233497807448547889781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2490977997076598063853041 1868233497807448547889781)
          ·
            refine ⟨175146890419448301364667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1868233497807448547889781 175146890419448301364667)
            ·
              refine ⟨262720335629172452047001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175146890419448301364667 262720335629172452047001)
              ·
                refine ⟨197040251721879339035251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262720335629172452047001 197040251721879339035251)
                ·
                  refine ⟨295560377582819008552877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197040251721879339035251 295560377582819008552877)
                  ·
                    refine ⟨110835141593557128207329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295560377582819008552877 110835141593557128207329)
                    ·
                      refine ⟨83126356195167846155497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110835141593557128207329 83126356195167846155497)
                      ·
                        rfl

theorem cell23_161888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_161888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161888 prefixEnd_161888 := by exact prefixLift 161888
  have htrace : WordTrace (prefixWord ++ tailWord_161888) baseStart_161888 baseEnd_161888 := by
    simpa [prefixWord, tailWord_161888, baseEnd_161888] using wordTrace_append hprefix tailTrace_161888
  have hstable : (prefixWord ++ tailWord_161888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161888).length < 2 ^ (prefixWord ++ tailWord_161888).sum := by decide
  have hdescent : baseEnd_161888 < baseStart_161888 := by decide
  rcases family_descends (prefixWord ++ tailWord_161888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161901 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_161901 : Nat := 118140960795 + 161901 * 2 ^ 59
def prefixEnd_161901 : Nat := 4983230072969 + 3 ^ 40 * 161901 * 2
def baseEnd_161901 : Nat := 83133031443676295292937

theorem tailTrace_161901 : CollatzResearch.WordTrace tailWord_161901 prefixEnd_161901 83133031443676295292937 := by
  unfold tailWord_161901
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905014586467802334541557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3936676390978534889694371 5905014586467802334541557)
  ·
    refine ⟨553595117481356468863271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5905014586467802334541557 553595117481356468863271)
    ·
      refine ⟨830392676222034703294907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553595117481356468863271 830392676222034703294907)
      ·
        refine ⟨1245589014333052054942361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830392676222034703294907 1245589014333052054942361)
        ·
          refine ⟨934191760749789041206771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1245589014333052054942361 934191760749789041206771)
          ·
            refine ⟨1401287641124683561810157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934191760749789041206771 1401287641124683561810157)
            ·
              refine ⟨525482865421756335678809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1401287641124683561810157 525482865421756335678809)
              ·
                refine ⟨394112149066317251759107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525482865421756335678809 394112149066317251759107)
                ·
                  refine ⟨591168223599475877638661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394112149066317251759107 591168223599475877638661)
                  ·
                    refine ⟨110844041924901727057249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 591168223599475877638661 110844041924901727057249)
                    ·
                      refine ⟨83133031443676295292937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110844041924901727057249 83133031443676295292937)
                      ·
                        rfl

theorem cell23_161901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_161901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161901 prefixEnd_161901 := by exact prefixLift 161901
  have htrace : WordTrace (prefixWord ++ tailWord_161901) baseStart_161901 baseEnd_161901 := by
    simpa [prefixWord, tailWord_161901, baseEnd_161901] using wordTrace_append hprefix tailTrace_161901
  have hstable : (prefixWord ++ tailWord_161901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161901).length < 2 ^ (prefixWord ++ tailWord_161901).sum := by decide
  have hdescent : baseEnd_161901 < baseStart_161901 := by decide
  rcases family_descends (prefixWord ++ tailWord_161901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161994 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_161994 : Nat := 118140960795 + 161994 * 2 ^ 59
def prefixEnd_161994 : Nat := 4983230072969 + 3 ^ 40 * 161994 * 2
def baseEnd_161994 : Nat := 83180785144544431430009

theorem tailTrace_161994 : CollatzResearch.WordTrace tailWord_161994 prefixEnd_161994 83180785144544431430009 := by
  unfold tailWord_161994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477101643782719804419259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3938937716753919478451357 1477101643782719804419259)
  ·
    refine ⟨2215652465674079706628889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1477101643782719804419259 2215652465674079706628889)
    ·
      refine ⟨1661739349255559779971667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2215652465674079706628889 1661739349255559779971667)
      ·
        refine ⟨2492609023883339669957501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661739349255559779971667 2492609023883339669957501)
        ·
          refine ⟨934728383956252376234063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2492609023883339669957501 934728383956252376234063)
          ·
            refine ⟨1402092575934378564351095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934728383956252376234063 1402092575934378564351095)
            ·
              refine ⟨2103138863901567846526643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402092575934378564351095 2103138863901567846526643)
              ·
                refine ⟨3154708295852351769789965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103138863901567846526643 3154708295852351769789965)
                ·
                  refine ⟨1183015610944631913671237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3154708295852351769789965 1183015610944631913671237)
                  ·
                    refine ⟨221815427052118483813357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1183015610944631913671237 221815427052118483813357)
                    ·
                      refine ⟨83180785144544431430009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 221815427052118483813357 83180785144544431430009)
                      ·
                        rfl

theorem cell23_161994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_161994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_161994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_161994 prefixEnd_161994 := by exact prefixLift 161994
  have htrace : WordTrace (prefixWord ++ tailWord_161994) baseStart_161994 baseEnd_161994 := by
    simpa [prefixWord, tailWord_161994, baseEnd_161994] using wordTrace_append hprefix tailTrace_161994
  have hstable : (prefixWord ++ tailWord_161994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161994).length < 2 ^ (prefixWord ++ tailWord_161994).sum := by decide
  have hdescent : baseEnd_161994 < baseStart_161994 := by decide
  rcases family_descends (prefixWord ++ tailWord_161994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162041 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 3]
def baseStart_162041 : Nat := 118140960795 + 162041 * 2 ^ 59
def prefixEnd_162041 : Nat := 4983230072969 + 3 ^ 40 * 162041 * 2
def baseEnd_162041 : Nat := 83204918735305747542293

theorem tailTrace_162041 : CollatzResearch.WordTrace tailWord_162041 prefixEnd_162041 83204918735305747542293 := by
  unfold tailWord_162041
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910120805960606244637977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3940080537307070829758651 5910120805960606244637977)
  ·
    refine ⟨4432590604470454683478483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5910120805960606244637977 4432590604470454683478483)
    ·
      refine ⟨6648885906705682025217725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4432590604470454683478483 6648885906705682025217725)
      ·
        refine ⟨2493332215014630759456647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6648885906705682025217725 2493332215014630759456647)
        ·
          refine ⟨3739998322521946139184971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493332215014630759456647 3739998322521946139184971)
          ·
            refine ⟨5609997483782919208777457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739998322521946139184971 5609997483782919208777457)
            ·
              refine ⟨4207498112837189406583093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5609997483782919208777457 4207498112837189406583093)
              ·
                refine ⟨394452948078486506867165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4207498112837189406583093 394452948078486506867165)
                ·
                  refine ⟨147919855529432440075187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394452948078486506867165 147919855529432440075187)
                  ·
                    refine ⟨221879783294148660112781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 147919855529432440075187 221879783294148660112781)
                    ·
                      refine ⟨83204918735305747542293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 221879783294148660112781 83204918735305747542293)
                      ·
                        rfl

theorem cell23_162041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_162041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162041 prefixEnd_162041 := by exact prefixLift 162041
  have htrace : WordTrace (prefixWord ++ tailWord_162041) baseStart_162041 baseEnd_162041 := by
    simpa [prefixWord, tailWord_162041, baseEnd_162041] using wordTrace_append hprefix tailTrace_162041
  have hstable : (prefixWord ++ tailWord_162041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162041).length < 2 ^ (prefixWord ++ tailWord_162041).sum := by decide
  have hdescent : baseEnd_162041 < baseStart_162041 := by decide
  rcases family_descends (prefixWord ++ tailWord_162041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162051 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 4, 3, 2]
def baseStart_162051 : Nat := 118140960795 + 162051 * 2 ^ 59
def prefixEnd_162051 : Nat := 4983230072969 + 3 ^ 40 * 162051 * 2
def baseEnd_162051 : Nat := 83210053541850708417247

theorem tailTrace_162051 : CollatzResearch.WordTrace tailWord_162051 prefixEnd_162051 83210053541850708417247 := by
  unfold tailWord_162051
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910485535924377952502007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3940323690616251968334671 5910485535924377952502007)
  ·
    refine ⟨8865728303886566928753011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5910485535924377952502007 8865728303886566928753011)
    ·
      refine ⟨13298592455829850393129517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8865728303886566928753011 13298592455829850393129517)
      ·
        refine ⟨4986972170936193897423569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13298592455829850393129517 4986972170936193897423569)
        ·
          refine ⟨3740229128202145423067677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4986972170936193897423569 3740229128202145423067677)
          ·
            refine ⟨1402585923075804533650379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3740229128202145423067677 1402585923075804533650379)
            ·
              refine ⟨2103878884613706800475569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402585923075804533650379 2103878884613706800475569)
              ·
                refine ⟨1577909163460280100356677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103878884613706800475569 1577909163460280100356677)
                ·
                  refine ⟨295857968148802518816877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577909163460280100356677 295857968148802518816877)
                  ·
                    refine ⟨110946738055800944556329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 295857968148802518816877 110946738055800944556329)
                    ·
                      refine ⟨83210053541850708417247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 110946738055800944556329 83210053541850708417247)
                      ·
                        rfl

theorem cell23_162051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_162051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162051 prefixEnd_162051 := by exact prefixLift 162051
  have htrace : WordTrace (prefixWord ++ tailWord_162051) baseStart_162051 baseEnd_162051 := by
    simpa [prefixWord, tailWord_162051, baseEnd_162051] using wordTrace_append hprefix tailTrace_162051
  have hstable : (prefixWord ++ tailWord_162051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162051).length < 2 ^ (prefixWord ++ tailWord_162051).sum := by decide
  have hdescent : baseEnd_162051 < baseStart_162051 := by decide
  rcases family_descends (prefixWord ++ tailWord_162051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162081 : List Nat := [1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_162081 : Nat := 118140960795 + 162081 * 2 ^ 59
def prefixEnd_162081 : Nat := 4983230072969 + 3 ^ 40 * 162081 * 2
def baseEnd_162081 : Nat := 83225457961485591042109

theorem tailTrace_162081 : CollatzResearch.WordTrace tailWord_162081 prefixEnd_162081 83225457961485591042109 := by
  unfold tailWord_162081
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911579725815693076094097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3941053150543795384062731 5911579725815693076094097)
  ·
    refine ⟨4433684794361769807070573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5911579725815693076094097 4433684794361769807070573)
    ·
      refine ⟨1662631797885663677651465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4433684794361769807070573 1662631797885663677651465)
      ·
        refine ⟨1246973848414247758238599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1662631797885663677651465 1246973848414247758238599)
        ·
          refine ⟨1870460772621371637357899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246973848414247758238599 1870460772621371637357899)
          ·
            refine ⟨2805691158932057456036849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870460772621371637357899 2805691158932057456036849)
            ·
              refine ⟨2104268369199043092027637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805691158932057456036849 2104268369199043092027637)
              ·
                refine ⟨197275159612410289877591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2104268369199043092027637 197275159612410289877591)
                ·
                  refine ⟨295912739418615434816387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197275159612410289877591 295912739418615434816387)
                  ·
                    refine ⟨443869109127923152224581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 295912739418615434816387 443869109127923152224581)
                    ·
                      refine ⟨83225457961485591042109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 443869109127923152224581 83225457961485591042109)
                      ·
                        rfl

theorem cell23_162081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_162081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162081 prefixEnd_162081 := by exact prefixLift 162081
  have htrace : WordTrace (prefixWord ++ tailWord_162081) baseStart_162081 baseEnd_162081 := by
    simpa [prefixWord, tailWord_162081, baseEnd_162081] using wordTrace_append hprefix tailTrace_162081
  have hstable : (prefixWord ++ tailWord_162081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162081).length < 2 ^ (prefixWord ++ tailWord_162081).sum := by decide
  have hdescent : baseEnd_162081 < baseStart_162081 := by decide
  rcases family_descends (prefixWord ++ tailWord_162081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162101 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_162101 : Nat := 118140960795 + 162101 * 2 ^ 59
def prefixEnd_162101 : Nat := 4983230072969 + 3 ^ 40 * 162101 * 2
def baseEnd_162101 : Nat := 83235727574575512792017

theorem tailTrace_162101 : CollatzResearch.WordTrace tailWord_162101 prefixEnd_162101 83235727574575512792017 := by
  unfold tailWord_162101
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912309185743236491822157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3941539457162157661214771 5912309185743236491822157)
  ·
    refine ⟨2217115944653713684433309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5912309185743236491822157 2217115944653713684433309)
    ·
      refine ⟨831418479245142631662491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2217115944653713684433309 831418479245142631662491)
      ·
        refine ⟨1247127718867713947493737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831418479245142631662491 1247127718867713947493737)
        ·
          refine ⟨935345789150785460620303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247127718867713947493737 935345789150785460620303)
          ·
            refine ⟨1403018683726178190930455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935345789150785460620303 1403018683726178190930455)
            ·
              refine ⟨2104528025589267286395683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403018683726178190930455 2104528025589267286395683)
              ·
                refine ⟨3156792038383900929593525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104528025589267286395683 3156792038383900929593525)
                ·
                  refine ⟨295949253598490712149393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3156792038383900929593525 295949253598490712149393)
                  ·
                    refine ⟨221961940198868034112045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 295949253598490712149393 221961940198868034112045)
                    ·
                      refine ⟨83235727574575512792017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 221961940198868034112045 83235727574575512792017)
                      ·
                        rfl

theorem cell23_162101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_162101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162101 prefixEnd_162101 := by exact prefixLift 162101
  have htrace : WordTrace (prefixWord ++ tailWord_162101) baseStart_162101 baseEnd_162101 := by
    simpa [prefixWord, tailWord_162101, baseEnd_162101] using wordTrace_append hprefix tailTrace_162101
  have hstable : (prefixWord ++ tailWord_162101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162101).length < 2 ^ (prefixWord ++ tailWord_162101).sum := by decide
  have hdescent : baseEnd_162101 < baseStart_162101 := by decide
  rcases family_descends (prefixWord ++ tailWord_162101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162104 : List Nat := [2, 1, 2, 1, 3, 1, 5, 8]
def baseStart_162104 : Nat := 118140960795 + 162104 * 2 ^ 59
def prefixEnd_162104 : Nat := 4983230072969 + 3 ^ 40 * 162104 * 2
def baseEnd_162104 : Nat := 3082861778390333372389

theorem tailTrace_162104 : CollatzResearch.WordTrace tailWord_162104 prefixEnd_162104 3082861778390333372389 := by
  unfold tailWord_162104
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956209302366184002090683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3941612403154912002787577 2956209302366184002090683)
  ·
    refine ⟨4434313953549276003136025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2956209302366184002090683 4434313953549276003136025)
    ·
      refine ⟨3325735465161957002352019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4434313953549276003136025 3325735465161957002352019)
      ·
        refine ⟨4988603197742935503528029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325735465161957002352019 4988603197742935503528029)
        ·
          refine ⟨1870726199153600813823011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4988603197742935503528029 1870726199153600813823011)
          ·
            refine ⟨2806089298730401220734517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870726199153600813823011 2806089298730401220734517)
            ·
              refine ⟨263070871755975114443861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2806089298730401220734517 263070871755975114443861)
              ·
                refine ⟨3082861778390333372389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 263070871755975114443861 3082861778390333372389)
                ·
                  rfl

theorem cell23_162104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 8].length) (baseStart_162104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162104 prefixEnd_162104 := by exact prefixLift 162104
  have htrace : WordTrace (prefixWord ++ tailWord_162104) baseStart_162104 baseEnd_162104 := by
    simpa [prefixWord, tailWord_162104, baseEnd_162104] using wordTrace_append hprefix tailTrace_162104
  have hstable : (prefixWord ++ tailWord_162104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162104).length < 2 ^ (prefixWord ++ tailWord_162104).sum := by decide
  have hdescent : baseEnd_162104 < baseStart_162104 := by decide
  rcases family_descends (prefixWord ++ tailWord_162104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162111 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 4]
def baseStart_162111 : Nat := 118140960795 + 162111 * 2 ^ 59
def prefixEnd_162111 : Nat := 4983230072969 + 3 ^ 40 * 162111 * 2
def baseEnd_162111 : Nat := 83240862381120473666971

theorem tailTrace_162111 : CollatzResearch.WordTrace tailWord_162111 prefixEnd_162111 83240862381120473666971 := by
  unfold tailWord_162111
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912673915707008199686187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3941782610471338799790791 5912673915707008199686187)
  ·
    refine ⟨8869010873560512299529281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5912673915707008199686187 8869010873560512299529281)
    ·
      refine ⟨6651758155170384224646961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8869010873560512299529281 6651758155170384224646961)
      ·
        refine ⟨4988818616377788168485221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6651758155170384224646961 4988818616377788168485221)
        ·
          refine ⟨935403490570835281590979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4988818616377788168485221 935403490570835281590979)
          ·
            refine ⟨1403105235856252922386469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935403490570835281590979 1403105235856252922386469)
            ·
              refine ⟨263082231723047422947463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1403105235856252922386469 263082231723047422947463)
              ·
                refine ⟨394623347584571134421195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263082231723047422947463 394623347584571134421195)
                ·
                  refine ⟨591935021376856701631793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394623347584571134421195 591935021376856701631793)
                  ·
                    refine ⟨443951266032642526223845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 591935021376856701631793 443951266032642526223845)
                    ·
                      refine ⟨83240862381120473666971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 443951266032642526223845 83240862381120473666971)
                      ·
                        rfl

theorem cell23_162111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_162111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162111 prefixEnd_162111 := by exact prefixLift 162111
  have htrace : WordTrace (prefixWord ++ tailWord_162111) baseStart_162111 baseEnd_162111 := by
    simpa [prefixWord, tailWord_162111, baseEnd_162111] using wordTrace_append hprefix tailTrace_162111
  have hstable : (prefixWord ++ tailWord_162111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162111).length < 2 ^ (prefixWord ++ tailWord_162111).sum := by decide
  have hdescent : baseEnd_162111 < baseStart_162111 := by decide
  rcases family_descends (prefixWord ++ tailWord_162111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162132 : List Nat := [2, 4, 1, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_162132 : Nat := 118140960795 + 162132 * 2 ^ 59
def prefixEnd_162132 : Nat := 4983230072969 + 3 ^ 40 * 162132 * 2
def baseEnd_162132 : Nat := 83251645474864891504375

theorem tailTrace_162132 : CollatzResearch.WordTrace tailWord_162132 prefixEnd_162132 83251645474864891504375 := by
  unfold tailWord_162132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956719924315464393100325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3942293232420619190800433 2956719924315464393100325)
  ·
    refine ⟨554384985809149573706311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2956719924315464393100325 554384985809149573706311)
    ·
      refine ⟨831577478713724360559467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554384985809149573706311 831577478713724360559467)
      ·
        refine ⟨1247366218070586540839201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831577478713724360559467 1247366218070586540839201)
        ·
          refine ⟨935524663552939905629401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247366218070586540839201 935524663552939905629401)
          ·
            refine ⟨701643497664704929222051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 935524663552939905629401 701643497664704929222051)
            ·
              refine ⟨1052465246497057393833077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701643497664704929222051 1052465246497057393833077)
              ·
                refine ⟨98668616859099130671851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1052465246497057393833077 98668616859099130671851)
                ·
                  refine ⟨148002925288648696007777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98668616859099130671851 148002925288648696007777)
                  ·
                    refine ⟨111002193966486522005833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 148002925288648696007777 111002193966486522005833)
                    ·
                      refine ⟨83251645474864891504375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111002193966486522005833 83251645474864891504375)
                      ·
                        rfl

theorem cell23_162132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_162132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162132 prefixEnd_162132 := by exact prefixLift 162132
  have htrace : WordTrace (prefixWord ++ tailWord_162132) baseStart_162132 baseEnd_162132 := by
    simpa [prefixWord, tailWord_162132, baseEnd_162132] using wordTrace_append hprefix tailTrace_162132
  have hstable : (prefixWord ++ tailWord_162132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162132).length < 2 ^ (prefixWord ++ tailWord_162132).sum := by decide
  have hdescent : baseEnd_162132 < baseStart_162132 := by decide
  rcases family_descends (prefixWord ++ tailWord_162132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162148 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_162148 : Nat := 118140960795 + 162148 * 2 ^ 59
def prefixEnd_162148 : Nat := 4983230072969 + 3 ^ 40 * 162148 * 2
def baseEnd_162148 : Nat := 83259861165336828904301

theorem tailTrace_162148 : CollatzResearch.WordTrace tailWord_162148 prefixEnd_162148 83259861165336828904301 := by
  unfold tailWord_162148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2957011708286481759391549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3942682277715309012522065 2957011708286481759391549)
  ·
    refine ⟨1108879390607430659771831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2957011708286481759391549 1108879390607430659771831)
    ·
      refine ⟨1663319085911145989657747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108879390607430659771831 1663319085911145989657747)
      ·
        refine ⟨2494978628866718984486621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663319085911145989657747 2494978628866718984486621)
        ·
          refine ⟨935616985825019619182483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2494978628866718984486621 935616985825019619182483)
          ·
            refine ⟨1403425478737529428773725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935616985825019619182483 1403425478737529428773725)
            ·
              refine ⟨526284554526573535790147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1403425478737529428773725 526284554526573535790147)
              ·
                refine ⟨789426831789860303685221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526284554526573535790147 789426831789860303685221)
                ·
                  refine ⟨148017530960598806940979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789426831789860303685221 148017530960598806940979)
                  ·
                    refine ⟨222026296440898210411469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148017530960598806940979 222026296440898210411469)
                    ·
                      refine ⟨83259861165336828904301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 222026296440898210411469 83259861165336828904301)
                      ·
                        rfl

theorem cell23_162148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_162148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162148 prefixEnd_162148 := by exact prefixLift 162148
  have htrace : WordTrace (prefixWord ++ tailWord_162148) baseStart_162148 baseEnd_162148 := by
    simpa [prefixWord, tailWord_162148, baseEnd_162148] using wordTrace_append hprefix tailTrace_162148
  have hstable : (prefixWord ++ tailWord_162148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162148).length < 2 ^ (prefixWord ++ tailWord_162148).sum := by decide
  have hdescent : baseEnd_162148 < baseStart_162148 := by decide
  rcases family_descends (prefixWord ++ tailWord_162148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162165 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_162165 : Nat := 118140960795 + 162165 * 2 ^ 59
def prefixEnd_162165 : Nat := 4983230072969 + 3 ^ 40 * 162165 * 2
def baseEnd_162165 : Nat := 83268590336463262391723

theorem tailTrace_162165 : CollatzResearch.WordTrace tailWord_162165 prefixEnd_162165 83268590336463262391723 := by
  unfold tailWord_162165
  simp only [CollatzResearch.WordTrace]
  refine ⟨5914643457511375422151949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3943095638340916948101299 5914643457511375422151949)
  ·
    refine ⟨2217991296566765783306981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5914643457511375422151949 2217991296566765783306981)
    ·
      refine ⟨415873368106268584370059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2217991296566765783306981 415873368106268584370059)
      ·
        refine ⟨623810052159402876555089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415873368106268584370059 623810052159402876555089)
        ·
          refine ⟨467857539119552157416317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 623810052159402876555089 467857539119552157416317)
          ·
            refine ⟨175446577169832059031119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467857539119552157416317 175446577169832059031119)
            ·
              refine ⟨263169865754748088546679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175446577169832059031119 263169865754748088546679)
              ·
                refine ⟨394754798632122132820019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263169865754748088546679 394754798632122132820019)
                ·
                  refine ⟨592132197948183199230029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 394754798632122132820019 592132197948183199230029)
                  ·
                    refine ⟨222049574230568699711261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 592132197948183199230029 222049574230568699711261)
                    ·
                      refine ⟨83268590336463262391723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 222049574230568699711261 83268590336463262391723)
                      ·
                        rfl

theorem cell23_162165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_162165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162165 prefixEnd_162165 := by exact prefixLift 162165
  have htrace : WordTrace (prefixWord ++ tailWord_162165) baseStart_162165 baseEnd_162165 := by
    simpa [prefixWord, tailWord_162165, baseEnd_162165] using wordTrace_append hprefix tailTrace_162165
  have hstable : (prefixWord ++ tailWord_162165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162165).length < 2 ^ (prefixWord ++ tailWord_162165).sum := by decide
  have hdescent : baseEnd_162165 < baseStart_162165 := by decide
  rcases family_descends (prefixWord ++ tailWord_162165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162211 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 7]
def baseStart_162211 : Nat := 118140960795 + 162211 * 2 ^ 59
def prefixEnd_162211 : Nat := 4983230072969 + 3 ^ 40 * 162211 * 2
def baseEnd_162211 : Nat := 9254690049618898046279

theorem tailTrace_162211 : CollatzResearch.WordTrace tailWord_162211 prefixEnd_162211 9254690049618898046279 := by
  unfold tailWord_162211
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916321215344725278326487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3944214143563150185550991 5916321215344725278326487)
  ·
    refine ⟨8874481823017087917489731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5916321215344725278326487 8874481823017087917489731)
    ·
      refine ⟨13311722734525631876234597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8874481823017087917489731 13311722734525631876234597)
      ·
        refine ⟨2495948012723555976793987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13311722734525631876234597 2495948012723555976793987)
        ·
          refine ⟨3743922019085333965190981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495948012723555976793987 3743922019085333965190981)
          ·
            refine ⟨701985378578500118473309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3743922019085333965190981 701985378578500118473309)
            ·
              refine ⟨263244516966937544427491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701985378578500118473309 263244516966937544427491)
              ·
                refine ⟨394866775450406316641237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263244516966937544427491 394866775450406316641237)
                ·
                  refine ⟨9254690049618898046279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 394866775450406316641237 9254690049618898046279)
                  ·
                    rfl

theorem cell23_162211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 7].length) (baseStart_162211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162211 prefixEnd_162211 := by exact prefixLift 162211
  have htrace : WordTrace (prefixWord ++ tailWord_162211) baseStart_162211 baseEnd_162211 := by
    simpa [prefixWord, tailWord_162211, baseEnd_162211] using wordTrace_append hprefix tailTrace_162211
  have hstable : (prefixWord ++ tailWord_162211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162211).length < 2 ^ (prefixWord ++ tailWord_162211).sum := by decide
  have hdescent : baseEnd_162211 < baseStart_162211 := by decide
  rcases family_descends (prefixWord ++ tailWord_162211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162288 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 3, 4]
def baseStart_162288 : Nat := 118140960795 + 162288 * 2 ^ 59
def prefixEnd_162288 : Nat := 4983230072969 + 3 ^ 40 * 162288 * 2
def baseEnd_162288 : Nat := 27777249485655427051219

theorem tailTrace_162288 : CollatzResearch.WordTrace tailWord_162288 prefixEnd_162288 27777249485655427051219 := by
  unfold tailWord_162288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959564818032883714439759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3946086424043844952586345 2959564818032883714439759)
  ·
    refine ⟨4439347227049325571659639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2959564818032883714439759 4439347227049325571659639)
    ·
      refine ⟨6659020840573988357489459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4439347227049325571659639 6659020840573988357489459)
      ·
        refine ⟨9988531260860982536234189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6659020840573988357489459 9988531260860982536234189)
        ·
          refine ⟨3745699222822868451087821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9988531260860982536234189 3745699222822868451087821)
          ·
            refine ⟨1404637208558575669157933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3745699222822868451087821 1404637208558575669157933)
            ·
              refine ⟨526738953209465875934225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1404637208558575669157933 526738953209465875934225)
              ·
                refine ⟨395054214907099406950669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526738953209465875934225 395054214907099406950669)
                ·
                  refine ⟨148145330590162277606501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395054214907099406950669 148145330590162277606501)
                  ·
                    refine ⟨27777249485655427051219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148145330590162277606501 27777249485655427051219)
                    ·
                      rfl

theorem cell23_162288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_162288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162288 prefixEnd_162288 := by exact prefixLift 162288
  have htrace : WordTrace (prefixWord ++ tailWord_162288) baseStart_162288 baseEnd_162288 := by
    simpa [prefixWord, tailWord_162288, baseEnd_162288] using wordTrace_append hprefix tailTrace_162288
  have hstable : (prefixWord ++ tailWord_162288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162288).length < 2 ^ (prefixWord ++ tailWord_162288).sum := by decide
  have hdescent : baseEnd_162288 < baseStart_162288 := by decide
  rcases family_descends (prefixWord ++ tailWord_162288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162298 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_162298 : Nat := 118140960795 + 162298 * 2 ^ 59
def prefixEnd_162298 : Nat := 4983230072969 + 3 ^ 40 * 162298 * 2
def baseEnd_162298 : Nat := 83336883263511242028611

theorem tailTrace_162298 : CollatzResearch.WordTrace tailWord_162298 prefixEnd_162298 83336883263511242028611 := by
  unfold tailWord_162298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479873591507384784185887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3946329577353026091162365 1479873591507384784185887)
  ·
    refine ⟨2219810387261077176278831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1479873591507384784185887 2219810387261077176278831)
    ·
      refine ⟨3329715580891615764418247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2219810387261077176278831 3329715580891615764418247)
      ·
        refine ⟨4994573371337423646627371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3329715580891615764418247 4994573371337423646627371)
        ·
          refine ⟨7491860057006135469941057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4994573371337423646627371 7491860057006135469941057)
          ·
            refine ⟨5618895042754601602455793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7491860057006135469941057 5618895042754601602455793)
            ·
              refine ⟨4214171282065951201841845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5618895042754601602455793 4214171282065951201841845)
              ·
                refine ⟨395078557693682925172673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4214171282065951201841845 395078557693682925172673)
                ·
                  refine ⟨296308918270262193879505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395078557693682925172673 296308918270262193879505)
                  ·
                    refine ⟨222231688702696645409629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 296308918270262193879505 222231688702696645409629)
                    ·
                      refine ⟨83336883263511242028611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 222231688702696645409629 83336883263511242028611)
                      ·
                        rfl

theorem cell23_162298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_162298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162298 prefixEnd_162298 := by exact prefixLift 162298
  have htrace : WordTrace (prefixWord ++ tailWord_162298) baseStart_162298 baseEnd_162298 := by
    simpa [prefixWord, tailWord_162298, baseEnd_162298] using wordTrace_append hprefix tailTrace_162298
  have hstable : (prefixWord ++ tailWord_162298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162298).length < 2 ^ (prefixWord ++ tailWord_162298).sum := by decide
  have hdescent : baseEnd_162298 < baseStart_162298 := by decide
  rcases family_descends (prefixWord ++ tailWord_162298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162301 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 8]
def baseStart_162301 : Nat := 118140960795 + 162301 * 2 ^ 59
def prefixEnd_162301 : Nat := 4983230072969 + 3 ^ 40 * 162301 * 2
def baseEnd_162301 : Nat := 9259824856163858921233

theorem tailTrace_162301 : CollatzResearch.WordTrace tailWord_162301 prefixEnd_162301 9259824856163858921233 := by
  unfold tailWord_162301
  simp only [CollatzResearch.WordTrace]
  refine ⟨5919603785018670649102757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3946402523345780432735171 5919603785018670649102757)
  ·
    refine ⟨1109925709691000746706767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5919603785018670649102757 1109925709691000746706767)
    ·
      refine ⟨1664888564536501120060151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109925709691000746706767 1664888564536501120060151)
      ·
        refine ⟨2497332846804751680090227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664888564536501120060151 2497332846804751680090227)
        ·
          refine ⟨3745999270207127520135341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2497332846804751680090227 3745999270207127520135341)
          ·
            refine ⟨1404749726327672820050753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3745999270207127520135341 1404749726327672820050753)
            ·
              refine ⟨1053562294745754615038065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404749726327672820050753 1053562294745754615038065)
              ·
                refine ⟨790171721059315961278549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053562294745754615038065 790171721059315961278549)
                ·
                  refine ⟨9259824856163858921233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 790171721059315961278549 9259824856163858921233)
                  ·
                    rfl

theorem cell23_162301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_162301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162301 prefixEnd_162301 := by exact prefixLift 162301
  have htrace : WordTrace (prefixWord ++ tailWord_162301) baseStart_162301 baseEnd_162301 := by
    simpa [prefixWord, tailWord_162301, baseEnd_162301] using wordTrace_append hprefix tailTrace_162301
  have hstable : (prefixWord ++ tailWord_162301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162301).length < 2 ^ (prefixWord ++ tailWord_162301).sum := by decide
  have hdescent : baseEnd_162301 < baseStart_162301 := by decide
  rcases family_descends (prefixWord ++ tailWord_162301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162308 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_162308 : Nat := 118140960795 + 162308 * 2 ^ 59
def prefixEnd_162308 : Nat := 4983230072969 + 3 ^ 40 * 162308 * 2
def baseEnd_162308 : Nat := 83342018070056202903565

theorem tailTrace_162308 : CollatzResearch.WordTrace tailWord_162308 prefixEnd_162308 83342018070056202903565 := by
  unfold tailWord_162308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959929547996655422303789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3946572730662207229738385 2959929547996655422303789)
  ·
    refine ⟨1109973580498745783363921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2959929547996655422303789 1109973580498745783363921)
    ·
      refine ⟨832480185374059337522941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109973580498745783363921 832480185374059337522941)
      ·
        refine ⟨312180069515272251571103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 832480185374059337522941 312180069515272251571103)
        ·
          refine ⟨468270104272908377356655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312180069515272251571103 468270104272908377356655)
          ·
            refine ⟨702405156409362566034983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468270104272908377356655 702405156409362566034983)
            ·
              refine ⟨1053607734614043849052475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702405156409362566034983 1053607734614043849052475)
              ·
                refine ⟨1580411601921065773578713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053607734614043849052475 1580411601921065773578713)
                ·
                  refine ⟨1185308701440799330184035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1580411601921065773578713 1185308701440799330184035)
                  ·
                    refine ⟨1777963052161198995276053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185308701440799330184035 1777963052161198995276053)
                    ·
                      refine ⟨83342018070056202903565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1777963052161198995276053 83342018070056202903565)
                      ·
                        rfl

theorem cell23_162308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_162308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162308 prefixEnd_162308 := by exact prefixLift 162308
  have htrace : WordTrace (prefixWord ++ tailWord_162308) baseStart_162308 baseEnd_162308 := by
    simpa [prefixWord, tailWord_162308, baseEnd_162308] using wordTrace_append hprefix tailTrace_162308
  have hstable : (prefixWord ++ tailWord_162308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162308).length < 2 ^ (prefixWord ++ tailWord_162308).sum := by decide
  have hdescent : baseEnd_162308 < baseStart_162308 := by decide
  rcases family_descends (prefixWord ++ tailWord_162308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162318 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_162318 : Nat := 118140960795 + 162318 * 2 ^ 59
def prefixEnd_162318 : Nat := 4983230072969 + 3 ^ 40 * 162318 * 2
def baseEnd_162318 : Nat := 9260794764066795975391

theorem tailTrace_162318 : CollatzResearch.WordTrace tailWord_162318 prefixEnd_162318 9260794764066795975391 := by
  unfold tailWord_162318
  simp only [CollatzResearch.WordTrace]
  refine ⟨740027978244635319058951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3946815883971388368314405 740027978244635319058951)
  ·
    refine ⟨1110041967366952978588427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 740027978244635319058951 1110041967366952978588427)
    ·
      refine ⟨1665062951050429467882641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110041967366952978588427 1665062951050429467882641)
      ·
        refine ⟨1248797213287822100911981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1665062951050429467882641 1248797213287822100911981)
        ·
          refine ⟨468298954982933287841993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1248797213287822100911981 468298954982933287841993)
          ·
            refine ⟨351224216237199965881495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468298954982933287841993 351224216237199965881495)
            ·
              refine ⟨526836324355799948822243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351224216237199965881495 526836324355799948822243)
              ·
                refine ⟨790254486533699923233365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526836324355799948822243 790254486533699923233365)
                ·
                  refine ⟨9260794764066795975391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 790254486533699923233365 9260794764066795975391)
                  ·
                    rfl

theorem cell23_162318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_162318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162318 prefixEnd_162318 := by exact prefixLift 162318
  have htrace : WordTrace (prefixWord ++ tailWord_162318) baseStart_162318 baseEnd_162318 := by
    simpa [prefixWord, tailWord_162318, baseEnd_162318] using wordTrace_append hprefix tailTrace_162318
  have hstable : (prefixWord ++ tailWord_162318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162318).length < 2 ^ (prefixWord ++ tailWord_162318).sum := by decide
  have hdescent : baseEnd_162318 < baseStart_162318 := by decide
  rcases family_descends (prefixWord ++ tailWord_162318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162341 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_162341 : Nat := 118140960795 + 162341 * 2 ^ 59
def prefixEnd_162341 : Nat := 4983230072969 + 3 ^ 40 * 162341 * 2
def baseEnd_162341 : Nat := 83358962931654573790913

theorem tailTrace_162341 : CollatzResearch.WordTrace tailWord_162341 prefixEnd_162341 83358962931654573790913 := by
  unfold tailWord_162341
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921062704873757480558877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3947375136582504987039251 5921062704873757480558877)
  ·
    refine ⟨2220398514327659055209579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5921062704873757480558877 2220398514327659055209579)
    ·
      refine ⟨3330597771491488582814369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220398514327659055209579 3330597771491488582814369)
      ·
        refine ⟨2497948328618616437110777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3330597771491488582814369 2497948328618616437110777)
        ·
          refine ⟨1873461246463962327833083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2497948328618616437110777 1873461246463962327833083)
          ·
            refine ⟨2810191869695943491749625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873461246463962327833083 2810191869695943491749625)
            ·
              refine ⟨2107643902271957618812219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2810191869695943491749625 2107643902271957618812219)
              ·
                refine ⟨3161465853407936428218329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107643902271957618812219 3161465853407936428218329)
                ·
                  refine ⟨2371099390055952321163747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161465853407936428218329 2371099390055952321163747)
                  ·
                    refine ⟨3556649085083928481745621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2371099390055952321163747 3556649085083928481745621)
                    ·
                      refine ⟨83358962931654573790913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3556649085083928481745621 83358962931654573790913)
                      ·
                        rfl

theorem cell23_162341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_162341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162341 prefixEnd_162341 := by exact prefixLift 162341
  have htrace : WordTrace (prefixWord ++ tailWord_162341) baseStart_162341 baseEnd_162341 := by
    simpa [prefixWord, tailWord_162341, baseEnd_162341] using wordTrace_append hprefix tailTrace_162341
  have hstable : (prefixWord ++ tailWord_162341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162341).length < 2 ^ (prefixWord ++ tailWord_162341).sum := by decide
  have hdescent : baseEnd_162341 < baseStart_162341 := by decide
  rcases family_descends (prefixWord ++ tailWord_162341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162351 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_162351 : Nat := 118140960795 + 162351 * 2 ^ 59
def prefixEnd_162351 : Nat := 4983230072969 + 3 ^ 40 * 162351 * 2
def baseEnd_162351 : Nat := 83364097738199534665867

theorem tailTrace_162351 : CollatzResearch.WordTrace tailWord_162351 prefixEnd_162351 83364097738199534665867 := by
  unfold tailWord_162351
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921427434837529188422907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3947618289891686125615271 5921427434837529188422907)
  ·
    refine ⟨8882141152256293782634361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5921427434837529188422907 8882141152256293782634361)
    ·
      refine ⟨6661605864192220336975771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8882141152256293782634361 6661605864192220336975771)
      ·
        refine ⟨9992408796288330505463657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6661605864192220336975771 9992408796288330505463657)
        ·
          refine ⟨7494306597216247879097743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9992408796288330505463657 7494306597216247879097743)
          ·
            refine ⟨11241459895824371818646615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494306597216247879097743 11241459895824371818646615)
            ·
              refine ⟨16862189843736557727969923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11241459895824371818646615 16862189843736557727969923)
              ·
                refine ⟨25293284765604836591954885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16862189843736557727969923 25293284765604836591954885)
                ·
                  refine ⟨4742490893550906860991541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25293284765604836591954885 4742490893550906860991541)
                  ·
                    refine ⟨444608521270397518217957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4742490893550906860991541 444608521270397518217957)
                    ·
                      refine ⟨83364097738199534665867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 444608521270397518217957 83364097738199534665867)
                      ·
                        rfl

theorem cell23_162351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_162351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162351 prefixEnd_162351 := by exact prefixLift 162351
  have htrace : WordTrace (prefixWord ++ tailWord_162351) baseStart_162351 baseEnd_162351 := by
    simpa [prefixWord, tailWord_162351, baseEnd_162351] using wordTrace_append hprefix tailTrace_162351
  have hstable : (prefixWord ++ tailWord_162351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162351).length < 2 ^ (prefixWord ++ tailWord_162351).sum := by decide
  have hdescent : baseEnd_162351 < baseStart_162351 := by decide
  rcases family_descends (prefixWord ++ tailWord_162351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162355 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 2, 3, 2]
def baseStart_162355 : Nat := 118140960795 + 162355 * 2 ^ 59
def prefixEnd_162355 : Nat := 4983230072969 + 3 ^ 40 * 162355 * 2
def baseEnd_162355 : Nat := 83366151660817519015849

theorem tailTrace_162355 : CollatzResearch.WordTrace tailWord_162355 prefixEnd_162355 83366151660817519015849 := by
  unfold tailWord_162355
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921573326823037871568519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3947715551215358581045679 5921573326823037871568519)
  ·
    refine ⟨8882359990234556807352779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5921573326823037871568519 8882359990234556807352779)
    ·
      refine ⟨13323539985351835211029169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8882359990234556807352779 13323539985351835211029169)
      ·
        refine ⟨9992654989013876408271877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13323539985351835211029169 9992654989013876408271877)
        ·
          refine ⟨1873622810440101826550977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9992654989013876408271877 1873622810440101826550977)
          ·
            refine ⟨1405217107830076369913233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873622810440101826550977 1405217107830076369913233)
            ·
              refine ⟨1053912830872557277434925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405217107830076369913233 1053912830872557277434925)
              ·
                refine ⟨395217311577208979038097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053912830872557277434925 395217311577208979038097)
                ·
                  refine ⟨296412983682906734278573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395217311577208979038097 296412983682906734278573)
                  ·
                    refine ⟨111154868881090025354465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296412983682906734278573 111154868881090025354465)
                    ·
                      refine ⟨83366151660817519015849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111154868881090025354465 83366151660817519015849)
                      ·
                        rfl

theorem cell23_162355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3, 2].length) (baseStart_162355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162355 prefixEnd_162355 := by exact prefixLift 162355
  have htrace : WordTrace (prefixWord ++ tailWord_162355) baseStart_162355 baseEnd_162355 := by
    simpa [prefixWord, tailWord_162355, baseEnd_162355] using wordTrace_append hprefix tailTrace_162355
  have hstable : (prefixWord ++ tailWord_162355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162355).length < 2 ^ (prefixWord ++ tailWord_162355).sum := by decide
  have hdescent : baseEnd_162355 < baseStart_162355 := by decide
  rcases family_descends (prefixWord ++ tailWord_162355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162365 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_162365 : Nat := 118140960795 + 162365 * 2 ^ 59
def prefixEnd_162365 : Nat := 4983230072969 + 3 ^ 40 * 162365 * 2
def baseEnd_162365 : Nat := 27790428822454159963601

theorem tailTrace_162365 : CollatzResearch.WordTrace tailWord_162365 prefixEnd_162365 27790428822454159963601 := by
  unfold tailWord_162365
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921938056786809579432549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3947958704524539719621699 5921938056786809579432549)
  ·
    refine ⟨1110363385647526796143603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5921938056786809579432549 1110363385647526796143603)
    ·
      refine ⟨1665545078471290194215405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110363385647526796143603 1665545078471290194215405)
      ·
        refine ⟨624579404426733822830777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1665545078471290194215405 624579404426733822830777)
        ·
          refine ⟨468434553320050367123083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624579404426733822830777 468434553320050367123083)
          ·
            refine ⟨702651829980075550684625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468434553320050367123083 702651829980075550684625)
            ·
              refine ⟨526988872485056663013469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702651829980075550684625 526988872485056663013469)
              ·
                refine ⟨197620827181896248630051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 526988872485056663013469 197620827181896248630051)
                ·
                  refine ⟨296431240772844372945077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197620827181896248630051 296431240772844372945077)
                  ·
                    refine ⟨27790428822454159963601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 296431240772844372945077 27790428822454159963601)
                    ·
                      rfl

theorem cell23_162365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_162365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162365 prefixEnd_162365 := by exact prefixLift 162365
  have htrace : WordTrace (prefixWord ++ tailWord_162365) baseStart_162365 baseEnd_162365 := by
    simpa [prefixWord, tailWord_162365, baseEnd_162365] using wordTrace_append hprefix tailTrace_162365
  have hstable : (prefixWord ++ tailWord_162365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162365).length < 2 ^ (prefixWord ++ tailWord_162365).sum := by decide
  have hdescent : baseEnd_162365 < baseStart_162365 := by decide
  rcases family_descends (prefixWord ++ tailWord_162365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162435 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 3]
def baseStart_162435 : Nat := 118140960795 + 162435 * 2 ^ 59
def prefixEnd_162435 : Nat := 4983230072969 + 3 ^ 40 * 162435 * 2
def baseEnd_162435 : Nat := 83407230113177206015481

theorem tailTrace_162435 : CollatzResearch.WordTrace tailWord_162435 prefixEnd_162435 83407230113177206015481 := by
  unfold tailWord_162435
  simp only [CollatzResearch.WordTrace]
  refine ⟨5924491166533211534480759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3949660777688807689653839 5924491166533211534480759)
  ·
    refine ⟨8886736749799817301721139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5924491166533211534480759 8886736749799817301721139)
    ·
      refine ⟨13330105124699725952581709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886736749799817301721139 13330105124699725952581709)
      ·
        refine ⟨4998789421762397232218141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13330105124699725952581709 4998789421762397232218141)
        ·
          refine ⟨1874546033160898962081803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4998789421762397232218141 1874546033160898962081803)
          ·
            refine ⟨2811819049741348443122705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874546033160898962081803 2811819049741348443122705)
            ·
              refine ⟨2108864287306011332342029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811819049741348443122705 2108864287306011332342029)
              ·
                refine ⟨790824107739754249628261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108864287306011332342029 790824107739754249628261)
                ·
                  refine ⟨148279520201203921805299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790824107739754249628261 148279520201203921805299)
                  ·
                    refine ⟨222419280301805882707949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148279520201203921805299 222419280301805882707949)
                    ·
                      refine ⟨83407230113177206015481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 222419280301805882707949 83407230113177206015481)
                      ·
                        rfl

theorem cell23_162435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_162435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162435 prefixEnd_162435 := by exact prefixLift 162435
  have htrace : WordTrace (prefixWord ++ tailWord_162435) baseStart_162435 baseEnd_162435 := by
    simpa [prefixWord, tailWord_162435, baseEnd_162435] using wordTrace_append hprefix tailTrace_162435
  have hstable : (prefixWord ++ tailWord_162435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162435).length < 2 ^ (prefixWord ++ tailWord_162435).sum := by decide
  have hdescent : baseEnd_162435 < baseStart_162435 := by decide
  rcases family_descends (prefixWord ++ tailWord_162435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162436 : List Nat := [2, 3, 2, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_162436 : Nat := 118140960795 + 162436 * 2 ^ 59
def prefixEnd_162436 : Nat := 4983230072969 + 3 ^ 40 * 162436 * 2
def baseEnd_162436 : Nat := 83407743593831702102977

theorem tailTrace_162436 : CollatzResearch.WordTrace tailWord_162436 prefixEnd_162436 83407743593831702102977 := by
  unfold tailWord_162436
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962263819764794352633581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3949685093019725803511441 2962263819764794352633581)
  ·
    refine ⟨1110848932411797882237593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2962263819764794352633581 1110848932411797882237593)
    ·
      refine ⟨833136699308848411678195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1110848932411797882237593 833136699308848411678195)
      ·
        refine ⟨1249705048963272617517293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833136699308848411678195 1249705048963272617517293)
        ·
          refine ⟨468639393361227231568985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1249705048963272617517293 468639393361227231568985)
          ·
            refine ⟨351479545020920423676739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468639393361227231568985 351479545020920423676739)
            ·
              refine ⟨527219317531380635515109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351479545020920423676739 527219317531380635515109)
              ·
                refine ⟨98853622037133869159083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527219317531380635515109 98853622037133869159083)
                ·
                  refine ⟨148280433055700803738625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98853622037133869159083 148280433055700803738625)
                  ·
                    refine ⟨111210324791775602803969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 148280433055700803738625 111210324791775602803969)
                    ·
                      refine ⟨83407743593831702102977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111210324791775602803969 83407743593831702102977)
                      ·
                        rfl

theorem cell23_162436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_162436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162436 prefixEnd_162436 := by exact prefixLift 162436
  have htrace : WordTrace (prefixWord ++ tailWord_162436) baseStart_162436 baseEnd_162436 := by
    simpa [prefixWord, tailWord_162436, baseEnd_162436] using wordTrace_append hprefix tailTrace_162436
  have hstable : (prefixWord ++ tailWord_162436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162436).length < 2 ^ (prefixWord ++ tailWord_162436).sum := by decide
  have hdescent : baseEnd_162436 < baseStart_162436 := by decide
  rcases family_descends (prefixWord ++ tailWord_162436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162442 : List Nat := [3, 1, 2, 3, 4, 1, 1, 8]
def baseStart_162442 : Nat := 118140960795 + 162442 * 2 ^ 59
def prefixEnd_162442 : Nat := 4983230072969 + 3 ^ 40 * 162442 * 2
def baseEnd_162442 : Nat := 3089289795472543652887

theorem tailTrace_162442 : CollatzResearch.WordTrace tailWord_162442 prefixEnd_162442 3089289795472543652887 := by
  unfold tailWord_162442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481186619376962932496395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3949830985005234486657053 1481186619376962932496395)
  ·
    refine ⟨2221779929065444398744593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1481186619376962932496395 2221779929065444398744593)
    ·
      refine ⟨1666334946799083299058445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2221779929065444398744593 1666334946799083299058445)
      ·
        refine ⟨624875605049656237146917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1666334946799083299058445 624875605049656237146917)
        ·
          refine ⟨117164175946810544465047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 624875605049656237146917 117164175946810544465047)
          ·
            refine ⟨175746263920215816697571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117164175946810544465047 175746263920215816697571)
            ·
              refine ⟨263619395880323725046357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175746263920215816697571 263619395880323725046357)
              ·
                refine ⟨3089289795472543652887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 263619395880323725046357 3089289795472543652887)
                ·
                  rfl

theorem cell23_162442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_162442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162442 prefixEnd_162442 := by exact prefixLift 162442
  have htrace : WordTrace (prefixWord ++ tailWord_162442) baseStart_162442 baseEnd_162442 := by
    simpa [prefixWord, tailWord_162442, baseEnd_162442] using wordTrace_append hprefix tailTrace_162442
  have hstable : (prefixWord ++ tailWord_162442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162442).length < 2 ^ (prefixWord ++ tailWord_162442).sum := by decide
  have hdescent : baseEnd_162442 < baseStart_162442 := by decide
  rcases family_descends (prefixWord ++ tailWord_162442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162452 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_162452 : Nat := 118140960795 + 162452 * 2 ^ 59
def prefixEnd_162452 : Nat := 4983230072969 + 3 ^ 40 * 162452 * 2
def baseEnd_162452 : Nat := 83415959284303639502903

theorem tailTrace_162452 : CollatzResearch.WordTrace tailWord_162452 prefixEnd_162452 83415959284303639502903 := by
  unfold tailWord_162452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962555603735811718924805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3950074138314415625233073 2962555603735811718924805)
  ·
    refine ⟨555479175700464697298401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2962555603735811718924805 555479175700464697298401)
    ·
      refine ⟨416609381775348522973801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 555479175700464697298401 416609381775348522973801)
      ·
        refine ⟨312457036331511392230351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 416609381775348522973801 312457036331511392230351)
        ·
          refine ⟨468685554497267088345527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312457036331511392230351 468685554497267088345527)
          ·
            refine ⟨703028331745900632518291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468685554497267088345527 703028331745900632518291)
            ·
              refine ⟨1054542497618850948777437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703028331745900632518291 1054542497618850948777437)
              ·
                refine ⟨395453436607069105791539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054542497618850948777437 395453436607069105791539)
                ·
                  refine ⟨593180154910603658687309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395453436607069105791539 593180154910603658687309)
                  ·
                    refine ⟨222442558091476372007741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593180154910603658687309 222442558091476372007741)
                    ·
                      refine ⟨83415959284303639502903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 222442558091476372007741 83415959284303639502903)
                      ·
                        rfl

theorem cell23_162452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_162452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162452 prefixEnd_162452 := by exact prefixLift 162452
  have htrace : WordTrace (prefixWord ++ tailWord_162452) baseStart_162452 baseEnd_162452 := by
    simpa [prefixWord, tailWord_162452, baseEnd_162452] using wordTrace_append hprefix tailTrace_162452
  have hstable : (prefixWord ++ tailWord_162452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162452).length < 2 ^ (prefixWord ++ tailWord_162452).sum := by decide
  have hdescent : baseEnd_162452 < baseStart_162452 := by decide
  rcases family_descends (prefixWord ++ tailWord_162452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162468 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_162468 : Nat := 118140960795 + 162468 * 2 ^ 59
def prefixEnd_162468 : Nat := 4983230072969 + 3 ^ 40 * 162468 * 2
def baseEnd_162468 : Nat := 27808058324925192300943

theorem tailTrace_162468 : CollatzResearch.WordTrace tailWord_162468 prefixEnd_162468 27808058324925192300943 := by
  unfold tailWord_162468
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962847387706829085216029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3950463183609105446954705 2962847387706829085216029)
  ·
    refine ⟨1111067770390060906956011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2962847387706829085216029 1111067770390060906956011)
    ·
      refine ⟨1666601655585091360434017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111067770390060906956011 1666601655585091360434017)
      ·
        refine ⟨1249951241688818520325513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1666601655585091360434017 1249951241688818520325513)
        ·
          refine ⟨937463431266613890244135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1249951241688818520325513 937463431266613890244135)
          ·
            refine ⟨1406195146899920835366203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937463431266613890244135 1406195146899920835366203)
            ·
              refine ⟨2109292720349881253049305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406195146899920835366203 2109292720349881253049305)
              ·
                refine ⟨1581969540262410939786979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109292720349881253049305 1581969540262410939786979)
                ·
                  refine ⟨2372954310393616409680469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581969540262410939786979 2372954310393616409680469)
                  ·
                    refine ⟨27808058324925192300943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2372954310393616409680469 27808058324925192300943)
                    ·
                      rfl

theorem cell23_162468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_162468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162468 prefixEnd_162468 := by exact prefixLift 162468
  have htrace : WordTrace (prefixWord ++ tailWord_162468) baseStart_162468 baseEnd_162468 := by
    simpa [prefixWord, tailWord_162468, baseEnd_162468] using wordTrace_append hprefix tailTrace_162468
  have hstable : (prefixWord ++ tailWord_162468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162468).length < 2 ^ (prefixWord ++ tailWord_162468).sum := by decide
  have hdescent : baseEnd_162468 < baseStart_162468 := by decide
  rcases family_descends (prefixWord ++ tailWord_162468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162479 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 1, 3, 2]
def baseStart_162479 : Nat := 118140960795 + 162479 * 2 ^ 59
def prefixEnd_162479 : Nat := 4983230072969 + 3 ^ 40 * 162479 * 2
def baseEnd_162479 : Nat := 83429823261975033865279

theorem tailTrace_162479 : CollatzResearch.WordTrace tailWord_162479 prefixEnd_162479 83429823261975033865279 := by
  unfold tailWord_162479
  simp only [CollatzResearch.WordTrace]
  refine ⟨5926095978373807049082491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3950730652249204699388327 5926095978373807049082491)
  ·
    refine ⟨8889143967560710573623737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5926095978373807049082491 8889143967560710573623737)
    ·
      refine ⟨6666857975670532930217803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8889143967560710573623737 6666857975670532930217803)
      ·
        refine ⟨10000286963505799395326705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666857975670532930217803 10000286963505799395326705)
        ·
          refine ⟨7500215222629349546495029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10000286963505799395326705 7500215222629349546495029)
          ·
            refine ⟨703145177121501519983909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7500215222629349546495029 703145177121501519983909)
            ·
              refine ⟨131839720710281534996983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 703145177121501519983909 131839720710281534996983)
              ·
                refine ⟨197759581065422302495475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131839720710281534996983 197759581065422302495475)
                ·
                  refine ⟨296639371598133453743213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197759581065422302495475 296639371598133453743213)
                  ·
                    refine ⟨111239764349300045153705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 296639371598133453743213 111239764349300045153705)
                    ·
                      refine ⟨83429823261975033865279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111239764349300045153705 83429823261975033865279)
                      ·
                        rfl

theorem cell23_162479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 3, 2].length) (baseStart_162479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162479 prefixEnd_162479 := by exact prefixLift 162479
  have htrace : WordTrace (prefixWord ++ tailWord_162479) baseStart_162479 baseEnd_162479 := by
    simpa [prefixWord, tailWord_162479, baseEnd_162479] using wordTrace_append hprefix tailTrace_162479
  have hstable : (prefixWord ++ tailWord_162479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162479).length < 2 ^ (prefixWord ++ tailWord_162479).sum := by decide
  have hdescent : baseEnd_162479 < baseStart_162479 := by decide
  rcases family_descends (prefixWord ++ tailWord_162479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162485 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_162485 : Nat := 118140960795 + 162485 * 2 ^ 59
def prefixEnd_162485 : Nat := 4983230072969 + 3 ^ 40 * 162485 * 2
def baseEnd_162485 : Nat := 27810968048634003463417

theorem tailTrace_162485 : CollatzResearch.WordTrace tailWord_162485 prefixEnd_162485 27810968048634003463417 := by
  unfold tailWord_162485
  simp only [CollatzResearch.WordTrace]
  refine ⟨5926314816352070073800909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3950876544234713382533939 5926314816352070073800909)
  ·
    refine ⟨2222368056132026277675341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5926314816352070073800909 2222368056132026277675341)
    ·
      refine ⟨833388021049509854128253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2222368056132026277675341 833388021049509854128253)
      ·
        refine ⟨312520507893566195298095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 833388021049509854128253 312520507893566195298095)
        ·
          refine ⟨468780761840349292947143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312520507893566195298095 468780761840349292947143)
          ·
            refine ⟨703171142760523939420715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468780761840349292947143 703171142760523939420715)
            ·
              refine ⟨1054756714140785909131073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703171142760523939420715 1054756714140785909131073)
              ·
                refine ⟨791067535605589431848305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054756714140785909131073 791067535605589431848305)
                ·
                  refine ⟨593300651704192073886229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 791067535605589431848305 593300651704192073886229)
                  ·
                    refine ⟨27810968048634003463417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 593300651704192073886229 27810968048634003463417)
                    ·
                      rfl

theorem cell23_162485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_162485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162485 prefixEnd_162485 := by exact prefixLift 162485
  have htrace : WordTrace (prefixWord ++ tailWord_162485) baseStart_162485 baseEnd_162485 := by
    simpa [prefixWord, tailWord_162485, baseEnd_162485] using wordTrace_append hprefix tailTrace_162485
  have hstable : (prefixWord ++ tailWord_162485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162485).length < 2 ^ (prefixWord ++ tailWord_162485).sum := by decide
  have hdescent : baseEnd_162485 < baseStart_162485 := by decide
  rcases family_descends (prefixWord ++ tailWord_162485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162486 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_162486 : Nat := 118140960795 + 162486 * 2 ^ 59
def prefixEnd_162486 : Nat := 4983230072969 + 3 ^ 40 * 162486 * 2
def baseEnd_162486 : Nat := 83433417626556506477747

theorem tailTrace_162486 : CollatzResearch.WordTrace tailWord_162486 prefixEnd_162486 83433417626556506477747 := by
  unfold tailWord_162486
  simp only [CollatzResearch.WordTrace]
  refine ⟨370396955584277952786707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3950900859565631496391541 370396955584277952786707)
  ·
    refine ⟨555595433376416929180061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 370396955584277952786707 555595433376416929180061)
    ·
      refine ⟨208348287516156348442523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 555595433376416929180061 208348287516156348442523)
      ·
        refine ⟨312522431274234522663785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208348287516156348442523 312522431274234522663785)
        ·
          refine ⟨234391823455675891997839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312522431274234522663785 234391823455675891997839)
          ·
            refine ⟨351587735183513837996759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234391823455675891997839 351587735183513837996759)
            ·
              refine ⟨527381602775270756995139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351587735183513837996759 527381602775270756995139)
              ·
                refine ⟨791072404162906135492709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527381602775270756995139 791072404162906135492709)
                ·
                  refine ⟨148326075780544900404883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 791072404162906135492709 148326075780544900404883)
                  ·
                    refine ⟨222489113670817350607325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148326075780544900404883 222489113670817350607325)
                    ·
                      refine ⟨83433417626556506477747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 222489113670817350607325 83433417626556506477747)
                      ·
                        rfl

theorem cell23_162486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_162486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162486 prefixEnd_162486 := by exact prefixLift 162486
  have htrace : WordTrace (prefixWord ++ tailWord_162486) baseStart_162486 baseEnd_162486 := by
    simpa [prefixWord, tailWord_162486, baseEnd_162486] using wordTrace_append hprefix tailTrace_162486
  have hstable : (prefixWord ++ tailWord_162486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162486).length < 2 ^ (prefixWord ++ tailWord_162486).sum := by decide
  have hdescent : baseEnd_162486 < baseStart_162486 := by decide
  rcases family_descends (prefixWord ++ tailWord_162486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162532 : List Nat := [2, 3, 1, 1, 1, 4, 3, 3, 5]
def baseStart_162532 : Nat := 118140960795 + 162532 * 2 ^ 59
def prefixEnd_162532 : Nat := 4983230072969 + 3 ^ 40 * 162532 * 2
def baseEnd_162532 : Nat := 9273004192962591833615

theorem tailTrace_162532 : CollatzResearch.WordTrace tailWord_162532 prefixEnd_162532 9273004192962591833615 := by
  unfold tailWord_162532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2964014523590898550380925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3952019364787864733841233 2964014523590898550380925)
  ·
    refine ⟨1111505446346586956392847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2964014523590898550380925 1111505446346586956392847)
    ·
      refine ⟨1667258169519880434589271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111505446346586956392847 1667258169519880434589271)
      ·
        refine ⟨2500887254279820651883907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667258169519880434589271 2500887254279820651883907)
        ·
          refine ⟨3751330881419730977825861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500887254279820651883907 3751330881419730977825861)
          ·
            refine ⟨703374540266199558342349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3751330881419730977825861 703374540266199558342349)
            ·
              refine ⟨263765452599824834378381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703374540266199558342349 263765452599824834378381)
              ·
                refine ⟨98912044724934312891893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263765452599824834378381 98912044724934312891893)
                ·
                  refine ⟨9273004192962591833615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98912044724934312891893 9273004192962591833615)
                  ·
                    rfl

theorem cell23_162532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_162532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162532 prefixEnd_162532 := by exact prefixLift 162532
  have htrace : WordTrace (prefixWord ++ tailWord_162532) baseStart_162532 baseEnd_162532 := by
    simpa [prefixWord, tailWord_162532, baseEnd_162532] using wordTrace_append hprefix tailTrace_162532
  have hstable : (prefixWord ++ tailWord_162532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162532).length < 2 ^ (prefixWord ++ tailWord_162532).sum := by decide
  have hdescent : baseEnd_162532 < baseStart_162532 := by decide
  rcases family_descends (prefixWord ++ tailWord_162532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162545 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 2, 5]
def baseStart_162545 : Nat := 118140960795 + 162545 * 2 ^ 59
def prefixEnd_162545 : Nat := 4983230072969 + 3 ^ 40 * 162545 * 2
def baseEnd_162545 : Nat := 27821237661723925213325

theorem tailTrace_162545 : CollatzResearch.WordTrace tailWord_162545 prefixEnd_162545 27821237661723925213325 := by
  unfold tailWord_162545
  simp only [CollatzResearch.WordTrace]
  refine ⟨5928503196134700320985089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3952335464089800213990059 5928503196134700320985089)
  ·
    refine ⟨4446377397101025240738817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5928503196134700320985089 4446377397101025240738817)
    ·
      refine ⟨3334783047825768930554113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4446377397101025240738817 3334783047825768930554113)
      ·
        refine ⟨2501087285869326697915585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3334783047825768930554113 2501087285869326697915585)
        ·
          refine ⟨1875815464401995023436689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2501087285869326697915585 1875815464401995023436689)
          ·
            refine ⟨1406861598301496267577517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875815464401995023436689 1406861598301496267577517)
            ·
              refine ⟨527573099363061100341569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1406861598301496267577517 527573099363061100341569)
              ·
                refine ⟨395679824522295825256177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527573099363061100341569 395679824522295825256177)
                ·
                  refine ⟨296759868391721868942133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 395679824522295825256177 296759868391721868942133)
                  ·
                    refine ⟨27821237661723925213325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 296759868391721868942133 27821237661723925213325)
                    ·
                      rfl

theorem cell23_162545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_162545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162545 prefixEnd_162545 := by exact prefixLift 162545
  have htrace : WordTrace (prefixWord ++ tailWord_162545) baseStart_162545 baseEnd_162545 := by
    simpa [prefixWord, tailWord_162545, baseEnd_162545] using wordTrace_append hprefix tailTrace_162545
  have hstable : (prefixWord ++ tailWord_162545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162545).length < 2 ^ (prefixWord ++ tailWord_162545).sum := by decide
  have hdescent : baseEnd_162545 < baseStart_162545 := by decide
  rcases family_descends (prefixWord ++ tailWord_162545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162575 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 5, 4]
def baseStart_162575 : Nat := 118140960795 + 162575 * 2 ^ 59
def prefixEnd_162575 : Nat := 4983230072969 + 3 ^ 40 * 162575 * 2
def baseEnd_162575 : Nat := 27826372468268886088279

theorem tailTrace_162575 : CollatzResearch.WordTrace tailWord_162575 prefixEnd_162575 27826372468268886088279 := by
  unfold tailWord_162575
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929597386026015444577179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3953064924017343629718119 5929597386026015444577179)
  ·
    refine ⟨8894396079039023166865769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5929597386026015444577179 8894396079039023166865769)
    ·
      refine ⟨6670797059279267375149327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8894396079039023166865769 6670797059279267375149327)
      ·
        refine ⟨10006195588918901062723991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6670797059279267375149327 10006195588918901062723991)
        ·
          refine ⟨15009293383378351594085987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10006195588918901062723991 15009293383378351594085987)
          ·
            refine ⟨22513940075067527391128981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15009293383378351594085987 22513940075067527391128981)
            ·
              refine ⟨1055340941018790346459171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22513940075067527391128981 1055340941018790346459171)
              ·
                refine ⟨1583011411528185519688757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055340941018790346459171 1583011411528185519688757)
                ·
                  refine ⟨148407319830767392470821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1583011411528185519688757 148407319830767392470821)
                  ·
                    refine ⟨27826372468268886088279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148407319830767392470821 27826372468268886088279)
                    ·
                      rfl

theorem cell23_162575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_162575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162575 prefixEnd_162575 := by exact prefixLift 162575
  have htrace : WordTrace (prefixWord ++ tailWord_162575) baseStart_162575 baseEnd_162575 := by
    simpa [prefixWord, tailWord_162575, baseEnd_162575] using wordTrace_append hprefix tailTrace_162575
  have hstable : (prefixWord ++ tailWord_162575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162575).length < 2 ^ (prefixWord ++ tailWord_162575).sum := by decide
  have hdescent : baseEnd_162575 < baseStart_162575 := by decide
  rcases family_descends (prefixWord ++ tailWord_162575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162609 : List Nat := [1, 2, 2, 3, 2, 1, 3, 4, 1, 4]
def baseStart_162609 : Nat := 118140960795 + 162609 * 2 ^ 59
def prefixEnd_162609 : Nat := 4983230072969 + 3 ^ 40 * 162609 * 2
def baseEnd_162609 : Nat := 27832191915686508413227

theorem tailTrace_162609 : CollatzResearch.WordTrace tailWord_162609 prefixEnd_162609 27832191915686508413227 := by
  unfold tailWord_162609
  simp only [CollatzResearch.WordTrace]
  refine ⟨5930837467902839251314881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3953891645268559500876587 5930837467902839251314881)
  ·
    refine ⟨4448128100927129438486161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5930837467902839251314881 4448128100927129438486161)
    ·
      refine ⟨3336096075695347078864621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4448128100927129438486161 3336096075695347078864621)
      ·
        refine ⟨1251036028385755154574233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3336096075695347078864621 1251036028385755154574233)
        ·
          refine ⟨938277021289316365930675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251036028385755154574233 938277021289316365930675)
          ·
            refine ⟨1407415531933974548896013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938277021289316365930675 1407415531933974548896013)
            ·
              refine ⟨527780824475240455836005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1407415531933974548896013 527780824475240455836005)
              ·
                refine ⟨98958904589107585469251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527780824475240455836005 98958904589107585469251)
                ·
                  refine ⟨148438356883661378203877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98958904589107585469251 148438356883661378203877)
                  ·
                    refine ⟨27832191915686508413227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148438356883661378203877 27832191915686508413227)
                    ·
                      rfl

theorem cell23_162609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_162609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162609 prefixEnd_162609 := by exact prefixLift 162609
  have htrace : WordTrace (prefixWord ++ tailWord_162609) baseStart_162609 baseEnd_162609 := by
    simpa [prefixWord, tailWord_162609, baseEnd_162609] using wordTrace_append hprefix tailTrace_162609
  have hstable : (prefixWord ++ tailWord_162609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162609).length < 2 ^ (prefixWord ++ tailWord_162609).sum := by decide
  have hdescent : baseEnd_162609 < baseStart_162609 := by decide
  rcases family_descends (prefixWord ++ tailWord_162609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162675 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5]
def baseStart_162675 : Nat := 118140960795 + 162675 * 2 ^ 59
def prefixEnd_162675 : Nat := 4983230072969 + 3 ^ 40 * 162675 * 2
def baseEnd_162675 : Nat := 83530465470256267014377

theorem tailTrace_162675 : CollatzResearch.WordTrace tailWord_162675 prefixEnd_162675 83530465470256267014377 := by
  unfold tailWord_162675
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933244685663732523217479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3955496457109155015478319 5933244685663732523217479)
  ·
    refine ⟨8899867028495598784826219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5933244685663732523217479 8899867028495598784826219)
    ·
      refine ⟨13349800542743398177239329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8899867028495598784826219 13349800542743398177239329)
      ·
        refine ⟨10012350407057548632929497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13349800542743398177239329 10012350407057548632929497)
        ·
          refine ⟨7509262805293161474697123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10012350407057548632929497 7509262805293161474697123)
          ·
            refine ⟨11263894207939742212045685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7509262805293161474697123 11263894207939742212045685)
            ·
              refine ⟨1055990081994350832379283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11263894207939742212045685 1055990081994350832379283)
              ·
                refine ⟨1583985122991526248568925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055990081994350832379283 1583985122991526248568925)
                ·
                  refine ⟨593994421121822343213347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1583985122991526248568925 593994421121822343213347)
                  ·
                    refine ⟨890991631682733514820021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 593994421121822343213347 890991631682733514820021)
                    ·
                      refine ⟨83530465470256267014377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 890991631682733514820021 83530465470256267014377)
                      ·
                        rfl

theorem cell23_162675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_162675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162675 prefixEnd_162675 := by exact prefixLift 162675
  have htrace : WordTrace (prefixWord ++ tailWord_162675) baseStart_162675 baseEnd_162675 := by
    simpa [prefixWord, tailWord_162675, baseEnd_162675] using wordTrace_append hprefix tailTrace_162675
  have hstable : (prefixWord ++ tailWord_162675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162675).length < 2 ^ (prefixWord ++ tailWord_162675).sum := by decide
  have hdescent : baseEnd_162675 < baseStart_162675 := by decide
  rcases family_descends (prefixWord ++ tailWord_162675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162709 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_162709 : Nat := 118140960795 + 162709 * 2 ^ 59
def prefixEnd_162709 : Nat := 4983230072969 + 3 ^ 40 * 162709 * 2
def baseEnd_162709 : Nat := 83547923812509133989221

theorem tailTrace_162709 : CollatzResearch.WordTrace tailWord_162709 prefixEnd_162709 83547923812509133989221 := by
  unfold tailWord_162709
  simp only [CollatzResearch.WordTrace]
  refine ⟨5934484767540556329955181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3956323178360370886636787 5934484767540556329955181)
  ·
    refine ⟨2225431787827708623733193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5934484767540556329955181 2225431787827708623733193)
    ·
      refine ⟨1669073840870781467799895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2225431787827708623733193 1669073840870781467799895)
      ·
        refine ⟨2503610761306172201699843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669073840870781467799895 2503610761306172201699843)
        ·
          refine ⟨3755416141959258302549765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2503610761306172201699843 3755416141959258302549765)
          ·
            refine ⟨704140526617360931728081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3755416141959258302549765 704140526617360931728081)
            ·
              refine ⟨528105394963020698796061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704140526617360931728081 528105394963020698796061)
              ·
                refine ⟨198039523111132762048523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528105394963020698796061 198039523111132762048523)
                ·
                  refine ⟨297059284666699143072785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198039523111132762048523 297059284666699143072785)
                  ·
                    refine ⟨222794463500024357304589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 297059284666699143072785 222794463500024357304589)
                    ·
                      refine ⟨83547923812509133989221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 222794463500024357304589 83547923812509133989221)
                      ·
                        rfl

theorem cell23_162709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_162709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162709 prefixEnd_162709 := by exact prefixLift 162709
  have htrace : WordTrace (prefixWord ++ tailWord_162709) baseStart_162709 baseEnd_162709 := by
    simpa [prefixWord, tailWord_162709, baseEnd_162709] using wordTrace_append hprefix tailTrace_162709
  have hstable : (prefixWord ++ tailWord_162709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162709).length < 2 ^ (prefixWord ++ tailWord_162709).sum := by decide
  have hdescent : baseEnd_162709 < baseStart_162709 := by decide
  rcases family_descends (prefixWord ++ tailWord_162709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162710 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_162710 : Nat := 118140960795 + 162710 * 2 ^ 59
def prefixEnd_162710 : Nat := 4983230072969 + 3 ^ 40 * 162710 * 2
def baseEnd_162710 : Nat := 83548437293163630076717

theorem tailTrace_162710 : CollatzResearch.WordTrace tailWord_162710 prefixEnd_162710 83548437293163630076717 := by
  unfold tailWord_162710
  simp only [CollatzResearch.WordTrace]
  refine ⟨370907577533558343796349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3956347493691289000494389 370907577533558343796349)
  ·
    refine ⟨139090341575084378923631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 370907577533558343796349 139090341575084378923631)
    ·
      refine ⟨208635512362626568385447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139090341575084378923631 208635512362626568385447)
      ·
        refine ⟨312953268543939852578171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208635512362626568385447 312953268543939852578171)
        ·
          refine ⟨469429902815909778867257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312953268543939852578171 469429902815909778867257)
          ·
            refine ⟨352072427111932334150443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469429902815909778867257 352072427111932334150443)
            ·
              refine ⟨528108640667898501225665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352072427111932334150443 528108640667898501225665)
              ·
                refine ⟨396081480500923875919249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528108640667898501225665 396081480500923875919249)
                ·
                  refine ⟨297061110375692906939437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396081480500923875919249 297061110375692906939437)
                  ·
                    refine ⟨111397916390884840102289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297061110375692906939437 111397916390884840102289)
                    ·
                      refine ⟨83548437293163630076717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111397916390884840102289 83548437293163630076717)
                      ·
                        rfl

theorem cell23_162710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_162710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162710 prefixEnd_162710 := by exact prefixLift 162710
  have htrace : WordTrace (prefixWord ++ tailWord_162710) baseStart_162710 baseEnd_162710 := by
    simpa [prefixWord, tailWord_162710, baseEnd_162710] using wordTrace_append hprefix tailTrace_162710
  have hstable : (prefixWord ++ tailWord_162710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162710).length < 2 ^ (prefixWord ++ tailWord_162710).sum := by decide
  have hdescent : baseEnd_162710 < baseStart_162710 := by decide
  rcases family_descends (prefixWord ++ tailWord_162710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162733 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_162733 : Nat := 118140960795 + 162733 * 2 ^ 59
def prefixEnd_162733 : Nat := 4983230072969 + 3 ^ 40 * 162733 * 2
def baseEnd_162733 : Nat := 27853415782739013363037

theorem tailTrace_162733 : CollatzResearch.WordTrace tailWord_162733 prefixEnd_162733 27853415782739013363037 := by
  unfold tailWord_162733
  simp only [CollatzResearch.WordTrace]
  refine ⟨5935360119453608428828853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3956906746302405619219235 5935360119453608428828853)
  ·
    refine ⟨556440011198775790202705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5935360119453608428828853 556440011198775790202705)
    ·
      refine ⟨417330008399081842652029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 556440011198775790202705 417330008399081842652029)
      ·
        refine ⟨156498753149655690994511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 417330008399081842652029 156498753149655690994511)
        ·
          refine ⟨234748129724483536491767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156498753149655690994511 234748129724483536491767)
          ·
            refine ⟨352122194586725304737651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234748129724483536491767 352122194586725304737651)
            ·
              refine ⟨528183291880087957106477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352122194586725304737651 528183291880087957106477)
              ·
                refine ⟨198068734455032983914929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528183291880087957106477 198068734455032983914929)
                ·
                  refine ⟨148551550841274737936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198068734455032983914929 148551550841274737936197)
                  ·
                    refine ⟨27853415782739013363037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148551550841274737936197 27853415782739013363037)
                    ·
                      rfl

theorem cell23_162733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_162733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162733 prefixEnd_162733 := by exact prefixLift 162733
  have htrace : WordTrace (prefixWord ++ tailWord_162733) baseStart_162733 baseEnd_162733 := by
    simpa [prefixWord, tailWord_162733, baseEnd_162733] using wordTrace_append hprefix tailTrace_162733
  have hstable : (prefixWord ++ tailWord_162733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162733).length < 2 ^ (prefixWord ++ tailWord_162733).sum := by decide
  have hdescent : baseEnd_162733 < baseStart_162733 := by decide
  rcases family_descends (prefixWord ++ tailWord_162733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162735 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_162735 : Nat := 118140960795 + 162735 * 2 ^ 59
def prefixEnd_162735 : Nat := 4983230072969 + 3 ^ 40 * 162735 * 2
def baseEnd_162735 : Nat := 83561274309526032264101

theorem tailTrace_162735 : CollatzResearch.WordTrace tailWord_162735 prefixEnd_162735 83561274309526032264101 := by
  unfold tailWord_162735
  simp only [CollatzResearch.WordTrace]
  refine ⟨5935433065446362770401659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3956955376964241846934439 5935433065446362770401659)
  ·
    refine ⟨8903149598169544155602489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5935433065446362770401659 8903149598169544155602489)
    ·
      refine ⟨6677362198627158116701867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8903149598169544155602489 6677362198627158116701867)
      ·
        refine ⟨10016043297940737175052801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6677362198627158116701867 10016043297940737175052801)
        ·
          refine ⟨7512032473455552881289601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10016043297940737175052801 7512032473455552881289601)
          ·
            refine ⟨5634024355091664660967201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7512032473455552881289601 5634024355091664660967201)
            ·
              refine ⟨4225518266318748495725401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5634024355091664660967201 4225518266318748495725401)
              ·
                refine ⟨3169138699739061371794051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4225518266318748495725401 3169138699739061371794051)
                ·
                  refine ⟨4753708049608592057691077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169138699739061371794051 4753708049608592057691077)
                  ·
                    refine ⟨891320259301611010817077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4753708049608592057691077 891320259301611010817077)
                    ·
                      refine ⟨83561274309526032264101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 891320259301611010817077 83561274309526032264101)
                      ·
                        rfl

theorem cell23_162735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_162735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162735 prefixEnd_162735 := by exact prefixLift 162735
  have htrace : WordTrace (prefixWord ++ tailWord_162735) baseStart_162735 baseEnd_162735 := by
    simpa [prefixWord, tailWord_162735, baseEnd_162735] using wordTrace_append hprefix tailTrace_162735
  have hstable : (prefixWord ++ tailWord_162735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162735).length < 2 ^ (prefixWord ++ tailWord_162735).sum := by decide
  have hdescent : baseEnd_162735 < baseStart_162735 := by decide
  rcases family_descends (prefixWord ++ tailWord_162735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162755 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 1, 8]
def baseStart_162755 : Nat := 118140960795 + 162755 * 2 ^ 59
def prefixEnd_162755 : Nat := 4983230072969 + 3 ^ 40 * 162755 * 2
def baseEnd_162755 : Nat := 27857181307538651338003

theorem tailTrace_162755 : CollatzResearch.WordTrace tailWord_162755 prefixEnd_162755 27857181307538651338003 := by
  unfold tailWord_162755
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936162525373906186129719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3957441683582604124086479 5936162525373906186129719)
  ·
    refine ⟨8904243788060859279194579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5936162525373906186129719 8904243788060859279194579)
    ·
      refine ⟨13356365682091288918791869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904243788060859279194579 13356365682091288918791869)
      ·
        refine ⟨5008637130784233344546951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13356365682091288918791869 5008637130784233344546951)
        ·
          refine ⟨7512955696176350016820427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008637130784233344546951 7512955696176350016820427)
          ·
            refine ⟨11269433544264525025230641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7512955696176350016820427 11269433544264525025230641)
            ·
              refine ⟨8452075158198393768922981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11269433544264525025230641 8452075158198393768922981)
              ·
                refine ⟨1584764092162198831673059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8452075158198393768922981 1584764092162198831673059)
                ·
                  refine ⟨2377146138243298247509589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584764092162198831673059 2377146138243298247509589)
                  ·
                    refine ⟨27857181307538651338003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2377146138243298247509589 27857181307538651338003)
                    ·
                      rfl

theorem cell23_162755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 8].length) (baseStart_162755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162755 prefixEnd_162755 := by exact prefixLift 162755
  have htrace : WordTrace (prefixWord ++ tailWord_162755) baseStart_162755 baseEnd_162755 := by
    simpa [prefixWord, tailWord_162755, baseEnd_162755] using wordTrace_append hprefix tailTrace_162755
  have hstable : (prefixWord ++ tailWord_162755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162755).length < 2 ^ (prefixWord ++ tailWord_162755).sum := by decide
  have hdescent : baseEnd_162755 < baseStart_162755 := by decide
  rcases family_descends (prefixWord ++ tailWord_162755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162773 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_162773 : Nat := 118140960795 + 162773 * 2 ^ 59
def prefixEnd_162773 : Nat := 4983230072969 + 3 ^ 40 * 162773 * 2
def baseEnd_162773 : Nat := 83580786574396883588927

theorem tailTrace_162773 : CollatzResearch.WordTrace tailWord_162773 prefixEnd_162773 83580786574396883588927 := by
  unfold tailWord_162773
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936819039308695260284973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3957879359539130173523315 5936819039308695260284973)
  ·
    refine ⟨2226307139740760722606865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5936819039308695260284973 2226307139740760722606865)
    ·
      refine ⟨1669730354805570541955149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2226307139740760722606865 1669730354805570541955149)
      ·
        refine ⟨626148883052088953233181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1669730354805570541955149 626148883052088953233181)
        ·
          refine ⟨234805831144533357462443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 626148883052088953233181 234805831144533357462443)
          ·
            refine ⟨352208746716800036193665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234805831144533357462443 352208746716800036193665)
            ·
              refine ⟨264156560037600027145249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352208746716800036193665 264156560037600027145249)
              ·
                refine ⟨198117420028200020358937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264156560037600027145249 198117420028200020358937)
                ·
                  refine ⟨148588065021150015269203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198117420028200020358937 148588065021150015269203)
                  ·
                    refine ⟨222882097531725022903805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148588065021150015269203 222882097531725022903805)
                    ·
                      refine ⟨83580786574396883588927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 222882097531725022903805 83580786574396883588927)
                      ·
                        rfl

theorem cell23_162773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_162773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162773 prefixEnd_162773 := by exact prefixLift 162773
  have htrace : WordTrace (prefixWord ++ tailWord_162773) baseStart_162773 baseEnd_162773 := by
    simpa [prefixWord, tailWord_162773, baseEnd_162773] using wordTrace_append hprefix tailTrace_162773
  have hstable : (prefixWord ++ tailWord_162773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162773).length < 2 ^ (prefixWord ++ tailWord_162773).sum := by decide
  have hdescent : baseEnd_162773 < baseStart_162773 := by decide
  rcases family_descends (prefixWord ++ tailWord_162773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162774 : List Nat := [5, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_162774 : Nat := 118140960795 + 162774 * 2 ^ 59
def prefixEnd_162774 : Nat := 4983230072969 + 3 ^ 40 * 162774 * 2
def baseEnd_162774 : Nat := 83581300055051379676423

theorem tailTrace_162774 : CollatzResearch.WordTrace tailWord_162774 prefixEnd_162774 83581300055051379676423 := by
  unfold tailWord_162774
  simp only [CollatzResearch.WordTrace]
  refine ⟨371053469519067026941961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3957903674870048287380917 371053469519067026941961)
  ·
    refine ⟨278290102139300270206471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 371053469519067026941961 278290102139300270206471)
    ·
      refine ⟨417435153208950405309707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278290102139300270206471 417435153208950405309707)
      ·
        refine ⟨626152729813425607964561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417435153208950405309707 626152729813425607964561)
        ·
          refine ⟨469614547360069205973421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626152729813425607964561 469614547360069205973421)
          ·
            refine ⟨176105455260025952240033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 469614547360069205973421 176105455260025952240033)
            ·
              refine ⟨132079091445019464180025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176105455260025952240033 132079091445019464180025)
              ·
                refine ⟨99059318583764598135019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132079091445019464180025 99059318583764598135019)
                ·
                  refine ⟨148588977875646897202529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99059318583764598135019 148588977875646897202529)
                  ·
                    refine ⟨111441733406735172901897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 148588977875646897202529 111441733406735172901897)
                    ·
                      refine ⟨83581300055051379676423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111441733406735172901897 83581300055051379676423)
                      ·
                        rfl

theorem cell23_162774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_162774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162774 prefixEnd_162774 := by exact prefixLift 162774
  have htrace : WordTrace (prefixWord ++ tailWord_162774) baseStart_162774 baseEnd_162774 := by
    simpa [prefixWord, tailWord_162774, baseEnd_162774] using wordTrace_append hprefix tailTrace_162774
  have hstable : (prefixWord ++ tailWord_162774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162774).length < 2 ^ (prefixWord ++ tailWord_162774).sum := by decide
  have hdescent : baseEnd_162774 < baseStart_162774 := by decide
  rcases family_descends (prefixWord ++ tailWord_162774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162792 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_162792 : Nat := 118140960795 + 162792 * 2 ^ 59
def prefixEnd_162792 : Nat := 4983230072969 + 3 ^ 40 * 162792 * 2
def baseEnd_162792 : Nat := 83590542706832309251339

theorem tailTrace_162792 : CollatzResearch.WordTrace tailWord_162792 prefixEnd_162792 83590542706832309251339 := by
  unfold tailWord_162792
  simp only [CollatzResearch.WordTrace]
  refine ⟨2968756013119930752613315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3958341350826574336817753 2968756013119930752613315)
  ·
    refine ⟨4453134019679896128919973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2968756013119930752613315 4453134019679896128919973)
    ·
      refine ⟨834962628689980524172495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4453134019679896128919973 834962628689980524172495)
      ·
        refine ⟨1252443943034970786258743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834962628689980524172495 1252443943034970786258743)
        ·
          refine ⟨1878665914552456179388115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252443943034970786258743 1878665914552456179388115)
          ·
            refine ⟨2817998871828684269082173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878665914552456179388115 2817998871828684269082173)
            ·
              refine ⟨1056749576935756600905815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2817998871828684269082173 1056749576935756600905815)
              ·
                refine ⟨1585124365403634901358723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056749576935756600905815 1585124365403634901358723)
                ·
                  refine ⟨2377686548105452352038085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585124365403634901358723 2377686548105452352038085)
                  ·
                    refine ⟨445816227769772316007141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2377686548105452352038085 445816227769772316007141)
                    ·
                      refine ⟨83590542706832309251339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 445816227769772316007141 83590542706832309251339)
                      ·
                        rfl

theorem cell23_162792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_162792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162792 prefixEnd_162792 := by exact prefixLift 162792
  have htrace : WordTrace (prefixWord ++ tailWord_162792) baseStart_162792 baseEnd_162792 := by
    simpa [prefixWord, tailWord_162792, baseEnd_162792] using wordTrace_append hprefix tailTrace_162792
  have hstable : (prefixWord ++ tailWord_162792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162792).length < 2 ^ (prefixWord ++ tailWord_162792).sum := by decide
  have hdescent : baseEnd_162792 < baseStart_162792 := by decide
  rcases family_descends (prefixWord ++ tailWord_162792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162830 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_162830 : Nat := 118140960795 + 162830 * 2 ^ 59
def prefixEnd_162830 : Nat := 4983230072969 + 3 ^ 40 * 162830 * 2
def baseEnd_162830 : Nat := 83610054971703160576165

theorem tailTrace_162830 : CollatzResearch.WordTrace tailWord_162830 prefixEnd_162830 83610054971703160576165 := by
  unfold tailWord_162830
  simp only [CollatzResearch.WordTrace]
  refine ⟨742362250012774249388743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3959265333401462663406629 742362250012774249388743)
  ·
    refine ⟨1113543375019161374083115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742362250012774249388743 1113543375019161374083115)
    ·
      refine ⟨1670315062528742061124673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1113543375019161374083115 1670315062528742061124673)
      ·
        refine ⟨1252736296896556545843505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1670315062528742061124673 1252736296896556545843505)
        ·
          refine ⟨939552222672417409382629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252736296896556545843505 939552222672417409382629)
          ·
            refine ⟨176166041751078264259243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 939552222672417409382629 176166041751078264259243)
            ·
              refine ⟨264249062626617396388865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176166041751078264259243 264249062626617396388865)
              ·
                refine ⟨198186796969963047291649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264249062626617396388865 198186796969963047291649)
                ·
                  refine ⟨148640097727472285468737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198186796969963047291649 148640097727472285468737)
                  ·
                    refine ⟨111480073295604214101553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 148640097727472285468737 111480073295604214101553)
                    ·
                      refine ⟨83610054971703160576165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111480073295604214101553 83610054971703160576165)
                      ·
                        rfl

theorem cell23_162830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_162830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162830 prefixEnd_162830 := by exact prefixLift 162830
  have htrace : WordTrace (prefixWord ++ tailWord_162830) baseStart_162830 baseEnd_162830 := by
    simpa [prefixWord, tailWord_162830, baseEnd_162830] using wordTrace_append hprefix tailTrace_162830
  have hstable : (prefixWord ++ tailWord_162830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162830).length < 2 ^ (prefixWord ++ tailWord_162830).sum := by decide
  have hdescent : baseEnd_162830 < baseStart_162830 := by decide
  rcases family_descends (prefixWord ++ tailWord_162830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162842 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_162842 : Nat := 118140960795 + 162842 * 2 ^ 59
def prefixEnd_162842 : Nat := 4983230072969 + 3 ^ 40 * 162842 * 2
def baseEnd_162842 : Nat := 83616216739557113626109

theorem tailTrace_162842 : CollatzResearch.WordTrace tailWord_162842 prefixEnd_162842 83616216739557113626109 := by
  unfold tailWord_162842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484833919014680011136695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3959557117372480029697853 1484833919014680011136695)
  ·
    refine ⟨2227250878522020016705043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1484833919014680011136695 2227250878522020016705043)
    ·
      refine ⟨3340876317783030025057565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227250878522020016705043 3340876317783030025057565)
      ·
        refine ⟨1252828619168636259396587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3340876317783030025057565 1252828619168636259396587)
        ·
          refine ⟨1879242928752954389094881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1252828619168636259396587 1879242928752954389094881)
          ·
            refine ⟨1409432196564715791821161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1879242928752954389094881 1409432196564715791821161)
            ·
              refine ⟨1057074147423536843865871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1409432196564715791821161 1057074147423536843865871)
              ·
                refine ⟨1585611221135305265798807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057074147423536843865871 1585611221135305265798807)
                ·
                  refine ⟨2378416831702957898698211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585611221135305265798807 2378416831702957898698211)
                  ·
                    refine ⟨3567625247554436848047317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2378416831702957898698211 3567625247554436848047317)
                    ·
                      refine ⟨83616216739557113626109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3567625247554436848047317 83616216739557113626109)
                      ·
                        rfl

theorem cell23_162842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_162842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162842 prefixEnd_162842 := by exact prefixLift 162842
  have htrace : WordTrace (prefixWord ++ tailWord_162842) baseStart_162842 baseEnd_162842 := by
    simpa [prefixWord, tailWord_162842, baseEnd_162842] using wordTrace_append hprefix tailTrace_162842
  have hstable : (prefixWord ++ tailWord_162842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162842).length < 2 ^ (prefixWord ++ tailWord_162842).sum := by decide
  have hdescent : baseEnd_162842 < baseStart_162842 := by decide
  rcases family_descends (prefixWord ++ tailWord_162842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162869 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_162869 : Nat := 118140960795 + 162869 * 2 ^ 59
def prefixEnd_162869 : Nat := 4983230072969 + 3 ^ 40 * 162869 * 2
def baseEnd_162869 : Nat := 83630080717228507988485

theorem tailTrace_162869 : CollatzResearch.WordTrace tailWord_162869 prefixEnd_162869 83630080717228507988485 := by
  unfold tailWord_162869
  simp only [CollatzResearch.WordTrace]
  refine ⟨5940320446960903655779661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3960213631307269103853107 5940320446960903655779661)
  ·
    refine ⟨2227620167610338870917373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5940320446960903655779661 2227620167610338870917373)
    ·
      refine ⟨835357562853877076594015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2227620167610338870917373 835357562853877076594015)
      ·
        refine ⟨1253036344280815614891023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835357562853877076594015 1253036344280815614891023)
        ·
          refine ⟨1879554516421223422336535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253036344280815614891023 1879554516421223422336535)
          ·
            refine ⟨2819331774631835133504803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879554516421223422336535 2819331774631835133504803)
            ·
              refine ⟨4228997661947752700257205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819331774631835133504803 4228997661947752700257205)
              ·
                refine ⟨396468530807601815649113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4228997661947752700257205 396468530807601815649113)
                ·
                  refine ⟨297351398105701361736835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396468530807601815649113 297351398105701361736835)
                  ·
                    refine ⟨446027097158552042605253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 297351398105701361736835 446027097158552042605253)
                    ·
                      refine ⟨83630080717228507988485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 446027097158552042605253 83630080717228507988485)
                      ·
                        rfl

theorem cell23_162869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_162869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162869 prefixEnd_162869 := by exact prefixLift 162869
  have htrace : WordTrace (prefixWord ++ tailWord_162869) baseStart_162869 baseEnd_162869 := by
    simpa [prefixWord, tailWord_162869, baseEnd_162869] using wordTrace_append hprefix tailTrace_162869
  have hstable : (prefixWord ++ tailWord_162869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162869).length < 2 ^ (prefixWord ++ tailWord_162869).sum := by decide
  have hdescent : baseEnd_162869 < baseStart_162869 := by decide
  rcases family_descends (prefixWord ++ tailWord_162869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162896 : List Nat := [2, 1, 1, 1, 1, 3, 1, 8, 1, 4]
def baseStart_162896 : Nat := 118140960795 + 162896 * 2 ^ 59
def prefixEnd_162896 : Nat := 4983230072969 + 3 ^ 40 * 162896 * 2
def baseEnd_162896 : Nat := 27881314898299967450287

theorem tailTrace_162896 : CollatzResearch.WordTrace tailWord_162896 prefixEnd_162896 27881314898299967450287 := by
  unfold tailWord_162896
  simp only [CollatzResearch.WordTrace]
  refine ⟨2970652608931543633506271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3960870145242058178008361 2970652608931543633506271)
  ·
    refine ⟨4455978913397315450259407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2970652608931543633506271 4455978913397315450259407)
    ·
      refine ⟨6683968370095973175389111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455978913397315450259407 6683968370095973175389111)
      ·
        refine ⟨10025952555143959763083667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6683968370095973175389111 10025952555143959763083667)
        ·
          refine ⟨15038928832715939644625501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10025952555143959763083667 15038928832715939644625501)
          ·
            refine ⟨5639598312268477366734563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15038928832715939644625501 5639598312268477366734563)
            ·
              refine ⟨8459397468402716050101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639598312268477366734563 8459397468402716050101845)
              ·
                refine ⟨99133564082844328712131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8459397468402716050101845 99133564082844328712131)
                ·
                  refine ⟨148700346124266493068197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99133564082844328712131 148700346124266493068197)
                  ·
                    refine ⟨27881314898299967450287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148700346124266493068197 27881314898299967450287)
                    ·
                      rfl

theorem cell23_162896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 4].length) (baseStart_162896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162896 prefixEnd_162896 := by exact prefixLift 162896
  have htrace : WordTrace (prefixWord ++ tailWord_162896) baseStart_162896 baseEnd_162896 := by
    simpa [prefixWord, tailWord_162896, baseEnd_162896] using wordTrace_append hprefix tailTrace_162896
  have hstable : (prefixWord ++ tailWord_162896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162896).length < 2 ^ (prefixWord ++ tailWord_162896).sum := by decide
  have hdescent : baseEnd_162896 < baseStart_162896 := by decide
  rcases family_descends (prefixWord ++ tailWord_162896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162939 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 1, 5]
def baseStart_162939 : Nat := 118140960795 + 162939 * 2 ^ 59
def prefixEnd_162939 : Nat := 4983230072969 + 3 ^ 40 * 162939 * 2
def baseEnd_162939 : Nat := 27888674787681078037721

theorem tailTrace_162939 : CollatzResearch.WordTrace tailWord_162939 prefixEnd_162939 27888674787681078037721 := by
  unfold tailWord_162939
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942873556707305610827871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3961915704471537073885247 5942873556707305610827871)
  ·
    refine ⟨8914310335060958416241807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5942873556707305610827871 8914310335060958416241807)
    ·
      refine ⟨13371465502591437624362711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8914310335060958416241807 13371465502591437624362711)
      ·
        refine ⟨20057198253887156436544067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13371465502591437624362711 20057198253887156436544067)
        ·
          refine ⟨30085797380830734654816101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20057198253887156436544067 30085797380830734654816101)
          ·
            refine ⟨5641087008905762747778019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30085797380830734654816101 5641087008905762747778019)
            ·
              refine ⟨8461630513358644121667029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641087008905762747778019 8461630513358644121667029)
              ·
                refine ⟨198319465156843221601571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8461630513358644121667029 198319465156843221601571)
                ·
                  refine ⟨297479197735264832402357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198319465156843221601571 297479197735264832402357)
                  ·
                    refine ⟨27888674787681078037721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 297479197735264832402357 27888674787681078037721)
                    ·
                      rfl

theorem cell23_162939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 5].length) (baseStart_162939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162939 prefixEnd_162939 := by exact prefixLift 162939
  have htrace : WordTrace (prefixWord ++ tailWord_162939) baseStart_162939 baseEnd_162939 := by
    simpa [prefixWord, tailWord_162939, baseEnd_162939] using wordTrace_append hprefix tailTrace_162939
  have hstable : (prefixWord ++ tailWord_162939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162939).length < 2 ^ (prefixWord ++ tailWord_162939).sum := by decide
  have hdescent : baseEnd_162939 < baseStart_162939 := by decide
  rcases family_descends (prefixWord ++ tailWord_162939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162969 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 8, 4]
def baseStart_162969 : Nat := 118140960795 + 162969 * 2 ^ 59
def prefixEnd_162969 : Nat := 4983230072969 + 3 ^ 40 * 162969 * 2
def baseEnd_162969 : Nat := 27893809594226038912675

theorem tailTrace_162969 : CollatzResearch.WordTrace tailWord_162969 prefixEnd_162969 27893809594226038912675 := by
  unfold tailWord_162969
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943967746598620734419961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3962645164399080489613307 5943967746598620734419961)
  ·
    refine ⟨4457975809948965550814971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5943967746598620734419961 4457975809948965550814971)
    ·
      refine ⟨6686963714923448326222457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4457975809948965550814971 6686963714923448326222457)
      ·
        refine ⟨5015222786192586244666843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6686963714923448326222457 5015222786192586244666843)
        ·
          refine ⟨7522834179288879367000265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5015222786192586244666843 7522834179288879367000265)
          ·
            refine ⟨5642125634466659525250199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7522834179288879367000265 5642125634466659525250199)
            ·
              refine ⟨8463188451699989287875299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642125634466659525250199 8463188451699989287875299)
              ·
                refine ⟨12694782677549983931812949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8463188451699989287875299 12694782677549983931812949)
                ·
                  refine ⟨148766984502538874200933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12694782677549983931812949 148766984502538874200933)
                  ·
                    refine ⟨27893809594226038912675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148766984502538874200933 27893809594226038912675)
                    ·
                      rfl

theorem cell23_162969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_162969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162969 prefixEnd_162969 := by exact prefixLift 162969
  have htrace : WordTrace (prefixWord ++ tailWord_162969) baseStart_162969 baseEnd_162969 := by
    simpa [prefixWord, tailWord_162969, baseEnd_162969] using wordTrace_append hprefix tailTrace_162969
  have hstable : (prefixWord ++ tailWord_162969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162969).length < 2 ^ (prefixWord ++ tailWord_162969).sum := by decide
  have hdescent : baseEnd_162969 < baseStart_162969 := by decide
  rcases family_descends (prefixWord ++ tailWord_162969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162976 : List Nat := [2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4]
def baseStart_162976 : Nat := 118140960795 + 162976 * 2 ^ 59
def prefixEnd_162976 : Nat := 4983230072969 + 3 ^ 40 * 162976 * 2
def baseEnd_162976 : Nat := 83685023147259589350493

theorem tailTrace_162976 : CollatzResearch.WordTrace tailWord_162976 prefixEnd_162976 83685023147259589350493 := by
  unfold tailWord_162976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972111528786630464962391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3962815371715507286616521 2972111528786630464962391)
  ·
    refine ⟨4458167293179945697443587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2972111528786630464962391 4458167293179945697443587)
    ·
      refine ⟨6687250939769918546165381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4458167293179945697443587 6687250939769918546165381)
      ·
        refine ⟨1253859551206859727406009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6687250939769918546165381 1253859551206859727406009)
        ·
          refine ⟨940394663405144795554507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253859551206859727406009 940394663405144795554507)
          ·
            refine ⟨1410591995107717193331761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940394663405144795554507 1410591995107717193331761)
            ·
              refine ⟨1057943996330787894998821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410591995107717193331761 1057943996330787894998821)
              ·
                refine ⟨198364499312022730312279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1057943996330787894998821 198364499312022730312279)
                ·
                  refine ⟨297546748968034095468419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198364499312022730312279 297546748968034095468419)
                  ·
                    refine ⟨446320123452051143202629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 297546748968034095468419 446320123452051143202629)
                    ·
                      refine ⟨83685023147259589350493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 446320123452051143202629 83685023147259589350493)
                      ·
                        rfl

theorem cell23_162976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_162976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162976 prefixEnd_162976 := by exact prefixLift 162976
  have htrace : WordTrace (prefixWord ++ tailWord_162976) baseStart_162976 baseEnd_162976 := by
    simpa [prefixWord, tailWord_162976, baseEnd_162976] using wordTrace_append hprefix tailTrace_162976
  have hstable : (prefixWord ++ tailWord_162976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162976).length < 2 ^ (prefixWord ++ tailWord_162976).sum := by decide
  have hdescent : baseEnd_162976 < baseStart_162976 := by decide
  rcases family_descends (prefixWord ++ tailWord_162976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162980 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_162980 : Nat := 118140960795 + 162980 * 2 ^ 59
def prefixEnd_162980 : Nat := 4983230072969 + 3 ^ 40 * 162980 * 2
def baseEnd_162980 : Nat := 83687077069877573700475

theorem tailTrace_162980 : CollatzResearch.WordTrace tailWord_162980 prefixEnd_162980 83687077069877573700475 := by
  unfold tailWord_162980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972184474779384806535197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3962912633039179742046929 2972184474779384806535197)
  ·
    refine ⟨1114569178042269302450699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2972184474779384806535197 1114569178042269302450699)
    ·
      refine ⟨1671853767063403953676049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114569178042269302450699 1671853767063403953676049)
      ·
        refine ⟨1253890325297552965257037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1671853767063403953676049 1253890325297552965257037)
        ·
          refine ⟨470208871986582361971389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1253890325297552965257037 470208871986582361971389)
          ·
            refine ⟨176328326994968385739271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470208871986582361971389 176328326994968385739271)
            ·
              refine ⟨264492490492452578608907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176328326994968385739271 264492490492452578608907)
              ·
                refine ⟨396738735738678867913361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264492490492452578608907 396738735738678867913361)
                ·
                  refine ⟨297554051804009150935021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 396738735738678867913361 297554051804009150935021)
                  ·
                    refine ⟨111582769426503431600633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 297554051804009150935021 111582769426503431600633)
                    ·
                      refine ⟨83687077069877573700475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111582769426503431600633 83687077069877573700475)
                      ·
                        rfl

theorem cell23_162980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_162980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162980 prefixEnd_162980 := by exact prefixLift 162980
  have htrace : WordTrace (prefixWord ++ tailWord_162980) baseStart_162980 baseEnd_162980 := by
    simpa [prefixWord, tailWord_162980, baseEnd_162980] using wordTrace_append hprefix tailTrace_162980
  have hstable : (prefixWord ++ tailWord_162980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162980).length < 2 ^ (prefixWord ++ tailWord_162980).sum := by decide
  have hdescent : baseEnd_162980 < baseStart_162980 := by decide
  rcases family_descends (prefixWord ++ tailWord_162980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162993 : List Nat := [1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_162993 : Nat := 118140960795 + 162993 * 2 ^ 59
def prefixEnd_162993 : Nat := 4983230072969 + 3 ^ 40 * 162993 * 2
def baseEnd_162993 : Nat := 83693752318386022837915

theorem tailTrace_162993 : CollatzResearch.WordTrace tailWord_162993 prefixEnd_162993 83693752318386022837915 := by
  unfold tailWord_162993
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944843098511672833293633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3963228732341115222195755 5944843098511672833293633)
  ·
    refine ⟨4458632323883754624970225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5944843098511672833293633 4458632323883754624970225)
    ·
      refine ⟨3343974242912815968727669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4458632323883754624970225 3343974242912815968727669)
      ·
        refine ⟨313497585273076497068219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3343974242912815968727669 313497585273076497068219)
        ·
          refine ⟨470246377909614745602329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313497585273076497068219 470246377909614745602329)
          ·
            refine ⟨352684783432211059201747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470246377909614745602329 352684783432211059201747)
            ·
              refine ⟨529027175148316588802621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352684783432211059201747 529027175148316588802621)
              ·
                refine ⟨198385190680618720800983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 529027175148316588802621 198385190680618720800983)
                ·
                  refine ⟨297577786020928081201475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198385190680618720800983 297577786020928081201475)
                  ·
                    refine ⟨446366679031392121802213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 297577786020928081201475 446366679031392121802213)
                    ·
                      refine ⟨83693752318386022837915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 446366679031392121802213 83693752318386022837915)
                      ·
                        rfl

theorem cell23_162993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_162993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_162993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_162993 prefixEnd_162993 := by exact prefixLift 162993
  have htrace : WordTrace (prefixWord ++ tailWord_162993) baseStart_162993 baseEnd_162993 := by
    simpa [prefixWord, tailWord_162993, baseEnd_162993] using wordTrace_append hprefix tailTrace_162993
  have hstable : (prefixWord ++ tailWord_162993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162993).length < 2 ^ (prefixWord ++ tailWord_162993).sum := by decide
  have hdescent : baseEnd_162993 < baseStart_162993 := by decide
  rcases family_descends (prefixWord ++ tailWord_162993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163039 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_163039 : Nat := 118140960795 + 163039 * 2 ^ 59
def prefixEnd_163039 : Nat := 4983230072969 + 3 ^ 40 * 163039 * 2
def baseEnd_163039 : Nat := 83717372428492842862703

theorem tailTrace_163039 : CollatzResearch.WordTrace tailWord_163039 prefixEnd_163039 83717372428492842862703 := by
  unfold tailWord_163039
  simp only [CollatzResearch.WordTrace]
  refine ⟨5946520856345022689468171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3964347237563348459645447 5946520856345022689468171)
  ·
    refine ⟨8919781284517534034202257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5946520856345022689468171 8919781284517534034202257)
    ·
      refine ⟨6689835963388150525651693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8919781284517534034202257 6689835963388150525651693)
      ·
        refine ⟨2508688486270556447119385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6689835963388150525651693 2508688486270556447119385)
        ·
          refine ⟨1881516364702917335339539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2508688486270556447119385 1881516364702917335339539)
          ·
            refine ⟨2822274547054376003009309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881516364702917335339539 2822274547054376003009309)
            ·
              refine ⟨1058352955145391001128491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2822274547054376003009309 1058352955145391001128491)
              ·
                refine ⟨1587529432718086501692737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058352955145391001128491 1587529432718086501692737)
                ·
                  refine ⟨1190647074538564876269553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1587529432718086501692737 1190647074538564876269553)
                  ·
                    refine ⟨892985305903923657202165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1190647074538564876269553 892985305903923657202165)
                    ·
                      refine ⟨83717372428492842862703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 892985305903923657202165 83717372428492842862703)
                      ·
                        rfl

theorem cell23_163039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_163039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163039 prefixEnd_163039 := by exact prefixLift 163039
  have htrace : WordTrace (prefixWord ++ tailWord_163039) baseStart_163039 baseEnd_163039 := by
    simpa [prefixWord, tailWord_163039, baseEnd_163039] using wordTrace_append hprefix tailTrace_163039
  have hstable : (prefixWord ++ tailWord_163039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163039).length < 2 ^ (prefixWord ++ tailWord_163039).sum := by decide
  have hdescent : baseEnd_163039 < baseStart_163039 := by decide
  rcases family_descends (prefixWord ++ tailWord_163039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163086 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_163086 : Nat := 118140960795 + 163086 * 2 ^ 59
def prefixEnd_163086 : Nat := 4983230072969 + 3 ^ 40 * 163086 * 2
def baseEnd_163086 : Nat := 83741506019254158974987

theorem tailTrace_163086 : CollatzResearch.WordTrace tailWord_163086 prefixEnd_163086 83741506019254158974987 := by
  unfold tailWord_163086
  simp only [CollatzResearch.WordTrace]
  refine ⟨743529385896843714553639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3965490058116499810952741 743529385896843714553639)
  ·
    refine ⟨1115294078845265571830459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 743529385896843714553639 1115294078845265571830459)
    ·
      refine ⟨1672941118267898357745689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115294078845265571830459 1672941118267898357745689)
      ·
        refine ⟨1254705838700923768309267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1672941118267898357745689 1254705838700923768309267)
        ·
          refine ⟨1882058758051385652463901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254705838700923768309267 1882058758051385652463901)
          ·
            refine ⟨705772034269269619673963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1882058758051385652463901 705772034269269619673963)
            ·
              refine ⟨1058658051403904429510945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705772034269269619673963 1058658051403904429510945)
              ·
                refine ⟨793993538552928322133209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058658051403904429510945 793993538552928322133209)
                ·
                  refine ⟨595495153914696241599907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 793993538552928322133209 595495153914696241599907)
                  ·
                    refine ⟨893242730872044362399861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 595495153914696241599907 893242730872044362399861)
                    ·
                      refine ⟨83741506019254158974987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 893242730872044362399861 83741506019254158974987)
                      ·
                        rfl

theorem cell23_163086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_163086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163086 prefixEnd_163086 := by exact prefixLift 163086
  have htrace : WordTrace (prefixWord ++ tailWord_163086) baseStart_163086 baseEnd_163086 := by
    simpa [prefixWord, tailWord_163086, baseEnd_163086] using wordTrace_append hprefix tailTrace_163086
  have hstable : (prefixWord ++ tailWord_163086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163086).length < 2 ^ (prefixWord ++ tailWord_163086).sum := by decide
  have hdescent : baseEnd_163086 < baseStart_163086 := by decide
  rcases family_descends (prefixWord ++ tailWord_163086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163089 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 9]
def baseStart_163089 : Nat := 118140960795 + 163089 * 2 ^ 59
def prefixEnd_163089 : Nat := 4983230072969 + 3 ^ 40 * 163089 * 2
def baseEnd_163089 : Nat := 9304782940135294137497

theorem tailTrace_163089 : CollatzResearch.WordTrace tailWord_163089 prefixEnd_163089 9304782940135294137497 := by
  unfold tailWord_163089
  simp only [CollatzResearch.WordTrace]
  refine ⟨5948344506163881228788321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3965563004109254152525547 5948344506163881228788321)
  ·
    refine ⟨4461258379622910921591241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5948344506163881228788321 4461258379622910921591241)
    ·
      refine ⟨3345943784717183191193431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4461258379622910921591241 3345943784717183191193431)
      ·
        refine ⟨5018915677075774786790147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345943784717183191193431 5018915677075774786790147)
        ·
          refine ⟨7528373515613662180185221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5018915677075774786790147 7528373515613662180185221)
          ·
            refine ⟨1411570034177561658784729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7528373515613662180185221 1411570034177561658784729)
            ·
              refine ⟨1058677525633171244088547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411570034177561658784729 1058677525633171244088547)
              ·
                refine ⟨1588016288449756866132821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058677525633171244088547 1588016288449756866132821)
                ·
                  refine ⟨9304782940135294137497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1588016288449756866132821 9304782940135294137497)
                  ·
                    rfl

theorem cell23_163089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 9].length) (baseStart_163089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163089 prefixEnd_163089 := by exact prefixLift 163089
  have htrace : WordTrace (prefixWord ++ tailWord_163089) baseStart_163089 baseEnd_163089 := by
    simpa [prefixWord, tailWord_163089, baseEnd_163089] using wordTrace_append hprefix tailTrace_163089
  have hstable : (prefixWord ++ tailWord_163089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163089).length < 2 ^ (prefixWord ++ tailWord_163089).sum := by decide
  have hdescent : baseEnd_163089 < baseStart_163089 := by decide
  rcases family_descends (prefixWord ++ tailWord_163089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163116 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_163116 : Nat := 118140960795 + 163116 * 2 ^ 59
def prefixEnd_163116 : Nat := 4983230072969 + 3 ^ 40 * 163116 * 2
def baseEnd_163116 : Nat := 83756910438889041599849

theorem tailTrace_163116 : CollatzResearch.WordTrace tailWord_163116 prefixEnd_163116 83756910438889041599849 := by
  unfold tailWord_163116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974664638533032420010601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3966219518044043226680801 2974664638533032420010601)
  ·
    refine ⟨2230998478899774315007951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2974664638533032420010601 2230998478899774315007951)
    ·
      refine ⟨3346497718349661472511927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230998478899774315007951 3346497718349661472511927)
      ·
        refine ⟨5019746577524492208767891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3346497718349661472511927 5019746577524492208767891)
        ·
          refine ⟨7529619866286738313151837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5019746577524492208767891 7529619866286738313151837)
          ·
            refine ⟨2823607449857526867431939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7529619866286738313151837 2823607449857526867431939)
            ·
              refine ⟨4235411174786290301147909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823607449857526867431939 4235411174786290301147909)
              ·
                refine ⟨794139595272429431465233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4235411174786290301147909 794139595272429431465233)
                ·
                  refine ⟨595604696454322073598925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 794139595272429431465233 595604696454322073598925)
                  ·
                    refine ⟨223351761170370777599597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595604696454322073598925 223351761170370777599597)
                    ·
                      refine ⟨83756910438889041599849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 223351761170370777599597 83756910438889041599849)
                      ·
                        rfl

theorem cell23_163116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_163116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163116 prefixEnd_163116 := by exact prefixLift 163116
  have htrace : WordTrace (prefixWord ++ tailWord_163116) baseStart_163116 baseEnd_163116 := by
    simpa [prefixWord, tailWord_163116, baseEnd_163116] using wordTrace_append hprefix tailTrace_163116
  have hstable : (prefixWord ++ tailWord_163116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163116).length < 2 ^ (prefixWord ++ tailWord_163116).sum := by decide
  have hdescent : baseEnd_163116 < baseStart_163116 := by decide
  rcases family_descends (prefixWord ++ tailWord_163116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163119 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 3, 7]
def baseStart_163119 : Nat := 118140960795 + 163119 * 2 ^ 59
def prefixEnd_163119 : Nat := 4983230072969 + 3 ^ 40 * 163119 * 2
def baseEnd_163119 : Nat := 27919483626950843287445

theorem tailTrace_163119 : CollatzResearch.WordTrace tailWord_163119 prefixEnd_163119 27919483626950843287445 := by
  unfold tailWord_163119
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949438696055196352380411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3966292464036797568253607 5949438696055196352380411)
  ·
    refine ⟨8924158044082794528570617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5949438696055196352380411 8924158044082794528570617)
    ·
      refine ⟨6693118533062095896427963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8924158044082794528570617 6693118533062095896427963)
      ·
        refine ⟨10039677799593143844641945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6693118533062095896427963 10039677799593143844641945)
        ·
          refine ⟨7529758349694857883481459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10039677799593143844641945 7529758349694857883481459)
          ·
            refine ⟨11294637524542286825222189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529758349694857883481459 11294637524542286825222189)
            ·
              refine ⟨4235489071703357559458321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11294637524542286825222189 4235489071703357559458321)
              ·
                refine ⟨3176616803777518169593741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4235489071703357559458321 3176616803777518169593741)
                ·
                  refine ⟨1191231301416569313597653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3176616803777518169593741 1191231301416569313597653)
                  ·
                    refine ⟨27919483626950843287445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1191231301416569313597653 27919483626950843287445)
                    ·
                      rfl

theorem cell23_163119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_163119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163119 prefixEnd_163119 := by exact prefixLift 163119
  have htrace : WordTrace (prefixWord ++ tailWord_163119) baseStart_163119 baseEnd_163119 := by
    simpa [prefixWord, tailWord_163119, baseEnd_163119] using wordTrace_append hprefix tailTrace_163119
  have hstable : (prefixWord ++ tailWord_163119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163119).length < 2 ^ (prefixWord ++ tailWord_163119).sum := by decide
  have hdescent : baseEnd_163119 < baseStart_163119 := by decide
  rcases family_descends (prefixWord ++ tailWord_163119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163123 : List Nat := [1, 1, 1, 2, 5, 3, 1, 4, 5]
def baseStart_163123 : Nat := 118140960795 + 163123 * 2 ^ 59
def prefixEnd_163123 : Nat := 4983230072969 + 3 ^ 40 * 163123 * 2
def baseEnd_163123 : Nat := 9306722755941168245813

theorem tailTrace_163123 : CollatzResearch.WordTrace tailWord_163123 prefixEnd_163123 9306722755941168245813 := by
  unfold tailWord_163123
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949584588040705035526023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3966389725360470023684015 5949584588040705035526023)
  ·
    refine ⟨8924376882061057553289035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5949584588040705035526023 8924376882061057553289035)
    ·
      refine ⟨13386565323091586329933553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8924376882061057553289035 13386565323091586329933553)
      ·
        refine ⟨10039923992318689747450165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13386565323091586329933553 10039923992318689747450165)
        ·
          refine ⟨941242874279877163823453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10039923992318689747450165 941242874279877163823453)
          ·
            refine ⟨352966077854953936433795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 941242874279877163823453 352966077854953936433795)
            ·
              refine ⟨529449116782430904650693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352966077854953936433795 529449116782430904650693)
              ·
                refine ⟨99271709396705794622005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529449116782430904650693 99271709396705794622005)
                ·
                  refine ⟨9306722755941168245813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99271709396705794622005 9306722755941168245813)
                  ·
                    rfl

theorem cell23_163123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 5].length) (baseStart_163123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163123 prefixEnd_163123 := by exact prefixLift 163123
  have htrace : WordTrace (prefixWord ++ tailWord_163123) baseStart_163123 baseEnd_163123 := by
    simpa [prefixWord, tailWord_163123, baseEnd_163123] using wordTrace_append hprefix tailTrace_163123
  have hstable : (prefixWord ++ tailWord_163123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163123).length < 2 ^ (prefixWord ++ tailWord_163123).sum := by decide
  have hdescent : baseEnd_163123 < baseStart_163123 := by decide
  rcases family_descends (prefixWord ++ tailWord_163123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163173 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 4, 4, 2]
def baseStart_163173 : Nat := 118140960795 + 163173 * 2 ^ 59
def prefixEnd_163173 : Nat := 4983230072969 + 3 ^ 40 * 163173 * 2
def baseEnd_163173 : Nat := 83786178836195318587087

theorem tailTrace_163173 : CollatzResearch.WordTrace tailWord_163173 prefixEnd_163173 83786178836195318587087 := by
  unfold tailWord_163173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951408237859563574846173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3967605491906375716564115 5951408237859563574846173)
  ·
    refine ⟨2231778089197336340567315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5951408237859563574846173 2231778089197336340567315)
    ·
      refine ⟨3347667133796004510850973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2231778089197336340567315 3347667133796004510850973)
      ·
        refine ⟨1255375175173501691569115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3347667133796004510850973 1255375175173501691569115)
        ·
          refine ⟨1883062762760252537353673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255375175173501691569115 1883062762760252537353673)
          ·
            refine ⟨1412297072070189403015255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883062762760252537353673 1412297072070189403015255)
            ·
              refine ⟨2118445608105284104522883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412297072070189403015255 2118445608105284104522883)
              ·
                refine ⟨3177668412157926156784325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118445608105284104522883 3177668412157926156784325)
                ·
                  refine ⟨595812827279611154397061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3177668412157926156784325 595812827279611154397061)
                  ·
                    refine ⟨111714905114927091449449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 595812827279611154397061 111714905114927091449449)
                    ·
                      refine ⟨83786178836195318587087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111714905114927091449449 83786178836195318587087)
                      ·
                        rfl

theorem cell23_163173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_163173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163173 prefixEnd_163173 := by exact prefixLift 163173
  have htrace : WordTrace (prefixWord ++ tailWord_163173) baseStart_163173 baseEnd_163173 := by
    simpa [prefixWord, tailWord_163173, baseEnd_163173] using wordTrace_append hprefix tailTrace_163173
  have hstable : (prefixWord ++ tailWord_163173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163173).length < 2 ^ (prefixWord ++ tailWord_163173).sum := by decide
  have hdescent : baseEnd_163173 < baseStart_163173 := by decide
  rcases family_descends (prefixWord ++ tailWord_163173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163183 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 3, 4]
def baseStart_163183 : Nat := 118140960795 + 163183 * 2 ^ 59
def prefixEnd_163183 : Nat := 4983230072969 + 3 ^ 40 * 163183 * 2
def baseEnd_163183 : Nat := 27930437880913426487347

theorem tailTrace_163183 : CollatzResearch.WordTrace tailWord_163183 prefixEnd_163183 27930437880913426487347 := by
  unfold tailWord_163183
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951772967823335282710203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3967848645215556855140135 5951772967823335282710203)
  ·
    refine ⟨8927659451735002924065305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5951772967823335282710203 8927659451735002924065305)
    ·
      refine ⟨6695744588801252193048979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8927659451735002924065305 6695744588801252193048979)
      ·
        refine ⟨10043616883201878289573469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695744588801252193048979 10043616883201878289573469)
        ·
          refine ⟨3766356331200704358590051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10043616883201878289573469 3766356331200704358590051)
          ·
            refine ⟨5649534496801056537885077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766356331200704358590051 5649534496801056537885077)
            ·
              refine ⟨264821929537549525213363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5649534496801056537885077 264821929537549525213363)
              ·
                refine ⟨397232894306324287820045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264821929537549525213363 397232894306324287820045)
                ·
                  refine ⟨148962335364871607932517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397232894306324287820045 148962335364871607932517)
                  ·
                    refine ⟨27930437880913426487347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148962335364871607932517 27930437880913426487347)
                    ·
                      rfl

theorem cell23_163183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_163183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163183 prefixEnd_163183 := by exact prefixLift 163183
  have htrace : WordTrace (prefixWord ++ tailWord_163183) baseStart_163183 baseEnd_163183 := by
    simpa [prefixWord, tailWord_163183, baseEnd_163183] using wordTrace_append hprefix tailTrace_163183
  have hstable : (prefixWord ++ tailWord_163183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163183).length < 2 ^ (prefixWord ++ tailWord_163183).sum := by decide
  have hdescent : baseEnd_163183 < baseStart_163183 := by decide
  rcases family_descends (prefixWord ++ tailWord_163183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163186 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_163186 : Nat := 118140960795 + 163186 * 2 ^ 59
def prefixEnd_163186 : Nat := 4983230072969 + 3 ^ 40 * 163186 * 2
def baseEnd_163186 : Nat := 83792854084703767724527

theorem tailTrace_163186 : CollatzResearch.WordTrace tailWord_163186 prefixEnd_163186 83792854084703767724527 := by
  unfold tailWord_163186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487970596703116698767353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3967921591208311196712941 1487970596703116698767353)
  ·
    refine ⟨1115977947527337524075515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1487970596703116698767353 1115977947527337524075515)
    ·
      refine ⟨1673966921291006286113273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115977947527337524075515 1673966921291006286113273)
      ·
        refine ⟨1255475190968254714584955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1673966921291006286113273 1255475190968254714584955)
        ·
          refine ⟨1883212786452382071877433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255475190968254714584955 1883212786452382071877433)
          ·
            refine ⟨1412409589839286553908075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883212786452382071877433 1412409589839286553908075)
            ·
              refine ⟨2118614384758929830862113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412409589839286553908075 2118614384758929830862113)
              ·
                refine ⟨1588960788569197373146585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118614384758929830862113 1588960788569197373146585)
                ·
                  refine ⟨1191720591426898029859939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1588960788569197373146585 1191720591426898029859939)
                  ·
                    refine ⟨1787580887140347044789909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1191720591426898029859939 1787580887140347044789909)
                    ·
                      refine ⟨83792854084703767724527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1787580887140347044789909 83792854084703767724527)
                      ·
                        rfl

theorem cell23_163186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_163186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163186 prefixEnd_163186 := by exact prefixLift 163186
  have htrace : WordTrace (prefixWord ++ tailWord_163186) baseStart_163186 baseEnd_163186 := by
    simpa [prefixWord, tailWord_163186, baseEnd_163186] using wordTrace_append hprefix tailTrace_163186
  have hstable : (prefixWord ++ tailWord_163186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163186).length < 2 ^ (prefixWord ++ tailWord_163186).sum := by decide
  have hdescent : baseEnd_163186 < baseStart_163186 := by decide
  rcases family_descends (prefixWord ++ tailWord_163186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163234 : List Nat := [3, 3, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_163234 : Nat := 118140960795 + 163234 * 2 ^ 59
def prefixEnd_163234 : Nat := 4983230072969 + 3 ^ 40 * 163234 * 2
def baseEnd_163234 : Nat := 27939167052039859974769

theorem tailTrace_163234 : CollatzResearch.WordTrace tailWord_163234 prefixEnd_163234 27939167052039859974769 := by
  unfold tailWord_163234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488408272659642748204189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3969088727092380661877837 1488408272659642748204189)
  ·
    refine ⟨558153102247366030576571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1488408272659642748204189 558153102247366030576571)
    ·
      refine ⟨837229653371049045864857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558153102247366030576571 837229653371049045864857)
      ·
        refine ⟨627922240028286784398643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 837229653371049045864857 627922240028286784398643)
        ·
          refine ⟨941883360042430176597965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627922240028286784398643 941883360042430176597965)
          ·
            refine ⟨353206260015911316224237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 941883360042430176597965 353206260015911316224237)
            ·
              refine ⟨132452347505966743584089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353206260015911316224237 132452347505966743584089)
              ·
                refine ⟨99339260629475057688067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132452347505966743584089 99339260629475057688067)
                ·
                  refine ⟨149008890944212586532101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99339260629475057688067 149008890944212586532101)
                  ·
                    refine ⟨27939167052039859974769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149008890944212586532101 27939167052039859974769)
                    ·
                      rfl

theorem cell23_163234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_163234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163234 prefixEnd_163234 := by exact prefixLift 163234
  have htrace : WordTrace (prefixWord ++ tailWord_163234) baseStart_163234 baseEnd_163234 := by
    simpa [prefixWord, tailWord_163234, baseEnd_163234] using wordTrace_append hprefix tailTrace_163234
  have hstable : (prefixWord ++ tailWord_163234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163234).length < 2 ^ (prefixWord ++ tailWord_163234).sum := by decide
  have hdescent : baseEnd_163234 < baseStart_163234 := by decide
  rcases family_descends (prefixWord ++ tailWord_163234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163236 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_163236 : Nat := 118140960795 + 163236 * 2 ^ 59
def prefixEnd_163236 : Nat := 4983230072969 + 3 ^ 40 * 163236 * 2
def baseEnd_163236 : Nat := 83818528117428572099297

theorem tailTrace_163236 : CollatzResearch.WordTrace tailWord_163236 prefixEnd_163236 83818528117428572099297 := by
  unfold tailWord_163236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976853018315662667194781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3969137357754216889593041 2976853018315662667194781)
  ·
    refine ⟨1116319881868373500198043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2976853018315662667194781 1116319881868373500198043)
    ·
      refine ⟨1674479822802560250297065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116319881868373500198043 1674479822802560250297065)
      ·
        refine ⟨1255859867101920187722799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674479822802560250297065 1255859867101920187722799)
        ·
          refine ⟨1883789800652880281584199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255859867101920187722799 1883789800652880281584199)
          ·
            refine ⟨2825684700979320422376299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883789800652880281584199 2825684700979320422376299)
            ·
              refine ⟨4238527051468980633564449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825684700979320422376299 4238527051468980633564449)
              ·
                refine ⟨3178895288601735475173337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4238527051468980633564449 3178895288601735475173337)
                ·
                  refine ⟨2384171466451301606380003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178895288601735475173337 2384171466451301606380003)
                  ·
                    refine ⟨3576257199676952409570005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384171466451301606380003 3576257199676952409570005)
                    ·
                      refine ⟨83818528117428572099297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3576257199676952409570005 83818528117428572099297)
                      ·
                        rfl

theorem cell23_163236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_163236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163236 prefixEnd_163236 := by exact prefixLift 163236
  have htrace : WordTrace (prefixWord ++ tailWord_163236) baseStart_163236 baseEnd_163236 := by
    simpa [prefixWord, tailWord_163236, baseEnd_163236] using wordTrace_append hprefix tailTrace_163236
  have hstable : (prefixWord ++ tailWord_163236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163236).length < 2 ^ (prefixWord ++ tailWord_163236).sum := by decide
  have hdescent : baseEnd_163236 < baseStart_163236 := by decide
  rcases family_descends (prefixWord ++ tailWord_163236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163260 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_163260 : Nat := 118140960795 + 163260 * 2 ^ 59
def prefixEnd_163260 : Nat := 4983230072969 + 3 ^ 40 * 163260 * 2
def baseEnd_163260 : Nat := 27943617217712159399729

theorem tailTrace_163260 : CollatzResearch.WordTrace tailWord_163260 prefixEnd_163260 27943617217712159399729 := by
  unfold tailWord_163260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977290694272188716631617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3969720925696251622175489 2977290694272188716631617)
  ·
    refine ⟨2232968020704141537473713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2977290694272188716631617 2232968020704141537473713)
    ·
      refine ⟨1674726015528106153105285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2232968020704141537473713 1674726015528106153105285)
      ·
        refine ⟨314011127911519903707241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1674726015528106153105285 314011127911519903707241)
        ·
          refine ⟨235508345933639927780431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314011127911519903707241 235508345933639927780431)
          ·
            refine ⟨353262518900459891670647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235508345933639927780431 353262518900459891670647)
            ·
              refine ⟨529893778350689837505971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353262518900459891670647 529893778350689837505971)
              ·
                refine ⟨794840667526034756258957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529893778350689837505971 794840667526034756258957)
                ·
                  refine ⟨298065250322263033597109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794840667526034756258957 298065250322263033597109)
                  ·
                    refine ⟨27943617217712159399729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 298065250322263033597109 27943617217712159399729)
                    ·
                      rfl

theorem cell23_163260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_163260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163260 prefixEnd_163260 := by exact prefixLift 163260
  have htrace : WordTrace (prefixWord ++ tailWord_163260) baseStart_163260 baseEnd_163260 := by
    simpa [prefixWord, tailWord_163260, baseEnd_163260] using wordTrace_append hprefix tailTrace_163260
  have hstable : (prefixWord ++ tailWord_163260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163260).length < 2 ^ (prefixWord ++ tailWord_163260).sum := by decide
  have hdescent : baseEnd_163260 < baseStart_163260 := by decide
  rcases family_descends (prefixWord ++ tailWord_163260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163263 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 2, 6, 2]
def baseStart_163263 : Nat := 118140960795 + 163263 * 2 ^ 59
def prefixEnd_163263 : Nat := 4983230072969 + 3 ^ 40 * 163263 * 2
def baseEnd_163263 : Nat := 83832392095099966461673

theorem tailTrace_163263 : CollatzResearch.WordTrace tailWord_163263 prefixEnd_163263 83832392095099966461673 := by
  unfold tailWord_163263
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954690807533508945622443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3969793871689005963748295 5954690807533508945622443)
  ·
    refine ⟨8932036211300263418433665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5954690807533508945622443 8932036211300263418433665)
    ·
      refine ⟨6699027158475197563825249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8932036211300263418433665 6699027158475197563825249)
      ·
        refine ⟨5024270368856398172868937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6699027158475197563825249 5024270368856398172868937)
        ·
          refine ⟨3768202776642298629651703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5024270368856398172868937 3768202776642298629651703)
          ·
            refine ⟨5652304164963447944477555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768202776642298629651703 5652304164963447944477555)
            ·
              refine ⟨8478456247445171916716333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652304164963447944477555 8478456247445171916716333)
              ·
                refine ⟨3179421092791939468768625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8478456247445171916716333 3179421092791939468768625)
                ·
                  refine ⟨2384565819593954601576469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179421092791939468768625 2384565819593954601576469)
                  ·
                    refine ⟨111776522793466621948897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2384565819593954601576469 111776522793466621948897)
                    ·
                      refine ⟨83832392095099966461673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111776522793466621948897 83832392095099966461673)
                      ·
                        rfl

theorem cell23_163263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_163263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163263 prefixEnd_163263 := by exact prefixLift 163263
  have htrace : WordTrace (prefixWord ++ tailWord_163263) baseStart_163263 baseEnd_163263 := by
    simpa [prefixWord, tailWord_163263, baseEnd_163263] using wordTrace_append hprefix tailTrace_163263
  have hstable : (prefixWord ++ tailWord_163263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163263).length < 2 ^ (prefixWord ++ tailWord_163263).sum := by decide
  have hdescent : baseEnd_163263 < baseStart_163263 := by decide
  rcases family_descends (prefixWord ++ tailWord_163263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163280 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 5, 2, 2]
def baseStart_163280 : Nat := 118140960795 + 163280 * 2 ^ 59
def prefixEnd_163280 : Nat := 4983230072969 + 3 ^ 40 * 163280 * 2
def baseEnd_163280 : Nat := 83841121266226399949095

theorem tailTrace_163280 : CollatzResearch.WordTrace tailWord_163280 prefixEnd_163280 83841121266226399949095 := by
  unfold tailWord_163280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977655424235960424495647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3970207232314613899327529 2977655424235960424495647)
  ·
    refine ⟨4466483136353940636743471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2977655424235960424495647 4466483136353940636743471)
    ·
      refine ⟨6699724704530910955115207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4466483136353940636743471 6699724704530910955115207)
      ·
        refine ⟨10049587056796366432672811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6699724704530910955115207 10049587056796366432672811)
        ·
          refine ⟨15074380585194549649009217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10049587056796366432672811 15074380585194549649009217)
          ·
            refine ⟨11305785438895912236756913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15074380585194549649009217 11305785438895912236756913)
            ·
              refine ⟨8479339079171934177567685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11305785438895912236756913 8479339079171934177567685)
              ·
                refine ⟨1589876077344737658293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8479339079171934177567685 1589876077344737658293941)
                ·
                  refine ⟨149050882251069155465057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1589876077344737658293941 149050882251069155465057)
                  ·
                    refine ⟨111788161688301866598793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149050882251069155465057 111788161688301866598793)
                    ·
                      refine ⟨83841121266226399949095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111788161688301866598793 83841121266226399949095)
                      ·
                        rfl

theorem cell23_163280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 5, 2, 2].length) (baseStart_163280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163280 prefixEnd_163280 := by exact prefixLift 163280
  have htrace : WordTrace (prefixWord ++ tailWord_163280) baseStart_163280 baseEnd_163280 := by
    simpa [prefixWord, tailWord_163280, baseEnd_163280] using wordTrace_append hprefix tailTrace_163280
  have hstable : (prefixWord ++ tailWord_163280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163280).length < 2 ^ (prefixWord ++ tailWord_163280).sum := by decide
  have hdescent : baseEnd_163280 < baseStart_163280 := by decide
  rcases family_descends (prefixWord ++ tailWord_163280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163290 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_163290 : Nat := 118140960795 + 163290 * 2 ^ 59
def prefixEnd_163290 : Nat := 4983230072969 + 3 ^ 40 * 163290 * 2
def baseEnd_163290 : Nat := 27948752024257120274683

theorem tailTrace_163290 : CollatzResearch.WordTrace tailWord_163290 prefixEnd_163290 27948752024257120274683 := by
  unfold tailWord_163290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488918894608923139213831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3970450385623795037903549 1488918894608923139213831)
  ·
    refine ⟨2233378341913384708820747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1488918894608923139213831 2233378341913384708820747)
    ·
      refine ⟨3350067512870077063231121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233378341913384708820747 3350067512870077063231121)
      ·
        refine ⟨2512550634652557797423341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3350067512870077063231121 2512550634652557797423341)
        ·
          refine ⟨942206487994709174033753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2512550634652557797423341 942206487994709174033753)
          ·
            refine ⟨706654865996031880525315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 942206487994709174033753 706654865996031880525315)
            ·
              refine ⟨1059982298994047820787973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706654865996031880525315 1059982298994047820787973)
              ·
                refine ⟨198746681061383966397745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1059982298994047820787973 198746681061383966397745)
                ·
                  refine ⟨149060010796037974798309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198746681061383966397745 149060010796037974798309)
                  ·
                    refine ⟨27948752024257120274683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149060010796037974798309 27948752024257120274683)
                    ·
                      rfl

theorem cell23_163290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_163290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163290 prefixEnd_163290 := by exact prefixLift 163290
  have htrace : WordTrace (prefixWord ++ tailWord_163290) baseStart_163290 baseEnd_163290 := by
    simpa [prefixWord, tailWord_163290, baseEnd_163290] using wordTrace_append hprefix tailTrace_163290
  have hstable : (prefixWord ++ tailWord_163290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163290).length < 2 ^ (prefixWord ++ tailWord_163290).sum := by decide
  have hdescent : baseEnd_163290 < baseStart_163290 := by decide
  rcases family_descends (prefixWord ++ tailWord_163290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163296 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_163296 : Nat := 118140960795 + 163296 * 2 ^ 59
def prefixEnd_163296 : Nat := 4983230072969 + 3 ^ 40 * 163296 * 2
def baseEnd_163296 : Nat := 83849336956698337349021

theorem tailTrace_163296 : CollatzResearch.WordTrace tailWord_163296 prefixEnd_163296 83849336956698337349021 := by
  unfold tailWord_163296
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977947208206977790786871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3970596277609303721049161 2977947208206977790786871)
  ·
    refine ⟨4466920812310466686180307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2977947208206977790786871 4466920812310466686180307)
    ·
      refine ⟨6700381218465700029270461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4466920812310466686180307 6700381218465700029270461)
      ·
        refine ⟨2512642956924637510976423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6700381218465700029270461 2512642956924637510976423)
        ·
          refine ⟨3768964435386956266464635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512642956924637510976423 3768964435386956266464635)
          ·
            refine ⟨5653446653080434399696953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768964435386956266464635 5653446653080434399696953)
            ·
              refine ⟨4240084989810325799772715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5653446653080434399696953 4240084989810325799772715)
              ·
                refine ⟨6360127484715488699659073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4240084989810325799772715 6360127484715488699659073)
                ·
                  refine ⟨4770095613536616524744305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6360127484715488699659073 4770095613536616524744305)
                  ·
                    refine ⟨3577571710152462393558229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4770095613536616524744305 3577571710152462393558229)
                    ·
                      refine ⟨83849336956698337349021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3577571710152462393558229 83849336956698337349021)
                      ·
                        rfl

theorem cell23_163296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_163296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163296 prefixEnd_163296 := by exact prefixLift 163296
  have htrace : WordTrace (prefixWord ++ tailWord_163296) baseStart_163296 baseEnd_163296 := by
    simpa [prefixWord, tailWord_163296, baseEnd_163296] using wordTrace_append hprefix tailTrace_163296
  have hstable : (prefixWord ++ tailWord_163296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163296).length < 2 ^ (prefixWord ++ tailWord_163296).sum := by decide
  have hdescent : baseEnd_163296 < baseStart_163296 := by decide
  rcases family_descends (prefixWord ++ tailWord_163296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163303 : List Nat := [1, 1, 5, 2, 1, 2, 3, 8]
def baseStart_163303 : Nat := 118140960795 + 163303 * 2 ^ 59
def prefixEnd_163303 : Nat := 4983230072969 + 3 ^ 40 * 163303 * 2
def baseEnd_163303 : Nat := 3105664123010363331907

theorem tailTrace_163303 : CollatzResearch.WordTrace tailWord_163303 prefixEnd_163303 3105664123010363331907 := by
  unfold tailWord_163303
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956149727388595777078563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3970766484925730518052375 5956149727388595777078563)
  ·
    refine ⟨8934224591082893665617845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5956149727388595777078563 8934224591082893665617845)
    ·
      refine ⟨837583555414021281151673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8934224591082893665617845 837583555414021281151673)
      ·
        refine ⟨628187666560515960863755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 837583555414021281151673 628187666560515960863755)
        ·
          refine ⟨942281499840773941295633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628187666560515960863755 942281499840773941295633)
          ·
            refine ⟨706711124880580455971725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 942281499840773941295633 706711124880580455971725)
            ·
              refine ⟨265016671830217670989397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 706711124880580455971725 265016671830217670989397)
              ·
                refine ⟨3105664123010363331907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 265016671830217670989397 3105664123010363331907)
                ·
                  rfl

theorem cell23_163303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 8].length) (baseStart_163303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163303 prefixEnd_163303 := by exact prefixLift 163303
  have htrace : WordTrace (prefixWord ++ tailWord_163303) baseStart_163303 baseEnd_163303 := by
    simpa [prefixWord, tailWord_163303, baseEnd_163303] using wordTrace_append hprefix tailTrace_163303
  have hstable : (prefixWord ++ tailWord_163303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163303).length < 2 ^ (prefixWord ++ tailWord_163303).sum := by decide
  have hdescent : baseEnd_163303 < baseStart_163303 := by decide
  rcases family_descends (prefixWord ++ tailWord_163303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163310 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_163310 : Nat := 118140960795 + 163310 * 2 ^ 59
def prefixEnd_163310 : Nat := 4983230072969 + 3 ^ 40 * 163310 * 2
def baseEnd_163310 : Nat := 83856525685861282573957

theorem tailTrace_163310 : CollatzResearch.WordTrace tailWord_163310 prefixEnd_163310 83856525685861282573957 := by
  unfold tailWord_163310
  simp only [CollatzResearch.WordTrace]
  refine ⟨744550629795404496572923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3970936692242157315055589 744550629795404496572923)
  ·
    refine ⟨1116825944693106744859385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744550629795404496572923 1116825944693106744859385)
    ·
      refine ⟨837619458519830058644539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116825944693106744859385 837619458519830058644539)
      ·
        refine ⟨1256429187779745087966809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837619458519830058644539 1256429187779745087966809)
        ·
          refine ⟨942321890834808815975107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1256429187779745087966809 942321890834808815975107)
          ·
            refine ⟨1413482836252213223962661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942321890834808815975107 1413482836252213223962661)
            ·
              refine ⟨265028031797289979492999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1413482836252213223962661 265028031797289979492999)
              ·
                refine ⟨397542047695934969239499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265028031797289979492999 397542047695934969239499)
                ·
                  refine ⟨596313071543902453859249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397542047695934969239499 596313071543902453859249)
                  ·
                    refine ⟨447234803657926840394437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 596313071543902453859249 447234803657926840394437)
                    ·
                      refine ⟨83856525685861282573957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 447234803657926840394437 83856525685861282573957)
                      ·
                        rfl

theorem cell23_163310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_163310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163310 prefixEnd_163310 := by exact prefixLift 163310
  have htrace : WordTrace (prefixWord ++ tailWord_163310) baseStart_163310 baseEnd_163310 := by
    simpa [prefixWord, tailWord_163310, baseEnd_163310] using wordTrace_append hprefix tailTrace_163310
  have hstable : (prefixWord ++ tailWord_163310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163310).length < 2 ^ (prefixWord ++ tailWord_163310).sum := by decide
  have hdescent : baseEnd_163310 < baseStart_163310 := by decide
  rcases family_descends (prefixWord ++ tailWord_163310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163314 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_163314 : Nat := 118140960795 + 163314 * 2 ^ 59
def prefixEnd_163314 : Nat := 4983230072969 + 3 ^ 40 * 163314 * 2
def baseEnd_163314 : Nat := 83858579608479266923939

theorem tailTrace_163314 : CollatzResearch.WordTrace tailWord_163314 prefixEnd_163314 83858579608479266923939 := by
  unfold tailWord_163314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489137732587186163932249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3971033953565829770485997 1489137732587186163932249)
  ·
    refine ⟨1116853299440389622949187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1489137732587186163932249 1116853299440389622949187)
    ·
      refine ⟨1675279949160584434423781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116853299440389622949187 1675279949160584434423781)
      ·
        refine ⟨314114990467609581454459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1675279949160584434423781 314114990467609581454459)
        ·
          refine ⟨471172485701414372181689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314114990467609581454459 471172485701414372181689)
          ·
            refine ⟨353379364276060779136267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471172485701414372181689 353379364276060779136267)
            ·
              refine ⟨530069046414091168704401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353379364276060779136267 530069046414091168704401)
              ·
                refine ⟨397551784810568376528301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530069046414091168704401 397551784810568376528301)
                ·
                  refine ⟨149081919303963141198113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397551784810568376528301 149081919303963141198113)
                  ·
                    refine ⟨111811439477972355898585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149081919303963141198113 111811439477972355898585)
                    ·
                      refine ⟨83858579608479266923939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111811439477972355898585 83858579608479266923939)
                      ·
                        rfl

theorem cell23_163314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_163314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163314 prefixEnd_163314 := by exact prefixLift 163314
  have htrace : WordTrace (prefixWord ++ tailWord_163314) baseStart_163314 baseEnd_163314 := by
    simpa [prefixWord, tailWord_163314, baseEnd_163314] using wordTrace_append hprefix tailTrace_163314
  have hstable : (prefixWord ++ tailWord_163314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163314).length < 2 ^ (prefixWord ++ tailWord_163314).sum := by decide
  have hdescent : baseEnd_163314 < baseStart_163314 := by decide
  rcases family_descends (prefixWord ++ tailWord_163314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163317 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_163317 : Nat := 118140960795 + 163317 * 2 ^ 59
def prefixEnd_163317 : Nat := 4983230072969 + 3 ^ 40 * 163317 * 2
def baseEnd_163317 : Nat := 83860120050442755186425

theorem tailTrace_163317 : CollatzResearch.WordTrace tailWord_163317 prefixEnd_163317 83860120050442755186425 := by
  unfold tailWord_163317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956660349337876168088205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3971106899558584112058803 5956660349337876168088205)
  ·
    refine ⟨2233747631001703563033077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5956660349337876168088205 2233747631001703563033077)
    ·
      refine ⟨209413840406409709034351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2233747631001703563033077 209413840406409709034351)
      ·
        refine ⟨314120760609614563551527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209413840406409709034351 314120760609614563551527)
        ·
          refine ⟨471181140914421845327291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314120760609614563551527 471181140914421845327291)
          ·
            refine ⟨706771711371632767990937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471181140914421845327291 706771711371632767990937)
            ·
              refine ⟨530078783528724575993203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706771711371632767990937 530078783528724575993203)
              ·
                refine ⟨795118175293086863989805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530078783528724575993203 795118175293086863989805)
                ·
                  refine ⟨298169315734907573996177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795118175293086863989805 298169315734907573996177)
                  ·
                    refine ⟨223626986801180680497133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 298169315734907573996177 223626986801180680497133)
                    ·
                      refine ⟨83860120050442755186425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 223626986801180680497133 83860120050442755186425)
                      ·
                        rfl

theorem cell23_163317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_163317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163317 prefixEnd_163317 := by exact prefixLift 163317
  have htrace : WordTrace (prefixWord ++ tailWord_163317) baseStart_163317 baseEnd_163317 := by
    simpa [prefixWord, tailWord_163317, baseEnd_163317] using wordTrace_append hprefix tailTrace_163317
  have hstable : (prefixWord ++ tailWord_163317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163317).length < 2 ^ (prefixWord ++ tailWord_163317).sum := by decide
  have hdescent : baseEnd_163317 < baseStart_163317 := by decide
  rcases family_descends (prefixWord ++ tailWord_163317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163347 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 3]
def baseStart_163347 : Nat := 118140960795 + 163347 * 2 ^ 59
def prefixEnd_163347 : Nat := 4983230072969 + 3 ^ 40 * 163347 * 2
def baseEnd_163347 : Nat := 83875524470077637811287

theorem tailTrace_163347 : CollatzResearch.WordTrace tailWord_163347 prefixEnd_163347 83875524470077637811287 := by
  unfold tailWord_163347
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957754539229191291680295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3971836359486127527786863 5957754539229191291680295)
  ·
    refine ⟨8936631808843786937520443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5957754539229191291680295 8936631808843786937520443)
    ·
      refine ⟨13404947713265680406280665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936631808843786937520443 13404947713265680406280665)
      ·
        refine ⟨10053710784949260304710499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13404947713265680406280665 10053710784949260304710499)
        ·
          refine ⟨15080566177423890457065749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10053710784949260304710499 15080566177423890457065749)
          ·
            refine ⟨706901539566744865174957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15080566177423890457065749 706901539566744865174957)
            ·
              refine ⟨265088077337529324440609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 706901539566744865174957 265088077337529324440609)
              ·
                refine ⟨198816058003146993330457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265088077337529324440609 198816058003146993330457)
                ·
                  refine ⟨149112043502360244997843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198816058003146993330457 149112043502360244997843)
                  ·
                    refine ⟨223668065253540367496765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149112043502360244997843 223668065253540367496765)
                    ·
                      refine ⟨83875524470077637811287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 223668065253540367496765 83875524470077637811287)
                      ·
                        rfl

theorem cell23_163347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 3].length) (baseStart_163347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163347 prefixEnd_163347 := by exact prefixLift 163347
  have htrace : WordTrace (prefixWord ++ tailWord_163347) baseStart_163347 baseEnd_163347 := by
    simpa [prefixWord, tailWord_163347, baseEnd_163347] using wordTrace_append hprefix tailTrace_163347
  have hstable : (prefixWord ++ tailWord_163347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163347).length < 2 ^ (prefixWord ++ tailWord_163347).sum := by decide
  have hdescent : baseEnd_163347 < baseStart_163347 := by decide
  rcases family_descends (prefixWord ++ tailWord_163347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163358 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_163358 : Nat := 118140960795 + 163358 * 2 ^ 59
def prefixEnd_163358 : Nat := 4983230072969 + 3 ^ 40 * 163358 * 2
def baseEnd_163358 : Nat := 27960390919092364924579

theorem tailTrace_163358 : CollatzResearch.WordTrace tailWord_163358 prefixEnd_163358 27960390919092364924579 := by
  unfold tailWord_163358
  simp only [CollatzResearch.WordTrace]
  refine ⟨744769467773667521291341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3972103828126226780220485 744769467773667521291341)
  ·
    refine ⟨279288550415125320484253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 744769467773667521291341 279288550415125320484253)
    ·
      refine ⟨104733206405671995181595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279288550415125320484253 104733206405671995181595)
      ·
        refine ⟨157099809608507992772393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104733206405671995181595 157099809608507992772393)
        ·
          refine ⟨117824857206380994579295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157099809608507992772393 117824857206380994579295)
          ·
            refine ⟨176737285809571491868943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117824857206380994579295 176737285809571491868943)
            ·
              refine ⟨265105928714357237803415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176737285809571491868943 265105928714357237803415)
              ·
                refine ⟨397658893071535856705123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265105928714357237803415 397658893071535856705123)
                ·
                  refine ⟨596488339607303785057685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397658893071535856705123 596488339607303785057685)
                  ·
                    refine ⟨27960390919092364924579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 596488339607303785057685 27960390919092364924579)
                    ·
                      rfl

theorem cell23_163358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_163358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163358 prefixEnd_163358 := by exact prefixLift 163358
  have htrace : WordTrace (prefixWord ++ tailWord_163358) baseStart_163358 baseEnd_163358 := by
    simpa [prefixWord, tailWord_163358, baseEnd_163358] using wordTrace_append hprefix tailTrace_163358
  have hstable : (prefixWord ++ tailWord_163358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163358).length < 2 ^ (prefixWord ++ tailWord_163358).sum := by decide
  have hdescent : baseEnd_163358 < baseStart_163358 := by decide
  rcases family_descends (prefixWord ++ tailWord_163358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163374 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_163374 : Nat := 118140960795 + 163374 * 2 ^ 59
def prefixEnd_163374 : Nat := 4983230072969 + 3 ^ 40 * 163374 * 2
def baseEnd_163374 : Nat := 83889388447749032173663

theorem tailTrace_163374 : CollatzResearch.WordTrace tailWord_163374 prefixEnd_163374 83889388447749032173663 := by
  unfold tailWord_163374
  simp only [CollatzResearch.WordTrace]
  refine ⟨744842413766421862864147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3972492873420916601942117 744842413766421862864147)
  ·
    refine ⟨1117263620649632794296221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744842413766421862864147 1117263620649632794296221)
    ·
      refine ⟨418973857743612297861083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1117263620649632794296221 418973857743612297861083)
      ·
        refine ⟨628460786615418446791625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418973857743612297861083 628460786615418446791625)
        ·
          refine ⟨471345589961563835093719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628460786615418446791625 471345589961563835093719)
          ·
            refine ⟨707018384942345752640579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471345589961563835093719 707018384942345752640579)
            ·
              refine ⟨1060527577413518628960869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707018384942345752640579 1060527577413518628960869)
              ·
                refine ⟨198848920765034742930163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1060527577413518628960869 198848920765034742930163)
                ·
                  refine ⟨298273381147552114395245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198848920765034742930163 298273381147552114395245)
                  ·
                    refine ⟨111852517930332042898217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 298273381147552114395245 111852517930332042898217)
                    ·
                      refine ⟨83889388447749032173663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111852517930332042898217 83889388447749032173663)
                      ·
                        rfl

theorem cell23_163374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_163374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163374 prefixEnd_163374 := by exact prefixLift 163374
  have htrace : WordTrace (prefixWord ++ tailWord_163374) baseStart_163374 baseEnd_163374 := by
    simpa [prefixWord, tailWord_163374, baseEnd_163374] using wordTrace_append hprefix tailTrace_163374
  have hstable : (prefixWord ++ tailWord_163374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163374).length < 2 ^ (prefixWord ++ tailWord_163374).sum := by decide
  have hdescent : baseEnd_163374 < baseStart_163374 := by decide
  rcases family_descends (prefixWord ++ tailWord_163374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163410 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 7]
def baseStart_163410 : Nat := 118140960795 + 163410 * 2 ^ 59
def prefixEnd_163410 : Nat := 4983230072969 + 3 ^ 40 * 163410 * 2
def baseEnd_163410 : Nat := 9323097083478987924833

theorem tailTrace_163410 : CollatzResearch.WordTrace tailWord_163410 prefixEnd_163410 9323097083478987924833 := by
  unfold tailWord_163410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490013084500238262805921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3973368225333968700815789 1490013084500238262805921)
  ·
    refine ⟨1117509813375178697104441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1490013084500238262805921 1117509813375178697104441)
    ·
      refine ⟨838132360031384022828331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1117509813375178697104441 838132360031384022828331)
      ·
        refine ⟨1257198540047076034242497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838132360031384022828331 1257198540047076034242497)
        ·
          refine ⟨942898905035307025681873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257198540047076034242497 942898905035307025681873)
          ·
            refine ⟨707174178776480269261405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 942898905035307025681873 707174178776480269261405)
            ·
              refine ⟨265190317041180100973027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 707174178776480269261405 265190317041180100973027)
              ·
                refine ⟨397785475561770151459541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265190317041180100973027 397785475561770151459541)
                ·
                  refine ⟨9323097083478987924833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 397785475561770151459541 9323097083478987924833)
                  ·
                    rfl

theorem cell23_163410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_163410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163410 prefixEnd_163410 := by exact prefixLift 163410
  have htrace : WordTrace (prefixWord ++ tailWord_163410) baseStart_163410 baseEnd_163410 := by
    simpa [prefixWord, tailWord_163410, baseEnd_163410] using wordTrace_append hprefix tailTrace_163410
  have hstable : (prefixWord ++ tailWord_163410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163410).length < 2 ^ (prefixWord ++ tailWord_163410).sum := by decide
  have hdescent : baseEnd_163410 < baseStart_163410 := by decide
  rcases family_descends (prefixWord ++ tailWord_163410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163440 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 2, 5]
def baseStart_163440 : Nat := 118140960795 + 163440 * 2 ^ 59
def prefixEnd_163440 : Nat := 4983230072969 + 3 ^ 40 * 163440 * 2
def baseEnd_163440 : Nat := 27974426056981924649453

theorem tailTrace_163440 : CollatzResearch.WordTrace tailWord_163440 prefixEnd_163440 27974426056981924649453 := by
  unfold tailWord_163440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2980573263946134087407887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3974097685261512116543849 2980573263946134087407887)
  ·
    refine ⟨4470859895919201131111831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2980573263946134087407887 4470859895919201131111831)
    ·
      refine ⟨6706289843878801696667747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4470859895919201131111831 6706289843878801696667747)
      ·
        refine ⟨10059434765818202545001621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6706289843878801696667747 10059434765818202545001621)
        ·
          refine ⟨471536004647728244296951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10059434765818202545001621 471536004647728244296951)
          ·
            refine ⟨707304006971592366445427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471536004647728244296951 707304006971592366445427)
            ·
              refine ⟨1060956010457388549668141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707304006971592366445427 1060956010457388549668141)
              ·
                refine ⟨397858503921520706125553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060956010457388549668141 397858503921520706125553)
                ·
                  refine ⟨298393877941140529594165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397858503921520706125553 298393877941140529594165)
                  ·
                    refine ⟨27974426056981924649453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 298393877941140529594165 27974426056981924649453)
                    ·
                      rfl

theorem cell23_163440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_163440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163440 prefixEnd_163440 := by exact prefixLift 163440
  have htrace : WordTrace (prefixWord ++ tailWord_163440) baseStart_163440 baseEnd_163440 := by
    simpa [prefixWord, tailWord_163440, baseEnd_163440] using wordTrace_append hprefix tailTrace_163440
  have hstable : (prefixWord ++ tailWord_163440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163440).length < 2 ^ (prefixWord ++ tailWord_163440).sum := by decide
  have hdescent : baseEnd_163440 < baseStart_163440 := by decide
  rcases family_descends (prefixWord ++ tailWord_163440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163443 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4]
def baseStart_163443 : Nat := 118140960795 + 163443 * 2 ^ 59
def prefixEnd_163443 : Nat := 4983230072969 + 3 ^ 40 * 163443 * 2
def baseEnd_163443 : Nat := 83924818612909262210845

theorem tailTrace_163443 : CollatzResearch.WordTrace tailWord_163443 prefixEnd_163443 83924818612909262210845 := by
  unfold tailWord_163443
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961255946881399687174983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3974170631254266458116655 5961255946881399687174983)
  ·
    refine ⟨8941883920322099530762475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5961255946881399687174983 8941883920322099530762475)
    ·
      refine ⟨13412825880483149296143713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8941883920322099530762475 13412825880483149296143713)
      ·
        refine ⟨10059619410362361972107785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13412825880483149296143713 10059619410362361972107785)
        ·
          refine ⟨7544714557771771479080839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10059619410362361972107785 7544714557771771479080839)
          ·
            refine ⟨11317071836657657218621259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7544714557771771479080839 11317071836657657218621259)
            ·
              refine ⟨16975607754986485827931889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11317071836657657218621259 16975607754986485827931889)
              ·
                refine ⟨12731705816239864370948917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16975607754986485827931889 12731705816239864370948917)
                ·
                  refine ⟨1193597420272487284776461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12731705816239864370948917 1193597420272487284776461)
                  ·
                    refine ⟨447599032602182731791173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1193597420272487284776461 447599032602182731791173)
                    ·
                      refine ⟨83924818612909262210845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 447599032602182731791173 83924818612909262210845)
                      ·
                        rfl

theorem cell23_163443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_163443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163443 prefixEnd_163443 := by exact prefixLift 163443
  have htrace : WordTrace (prefixWord ++ tailWord_163443) baseStart_163443 baseEnd_163443 := by
    simpa [prefixWord, tailWord_163443, baseEnd_163443] using wordTrace_append hprefix tailTrace_163443
  have hstable : (prefixWord ++ tailWord_163443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163443).length < 2 ^ (prefixWord ++ tailWord_163443).sum := by decide
  have hdescent : baseEnd_163443 < baseStart_163443 := by decide
  rcases family_descends (prefixWord ++ tailWord_163443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163473 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_163473 : Nat := 118140960795 + 163473 * 2 ^ 59
def prefixEnd_163473 : Nat := 4983230072969 + 3 ^ 40 * 163473 * 2
def baseEnd_163473 : Nat := 83940223032544144835707

theorem tailTrace_163473 : CollatzResearch.WordTrace tailWord_163473 prefixEnd_163473 83940223032544144835707 := by
  unfold tailWord_163473
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962350136772714810767073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3974900091181809873844715 5962350136772714810767073)
  ·
    refine ⟨4471762602579536108075305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5962350136772714810767073 4471762602579536108075305)
    ·
      refine ⟨3353821951934652081056479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4471762602579536108075305 3353821951934652081056479)
      ·
        refine ⟨5030732927901978121584719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353821951934652081056479 5030732927901978121584719)
        ·
          refine ⟨7546099391852967182377079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030732927901978121584719 7546099391852967182377079)
          ·
            refine ⟨11319149087779450773565619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7546099391852967182377079 11319149087779450773565619)
            ·
              refine ⟨16978723631669176160348429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11319149087779450773565619 16978723631669176160348429)
              ·
                refine ⟨6367021361875941060130661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16978723631669176160348429 6367021361875941060130661)
                ·
                  refine ⟨1193816505351738948774499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6367021361875941060130661 1193816505351738948774499)
                  ·
                    refine ⟨1790724758027608423161749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1193816505351738948774499 1790724758027608423161749)
                    ·
                      refine ⟨83940223032544144835707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1790724758027608423161749 83940223032544144835707)
                      ·
                        rfl

theorem cell23_163473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_163473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163473 prefixEnd_163473 := by exact prefixLift 163473
  have htrace : WordTrace (prefixWord ++ tailWord_163473) baseStart_163473 baseEnd_163473 := by
    simpa [prefixWord, tailWord_163473, baseEnd_163473] using wordTrace_append hprefix tailTrace_163473
  have hstable : (prefixWord ++ tailWord_163473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163473).length < 2 ^ (prefixWord ++ tailWord_163473).sum := by decide
  have hdescent : baseEnd_163473 < baseStart_163473 := by decide
  rcases family_descends (prefixWord ++ tailWord_163473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163537 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 1, 5, 2]
def baseStart_163537 : Nat := 118140960795 + 163537 * 2 ^ 59
def prefixEnd_163537 : Nat := 4983230072969 + 3 ^ 40 * 163537 * 2
def baseEnd_163537 : Nat := 83973085794431894435413

theorem tailTrace_163537 : CollatzResearch.WordTrace tailWord_163537 prefixEnd_163537 83973085794431894435413 := by
  unfold tailWord_163537
  simp only [CollatzResearch.WordTrace]
  refine ⟨5964684408540853741096865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3976456272360569160731243 5964684408540853741096865)
  ·
    refine ⟨4473513306405640305822649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5964684408540853741096865 4473513306405640305822649)
    ·
      refine ⟨3355134979804230229366987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4473513306405640305822649 3355134979804230229366987)
      ·
        refine ⟨5032702469706345344050481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355134979804230229366987 5032702469706345344050481)
        ·
          refine ⟨3774526852279759008037861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5032702469706345344050481 3774526852279759008037861)
          ·
            refine ⟨707723784802454814007099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3774526852279759008037861 707723784802454814007099)
            ·
              refine ⟨1061585677203682221010649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707723784802454814007099 1061585677203682221010649)
              ·
                refine ⟨796189257902761665757987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061585677203682221010649 796189257902761665757987)
                ·
                  refine ⟨1194283886854142498636981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 796189257902761665757987 1194283886854142498636981)
                  ·
                    refine ⟨111964114392575859247217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1194283886854142498636981 111964114392575859247217)
                    ·
                      refine ⟨83973085794431894435413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 111964114392575859247217 83973085794431894435413)
                      ·
                        rfl

theorem cell23_163537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_163537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163537 prefixEnd_163537 := by exact prefixLift 163537
  have htrace : WordTrace (prefixWord ++ tailWord_163537) baseStart_163537 baseEnd_163537 := by
    simpa [prefixWord, tailWord_163537, baseEnd_163537] using wordTrace_append hprefix tailTrace_163537
  have hstable : (prefixWord ++ tailWord_163537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163537).length < 2 ^ (prefixWord ++ tailWord_163537).sum := by decide
  have hdescent : baseEnd_163537 < baseStart_163537 := by decide
  rcases family_descends (prefixWord ++ tailWord_163537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163567 : List Nat := [1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 4]
def baseStart_163567 : Nat := 118140960795 + 163567 * 2 ^ 59
def prefixEnd_163567 : Nat := 4983230072969 + 3 ^ 40 * 163567 * 2
def baseEnd_163567 : Nat := 83988490214066777060275

theorem tailTrace_163567 : CollatzResearch.WordTrace tailWord_163567 prefixEnd_163567 83988490214066777060275 := by
  unfold tailWord_163567
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965778598432168864688955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3977185732288112576459303 5965778598432168864688955)
  ·
    refine ⟨8948667897648253297033433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5965778598432168864688955 8948667897648253297033433)
    ·
      refine ⟨6711500923236189972775075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8948667897648253297033433 6711500923236189972775075)
      ·
        refine ⟨10067251384854284959162613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6711500923236189972775075 10067251384854284959162613)
        ·
          refine ⟨943804817330089214921495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10067251384854284959162613 943804817330089214921495)
          ·
            refine ⟨1415707225995133822382243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943804817330089214921495 1415707225995133822382243)
            ·
              refine ⟨2123560838992700733573365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415707225995133822382243 2123560838992700733573365)
              ·
                refine ⟨199083828655565693772503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2123560838992700733573365 199083828655565693772503)
                ·
                  refine ⟨298625742983348540658755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199083828655565693772503 298625742983348540658755)
                  ·
                    refine ⟨447938614475022810988133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 298625742983348540658755 447938614475022810988133)
                    ·
                      refine ⟨83988490214066777060275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 447938614475022810988133 83988490214066777060275)
                      ·
                        rfl

theorem cell23_163567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_163567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163567 prefixEnd_163567 := by exact prefixLift 163567
  have htrace : WordTrace (prefixWord ++ tailWord_163567) baseStart_163567 baseEnd_163567 := by
    simpa [prefixWord, tailWord_163567, baseEnd_163567] using wordTrace_append hprefix tailTrace_163567
  have hstable : (prefixWord ++ tailWord_163567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163567).length < 2 ^ (prefixWord ++ tailWord_163567).sum := by decide
  have hdescent : baseEnd_163567 < baseStart_163567 := by decide
  rcases family_descends (prefixWord ++ tailWord_163567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163580 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_163580 : Nat := 118140960795 + 163580 * 2 ^ 59
def prefixEnd_163580 : Nat := 4983230072969 + 3 ^ 40 * 163580 * 2
def baseEnd_163580 : Nat := 83995165462575226197715

theorem tailTrace_163580 : CollatzResearch.WordTrace tailWord_163580 prefixEnd_163580 83995165462575226197715 := by
  unfold tailWord_163580
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983126373692536042456097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3977501831590048056608129 2983126373692536042456097)
  ·
    refine ⟨2237344780269402031842073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2983126373692536042456097 2237344780269402031842073)
    ·
      refine ⟨1678008585202051523881555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237344780269402031842073 1678008585202051523881555)
      ·
        refine ⟨2517012877803077285822333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678008585202051523881555 2517012877803077285822333)
        ·
          refine ⟨943879829176153982183375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2517012877803077285822333 943879829176153982183375)
          ·
            refine ⟨1415819743764230973275063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943879829176153982183375 1415819743764230973275063)
            ·
              refine ⟨2123729615646346459912595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415819743764230973275063 2123729615646346459912595)
              ·
                refine ⟨3185594423469519689868893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2123729615646346459912595 3185594423469519689868893)
                ·
                  refine ⟨1194597908801069883700835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3185594423469519689868893 1194597908801069883700835)
                  ·
                    refine ⟨1791896863201604825551253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1194597908801069883700835 1791896863201604825551253)
                    ·
                      refine ⟨83995165462575226197715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1791896863201604825551253 83995165462575226197715)
                      ·
                        rfl

theorem cell23_163580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_163580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163580 prefixEnd_163580 := by exact prefixLift 163580
  have htrace : WordTrace (prefixWord ++ tailWord_163580) baseStart_163580 baseEnd_163580 := by
    simpa [prefixWord, tailWord_163580, baseEnd_163580] using wordTrace_append hprefix tailTrace_163580
  have hstable : (prefixWord ++ tailWord_163580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163580).length < 2 ^ (prefixWord ++ tailWord_163580).sum := by decide
  have hdescent : baseEnd_163580 < baseStart_163580 := by decide
  rcases family_descends (prefixWord ++ tailWord_163580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163594 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_163594 : Nat := 118140960795 + 163594 * 2 ^ 59
def prefixEnd_163594 : Nat := 4983230072969 + 3 ^ 40 * 163594 * 2
def baseEnd_163594 : Nat := 28000784730579390474217

theorem tailTrace_163594 : CollatzResearch.WordTrace tailWord_163594 prefixEnd_163594 28000784730579390474217 := by
  unfold tailWord_163594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491690842333588118980459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3977842246222901650614557 1491690842333588118980459)
  ·
    refine ⟨2237536263500382178470689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1491690842333588118980459 2237536263500382178470689)
    ·
      refine ⟨1678152197625286633853017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237536263500382178470689 1678152197625286633853017)
      ·
        refine ⟨1258614148218964975389763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678152197625286633853017 1258614148218964975389763)
        ·
          refine ⟨1887921222328447463084645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258614148218964975389763 1887921222328447463084645)
          ·
            refine ⟨353985229186583899328371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1887921222328447463084645 353985229186583899328371)
            ·
              refine ⟨530977843779875848992557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353985229186583899328371 530977843779875848992557)
              ·
                refine ⟨199116691417453443372209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530977843779875848992557 199116691417453443372209)
                ·
                  refine ⟨149337518563090082529157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199116691417453443372209 149337518563090082529157)
                  ·
                    refine ⟨28000784730579390474217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149337518563090082529157 28000784730579390474217)
                    ·
                      rfl

theorem cell23_163594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_163594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163594 prefixEnd_163594 := by exact prefixLift 163594
  have htrace : WordTrace (prefixWord ++ tailWord_163594) baseStart_163594 baseEnd_163594 := by
    simpa [prefixWord, tailWord_163594, baseEnd_163594] using wordTrace_append hprefix tailTrace_163594
  have hstable : (prefixWord ++ tailWord_163594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163594).length < 2 ^ (prefixWord ++ tailWord_163594).sum := by decide
  have hdescent : baseEnd_163594 < baseStart_163594 := by decide
  rcases family_descends (prefixWord ++ tailWord_163594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163617 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_163617 : Nat := 118140960795 + 163617 * 2 ^ 59
def prefixEnd_163617 : Nat := 4983230072969 + 3 ^ 40 * 163617 * 2
def baseEnd_163617 : Nat := 84014164246791581435045

theorem tailTrace_163617 : CollatzResearch.WordTrace tailWord_163617 prefixEnd_163617 84014164246791581435045 := by
  unfold tailWord_163617
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967602248251027404009105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3978401498834018269339403 5967602248251027404009105)
  ·
    refine ⟨4475701686188270553006829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5967602248251027404009105 4475701686188270553006829)
    ·
      refine ⟨1678388132320601457377561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4475701686188270553006829 1678388132320601457377561)
      ·
        refine ⟨1258791099240451093033171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678388132320601457377561 1258791099240451093033171)
        ·
          refine ⟨1888186648860676639549757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258791099240451093033171 1888186648860676639549757)
          ·
            refine ⟨708069993322753739831159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1888186648860676639549757 708069993322753739831159)
            ·
              refine ⟨1062104989984130609746739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708069993322753739831159 1062104989984130609746739)
              ·
                refine ⟨1593157484976195914620109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062104989984130609746739 1593157484976195914620109)
                ·
                  refine ⟨597434056866073467982541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1593157484976195914620109 597434056866073467982541)
                  ·
                    refine ⟨224037771324777550493453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 597434056866073467982541 224037771324777550493453)
                    ·
                      refine ⟨84014164246791581435045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 224037771324777550493453 84014164246791581435045)
                      ·
                        rfl

theorem cell23_163617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_163617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163617 prefixEnd_163617 := by exact prefixLift 163617
  have htrace : WordTrace (prefixWord ++ tailWord_163617) baseStart_163617 baseEnd_163617 := by
    simpa [prefixWord, tailWord_163617, baseEnd_163617] using wordTrace_append hprefix tailTrace_163617
  have hstable : (prefixWord ++ tailWord_163617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163617).length < 2 ^ (prefixWord ++ tailWord_163617).sum := by decide
  have hdescent : baseEnd_163617 < baseStart_163617 := by decide
  rcases family_descends (prefixWord ++ tailWord_163617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163618 : List Nat := [3, 3, 1, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_163618 : Nat := 118140960795 + 163618 * 2 ^ 59
def prefixEnd_163618 : Nat := 4983230072969 + 3 ^ 40 * 163618 * 2
def baseEnd_163618 : Nat := 84014677727446077522541

theorem tailTrace_163618 : CollatzResearch.WordTrace tailWord_163618 prefixEnd_163618 84014677727446077522541 := by
  unfold tailWord_163618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491909680311851143698877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3978425814164936383197005 1491909680311851143698877)
  ·
    refine ⟨559466130116944178887079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1491909680311851143698877 559466130116944178887079)
    ·
      refine ⟨839199195175416268330619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559466130116944178887079 839199195175416268330619)
      ·
        refine ⟨1258798792763124402495929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839199195175416268330619 1258798792763124402495929)
        ·
          refine ⟨944099094572343301871947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258798792763124402495929 944099094572343301871947)
          ·
            refine ⟨1416148641858514952807921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944099094572343301871947 1416148641858514952807921)
            ·
              refine ⟨1062111481393886214605941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416148641858514952807921 1062111481393886214605941)
              ·
                refine ⟨99572951380676832619307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1062111481393886214605941 99572951380676832619307)
                ·
                  refine ⟨149359427071015248928961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99572951380676832619307 149359427071015248928961)
                  ·
                    refine ⟨112019570303261436696721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149359427071015248928961 112019570303261436696721)
                    ·
                      refine ⟨84014677727446077522541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112019570303261436696721 84014677727446077522541)
                      ·
                        rfl

theorem cell23_163618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_163618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163618 prefixEnd_163618 := by exact prefixLift 163618
  have htrace : WordTrace (prefixWord ++ tailWord_163618) baseStart_163618 baseEnd_163618 := by
    simpa [prefixWord, tailWord_163618, baseEnd_163618] using wordTrace_append hprefix tailTrace_163618
  have hstable : (prefixWord ++ tailWord_163618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163618).length < 2 ^ (prefixWord ++ tailWord_163618).sum := by decide
  have hdescent : baseEnd_163618 < baseStart_163618 := by decide
  rcases family_descends (prefixWord ++ tailWord_163618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163621 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 1, 2, 3]
def baseStart_163621 : Nat := 118140960795 + 163621 * 2 ^ 59
def prefixEnd_163621 : Nat := 4983230072969 + 3 ^ 40 * 163621 * 2
def baseEnd_163621 : Nat := 84016218169409565785027

theorem tailTrace_163621 : CollatzResearch.WordTrace tailWord_163621 prefixEnd_163621 84016218169409565785027 := by
  unfold tailWord_163621
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967748140236536087154717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3978498760157690724769811 5967748140236536087154717)
  ·
    refine ⟨2237905552588701032683019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5967748140236536087154717 2237905552588701032683019)
    ·
      refine ⟨3356858328883051549024529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2237905552588701032683019 3356858328883051549024529)
      ·
        refine ⟨2517643746662288661768397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3356858328883051549024529 2517643746662288661768397)
        ·
          refine ⟨944116404998358248163149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2517643746662288661768397 944116404998358248163149)
          ·
            refine ⟨354043651874384343061181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 944116404998358248163149 354043651874384343061181)
            ·
              refine ⟨132766369452894128647943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354043651874384343061181 132766369452894128647943)
              ·
                refine ⟨199149554179341192971915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132766369452894128647943 199149554179341192971915)
                ·
                  refine ⟨298724331269011789457873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199149554179341192971915 298724331269011789457873)
                  ·
                    refine ⟨224043248451758842093405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 298724331269011789457873 224043248451758842093405)
                    ·
                      refine ⟨84016218169409565785027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 224043248451758842093405 84016218169409565785027)
                      ·
                        rfl

theorem cell23_163621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_163621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163621 prefixEnd_163621 := by exact prefixLift 163621
  have htrace : WordTrace (prefixWord ++ tailWord_163621) baseStart_163621 baseEnd_163621 := by
    simpa [prefixWord, tailWord_163621, baseEnd_163621] using wordTrace_append hprefix tailTrace_163621
  have hstable : (prefixWord ++ tailWord_163621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163621).length < 2 ^ (prefixWord ++ tailWord_163621).sum := by decide
  have hdescent : baseEnd_163621 < baseStart_163621 := by decide
  rcases family_descends (prefixWord ++ tailWord_163621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163641 : List Nat := [1, 2, 1, 7, 2, 1, 1, 8]
def baseStart_163641 : Nat := 118140960795 + 163641 * 2 ^ 59
def prefixEnd_163641 : Nat := 4983230072969 + 3 ^ 40 * 163641 * 2
def baseEnd_163641 : Nat := 3112092140092573612405

theorem tailTrace_163641 : CollatzResearch.WordTrace tailWord_163641 prefixEnd_163641 3112092140092573612405 := by
  unfold tailWord_163641
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968477600164079502882777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3978985066776053001921851 5968477600164079502882777)
  ·
    refine ⟨4476358200123059627162083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5968477600164079502882777 4476358200123059627162083)
    ·
      refine ⟨6714537300184589440743125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4476358200123059627162083 6714537300184589440743125)
      ·
        refine ⟨157371967973076315017417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6714537300184589440743125 157371967973076315017417)
        ·
          refine ⟨118028975979807236263063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157371967973076315017417 118028975979807236263063)
          ·
            refine ⟨177043463969710854394595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118028975979807236263063 177043463969710854394595)
            ·
              refine ⟨265565195954566281591893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177043463969710854394595 265565195954566281591893)
              ·
                refine ⟨3112092140092573612405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 265565195954566281591893 3112092140092573612405)
                ·
                  rfl

theorem cell23_163641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 8].length) (baseStart_163641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163641 prefixEnd_163641 := by exact prefixLift 163641
  have htrace : WordTrace (prefixWord ++ tailWord_163641) baseStart_163641 baseEnd_163641 := by
    simpa [prefixWord, tailWord_163641, baseEnd_163641] using wordTrace_append hprefix tailTrace_163641
  have hstable : (prefixWord ++ tailWord_163641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163641).length < 2 ^ (prefixWord ++ tailWord_163641).sum := by decide
  have hdescent : baseEnd_163641 < baseStart_163641 := by decide
  rcases family_descends (prefixWord ++ tailWord_163641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163644 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_163644 : Nat := 118140960795 + 163644 * 2 ^ 59
def prefixEnd_163644 : Nat := 4983230072969 + 3 ^ 40 * 163644 * 2
def baseEnd_163644 : Nat := 84028028224462975797421

theorem tailTrace_163644 : CollatzResearch.WordTrace tailWord_163644 prefixEnd_163644 84028028224462975797421 := by
  unfold tailWord_163644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984293509576605507620993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3979058012768807343494657 2984293509576605507620993)
  ·
    refine ⟨2238220132182454130715745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2984293509576605507620993 2238220132182454130715745)
    ·
      refine ⟨1678665099136840598036809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2238220132182454130715745 1678665099136840598036809)
      ·
        refine ⟨1258998824352630448527607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1678665099136840598036809 1258998824352630448527607)
        ·
          refine ⟨1888498236528945672791411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258998824352630448527607 1888498236528945672791411)
          ·
            refine ⟨2832747354793418509187117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888498236528945672791411 2832747354793418509187117)
            ·
              refine ⟨1062280258047531940945169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2832747354793418509187117 1062280258047531940945169)
              ·
                refine ⟨796710193535648955708877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062280258047531940945169 796710193535648955708877)
                ·
                  refine ⟨298766322575868358390829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796710193535648955708877 298766322575868358390829)
                  ·
                    refine ⟨112037370965950634396561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 298766322575868358390829 112037370965950634396561)
                    ·
                      refine ⟨84028028224462975797421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112037370965950634396561 84028028224462975797421)
                      ·
                        rfl

theorem cell23_163644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_163644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163644 prefixEnd_163644 := by exact prefixLift 163644
  have htrace : WordTrace (prefixWord ++ tailWord_163644) baseStart_163644 baseEnd_163644 := by
    simpa [prefixWord, tailWord_163644, baseEnd_163644] using wordTrace_append hprefix tailTrace_163644
  have hstable : (prefixWord ++ tailWord_163644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163644).length < 2 ^ (prefixWord ++ tailWord_163644).sum := by decide
  have hdescent : baseEnd_163644 < baseStart_163644 := by decide
  rcases family_descends (prefixWord ++ tailWord_163644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163674 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2]
def baseStart_163674 : Nat := 118140960795 + 163674 * 2 ^ 59
def prefixEnd_163674 : Nat := 4983230072969 + 3 ^ 40 * 163674 * 2
def baseEnd_163674 : Nat := 84043432644097858422283

theorem tailTrace_163674 : CollatzResearch.WordTrace tailWord_163674 prefixEnd_163674 84043432644097858422283 := by
  unfold tailWord_163674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492420302261131534708519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3979787472696350759222717 1492420302261131534708519)
  ·
    refine ⟨2238630453391697302062779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1492420302261131534708519 2238630453391697302062779)
    ·
      refine ⟨3357945680087545953094169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238630453391697302062779 3357945680087545953094169)
      ·
        refine ⟨2518459260065659464820627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3357945680087545953094169 2518459260065659464820627)
        ·
          refine ⟨3777688890098489197230941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518459260065659464820627 3777688890098489197230941)
          ·
            refine ⟨1416633333786933448961603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3777688890098489197230941 1416633333786933448961603)
            ·
              refine ⟨2124950000680400173442405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416633333786933448961603 2124950000680400173442405)
              ·
                refine ⟨398428125127575032520451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2124950000680400173442405 398428125127575032520451)
                ·
                  refine ⟨597642187691362548780677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398428125127575032520451 597642187691362548780677)
                  ·
                    refine ⟨112057910192130477896377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 597642187691362548780677 112057910192130477896377)
                    ·
                      refine ⟨84043432644097858422283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112057910192130477896377 84043432644097858422283)
                      ·
                        rfl

theorem cell23_163674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_163674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163674 prefixEnd_163674 := by exact prefixLift 163674
  have htrace : WordTrace (prefixWord ++ tailWord_163674) baseStart_163674 baseEnd_163674 := by
    simpa [prefixWord, tailWord_163674, baseEnd_163674] using wordTrace_append hprefix tailTrace_163674
  have hstable : (prefixWord ++ tailWord_163674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163674).length < 2 ^ (prefixWord ++ tailWord_163674).sum := by decide
  have hdescent : baseEnd_163674 < baseStart_163674 := by decide
  rcases family_descends (prefixWord ++ tailWord_163674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163687 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_163687 : Nat := 118140960795 + 163687 * 2 ^ 59
def prefixEnd_163687 : Nat := 4983230072969 + 3 ^ 40 * 163687 * 2
def baseEnd_163687 : Nat := 84050107892606307559723

theorem tailTrace_163687 : CollatzResearch.WordTrace tailWord_163687 prefixEnd_163687 84050107892606307559723 := by
  unfold tailWord_163687
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970155357997429359057315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3980103571998286239371543 5970155357997429359057315)
  ·
    refine ⟨8955233036996144038585973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5970155357997429359057315 8955233036996144038585973)
    ·
      refine ⟨839553097218388503617435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8955233036996144038585973 839553097218388503617435)
      ·
        refine ⟨1259329645827582755426153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839553097218388503617435 1259329645827582755426153)
        ·
          refine ⟨944497234370687066569615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259329645827582755426153 944497234370687066569615)
          ·
            refine ⟨1416745851556030599854423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944497234370687066569615 1416745851556030599854423)
            ·
              refine ⟨2125118777334045899781635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416745851556030599854423 2125118777334045899781635)
              ·
                refine ⟨3187678166001068849672453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125118777334045899781635 3187678166001068849672453)
                ·
                  refine ⟨597689656125200409313585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3187678166001068849672453 597689656125200409313585)
                  ·
                    refine ⟨448267242093900306985189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 597689656125200409313585 448267242093900306985189)
                    ·
                      refine ⟨84050107892606307559723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 448267242093900306985189 84050107892606307559723)
                      ·
                        rfl

theorem cell23_163687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_163687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163687 prefixEnd_163687 := by exact prefixLift 163687
  have htrace : WordTrace (prefixWord ++ tailWord_163687) baseStart_163687 baseEnd_163687 := by
    simpa [prefixWord, tailWord_163687, baseEnd_163687] using wordTrace_append hprefix tailTrace_163687
  have hstable : (prefixWord ++ tailWord_163687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163687).length < 2 ^ (prefixWord ++ tailWord_163687).sum := by decide
  have hdescent : baseEnd_163687 < baseStart_163687 := by decide
  rcases family_descends (prefixWord ++ tailWord_163687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163697 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 7]
def baseStart_163697 : Nat := 118140960795 + 163697 * 2 ^ 59
def prefixEnd_163697 : Nat := 4983230072969 + 3 ^ 40 * 163697 * 2
def baseEnd_163697 : Nat := 9339471411016807603853

theorem tailTrace_163697 : CollatzResearch.WordTrace tailWord_163697 prefixEnd_163697 9339471411016807603853 := by
  unfold tailWord_163697
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970520087961201066921345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3980346725307467377947563 5970520087961201066921345)
  ·
    refine ⟨4477890065970900800191009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5970520087961201066921345 4477890065970900800191009)
    ·
      refine ⟨3358417549478175600143257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4477890065970900800191009 3358417549478175600143257)
      ·
        refine ⟨2518813162108631700107443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3358417549478175600143257 2518813162108631700107443)
        ·
          refine ⟨3778219743162947550161165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2518813162108631700107443 3778219743162947550161165)
          ·
            refine ⟨1416832403686105331310437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3778219743162947550161165 1416832403686105331310437)
            ·
              refine ⟨265656075691144749620707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1416832403686105331310437 265656075691144749620707)
              ·
                refine ⟨398484113536717124431061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265656075691144749620707 398484113536717124431061)
                ·
                  refine ⟨9339471411016807603853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 398484113536717124431061 9339471411016807603853)
                  ·
                    rfl

theorem cell23_163697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 7].length) (baseStart_163697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163697 prefixEnd_163697 := by exact prefixLift 163697
  have htrace : WordTrace (prefixWord ++ tailWord_163697) baseStart_163697 baseEnd_163697 := by
    simpa [prefixWord, tailWord_163697, baseEnd_163697] using wordTrace_append hprefix tailTrace_163697
  have hstable : (prefixWord ++ tailWord_163697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163697).length < 2 ^ (prefixWord ++ tailWord_163697).sum := by decide
  have hdescent : baseEnd_163697 < baseStart_163697 := by decide
  rcases family_descends (prefixWord ++ tailWord_163697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163791 : List Nat := [1, 1, 2, 1, 1, 5, 2, 5, 1, 4]
def baseStart_163791 : Nat := 118140960795 + 163791 * 2 ^ 59
def prefixEnd_163791 : Nat := 4983230072969 + 3 ^ 40 * 163791 * 2
def baseEnd_163791 : Nat := 28034503293557966886415

theorem tailTrace_163791 : CollatzResearch.WordTrace tailWord_163791 prefixEnd_163791 28034503293557966886415 := by
  unfold tailWord_163791
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973948549620655120843227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3982632366413770080562151 5973948549620655120843227)
  ·
    refine ⟨8960922824430982681264841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5973948549620655120843227 8960922824430982681264841)
    ·
      refine ⟨6720692118323237010948631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8960922824430982681264841 6720692118323237010948631)
      ·
        refine ⟨10081038177484855516422947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720692118323237010948631 10081038177484855516422947)
        ·
          refine ⟨15121557266227283274634421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10081038177484855516422947 15121557266227283274634421)
          ·
            refine ⟨1417645993708807806996977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15121557266227283274634421 1417645993708807806996977)
            ·
              refine ⟨1063234495281605855247733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1417645993708807806996977 1063234495281605855247733)
              ·
                refine ⟨99678233932650548929475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1063234495281605855247733 99678233932650548929475)
                ·
                  refine ⟨149517350898975823394213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99678233932650548929475 149517350898975823394213)
                  ·
                    refine ⟨28034503293557966886415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149517350898975823394213 28034503293557966886415)
                    ·
                      rfl

theorem cell23_163791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 4].length) (baseStart_163791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163791 prefixEnd_163791 := by exact prefixLift 163791
  have htrace : WordTrace (prefixWord ++ tailWord_163791) baseStart_163791 baseEnd_163791 := by
    simpa [prefixWord, tailWord_163791, baseEnd_163791] using wordTrace_append hprefix tailTrace_163791
  have hstable : (prefixWord ++ tailWord_163791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163791).length < 2 ^ (prefixWord ++ tailWord_163791).sum := by decide
  have hdescent : baseEnd_163791 < baseStart_163791 := by decide
  rcases family_descends (prefixWord ++ tailWord_163791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163841 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_163841 : Nat := 118140960795 + 163841 * 2 ^ 59
def prefixEnd_163841 : Nat := 4983230072969 + 3 ^ 40 * 163841 * 2
def baseEnd_163841 : Nat := 84129183913398705034015

theorem tailTrace_163841 : CollatzResearch.WordTrace tailWord_163841 prefixEnd_163841 84129183913398705034015 := by
  unfold tailWord_163841
  simp only [CollatzResearch.WordTrace]
  refine ⟨5975772199439513660163377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3983848132959675773442251 5975772199439513660163377)
  ·
    refine ⟨4481829149579635245122533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5975772199439513660163377 4481829149579635245122533)
    ·
      refine ⟨840342965546181608460475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4481829149579635245122533 840342965546181608460475)
      ·
        refine ⟨1260514448319272412690713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840342965546181608460475 1260514448319272412690713)
        ·
          refine ⟨945385836239454309518035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260514448319272412690713 945385836239454309518035)
          ·
            refine ⟨1418078754359181464277053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945385836239454309518035 1418078754359181464277053)
            ·
              refine ⟨531779532884693049103895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1418078754359181464277053 531779532884693049103895)
              ·
                refine ⟨797669299327039573655843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531779532884693049103895 797669299327039573655843)
                ·
                  refine ⟨1196503948990559360483765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797669299327039573655843 1196503948990559360483765)
                  ·
                    refine ⟨112172245217864940045353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1196503948990559360483765 112172245217864940045353)
                    ·
                      refine ⟨84129183913398705034015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112172245217864940045353 84129183913398705034015)
                      ·
                        rfl

theorem cell23_163841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_163841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163841 prefixEnd_163841 := by exact prefixLift 163841
  have htrace : WordTrace (prefixWord ++ tailWord_163841) baseStart_163841 baseEnd_163841 := by
    simpa [prefixWord, tailWord_163841, baseEnd_163841] using wordTrace_append hprefix tailTrace_163841
  have hstable : (prefixWord ++ tailWord_163841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163841).length < 2 ^ (prefixWord ++ tailWord_163841).sum := by decide
  have hdescent : baseEnd_163841 < baseStart_163841 := by decide
  rcases family_descends (prefixWord ++ tailWord_163841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163884 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_163884 : Nat := 118140960795 + 163884 * 2 ^ 59
def prefixEnd_163884 : Nat := 4983230072969 + 3 ^ 40 * 163884 * 2
def baseEnd_163884 : Nat := 84151263581542036796317

theorem tailTrace_163884 : CollatzResearch.WordTrace tailWord_163884 prefixEnd_163884 84151263581542036796317 := by
  unfold tailWord_163884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988670269141866001989353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3984893692189154669319137 2988670269141866001989353)
  ·
    refine ⟨2241502701856399501492015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2988670269141866001989353 2241502701856399501492015)
    ·
      refine ⟨3362254052784599252238023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2241502701856399501492015 3362254052784599252238023)
      ·
        refine ⟨5043381079176898878357035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3362254052784599252238023 5043381079176898878357035)
        ·
          refine ⟨7565071618765348317535553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5043381079176898878357035 7565071618765348317535553)
          ·
            refine ⟨5673803714074011238151665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7565071618765348317535553 5673803714074011238151665)
            ·
              refine ⟨4255352785555508428613749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5673803714074011238151665 4255352785555508428613749)
              ·
                refine ⟨398939323645828915182539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4255352785555508428613749 398939323645828915182539)
                ·
                  refine ⟨598408985468743372773809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398939323645828915182539 598408985468743372773809)
                  ·
                    refine ⟨448806739101557529580357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 598408985468743372773809 448806739101557529580357)
                    ·
                      refine ⟨84151263581542036796317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 448806739101557529580357 84151263581542036796317)
                      ·
                        rfl

theorem cell23_163884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_163884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163884 prefixEnd_163884 := by exact prefixLift 163884
  have htrace : WordTrace (prefixWord ++ tailWord_163884) baseStart_163884 baseEnd_163884 := by
    simpa [prefixWord, tailWord_163884, baseEnd_163884] using wordTrace_append hprefix tailTrace_163884
  have hstable : (prefixWord ++ tailWord_163884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163884).length < 2 ^ (prefixWord ++ tailWord_163884).sum := by decide
  have hdescent : baseEnd_163884 < baseStart_163884 := by decide
  rcases family_descends (prefixWord ++ tailWord_163884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163888 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 3, 2, 2]
def baseStart_163888 : Nat := 118140960795 + 163888 * 2 ^ 59
def prefixEnd_163888 : Nat := 4983230072969 + 3 ^ 40 * 163888 * 2
def baseEnd_163888 : Nat := 84153317504160021146299

theorem tailTrace_163888 : CollatzResearch.WordTrace tailWord_163888 prefixEnd_163888 84153317504160021146299 := by
  unfold tailWord_163888
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988743215134620343562159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3984990953512827124749545 2988743215134620343562159)
  ·
    refine ⟨4483114822701930515343239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2988743215134620343562159 4483114822701930515343239)
    ·
      refine ⟨6724672234052895773014859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4483114822701930515343239 6724672234052895773014859)
      ·
        refine ⟨10087008351079343659522289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6724672234052895773014859 10087008351079343659522289)
        ·
          refine ⟨7565256263309507744641717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10087008351079343659522289 7565256263309507744641717)
          ·
            refine ⟨709242774685266351060161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7565256263309507744641717 709242774685266351060161)
            ·
              refine ⟨531932081013949763295121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709242774685266351060161 531932081013949763295121)
              ·
                refine ⟨398949060760462322471341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531932081013949763295121 398949060760462322471341)
                ·
                  refine ⟨149605897785173370926753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398949060760462322471341 149605897785173370926753)
                  ·
                    refine ⟨112204423338880028195065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149605897785173370926753 112204423338880028195065)
                    ·
                      refine ⟨84153317504160021146299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112204423338880028195065 84153317504160021146299)
                      ·
                        rfl

theorem cell23_163888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3, 2, 2].length) (baseStart_163888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163888 prefixEnd_163888 := by exact prefixLift 163888
  have htrace : WordTrace (prefixWord ++ tailWord_163888) baseStart_163888 baseEnd_163888 := by
    simpa [prefixWord, tailWord_163888, baseEnd_163888] using wordTrace_append hprefix tailTrace_163888
  have hstable : (prefixWord ++ tailWord_163888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163888).length < 2 ^ (prefixWord ++ tailWord_163888).sum := by decide
  have hdescent : baseEnd_163888 < baseStart_163888 := by decide
  rcases family_descends (prefixWord ++ tailWord_163888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163891 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 3]
def baseStart_163891 : Nat := 118140960795 + 163891 * 2 ^ 59
def prefixEnd_163891 : Nat := 4983230072969 + 3 ^ 40 * 163891 * 2
def baseEnd_163891 : Nat := 84154857946123509408785

theorem tailTrace_163891 : CollatzResearch.WordTrace tailWord_163891 prefixEnd_163891 84154857946123509408785 := by
  unfold tailWord_163891
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977595849258372199483527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3985063899505581466322351 5977595849258372199483527)
  ·
    refine ⟨8966393773887558299225291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5977595849258372199483527 8966393773887558299225291)
    ·
      refine ⟨13449590660831337448837937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8966393773887558299225291 13449590660831337448837937)
      ·
        refine ⟨10087192995623503086628453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13449590660831337448837937 10087192995623503086628453)
        ·
          refine ⟨1891348686679406828742835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10087192995623503086628453 1891348686679406828742835)
          ·
            refine ⟨2837023030019110243114253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891348686679406828742835 2837023030019110243114253)
            ·
              refine ⟨1063883636257166341167845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2837023030019110243114253 1063883636257166341167845)
              ·
                refine ⟨199478181798218688968971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1063883636257166341167845 199478181798218688968971)
                ·
                  refine ⟨299217272697328033453457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199478181798218688968971 299217272697328033453457)
                  ·
                    refine ⟨224412954522996025090093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299217272697328033453457 224412954522996025090093)
                    ·
                      refine ⟨84154857946123509408785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 224412954522996025090093 84154857946123509408785)
                      ·
                        rfl

theorem cell23_163891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_163891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163891 prefixEnd_163891 := by exact prefixLift 163891
  have htrace : WordTrace (prefixWord ++ tailWord_163891) baseStart_163891 baseEnd_163891 := by
    simpa [prefixWord, tailWord_163891, baseEnd_163891] using wordTrace_append hprefix tailTrace_163891
  have hstable : (prefixWord ++ tailWord_163891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163891).length < 2 ^ (prefixWord ++ tailWord_163891).sum := by decide
  have hdescent : baseEnd_163891 < baseStart_163891 := by decide
  rcases family_descends (prefixWord ++ tailWord_163891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163922 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_163922 : Nat := 118140960795 + 163922 * 2 ^ 59
def prefixEnd_163922 : Nat := 4983230072969 + 3 ^ 40 * 163922 * 2
def baseEnd_163922 : Nat := 84170775846412888121143

theorem tailTrace_163922 : CollatzResearch.WordTrace tailWord_163922 prefixEnd_163922 84170775846412888121143 := by
  unfold tailWord_163922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1494681628036516123465505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3985817674764042995908013 1494681628036516123465505)
  ·
    refine ⟨1121011221027387092599129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1494681628036516123465505 1121011221027387092599129)
    ·
      refine ⟨840758415770540319449347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1121011221027387092599129 840758415770540319449347)
      ·
        refine ⟨1261137623655810479174021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840758415770540319449347 1261137623655810479174021)
        ·
          refine ⟨236463304435464464845129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1261137623655810479174021 236463304435464464845129)
          ·
            refine ⟨177347478326598348633847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236463304435464464845129 177347478326598348633847)
            ·
              refine ⟨266021217489897522950771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177347478326598348633847 266021217489897522950771)
              ·
                refine ⟨399031826234846284426157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266021217489897522950771 399031826234846284426157)
                ·
                  refine ⟨149636934838067356659809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399031826234846284426157 149636934838067356659809)
                  ·
                    refine ⟨112227701128550517494857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149636934838067356659809 112227701128550517494857)
                    ·
                      refine ⟨84170775846412888121143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112227701128550517494857 84170775846412888121143)
                      ·
                        rfl

theorem cell23_163922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_163922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163922 prefixEnd_163922 := by exact prefixLift 163922
  have htrace : WordTrace (prefixWord ++ tailWord_163922) baseStart_163922 baseEnd_163922 := by
    simpa [prefixWord, tailWord_163922, baseEnd_163922] using wordTrace_append hprefix tailTrace_163922
  have hstable : (prefixWord ++ tailWord_163922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163922).length < 2 ^ (prefixWord ++ tailWord_163922).sum := by decide
  have hdescent : baseEnd_163922 < baseStart_163922 := by decide
  rcases family_descends (prefixWord ++ tailWord_163922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163924 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_163924 : Nat := 118140960795 + 163924 * 2 ^ 59
def prefixEnd_163924 : Nat := 4983230072969 + 3 ^ 40 * 163924 * 2
def baseEnd_163924 : Nat := 28057267602573960098711

theorem tailTrace_163924 : CollatzResearch.WordTrace tailWord_163924 prefixEnd_163924 28057267602573960098711 := by
  unfold tailWord_163924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989399729069409417717413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3985866305425879223623217 2989399729069409417717413)
  ·
    refine ⟨560512449200514265822015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2989399729069409417717413 560512449200514265822015)
    ·
      refine ⟨840768673800771398733023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560512449200514265822015 840768673800771398733023)
      ·
        refine ⟨1261153010701157098099535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840768673800771398733023 1261153010701157098099535)
        ·
          refine ⟨1891729516051735647149303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261153010701157098099535 1891729516051735647149303)
          ·
            refine ⟨2837594274077603470723955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891729516051735647149303 2837594274077603470723955)
            ·
              refine ⟨4256391411116405206085933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837594274077603470723955 4256391411116405206085933)
              ·
                refine ⟨1596146779168651952282225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4256391411116405206085933 1596146779168651952282225)
                ·
                  refine ⟨1197110084376488964211669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1596146779168651952282225 1197110084376488964211669)
                  ·
                    refine ⟨28057267602573960098711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1197110084376488964211669 28057267602573960098711)
                    ·
                      rfl

theorem cell23_163924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_163924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163924 prefixEnd_163924 := by exact prefixLift 163924
  have htrace : WordTrace (prefixWord ++ tailWord_163924) baseStart_163924 baseEnd_163924 := by
    simpa [prefixWord, tailWord_163924, baseEnd_163924] using wordTrace_append hprefix tailTrace_163924
  have hstable : (prefixWord ++ tailWord_163924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163924).length < 2 ^ (prefixWord ++ tailWord_163924).sum := by decide
  have hdescent : baseEnd_163924 < baseStart_163924 := by decide
  rcases family_descends (prefixWord ++ tailWord_163924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163948 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 3, 3, 2]
def baseStart_163948 : Nat := 118140960795 + 163948 * 2 ^ 59
def prefixEnd_163948 : Nat := 4983230072969 + 3 ^ 40 * 163948 * 2
def baseEnd_163948 : Nat := 84184126343429786396023

theorem tailTrace_163948 : CollatzResearch.WordTrace tailWord_163948 prefixEnd_163948 84184126343429786396023 := by
  unfold tailWord_163948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989837405025935467154249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3986449873367913956205665 2989837405025935467154249)
  ·
    refine ⟨2242378053769451600365687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2989837405025935467154249 2242378053769451600365687)
    ·
      refine ⟨3363567080654177400548531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2242378053769451600365687 3363567080654177400548531)
      ·
        refine ⟨5045350620981266100822797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363567080654177400548531 5045350620981266100822797)
        ·
          refine ⟨1892006482867974787808549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5045350620981266100822797 1892006482867974787808549)
          ·
            refine ⟨354751215537745272714103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1892006482867974787808549 354751215537745272714103)
            ·
              refine ⟨532126823306617909071155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354751215537745272714103 532126823306617909071155)
              ·
                refine ⟨798190234959926863606733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532126823306617909071155 798190234959926863606733)
                ·
                  refine ⟨299321338109972573852525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798190234959926863606733 299321338109972573852525)
                  ·
                    refine ⟨112245501791239715194697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299321338109972573852525 112245501791239715194697)
                    ·
                      refine ⟨84184126343429786396023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112245501791239715194697 84184126343429786396023)
                      ·
                        rfl

theorem cell23_163948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_163948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163948 prefixEnd_163948 := by exact prefixLift 163948
  have htrace : WordTrace (prefixWord ++ tailWord_163948) baseStart_163948 baseEnd_163948 := by
    simpa [prefixWord, tailWord_163948, baseEnd_163948] using wordTrace_append hprefix tailTrace_163948
  have hstable : (prefixWord ++ tailWord_163948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163948).length < 2 ^ (prefixWord ++ tailWord_163948).sum := by decide
  have hdescent : baseEnd_163948 < baseStart_163948 := by decide
  rcases family_descends (prefixWord ++ tailWord_163948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163984 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 7]
def baseStart_163984 : Nat := 118140960795 + 163984 * 2 ^ 59
def prefixEnd_163984 : Nat := 4983230072969 + 3 ^ 40 * 163984 * 2
def baseEnd_163984 : Nat := 9355845738554627282873

theorem tailTrace_163984 : CollatzResearch.WordTrace tailWord_163984 prefixEnd_163984 9355845738554627282873 := by
  unfold tailWord_163984
  simp only [CollatzResearch.WordTrace]
  refine ⟨2990493918960724541309503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3987325225280966055079337 2990493918960724541309503)
  ·
    refine ⟨4485740878441086811964255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2990493918960724541309503 4485740878441086811964255)
    ·
      refine ⟨6728611317661630217946383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4485740878441086811964255 6728611317661630217946383)
      ·
        refine ⟨10092916976492445326919575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728611317661630217946383 10092916976492445326919575)
        ·
          refine ⟨15139375464738667990379363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10092916976492445326919575 15139375464738667990379363)
          ·
            refine ⟨22709063197108001985569045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15139375464738667990379363 22709063197108001985569045)
            ·
              refine ⟨1064487337364437593073549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22709063197108001985569045 1064487337364437593073549)
              ·
                refine ⟨399182751511664097402581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1064487337364437593073549 399182751511664097402581)
                ·
                  refine ⟨9355845738554627282873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 399182751511664097402581 9355845738554627282873)
                  ·
                    rfl

theorem cell23_163984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_163984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_163984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_163984 prefixEnd_163984 := by exact prefixLift 163984
  have htrace : WordTrace (prefixWord ++ tailWord_163984) baseStart_163984 baseEnd_163984 := by
    simpa [prefixWord, tailWord_163984, baseEnd_163984] using wordTrace_append hprefix tailTrace_163984
  have hstable : (prefixWord ++ tailWord_163984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163984).length < 2 ^ (prefixWord ++ tailWord_163984).sum := by decide
  have hdescent : baseEnd_163984 < baseStart_163984 := by decide
  rcases family_descends (prefixWord ++ tailWord_163984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164001 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 7]
def baseStart_164001 : Nat := 118140960795 + 164001 * 2 ^ 59
def prefixEnd_164001 : Nat := 4983230072969 + 3 ^ 40 * 164001 * 2
def baseEnd_164001 : Nat := 9356815646457564337031

theorem tailTrace_164001 : CollatzResearch.WordTrace tailWord_164001 prefixEnd_164001 9356815646457564337031 := by
  unfold tailWord_164001
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981607878859860985987857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3987738585906573990658571 5981607878859860985987857)
  ·
    refine ⟨4486205909144895739490893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5981607878859860985987857 4486205909144895739490893)
    ·
      refine ⟨1682327215929335902309085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4486205909144895739490893 1682327215929335902309085)
      ·
        refine ⟨630872705973500963365907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1682327215929335902309085 630872705973500963365907)
        ·
          refine ⟨946309058960251445048861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630872705973500963365907 946309058960251445048861)
          ·
            refine ⟨354865897110094291893323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 946309058960251445048861 354865897110094291893323)
            ·
              refine ⟨532298845665141437839985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354865897110094291893323 532298845665141437839985)
              ·
                refine ⟨399224134248856078379989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532298845665141437839985 399224134248856078379989)
                ·
                  refine ⟨9356815646457564337031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 399224134248856078379989 9356815646457564337031)
                  ·
                    rfl

theorem cell23_164001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 7].length) (baseStart_164001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164001 prefixEnd_164001 := by exact prefixLift 164001
  have htrace : WordTrace (prefixWord ++ tailWord_164001) baseStart_164001 baseEnd_164001 := by
    simpa [prefixWord, tailWord_164001, baseEnd_164001] using wordTrace_append hprefix tailTrace_164001
  have hstable : (prefixWord ++ tailWord_164001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164001).length < 2 ^ (prefixWord ++ tailWord_164001).sum := by decide
  have hdescent : baseEnd_164001 < baseStart_164001 := by decide
  rcases family_descends (prefixWord ++ tailWord_164001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164018 : List Nat := [3, 2, 1, 1, 1, 3, 4, 3, 5]
def baseStart_164018 : Nat := 118140960795 + 164018 * 2 ^ 59
def prefixEnd_164018 : Nat := 4983230072969 + 3 ^ 40 * 164018 * 2
def baseEnd_164018 : Nat := 9357785554360501391189

theorem tailTrace_164018 : CollatzResearch.WordTrace tailWord_164018 prefixEnd_164018 9357785554360501391189 := by
  unfold tailWord_164018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495556979949568222339177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3988151946532181926237805 1495556979949568222339177)
  ·
    refine ⟨1121667734962176166754383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1495556979949568222339177 1121667734962176166754383)
    ·
      refine ⟨1682501602443264250131575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1121667734962176166754383 1682501602443264250131575)
      ·
        refine ⟨2523752403664896375197363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682501602443264250131575 2523752403664896375197363)
        ·
          refine ⟨3785628605497344562796045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523752403664896375197363 3785628605497344562796045)
          ·
            refine ⟨1419610727061504211048517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3785628605497344562796045 1419610727061504211048517)
            ·
              refine ⟨266177011324032039571597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1419610727061504211048517 266177011324032039571597)
              ·
                refine ⟨99816379246512014839349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266177011324032039571597 99816379246512014839349)
                ·
                  refine ⟨9357785554360501391189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99816379246512014839349 9357785554360501391189)
                  ·
                    rfl

theorem cell23_164018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_164018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164018 prefixEnd_164018 := by exact prefixLift 164018
  have htrace : WordTrace (prefixWord ++ tailWord_164018) baseStart_164018 baseEnd_164018 := by
    simpa [prefixWord, tailWord_164018, baseEnd_164018] using wordTrace_append hprefix tailTrace_164018
  have hstable : (prefixWord ++ tailWord_164018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164018).length < 2 ^ (prefixWord ++ tailWord_164018).sum := by decide
  have hdescent : baseEnd_164018 < baseStart_164018 := by decide
  rcases family_descends (prefixWord ++ tailWord_164018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164101 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_164101 : Nat := 118140960795 + 164101 * 2 ^ 59
def prefixEnd_164101 : Nat := 4983230072969 + 3 ^ 40 * 164101 * 2
def baseEnd_164101 : Nat := 84262688883567687782819

theorem tailTrace_164101 : CollatzResearch.WordTrace tailWord_164101 prefixEnd_164101 84262688883567687782819 := by
  unfold tailWord_164101
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985255178497578064628157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3990170118998385376418771 5985255178497578064628157)
  ·
    refine ⟨2244470691936591774235559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5985255178497578064628157 2244470691936591774235559)
    ·
      refine ⟨3366706037904887661353339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244470691936591774235559 3366706037904887661353339)
      ·
        refine ⟨5050059056857331492030009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3366706037904887661353339 5050059056857331492030009)
        ·
          refine ⟨3787544292642998619022507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5050059056857331492030009 3787544292642998619022507)
          ·
            refine ⟨5681316438964497928533761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787544292642998619022507 5681316438964497928533761)
            ·
              refine ⟨4260987329223373446400321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5681316438964497928533761 4260987329223373446400321)
              ·
                refine ⟨3195740496917530084800241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4260987329223373446400321 3195740496917530084800241)
                ·
                  refine ⟨2396805372688147563600181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3195740496917530084800241 2396805372688147563600181)
                  ·
                    refine ⟨224700503689513834087517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2396805372688147563600181 224700503689513834087517)
                    ·
                      refine ⟨84262688883567687782819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 224700503689513834087517 84262688883567687782819)
                      ·
                        rfl

theorem cell23_164101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_164101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164101 prefixEnd_164101 := by exact prefixLift 164101
  have htrace : WordTrace (prefixWord ++ tailWord_164101) baseStart_164101 baseEnd_164101 := by
    simpa [prefixWord, tailWord_164101, baseEnd_164101] using wordTrace_append hprefix tailTrace_164101
  have hstable : (prefixWord ++ tailWord_164101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164101).length < 2 ^ (prefixWord ++ tailWord_164101).sum := by decide
  have hdescent : baseEnd_164101 < baseStart_164101 := by decide
  rcases family_descends (prefixWord ++ tailWord_164101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164142 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_164142 : Nat := 118140960795 + 164142 * 2 ^ 59
def prefixEnd_164142 : Nat := 4983230072969 + 3 ^ 40 * 164142 * 2
def baseEnd_164142 : Nat := 9364860176711336374459

theorem tailTrace_164142 : CollatzResearch.WordTrace tailWord_164142 prefixEnd_164142 9364860176711336374459 := by
  unfold tailWord_164142
  simp only [CollatzResearch.WordTrace]
  refine ⟨748343821418630258358835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3991167047566028044580453 748343821418630258358835)
  ·
    refine ⟨1122515732127945387538253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748343821418630258358835 1122515732127945387538253)
    ·
      refine ⟨420943399547979520326845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1122515732127945387538253 420943399547979520326845)
      ·
        refine ⟨157853774830492320122567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 420943399547979520326845 157853774830492320122567)
        ·
          refine ⟨236780662245738480183851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157853774830492320122567 236780662245738480183851)
          ·
            refine ⟨355170993368607720275777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236780662245738480183851 355170993368607720275777)
            ·
              refine ⟨266378245026455790206833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355170993368607720275777 266378245026455790206833)
              ·
                refine ⟨199783683769841842655125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266378245026455790206833 199783683769841842655125)
                ·
                  refine ⟨9364860176711336374459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 199783683769841842655125 9364860176711336374459)
                  ·
                    rfl

theorem cell23_164142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_164142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164142 prefixEnd_164142 := by exact prefixLift 164142
  have htrace : WordTrace (prefixWord ++ tailWord_164142) baseStart_164142 baseEnd_164142 := by
    simpa [prefixWord, tailWord_164142, baseEnd_164142] using wordTrace_append hprefix tailTrace_164142
  have hstable : (prefixWord ++ tailWord_164142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164142).length < 2 ^ (prefixWord ++ tailWord_164142).sum := by decide
  have hdescent : baseEnd_164142 < baseStart_164142 := by decide
  rcases family_descends (prefixWord ++ tailWord_164142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164146 : List Nat := [3, 2, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_164146 : Nat := 118140960795 + 164146 * 2 ^ 59
def prefixEnd_164146 : Nat := 4983230072969 + 3 ^ 40 * 164146 * 2
def baseEnd_164146 : Nat := 28095265171006670573371

theorem tailTrace_164146 : CollatzResearch.WordTrace tailWord_164146 prefixEnd_164146 28095265171006670573371 := by
  unfold tailWord_164146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1496724115833637687504073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3991264308889700500010861 1496724115833637687504073)
  ·
    refine ⟨1122543086875228265628055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1496724115833637687504073 1122543086875228265628055)
    ·
      refine ⟨1683814630312842398442083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122543086875228265628055 1683814630312842398442083)
      ·
        refine ⟨2525721945469263597663125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683814630312842398442083 2525721945469263597663125)
        ·
          refine ⟨118393216193871731140459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2525721945469263597663125 118393216193871731140459)
          ·
            refine ⟨177589824290807596710689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118393216193871731140459 177589824290807596710689)
            ·
              refine ⟨133192368218105697533017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177589824290807596710689 133192368218105697533017)
              ·
                refine ⟨99894276163579273149763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133192368218105697533017 99894276163579273149763)
                ·
                  refine ⟨149841414245368909724645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99894276163579273149763 149841414245368909724645)
                  ·
                    refine ⟨28095265171006670573371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149841414245368909724645 28095265171006670573371)
                    ·
                      rfl

theorem cell23_164146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_164146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164146 prefixEnd_164146 := by exact prefixLift 164146
  have htrace : WordTrace (prefixWord ++ tailWord_164146) baseStart_164146 baseEnd_164146 := by
    simpa [prefixWord, tailWord_164146, baseEnd_164146] using wordTrace_append hprefix tailTrace_164146
  have hstable : (prefixWord ++ tailWord_164146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164146).length < 2 ^ (prefixWord ++ tailWord_164146).sum := by decide
  have hdescent : baseEnd_164146 < baseStart_164146 := by decide
  rcases family_descends (prefixWord ++ tailWord_164146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164195 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 3]
def baseStart_164195 : Nat := 118140960795 + 164195 * 2 ^ 59
def prefixEnd_164195 : Nat := 4983230072969 + 3 ^ 40 * 164195 * 2
def baseEnd_164195 : Nat := 84310956065090320007387

theorem tailTrace_164195 : CollatzResearch.WordTrace tailWord_164195 prefixEnd_164195 84310956065090320007387 := by
  unfold tailWord_164195
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988683640157032118550039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3992455760104688079033359 5988683640157032118550039)
  ·
    refine ⟨8983025460235548177825059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5988683640157032118550039 8983025460235548177825059)
    ·
      refine ⟨13474538190353322266737589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8983025460235548177825059 13474538190353322266737589)
      ·
        refine ⟨1263237955345623962506649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13474538190353322266737589 1263237955345623962506649)
        ·
          refine ⟨947428466509217971879987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263237955345623962506649 947428466509217971879987)
          ·
            refine ⟨1421142699763826957819981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947428466509217971879987 1421142699763826957819981)
            ·
              refine ⟨532928512411435109182493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1421142699763826957819981 532928512411435109182493)
              ·
                refine ⟨199848192154288165943435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 532928512411435109182493 199848192154288165943435)
                ·
                  refine ⟨299772288231432248915153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199848192154288165943435 299772288231432248915153)
                  ·
                    refine ⟨224829216173574186686365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299772288231432248915153 224829216173574186686365)
                    ·
                      refine ⟨84310956065090320007387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 224829216173574186686365 84310956065090320007387)
                      ·
                        rfl

theorem cell23_164195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_164195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164195 prefixEnd_164195 := by exact prefixLift 164195
  have htrace : WordTrace (prefixWord ++ tailWord_164195) baseStart_164195 baseEnd_164195 := by
    simpa [prefixWord, tailWord_164195, baseEnd_164195] using wordTrace_append hprefix tailTrace_164195
  have hstable : (prefixWord ++ tailWord_164195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164195).length < 2 ^ (prefixWord ++ tailWord_164195).sum := by decide
  have hdescent : baseEnd_164195 < baseStart_164195 := by decide
  rcases family_descends (prefixWord ++ tailWord_164195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164202 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_164202 : Nat := 118140960795 + 164202 * 2 ^ 59
def prefixEnd_164202 : Nat := 4983230072969 + 3 ^ 40 * 164202 * 2
def baseEnd_164202 : Nat := 28104850143223930873285

theorem tailTrace_164202 : CollatzResearch.WordTrace tailWord_164202 prefixEnd_164202 28104850143223930873285 := by
  unfold tailWord_164202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497234737782918078513715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3992625967421114876036573 1497234737782918078513715)
  ·
    refine ⟨2245852106674377117770573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497234737782918078513715 2245852106674377117770573)
    ·
      refine ⟨842194540002891419163965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2245852106674377117770573 842194540002891419163965)
      ·
        refine ⟨315822952501084282186487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 842194540002891419163965 315822952501084282186487)
        ·
          refine ⟨473734428751626423279731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315822952501084282186487 473734428751626423279731)
          ·
            refine ⟨710601643127439634919597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473734428751626423279731 710601643127439634919597)
            ·
              refine ⟨266475616172789863094849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710601643127439634919597 266475616172789863094849)
              ·
                refine ⟨199856712129592397321137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266475616172789863094849 199856712129592397321137)
                ·
                  refine ⟨149892534097194297990853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199856712129592397321137 149892534097194297990853)
                  ·
                    refine ⟨28104850143223930873285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149892534097194297990853 28104850143223930873285)
                    ·
                      rfl

theorem cell23_164202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_164202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164202 prefixEnd_164202 := by exact prefixLift 164202
  have htrace : WordTrace (prefixWord ++ tailWord_164202) baseStart_164202 baseEnd_164202 := by
    simpa [prefixWord, tailWord_164202, baseEnd_164202] using wordTrace_append hprefix tailTrace_164202
  have hstable : (prefixWord ++ tailWord_164202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164202).length < 2 ^ (prefixWord ++ tailWord_164202).sum := by decide
  have hdescent : baseEnd_164202 < baseStart_164202 := by decide
  rcases family_descends (prefixWord ++ tailWord_164202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164246 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_164246 : Nat := 118140960795 + 164246 * 2 ^ 59
def prefixEnd_164246 : Nat := 4983230072969 + 3 ^ 40 * 164246 * 2
def baseEnd_164246 : Nat := 84337143578469620469653

theorem tailTrace_164246 : CollatzResearch.WordTrace tailWord_164246 prefixEnd_164246 84337143578469620469653 := by
  unfold tailWord_164246
  simp only [CollatzResearch.WordTrace]
  refine ⟨374408985185766739291037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3993695841981511885771061 374408985185766739291037)
  ·
    refine ⟨140403369444662527234139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 374408985185766739291037 140403369444662527234139)
    ·
      refine ⟨210605054166993790851209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140403369444662527234139 210605054166993790851209)
      ·
        refine ⟨157953790625245343138407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210605054166993790851209 157953790625245343138407)
        ·
          refine ⟨236930685937868014707611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157953790625245343138407 236930685937868014707611)
          ·
            refine ⟨355396028906802022061417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236930685937868014707611 355396028906802022061417)
            ·
              refine ⟨266547021680101516546063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355396028906802022061417 266547021680101516546063)
              ·
                refine ⟨399820532520152274819095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266547021680101516546063 399820532520152274819095)
                ·
                  refine ⟨599730798780228412228643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399820532520152274819095 599730798780228412228643)
                  ·
                    refine ⟨899596198170342618342965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 599730798780228412228643 899596198170342618342965)
                    ·
                      refine ⟨84337143578469620469653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 899596198170342618342965 84337143578469620469653)
                      ·
                        rfl

theorem cell23_164246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_164246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164246 prefixEnd_164246 := by exact prefixLift 164246
  have htrace : WordTrace (prefixWord ++ tailWord_164246) baseStart_164246 baseEnd_164246 := by
    simpa [prefixWord, tailWord_164246, baseEnd_164246] using wordTrace_append hprefix tailTrace_164246
  have hstable : (prefixWord ++ tailWord_164246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164246).length < 2 ^ (prefixWord ++ tailWord_164246).sum := by decide
  have hdescent : baseEnd_164246 < baseStart_164246 := by decide
  rcases family_descends (prefixWord ++ tailWord_164246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164268 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_164268 : Nat := 118140960795 + 164268 * 2 ^ 59
def prefixEnd_164268 : Nat := 4983230072969 + 3 ^ 40 * 164268 * 2
def baseEnd_164268 : Nat := 84348440152868534394551

theorem tailTrace_164268 : CollatzResearch.WordTrace tailWord_164268 prefixEnd_164268 84348440152868534394551 := by
  unfold tailWord_164268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995673084446282792978729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3994230779261710390638305 2995673084446282792978729)
  ·
    refine ⟨2246754813334712094734047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2995673084446282792978729 2246754813334712094734047)
    ·
      refine ⟨3370132220002068142101071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246754813334712094734047 3370132220002068142101071)
      ·
        refine ⟨5055198330003102213151607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370132220002068142101071 5055198330003102213151607)
        ·
          refine ⟨7582797495004653319727411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055198330003102213151607 7582797495004653319727411)
          ·
            refine ⟨11374196242506979979591117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7582797495004653319727411 11374196242506979979591117)
            ·
              refine ⟨4265323590940117492346669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11374196242506979979591117 4265323590940117492346669)
              ·
                refine ⟨1599496346602544059630001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4265323590940117492346669 1599496346602544059630001)
                ·
                  refine ⟨1199622259951908044722501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1599496346602544059630001 1199622259951908044722501)
                  ·
                    refine ⟨224929173740982758385469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1199622259951908044722501 224929173740982758385469)
                    ·
                      refine ⟨84348440152868534394551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 224929173740982758385469 84348440152868534394551)
                      ·
                        rfl

theorem cell23_164268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_164268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164268 prefixEnd_164268 := by exact prefixLift 164268
  have htrace : WordTrace (prefixWord ++ tailWord_164268) baseStart_164268 baseEnd_164268 := by
    simpa [prefixWord, tailWord_164268, baseEnd_164268] using wordTrace_append hprefix tailTrace_164268
  have hstable : (prefixWord ++ tailWord_164268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164268).length < 2 ^ (prefixWord ++ tailWord_164268).sum := by decide
  have hdescent : baseEnd_164268 < baseStart_164268 := by decide
  rcases family_descends (prefixWord ++ tailWord_164268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164342 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_164342 : Nat := 118140960795 + 164342 * 2 ^ 59
def prefixEnd_164342 : Nat := 4983230072969 + 3 ^ 40 * 164342 * 2
def baseEnd_164342 : Nat := 84386437721301244869211

theorem tailTrace_164342 : CollatzResearch.WordTrace tailWord_164342 prefixEnd_164342 84386437721301244869211 := by
  unfold tailWord_164342
  simp only [CollatzResearch.WordTrace]
  refine ⟨374627823164029764009455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3996030113749650816100853 374627823164029764009455)
  ·
    refine ⟨561941734746044646014183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374627823164029764009455 561941734746044646014183)
    ·
      refine ⟨842912602119066969021275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561941734746044646014183 842912602119066969021275)
      ·
        refine ⟨1264368903178600453531913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842912602119066969021275 1264368903178600453531913)
        ·
          refine ⟨948276677383950340148935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264368903178600453531913 948276677383950340148935)
          ·
            refine ⟨1422415016075925510223403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948276677383950340148935 1422415016075925510223403)
            ·
              refine ⟨2133622524113888265335105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422415016075925510223403 2133622524113888265335105)
              ·
                refine ⟨1600216893085416199001329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133622524113888265335105 1600216893085416199001329)
                ·
                  refine ⟨1200162669814062149250997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600216893085416199001329 1200162669814062149250997)
                  ·
                    refine ⟨112515250295068326492281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1200162669814062149250997 112515250295068326492281)
                    ·
                      refine ⟨84386437721301244869211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112515250295068326492281 84386437721301244869211)
                      ·
                        rfl

theorem cell23_164342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_164342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164342 prefixEnd_164342 := by exact prefixLift 164342
  have htrace : WordTrace (prefixWord ++ tailWord_164342) baseStart_164342 baseEnd_164342 := by
    simpa [prefixWord, tailWord_164342, baseEnd_164342] using wordTrace_append hprefix tailTrace_164342
  have hstable : (prefixWord ++ tailWord_164342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164342).length < 2 ^ (prefixWord ++ tailWord_164342).sum := by decide
  have hdescent : baseEnd_164342 < baseStart_164342 := by decide
  rcases family_descends (prefixWord ++ tailWord_164342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164355 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 1, 6, 2]
def baseStart_164355 : Nat := 118140960795 + 164355 * 2 ^ 59
def prefixEnd_164355 : Nat := 4983230072969 + 3 ^ 40 * 164355 * 2
def baseEnd_164355 : Nat := 84393112969809694006651

theorem tailTrace_164355 : CollatzResearch.WordTrace tailWord_164355 prefixEnd_164355 84393112969809694006651 := by
  unfold tailWord_164355
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994519319577379444374519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3996346213051586296249679 5994519319577379444374519)
  ·
    refine ⟨8991778979366069166561779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5994519319577379444374519 8991778979366069166561779)
    ·
      refine ⟨13487668469049103749842669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8991778979366069166561779 13487668469049103749842669)
      ·
        refine ⟨5057875675893413906191001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13487668469049103749842669 5057875675893413906191001)
        ·
          refine ⟨3793406756920060429643251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5057875675893413906191001 3793406756920060429643251)
          ·
            refine ⟨5690110135380090644464877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793406756920060429643251 5690110135380090644464877)
            ·
              refine ⟨2133791300767533991674329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5690110135380090644464877 2133791300767533991674329)
              ·
                refine ⟨1600343475575650493755747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133791300767533991674329 1600343475575650493755747)
                ·
                  refine ⟨2400515213363475740633621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600343475575650493755747 2400515213363475740633621)
                  ·
                    refine ⟨112524150626412925342201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2400515213363475740633621 112524150626412925342201)
                    ·
                      refine ⟨84393112969809694006651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112524150626412925342201 84393112969809694006651)
                      ·
                        rfl

theorem cell23_164355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_164355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164355 prefixEnd_164355 := by exact prefixLift 164355
  have htrace : WordTrace (prefixWord ++ tailWord_164355) baseStart_164355 baseEnd_164355 := by
    simpa [prefixWord, tailWord_164355, baseEnd_164355] using wordTrace_append hprefix tailTrace_164355
  have hstable : (prefixWord ++ tailWord_164355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164355).length < 2 ^ (prefixWord ++ tailWord_164355).sum := by decide
  have hdescent : baseEnd_164355 < baseStart_164355 := by decide
  rcases family_descends (prefixWord ++ tailWord_164355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164392 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_164392 : Nat := 118140960795 + 164392 * 2 ^ 59
def prefixEnd_164392 : Nat := 4983230072969 + 3 ^ 40 * 164392 * 2
def baseEnd_164392 : Nat := 84412111754026049243981

theorem tailTrace_164392 : CollatzResearch.WordTrace tailWord_164392 prefixEnd_164392 84412111754026049243981 := by
  unfold tailWord_164392
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997934410221667381735715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3997245880295556508980953 2997934410221667381735715)
  ·
    refine ⟨4496901615332501072603573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997934410221667381735715 4496901615332501072603573)
    ·
      refine ⟨421584526437421975556585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4496901615332501072603573 421584526437421975556585)
      ·
        refine ⟨316188394828066481667439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421584526437421975556585 316188394828066481667439)
        ·
          refine ⟨474282592242099722501159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316188394828066481667439 474282592242099722501159)
          ·
            refine ⟨711423888363149583751739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474282592242099722501159 711423888363149583751739)
            ·
              refine ⟨1067135832544724375627609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711423888363149583751739 1067135832544724375627609)
              ·
                refine ⟨800351874408543281720707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067135832544724375627609 800351874408543281720707)
                ·
                  refine ⟨1200527811612814922581061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800351874408543281720707 1200527811612814922581061)
                  ·
                    refine ⟨225098964677402797983949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1200527811612814922581061 225098964677402797983949)
                    ·
                      refine ⟨84412111754026049243981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225098964677402797983949 84412111754026049243981)
                      ·
                        rfl

theorem cell23_164392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_164392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164392 prefixEnd_164392 := by exact prefixLift 164392
  have htrace : WordTrace (prefixWord ++ tailWord_164392) baseStart_164392 baseEnd_164392 := by
    simpa [prefixWord, tailWord_164392, baseEnd_164392] using wordTrace_append hprefix tailTrace_164392
  have hstable : (prefixWord ++ tailWord_164392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164392).length < 2 ^ (prefixWord ++ tailWord_164392).sum := by decide
  have hdescent : baseEnd_164392 < baseStart_164392 := by decide
  rcases family_descends (prefixWord ++ tailWord_164392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164405 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_164405 : Nat := 118140960795 + 164405 * 2 ^ 59
def prefixEnd_164405 : Nat := 4983230072969 + 3 ^ 40 * 164405 * 2
def baseEnd_164405 : Nat := 84418787002534498381421

theorem tailTrace_164405 : CollatzResearch.WordTrace tailWord_164405 prefixEnd_164405 84418787002534498381421 := by
  unfold tailWord_164405
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996342969396237983694669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3997561979597491989129779 5996342969396237983694669)
  ·
    refine ⟨2248628613523589243885501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5996342969396237983694669 2248628613523589243885501)
    ·
      refine ⟨843235730071345966457063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2248628613523589243885501 843235730071345966457063)
      ·
        refine ⟨1264853595107018949685595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843235730071345966457063 1264853595107018949685595)
        ·
          refine ⟨1897280392660528424528393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264853595107018949685595 1897280392660528424528393)
          ·
            refine ⟨1422960294495396318396295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897280392660528424528393 1422960294495396318396295)
            ·
              refine ⟨2134440441743094477594443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422960294495396318396295 2134440441743094477594443)
              ·
                refine ⟨3201660662614641716391665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134440441743094477594443 3201660662614641716391665)
                ·
                  refine ⟨2401245496960981287293749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201660662614641716391665 2401245496960981287293749)
                  ·
                    refine ⟨225116765340091995683789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2401245496960981287293749 225116765340091995683789)
                    ·
                      refine ⟨84418787002534498381421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225116765340091995683789 84418787002534498381421)
                      ·
                        rfl

theorem cell23_164405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_164405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164405 prefixEnd_164405 := by exact prefixLift 164405
  have htrace : WordTrace (prefixWord ++ tailWord_164405) baseStart_164405 baseEnd_164405 := by
    simpa [prefixWord, tailWord_164405, baseEnd_164405] using wordTrace_append hprefix tailTrace_164405
  have hstable : (prefixWord ++ tailWord_164405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164405).length < 2 ^ (prefixWord ++ tailWord_164405).sum := by decide
  have hdescent : baseEnd_164405 < baseStart_164405 := by decide
  rcases family_descends (prefixWord ++ tailWord_164405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164455 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 1, 6]
def baseStart_164455 : Nat := 118140960795 + 164455 * 2 ^ 59
def prefixEnd_164455 : Nat := 4983230072969 + 3 ^ 40 * 164455 * 2
def baseEnd_164455 : Nat := 28148153678419767585397

theorem tailTrace_164455 : CollatzResearch.WordTrace tailWord_164455 prefixEnd_164455 28148153678419767585397 := by
  unfold tailWord_164455
  simp only [CollatzResearch.WordTrace]
  refine ⟨5998166619215096523014819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3998777746143397682009879 5998166619215096523014819)
  ·
    refine ⟨8997249928822644784522229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5998166619215096523014819 8997249928822644784522229)
    ·
      refine ⟨843492180827122948548959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8997249928822644784522229 843492180827122948548959)
      ·
        refine ⟨1265238271240684422823439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843492180827122948548959 1265238271240684422823439)
        ·
          refine ⟨1897857406861026634235159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265238271240684422823439 1897857406861026634235159)
          ·
            refine ⟨2846786110291539951352739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897857406861026634235159 2846786110291539951352739)
            ·
              refine ⟨4270179165437309927029109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846786110291539951352739 4270179165437309927029109)
              ·
                refine ⟨400329296759747805658979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4270179165437309927029109 400329296759747805658979)
                ·
                  refine ⟨600493945139621708488469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400329296759747805658979 600493945139621708488469)
                  ·
                    refine ⟨28148153678419767585397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 600493945139621708488469 28148153678419767585397)
                    ·
                      rfl

theorem cell23_164455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_164455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164455 prefixEnd_164455 := by exact prefixLift 164455
  have htrace : WordTrace (prefixWord ++ tailWord_164455) baseStart_164455 baseEnd_164455 := by
    simpa [prefixWord, tailWord_164455, baseEnd_164455] using wordTrace_append hprefix tailTrace_164455
  have hstable : (prefixWord ++ tailWord_164455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164455).length < 2 ^ (prefixWord ++ tailWord_164455).sum := by decide
  have hdescent : baseEnd_164455 < baseStart_164455 := by decide
  rcases family_descends (prefixWord ++ tailWord_164455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164466 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_164466 : Nat := 118140960795 + 164466 * 2 ^ 59
def prefixEnd_164466 : Nat := 4983230072969 + 3 ^ 40 * 164466 * 2
def baseEnd_164466 : Nat := 84450109322458759718641

theorem tailTrace_164466 : CollatzResearch.WordTrace tailWord_164466 prefixEnd_164466 84450109322458759718641 := by
  unfold tailWord_164466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499641955543811350416313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3999045214783496934443501 1499641955543811350416313)
  ·
    refine ⟨1124731466657858512812235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1499641955543811350416313 1124731466657858512812235)
    ·
      refine ⟨1687097199986787769218353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1124731466657858512812235 1687097199986787769218353)
      ·
        refine ⟨1265322899990090826913765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1687097199986787769218353 1265322899990090826913765)
        ·
          refine ⟨237248043748142030046331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1265322899990090826913765 237248043748142030046331)
          ·
            refine ⟨355872065622213045069497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237248043748142030046331 355872065622213045069497)
            ·
              refine ⟨266904049216659783802123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355872065622213045069497 266904049216659783802123)
              ·
                refine ⟨400356073824989675703185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266904049216659783802123 400356073824989675703185)
                ·
                  refine ⟨300267055368742256777389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400356073824989675703185 300267055368742256777389)
                  ·
                    refine ⟨112600145763278346291521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300267055368742256777389 112600145763278346291521)
                    ·
                      refine ⟨84450109322458759718641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112600145763278346291521 84450109322458759718641)
                      ·
                        rfl

theorem cell23_164466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_164466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164466 prefixEnd_164466 := by exact prefixLift 164466
  have htrace : WordTrace (prefixWord ++ tailWord_164466) baseStart_164466 baseEnd_164466 := by
    simpa [prefixWord, tailWord_164466, baseEnd_164466] using wordTrace_append hprefix tailTrace_164466
  have hstable : (prefixWord ++ tailWord_164466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164466).length < 2 ^ (prefixWord ++ tailWord_164466).sum := by decide
  have hdescent : baseEnd_164466 < baseStart_164466 := by decide
  rcases family_descends (prefixWord ++ tailWord_164466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164490 : List Nat := [3, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_164490 : Nat := 118140960795 + 164490 * 2 ^ 59
def prefixEnd_164490 : Nat := 4983230072969 + 3 ^ 40 * 164490 * 2
def baseEnd_164490 : Nat := 84462432858166665818531

theorem tailTrace_164490 : CollatzResearch.WordTrace tailWord_164490 prefixEnd_164490 84462432858166665818531 := by
  unfold tailWord_164490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499860793522074375134731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3999628782725531667025949 1499860793522074375134731)
  ·
    refine ⟨2249791190283111562702097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1499860793522074375134731 2249791190283111562702097)
    ·
      refine ⟨1687343392712333672026573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2249791190283111562702097 1687343392712333672026573)
      ·
        refine ⟨632753772267125127009965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1687343392712333672026573 632753772267125127009965)
        ·
          refine ⟨237282664600171922628737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632753772267125127009965 237282664600171922628737)
          ·
            refine ⟨177961998450128941971553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237282664600171922628737 177961998450128941971553)
            ·
              refine ⟨133471498837596706478665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177961998450128941971553 133471498837596706478665)
              ·
                refine ⟨100103624128197529858999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133471498837596706478665 100103624128197529858999)
                ·
                  refine ⟨150155436192296294788499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100103624128197529858999 150155436192296294788499)
                  ·
                    refine ⟨225233154288444442182749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150155436192296294788499 225233154288444442182749)
                    ·
                      refine ⟨84462432858166665818531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225233154288444442182749 84462432858166665818531)
                      ·
                        rfl

theorem cell23_164490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_164490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164490 prefixEnd_164490 := by exact prefixLift 164490
  have htrace : WordTrace (prefixWord ++ tailWord_164490) baseStart_164490 baseEnd_164490 := by
    simpa [prefixWord, tailWord_164490, baseEnd_164490] using wordTrace_append hprefix tailTrace_164490
  have hstable : (prefixWord ++ tailWord_164490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164490).length < 2 ^ (prefixWord ++ tailWord_164490).sum := by decide
  have hdescent : baseEnd_164490 < baseStart_164490 := by decide
  rcases family_descends (prefixWord ++ tailWord_164490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164533 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_164533 : Nat := 118140960795 + 164533 * 2 ^ 59
def prefixEnd_164533 : Nat := 4983230072969 + 3 ^ 40 * 164533 * 2
def baseEnd_164533 : Nat := 84484512526309997580833

theorem tailTrace_164533 : CollatzResearch.WordTrace tailWord_164533 prefixEnd_164533 84484512526309997580833 := by
  unfold tailWord_164533
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001011512932515844354253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4000674341955010562902835 6001011512932515844354253)
  ·
    refine ⟨2250379317349693441632845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6001011512932515844354253 2250379317349693441632845)
    ·
      refine ⟨843892244006135040612317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2250379317349693441632845 843892244006135040612317)
      ·
        refine ⟨316459591502300640229619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 843892244006135040612317 316459591502300640229619)
        ·
          refine ⟨474689387253450960344429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316459591502300640229619 474689387253450960344429)
          ·
            refine ⟨178008520220044110129161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474689387253450960344429 178008520220044110129161)
            ·
              refine ⟨133506390165033082596871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178008520220044110129161 133506390165033082596871)
              ·
                refine ⟨200259585247549623895307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133506390165033082596871 200259585247549623895307)
                ·
                  refine ⟨300389377871324435842961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200259585247549623895307 300389377871324435842961)
                  ·
                    refine ⟨225292033403493326882221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 300389377871324435842961 225292033403493326882221)
                    ·
                      refine ⟨84484512526309997580833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225292033403493326882221 84484512526309997580833)
                      ·
                        rfl

theorem cell23_164533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_164533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164533 prefixEnd_164533 := by exact prefixLift 164533
  have htrace : WordTrace (prefixWord ++ tailWord_164533) baseStart_164533 baseEnd_164533 := by
    simpa [prefixWord, tailWord_164533, baseEnd_164533] using wordTrace_append hprefix tailTrace_164533
  have hstable : (prefixWord ++ tailWord_164533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164533).length < 2 ^ (prefixWord ++ tailWord_164533).sum := by decide
  have hdescent : baseEnd_164533 < baseStart_164533 := by decide
  rcases family_descends (prefixWord ++ tailWord_164533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164555 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5]
def baseStart_164555 : Nat := 118140960795 + 164555 * 2 ^ 59
def prefixEnd_164555 : Nat := 4983230072969 + 3 ^ 40 * 164555 * 2
def baseEnd_164555 : Nat := 84495809100708911505731

theorem tailTrace_164555 : CollatzResearch.WordTrace tailWord_164555 prefixEnd_164555 84495809100708911505731 := by
  unfold tailWord_164555
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001813918852813601655119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4001209279235209067770079 6001813918852813601655119)
  ·
    refine ⟨9002720878279220402482679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6001813918852813601655119 9002720878279220402482679)
    ·
      refine ⟨13504081317418830603724019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9002720878279220402482679 13504081317418830603724019)
      ·
        refine ⟨20256121976128245905586029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13504081317418830603724019 20256121976128245905586029)
        ·
          refine ⟨7596045741048092214594761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20256121976128245905586029 7596045741048092214594761)
          ·
            refine ⟨5697034305786069160946071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7596045741048092214594761 5697034305786069160946071)
            ·
              refine ⟨8545551458679103741419107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697034305786069160946071 8545551458679103741419107)
              ·
                refine ⟨12818327188018655612128661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8545551458679103741419107 12818327188018655612128661)
                ·
                  refine ⟨600859086938374481818531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12818327188018655612128661 600859086938374481818531)
                  ·
                    refine ⟨901288630407561722727797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 600859086938374481818531 901288630407561722727797)
                    ·
                      refine ⟨84495809100708911505731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 901288630407561722727797 84495809100708911505731)
                      ·
                        rfl

theorem cell23_164555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_164555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164555 prefixEnd_164555 := by exact prefixLift 164555
  have htrace : WordTrace (prefixWord ++ tailWord_164555) baseStart_164555 baseEnd_164555 := by
    simpa [prefixWord, tailWord_164555, baseEnd_164555] using wordTrace_append hprefix tailTrace_164555
  have hstable : (prefixWord ++ tailWord_164555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164555).length < 2 ^ (prefixWord ++ tailWord_164555).sum := by decide
  have hdescent : baseEnd_164555 < baseStart_164555 := by decide
  rcases family_descends (prefixWord ++ tailWord_164555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164602 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_164602 : Nat := 118140960795 + 164602 * 2 ^ 59
def prefixEnd_164602 : Nat := 4983230072969 + 3 ^ 40 * 164602 * 2
def baseEnd_164602 : Nat := 84519942691470227618015

theorem tailTrace_164602 : CollatzResearch.WordTrace tailWord_164602 prefixEnd_164602 84519942691470227618015 := by
  unfold tailWord_164602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500882037420635157154015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4002352099788360419077373 1500882037420635157154015)
  ·
    refine ⟨2251323056130952735731023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1500882037420635157154015 2251323056130952735731023)
    ·
      refine ⟨3376984584196429103596535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2251323056130952735731023 3376984584196429103596535)
      ·
        refine ⟨5065476876294643655394803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3376984584196429103596535 5065476876294643655394803)
        ·
          refine ⟨7598215314441965483092205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5065476876294643655394803 7598215314441965483092205)
          ·
            refine ⟨2849330742915737056159577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7598215314441965483092205 2849330742915737056159577)
            ·
              refine ⟨2136998057186802792119683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849330742915737056159577 2136998057186802792119683)
              ·
                refine ⟨3205497085780204188179525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136998057186802792119683 3205497085780204188179525)
                ·
                  refine ⟨601030703583788285283661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3205497085780204188179525 601030703583788285283661)
                  ·
                    refine ⟨225386513843920606981373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601030703583788285283661 225386513843920606981373)
                    ·
                      refine ⟨84519942691470227618015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225386513843920606981373 84519942691470227618015)
                      ·
                        rfl

theorem cell23_164602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_164602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164602 prefixEnd_164602 := by exact prefixLift 164602
  have htrace : WordTrace (prefixWord ++ tailWord_164602) baseStart_164602 baseEnd_164602 := by
    simpa [prefixWord, tailWord_164602, baseEnd_164602] using wordTrace_append hprefix tailTrace_164602
  have hstable : (prefixWord ++ tailWord_164602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164602).length < 2 ^ (prefixWord ++ tailWord_164602).sum := by decide
  have hdescent : baseEnd_164602 < baseStart_164602 := by decide
  rcases family_descends (prefixWord ++ tailWord_164602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164622 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_164622 : Nat := 118140960795 + 164622 * 2 ^ 59
def prefixEnd_164622 : Nat := 4983230072969 + 3 ^ 40 * 164622 * 2
def baseEnd_164622 : Nat := 28176737434853383122641

theorem tailTrace_164622 : CollatzResearch.WordTrace tailWord_164622 prefixEnd_164622 28176737434853383122641 := by
  unfold tailWord_164622
  simp only [CollatzResearch.WordTrace]
  refine ⟨750532201201260505543015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4002838406406722696229413 750532201201260505543015)
  ·
    refine ⟨1125798301801890758314523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 750532201201260505543015 1125798301801890758314523)
    ·
      refine ⟨1688697452702836137471785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125798301801890758314523 1688697452702836137471785)
      ·
        refine ⟨1266523089527127103103839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1688697452702836137471785 1266523089527127103103839)
        ·
          refine ⟨1899784634290690654655759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266523089527127103103839 1899784634290690654655759)
          ·
            refine ⟨2849676951436035981983639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899784634290690654655759 2849676951436035981983639)
            ·
              refine ⟨4274515427154053972975459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849676951436035981983639 4274515427154053972975459)
              ·
                refine ⟨6411773140731080959463189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4274515427154053972975459 6411773140731080959463189)
                ·
                  refine ⟨300551865971769419974837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6411773140731080959463189 300551865971769419974837)
                  ·
                    refine ⟨28176737434853383122641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 300551865971769419974837 28176737434853383122641)
                    ·
                      rfl

theorem cell23_164622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_164622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164622 prefixEnd_164622 := by exact prefixLift 164622
  have htrace : WordTrace (prefixWord ++ tailWord_164622) baseStart_164622 baseEnd_164622 := by
    simpa [prefixWord, tailWord_164622, baseEnd_164622] using wordTrace_append hprefix tailTrace_164622
  have hstable : (prefixWord ++ tailWord_164622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164622).length < 2 ^ (prefixWord ++ tailWord_164622).sum := by decide
  have hdescent : baseEnd_164622 < baseStart_164622 := by decide
  rcases family_descends (prefixWord ++ tailWord_164622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164639 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 2, 5]
def baseStart_164639 : Nat := 118140960795 + 164639 * 2 ^ 59
def prefixEnd_164639 : Nat := 4983230072969 + 3 ^ 40 * 164639 * 2
def baseEnd_164639 : Nat := 28179647158562194285115

theorem tailTrace_164639 : CollatzResearch.WordTrace tailWord_164639 prefixEnd_164639 28179647158562194285115 := by
  unfold tailWord_164639
  simp only [CollatzResearch.WordTrace]
  refine ⟨6004877650548495947712971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4003251767032330631808647 6004877650548495947712971)
  ·
    refine ⟨9007316475822743921569457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6004877650548495947712971 9007316475822743921569457)
    ·
      refine ⟨6755487356867057941177093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9007316475822743921569457 6755487356867057941177093)
      ·
        refine ⟨1266653879412573363970705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6755487356867057941177093 1266653879412573363970705)
        ·
          refine ⟨949990409559430022978029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266653879412573363970705 949990409559430022978029)
          ·
            refine ⟨356246403584786258616761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 949990409559430022978029 356246403584786258616761)
            ·
              refine ⟨267184802688589693962571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356246403584786258616761 267184802688589693962571)
              ·
                refine ⟨400777204032884540943857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267184802688589693962571 400777204032884540943857)
                ·
                  refine ⟨300582903024663405707893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400777204032884540943857 300582903024663405707893)
                  ·
                    refine ⟨28179647158562194285115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 300582903024663405707893 28179647158562194285115)
                    ·
                      rfl

theorem cell23_164639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_164639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164639 prefixEnd_164639 := by exact prefixLift 164639
  have htrace : WordTrace (prefixWord ++ tailWord_164639) baseStart_164639 baseEnd_164639 := by
    simpa [prefixWord, tailWord_164639, baseEnd_164639] using wordTrace_append hprefix tailTrace_164639
  have hstable : (prefixWord ++ tailWord_164639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164639).length < 2 ^ (prefixWord ++ tailWord_164639).sum := by decide
  have hdescent : baseEnd_164639 < baseStart_164639 := by decide
  rcases family_descends (prefixWord ++ tailWord_164639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164659 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 4]
def baseStart_164659 : Nat := 118140960795 + 164659 * 2 ^ 59
def prefixEnd_164659 : Nat := 4983230072969 + 3 ^ 40 * 164659 * 2
def baseEnd_164659 : Nat := 84549211088776504605253

theorem tailTrace_164659 : CollatzResearch.WordTrace tailWord_164659 prefixEnd_164659 84549211088776504605253 := by
  unfold tailWord_164659
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005607110476039363441031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4003738073650692908960687 6005607110476039363441031)
  ·
    refine ⟨9008410665714059045161547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6005607110476039363441031 9008410665714059045161547)
    ·
      refine ⟨13512615998571088567742321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9008410665714059045161547 13512615998571088567742321)
      ·
        refine ⟨10134461998928316425806741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13512615998571088567742321 10134461998928316425806741)
        ·
          refine ⟨475052906199764832459691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10134461998928316425806741 475052906199764832459691)
          ·
            refine ⟨712579359299647248689537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475052906199764832459691 712579359299647248689537)
            ·
              refine ⟨534434519474735436517153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712579359299647248689537 534434519474735436517153)
              ·
                refine ⟨400825889606051577387865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534434519474735436517153 400825889606051577387865)
                ·
                  refine ⟨300619417204538683040899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400825889606051577387865 300619417204538683040899)
                  ·
                    refine ⟨450929125806808024561349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300619417204538683040899 450929125806808024561349)
                    ·
                      refine ⟨84549211088776504605253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 450929125806808024561349 84549211088776504605253)
                      ·
                        rfl

theorem cell23_164659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_164659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164659 prefixEnd_164659 := by exact prefixLift 164659
  have htrace : WordTrace (prefixWord ++ tailWord_164659) baseStart_164659 baseEnd_164659 := by
    simpa [prefixWord, tailWord_164659, baseEnd_164659] using wordTrace_append hprefix tailTrace_164659
  have hstable : (prefixWord ++ tailWord_164659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164659).length < 2 ^ (prefixWord ++ tailWord_164659).sum := by decide
  have hdescent : baseEnd_164659 < baseStart_164659 := by decide
  rcases family_descends (prefixWord ++ tailWord_164659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164660 : List Nat := [2, 5, 1, 1, 3, 2, 2, 2, 5]
def baseStart_164660 : Nat := 118140960795 + 164660 * 2 ^ 59
def prefixEnd_164660 : Nat := 4983230072969 + 3 ^ 40 * 164660 * 2
def baseEnd_164660 : Nat := 9394413841047888965861

theorem tailTrace_164660 : CollatzResearch.WordTrace tailWord_164660 prefixEnd_164660 9394413841047888965861 := by
  unfold tailWord_164660
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002821791736208267113717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4003762388981611022818289 3002821791736208267113717)
  ·
    refine ⟨281514542975269525041911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3002821791736208267113717 281514542975269525041911)
    ·
      refine ⟨422271814462904287562867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281514542975269525041911 422271814462904287562867)
      ·
        refine ⟨633407721694356431344301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422271814462904287562867 633407721694356431344301)
        ·
          refine ⟨237527895635383661754113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 633407721694356431344301 237527895635383661754113)
          ·
            refine ⟨178145921726537746315585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237527895635383661754113 178145921726537746315585)
            ·
              refine ⟨133609441294903309736689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178145921726537746315585 133609441294903309736689)
              ·
                refine ⟨100207080971177482302517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133609441294903309736689 100207080971177482302517)
                ·
                  refine ⟨9394413841047888965861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100207080971177482302517 9394413841047888965861)
                  ·
                    rfl

theorem cell23_164660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_164660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164660 prefixEnd_164660 := by exact prefixLift 164660
  have htrace : WordTrace (prefixWord ++ tailWord_164660) baseStart_164660 baseEnd_164660 := by
    simpa [prefixWord, tailWord_164660, baseEnd_164660] using wordTrace_append hprefix tailTrace_164660
  have hstable : (prefixWord ++ tailWord_164660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164660).length < 2 ^ (prefixWord ++ tailWord_164660).sum := by decide
  have hdescent : baseEnd_164660 < baseStart_164660 := by decide
  rcases family_descends (prefixWord ++ tailWord_164660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164746 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_164746 : Nat := 118140960795 + 164746 * 2 ^ 59
def prefixEnd_164746 : Nat := 4983230072969 + 3 ^ 40 * 164746 * 2
def baseEnd_164746 : Nat := 28197961301905888072451

theorem tailTrace_164746 : CollatzResearch.WordTrace tailWord_164746 prefixEnd_164746 28197961301905888072451 := by
  unfold tailWord_164746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502195065290213305464523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4005853507440568814572061 1502195065290213305464523)
  ·
    refine ⟨2253292597935319958196785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1502195065290213305464523 2253292597935319958196785)
    ·
      refine ⟨1689969448451489968647589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2253292597935319958196785 1689969448451489968647589)
      ·
        refine ⟨316869271584654369121423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1689969448451489968647589 316869271584654369121423)
        ·
          refine ⟨475303907376981553682135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316869271584654369121423 475303907376981553682135)
          ·
            refine ⟨712955861065472330523203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475303907376981553682135 712955861065472330523203)
            ·
              refine ⟨1069433791598208495784805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712955861065472330523203 1069433791598208495784805)
              ·
                refine ⟨200518835924664092959651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1069433791598208495784805 200518835924664092959651)
                ·
                  refine ⟨300778253886996139439477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200518835924664092959651 300778253886996139439477)
                  ·
                    refine ⟨28197961301905888072451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 300778253886996139439477 28197961301905888072451)
                    ·
                      rfl

theorem cell23_164746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_164746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164746 prefixEnd_164746 := by exact prefixLift 164746
  have htrace : WordTrace (prefixWord ++ tailWord_164746) baseStart_164746 baseEnd_164746 := by
    simpa [prefixWord, tailWord_164746, baseEnd_164746] using wordTrace_append hprefix tailTrace_164746
  have hstable : (prefixWord ++ tailWord_164746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164746).length < 2 ^ (prefixWord ++ tailWord_164746).sum := by decide
  have hdescent : baseEnd_164746 < baseStart_164746 := by decide
  rcases family_descends (prefixWord ++ tailWord_164746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164759 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 6, 4]
def baseStart_164759 : Nat := 118140960795 + 164759 * 2 ^ 59
def prefixEnd_164759 : Nat := 4983230072969 + 3 ^ 40 * 164759 * 2
def baseEnd_164759 : Nat := 28200186384742037784931

theorem tailTrace_164759 : CollatzResearch.WordTrace tailWord_164759 prefixEnd_164759 28200186384742037784931 := by
  unfold tailWord_164759
  simp only [CollatzResearch.WordTrace]
  refine ⟨6009254410113756442081331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4006169606742504294720887 6009254410113756442081331)
  ·
    refine ⟨9013881615170634663121997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6009254410113756442081331 9013881615170634663121997)
    ·
      refine ⟨3380205605688987998670749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9013881615170634663121997 3380205605688987998670749)
      ·
        refine ⟨1267577102133370499501531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3380205605688987998670749 1267577102133370499501531)
        ·
          refine ⟨1901365653200055749252297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267577102133370499501531 1901365653200055749252297)
          ·
            refine ⟨1426024239900041811939223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1901365653200055749252297 1426024239900041811939223)
            ·
              refine ⟨2139036359850062717908835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426024239900041811939223 2139036359850062717908835)
              ·
                refine ⟨3208554539775094076863253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139036359850062717908835 3208554539775094076863253)
                ·
                  refine ⟨150400994051957534852965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3208554539775094076863253 150400994051957534852965)
                  ·
                    refine ⟨28200186384742037784931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150400994051957534852965 28200186384742037784931)
                    ·
                      rfl

theorem cell23_164759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_164759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164759 prefixEnd_164759 := by exact prefixLift 164759
  have htrace : WordTrace (prefixWord ++ tailWord_164759) baseStart_164759 baseEnd_164759 := by
    simpa [prefixWord, tailWord_164759, baseEnd_164759] using wordTrace_append hprefix tailTrace_164759
  have hstable : (prefixWord ++ tailWord_164759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164759).length < 2 ^ (prefixWord ++ tailWord_164759).sum := by decide
  have hdescent : baseEnd_164759 < baseStart_164759 := by decide
  rcases family_descends (prefixWord ++ tailWord_164759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164789 : List Nat := [1, 3, 3, 2, 1, 1, 4, 8]
def baseStart_164789 : Nat := 118140960795 + 164789 * 2 ^ 59
def prefixEnd_164789 : Nat := 4983230072969 + 3 ^ 40 * 164789 * 2
def baseEnd_164789 : Nat := 3133924576809666517765

theorem tailTrace_164789 : CollatzResearch.WordTrace tailWord_164789 prefixEnd_164789 3133924576809666517765 := by
  unfold tailWord_164789
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010348600005071565673421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4006899066670047710448947 6010348600005071565673421)
  ·
    refine ⟨2253880725001901837127533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6010348600005071565673421 2253880725001901837127533)
    ·
      refine ⟨845205271875713188922825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2253880725001901837127533 845205271875713188922825)
      ·
        refine ⟨633903953906784891692119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 845205271875713188922825 633903953906784891692119)
        ·
          refine ⟨950855930860177337538179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633903953906784891692119 950855930860177337538179)
          ·
            refine ⟨1426283896290266006307269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950855930860177337538179 1426283896290266006307269)
            ·
              refine ⟨267428230554424876182613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1426283896290266006307269 267428230554424876182613)
              ·
                refine ⟨3133924576809666517765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 267428230554424876182613 3133924576809666517765)
                ·
                  rfl

theorem cell23_164789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 8].length) (baseStart_164789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164789 prefixEnd_164789 := by exact prefixLift 164789
  have htrace : WordTrace (prefixWord ++ tailWord_164789) baseStart_164789 baseEnd_164789 := by
    simpa [prefixWord, tailWord_164789, baseEnd_164789] using wordTrace_append hprefix tailTrace_164789
  have hstable : (prefixWord ++ tailWord_164789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164789).length < 2 ^ (prefixWord ++ tailWord_164789).sum := by decide
  have hdescent : baseEnd_164789 < baseStart_164789 := by decide
  rcases family_descends (prefixWord ++ tailWord_164789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164793 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 2, 4]
def baseStart_164793 : Nat := 118140960795 + 164793 * 2 ^ 59
def prefixEnd_164793 : Nat := 4983230072969 + 3 ^ 40 * 164793 * 2
def baseEnd_164793 : Nat := 28206005832159660109879

theorem tailTrace_164793 : CollatzResearch.WordTrace tailWord_164793 prefixEnd_164793 28206005832159660109879 := by
  unfold tailWord_164793
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010494491990580248819033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4006996327993720165879355 6010494491990580248819033)
  ·
    refine ⟨4507870868992935186614275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6010494491990580248819033 4507870868992935186614275)
    ·
      refine ⟨6761806303489402779921413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4507870868992935186614275 6761806303489402779921413)
      ·
        refine ⟨1267838681904263021235265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6761806303489402779921413 1267838681904263021235265)
        ·
          refine ⟨950879011428197265926449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1267838681904263021235265 950879011428197265926449)
          ·
            refine ⟨713159258571147949444837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950879011428197265926449 713159258571147949444837)
            ·
              refine ⟨133717360982090240520907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 713159258571147949444837 133717360982090240520907)
              ·
                refine ⟨200576041473135360781361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133717360982090240520907 200576041473135360781361)
                ·
                  refine ⟨150432031104851520586021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200576041473135360781361 150432031104851520586021)
                  ·
                    refine ⟨28206005832159660109879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150432031104851520586021 28206005832159660109879)
                    ·
                      rfl

theorem cell23_164793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 4].length) (baseStart_164793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164793 prefixEnd_164793 := by exact prefixLift 164793
  have htrace : WordTrace (prefixWord ++ tailWord_164793) baseStart_164793 baseEnd_164793 := by
    simpa [prefixWord, tailWord_164793, baseEnd_164793] using wordTrace_append hprefix tailTrace_164793
  have hstable : (prefixWord ++ tailWord_164793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164793).length < 2 ^ (prefixWord ++ tailWord_164793).sum := by decide
  have hdescent : baseEnd_164793 < baseStart_164793 := by decide
  rcases family_descends (prefixWord ++ tailWord_164793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164820 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_164820 : Nat := 118140960795 + 164820 * 2 ^ 59
def prefixEnd_164820 : Nat := 4983230072969 + 3 ^ 40 * 164820 * 2
def baseEnd_164820 : Nat := 84631881474150374692013

theorem tailTrace_164820 : CollatzResearch.WordTrace tailWord_164820 prefixEnd_164820 84631881474150374692013 := by
  unfold tailWord_164820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005739631446381930025957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4007652841928509240034609 3005739631446381930025957)
  ·
    refine ⟨563576180896196611879867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3005739631446381930025957 563576180896196611879867)
    ·
      refine ⟨845364271344294917819801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563576180896196611879867 845364271344294917819801)
      ·
        refine ⟨634023203508221188364851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 845364271344294917819801 634023203508221188364851)
        ·
          refine ⟨951034805262331782547277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634023203508221188364851 951034805262331782547277)
          ·
            refine ⟨356638051973374418455229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 951034805262331782547277 356638051973374418455229)
            ·
              refine ⟨133739269490015406920711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356638051973374418455229 133739269490015406920711)
              ·
                refine ⟨200608904235023110381067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133739269490015406920711 200608904235023110381067)
                ·
                  refine ⟨300913356352534665571601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200608904235023110381067 300913356352534665571601)
                  ·
                    refine ⟨225685017264400999178701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 300913356352534665571601 225685017264400999178701)
                    ·
                      refine ⟨84631881474150374692013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225685017264400999178701 84631881474150374692013)
                      ·
                        rfl

theorem cell23_164820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_164820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164820 prefixEnd_164820 := by exact prefixLift 164820
  have htrace : WordTrace (prefixWord ++ tailWord_164820) baseStart_164820 baseEnd_164820 := by
    simpa [prefixWord, tailWord_164820, baseEnd_164820] using wordTrace_append hprefix tailTrace_164820
  have hstable : (prefixWord ++ tailWord_164820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164820).length < 2 ^ (prefixWord ++ tailWord_164820).sum := by decide
  have hdescent : baseEnd_164820 < baseStart_164820 := by decide
  rcases family_descends (prefixWord ++ tailWord_164820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164834 : List Nat := [3, 3, 3, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_164834 : Nat := 118140960795 + 164834 * 2 ^ 59
def prefixEnd_164834 : Nat := 4983230072969 + 3 ^ 40 * 164834 * 2
def baseEnd_164834 : Nat := 84639070203313319916949

theorem tailTrace_164834 : CollatzResearch.WordTrace tailWord_164834 prefixEnd_164834 84639070203313319916949 := by
  unfold tailWord_164834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502997471210511062765389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4007993256561362834041037 1502997471210511062765389)
  ·
    refine ⟨563624051703941648537021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1502997471210511062765389 563624051703941648537021)
    ·
      refine ⟨211359019388978118201383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 563624051703941648537021 211359019388978118201383)
      ·
        refine ⟨317038529083467177302075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211359019388978118201383 317038529083467177302075)
        ·
          refine ⟨475557793625200765953113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317038529083467177302075 475557793625200765953113)
          ·
            refine ⟨356668345218900574464835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475557793625200765953113 356668345218900574464835)
            ·
              refine ⟨535002517828350861697253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356668345218900574464835 535002517828350861697253)
              ·
                refine ⟨100312972092815786568235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535002517828350861697253 100312972092815786568235)
                ·
                  refine ⟨150469458139223679852353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100312972092815786568235 150469458139223679852353)
                  ·
                    refine ⟨112852093604417759889265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150469458139223679852353 112852093604417759889265)
                    ·
                      refine ⟨84639070203313319916949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112852093604417759889265 84639070203313319916949)
                      ·
                        rfl

theorem cell23_164834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_164834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164834 prefixEnd_164834 := by exact prefixLift 164834
  have htrace : WordTrace (prefixWord ++ tailWord_164834) baseStart_164834 baseEnd_164834 := by
    simpa [prefixWord, tailWord_164834, baseEnd_164834] using wordTrace_append hprefix tailTrace_164834
  have hstable : (prefixWord ++ tailWord_164834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164834).length < 2 ^ (prefixWord ++ tailWord_164834).sum := by decide
  have hdescent : baseEnd_164834 < baseStart_164834 := by decide
  rcases family_descends (prefixWord ++ tailWord_164834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164849 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 1, 8]
def baseStart_164849 : Nat := 118140960795 + 164849 * 2 ^ 59
def prefixEnd_164849 : Nat := 4983230072969 + 3 ^ 40 * 164849 * 2
def baseEnd_164849 : Nat := 28215590804376920409793

theorem tailTrace_164849 : CollatzResearch.WordTrace tailWord_164849 prefixEnd_164849 28215590804376920409793 := by
  unfold tailWord_164849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012536979787701812857601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4008357986525134541905067 6012536979787701812857601)
  ·
    refine ⟨4509402734840776359643201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6012536979787701812857601 4509402734840776359643201)
    ·
      refine ⟨3382052051130582269732401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4509402734840776359643201 3382052051130582269732401)
      ·
        refine ⟨2536539038347936702299301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3382052051130582269732401 2536539038347936702299301)
        ·
          refine ⟨475601069690238131681119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2536539038347936702299301 475601069690238131681119)
          ·
            refine ⟨713401604535357197521679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475601069690238131681119 713401604535357197521679)
            ·
              refine ⟨1070102406803035796282519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713401604535357197521679 1070102406803035796282519)
              ·
                refine ⟨1605153610204553694423779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070102406803035796282519 1605153610204553694423779)
                ·
                  refine ⟨2407730415306830541635669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605153610204553694423779 2407730415306830541635669)
                  ·
                    refine ⟨28215590804376920409793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2407730415306830541635669 28215590804376920409793)
                    ·
                      rfl

theorem cell23_164849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_164849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164849 prefixEnd_164849 := by exact prefixLift 164849
  have htrace : WordTrace (prefixWord ++ tailWord_164849) baseStart_164849 baseEnd_164849 := by
    simpa [prefixWord, tailWord_164849, baseEnd_164849] using wordTrace_append hprefix tailTrace_164849
  have hstable : (prefixWord ++ tailWord_164849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164849).length < 2 ^ (prefixWord ++ tailWord_164849).sum := by decide
  have hdescent : baseEnd_164849 < baseStart_164849 := by decide
  rcases family_descends (prefixWord ++ tailWord_164849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164850 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_164850 : Nat := 118140960795 + 164850 * 2 ^ 59
def prefixEnd_164850 : Nat := 4983230072969 + 3 ^ 40 * 164850 * 2
def baseEnd_164850 : Nat := 84647285893785257316875

theorem tailTrace_164850 : CollatzResearch.WordTrace tailWord_164850 prefixEnd_164850 84647285893785257316875 := by
  unfold tailWord_164850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503143363196019745911001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4008382301856052655762669 1503143363196019745911001)
  ·
    refine ⟨1127357522397014809433251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1503143363196019745911001 1127357522397014809433251)
    ·
      refine ⟨1691036283595522214149877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127357522397014809433251 1691036283595522214149877)
      ·
        refine ⟨158534651587080207576551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1691036283595522214149877 158534651587080207576551)
        ·
          refine ⟨237801977380620311364827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158534651587080207576551 237801977380620311364827)
          ·
            refine ⟨356702966070930467047241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237801977380620311364827 356702966070930467047241)
            ·
              refine ⟨267527224553197850285431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356702966070930467047241 267527224553197850285431)
              ·
                refine ⟨401290836829796775428147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267527224553197850285431 401290836829796775428147)
                ·
                  refine ⟨601936255244695163142221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401290836829796775428147 601936255244695163142221)
                  ·
                    refine ⟨225726095716760686178333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601936255244695163142221 225726095716760686178333)
                    ·
                      refine ⟨84647285893785257316875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225726095716760686178333 84647285893785257316875)
                      ·
                        rfl

theorem cell23_164850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_164850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164850 prefixEnd_164850 := by exact prefixLift 164850
  have htrace : WordTrace (prefixWord ++ tailWord_164850) baseStart_164850 baseEnd_164850 := by
    simpa [prefixWord, tailWord_164850, baseEnd_164850] using wordTrace_append hprefix tailTrace_164850
  have hstable : (prefixWord ++ tailWord_164850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164850).length < 2 ^ (prefixWord ++ tailWord_164850).sum := by decide
  have hdescent : baseEnd_164850 < baseStart_164850 := by decide
  rcases family_descends (prefixWord ++ tailWord_164850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164859 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 3]
def baseStart_164859 : Nat := 118140960795 + 164859 * 2 ^ 59
def prefixEnd_164859 : Nat := 4983230072969 + 3 ^ 40 * 164859 * 2
def baseEnd_164859 : Nat := 84651907219675722104333

theorem tailTrace_164859 : CollatzResearch.WordTrace tailWord_164859 prefixEnd_164859 84651907219675722104333 := by
  unfold tailWord_164859
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012901709751473520721631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4008601139834315680481087 6012901709751473520721631)
  ·
    refine ⟨9019352564627210281082447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6012901709751473520721631 9019352564627210281082447)
    ·
      refine ⟨13529028846940815421623671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9019352564627210281082447 13529028846940815421623671)
      ·
        refine ⟨20293543270411223132435507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13529028846940815421623671 20293543270411223132435507)
        ·
          refine ⟨30440314905616834698653261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20293543270411223132435507 30440314905616834698653261)
          ·
            refine ⟨11415118089606313011994973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30440314905616834698653261 11415118089606313011994973)
            ·
              refine ⟨4280669283602367379498115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11415118089606313011994973 4280669283602367379498115)
              ·
                refine ⟨6421003925403551069247173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4280669283602367379498115 6421003925403551069247173)
                ·
                  refine ⟨1203938236013165825483845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6421003925403551069247173 1203938236013165825483845)
                  ·
                    refine ⟨225738419252468592278221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203938236013165825483845 225738419252468592278221)
                    ·
                      refine ⟨84651907219675722104333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225738419252468592278221 84651907219675722104333)
                      ·
                        rfl

theorem cell23_164859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 3].length) (baseStart_164859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164859 prefixEnd_164859 := by exact prefixLift 164859
  have htrace : WordTrace (prefixWord ++ tailWord_164859) baseStart_164859 baseEnd_164859 := by
    simpa [prefixWord, tailWord_164859, baseEnd_164859] using wordTrace_append hprefix tailTrace_164859
  have hstable : (prefixWord ++ tailWord_164859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164859).length < 2 ^ (prefixWord ++ tailWord_164859).sum := by decide
  have hdescent : baseEnd_164859 < baseStart_164859 := by decide
  rcases family_descends (prefixWord ++ tailWord_164859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164869 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_164869 : Nat := 118140960795 + 164869 * 2 ^ 59
def prefixEnd_164869 : Nat := 4983230072969 + 3 ^ 40 * 164869 * 2
def baseEnd_164869 : Nat := 84657042026220682979287

theorem tailTrace_164869 : CollatzResearch.WordTrace tailWord_164869 prefixEnd_164869 84657042026220682979287 := by
  unfold tailWord_164869
  simp only [CollatzResearch.WordTrace]
  refine ⟨6013266439715245228585661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4008844293143496819057107 6013266439715245228585661)
  ·
    refine ⟨2254974914893216960719623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6013266439715245228585661 2254974914893216960719623)
    ·
      refine ⟨3382462372339825441079435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2254974914893216960719623 3382462372339825441079435)
      ·
        refine ⟨5073693558509738161619153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382462372339825441079435 5073693558509738161619153)
        ·
          refine ⟨3805270168882303621214365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5073693558509738161619153 3805270168882303621214365)
          ·
            refine ⟨1426976313330863857955387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3805270168882303621214365 1426976313330863857955387)
            ·
              refine ⟨2140464469996295786933081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426976313330863857955387 2140464469996295786933081)
              ·
                refine ⟨1605348352497221840199811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140464469996295786933081 1605348352497221840199811)
                ·
                  refine ⟨2408022528745832760299717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605348352497221840199811 2408022528745832760299717)
                  ·
                    refine ⟨451504224139843642556197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2408022528745832760299717 451504224139843642556197)
                    ·
                      refine ⟨84657042026220682979287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 451504224139843642556197 84657042026220682979287)
                      ·
                        rfl

theorem cell23_164869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_164869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164869 prefixEnd_164869 := by exact prefixLift 164869
  have htrace : WordTrace (prefixWord ++ tailWord_164869) baseStart_164869 baseEnd_164869 := by
    simpa [prefixWord, tailWord_164869, baseEnd_164869] using wordTrace_append hprefix tailTrace_164869
  have hstable : (prefixWord ++ tailWord_164869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164869).length < 2 ^ (prefixWord ++ tailWord_164869).sum := by decide
  have hdescent : baseEnd_164869 < baseStart_164869 := by decide
  rcases family_descends (prefixWord ++ tailWord_164869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164903 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_164903 : Nat := 118140960795 + 164903 * 2 ^ 59
def prefixEnd_164903 : Nat := 4983230072969 + 3 ^ 40 * 164903 * 2
def baseEnd_164903 : Nat := 84674500368473549954131

theorem tailTrace_164903 : CollatzResearch.WordTrace tailWord_164903 prefixEnd_164903 84674500368473549954131 := by
  unfold tailWord_164903
  simp only [CollatzResearch.WordTrace]
  refine ⟨6014506521592069035323363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4009671014394712690215575 6014506521592069035323363)
  ·
    refine ⟨9021759782388103552985045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6014506521592069035323363 9021759782388103552985045)
    ·
      refine ⟨211447494899721177023087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9021759782388103552985045 211447494899721177023087)
      ·
        refine ⟨317171242349581765534631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211447494899721177023087 317171242349581765534631)
        ·
          refine ⟨475756863524372648301947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317171242349581765534631 475756863524372648301947)
          ·
            refine ⟨713635295286558972452921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475756863524372648301947 713635295286558972452921)
            ·
              refine ⟨535226471464919229339691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713635295286558972452921 535226471464919229339691)
              ·
                refine ⟨802839707197378844009537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535226471464919229339691 802839707197378844009537)
                ·
                  refine ⟨602129780398034133007153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 802839707197378844009537 602129780398034133007153)
                  ·
                    refine ⟨451597335298525599755365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 602129780398034133007153 451597335298525599755365)
                    ·
                      refine ⟨84674500368473549954131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 451597335298525599755365 84674500368473549954131)
                      ·
                        rfl

theorem cell23_164903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_164903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164903 prefixEnd_164903 := by exact prefixLift 164903
  have htrace : WordTrace (prefixWord ++ tailWord_164903) baseStart_164903 baseEnd_164903 := by
    simpa [prefixWord, tailWord_164903, baseEnd_164903] using wordTrace_append hprefix tailTrace_164903
  have hstable : (prefixWord ++ tailWord_164903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164903).length < 2 ^ (prefixWord ++ tailWord_164903).sum := by decide
  have hdescent : baseEnd_164903 < baseStart_164903 := by decide
  rcases family_descends (prefixWord ++ tailWord_164903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164919 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_164919 : Nat := 118140960795 + 164919 * 2 ^ 59
def prefixEnd_164919 : Nat := 4983230072969 + 3 ^ 40 * 164919 * 2
def baseEnd_164919 : Nat := 84682716058945487354057

theorem tailTrace_164919 : CollatzResearch.WordTrace tailWord_164919 prefixEnd_164919 84682716058945487354057 := by
  unfold tailWord_164919
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015090089534103767905811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4010060059689402511937207 6015090089534103767905811)
  ·
    refine ⟨9022635134301155651858717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015090089534103767905811 9022635134301155651858717)
    ·
      refine ⟨3383488175362933369447019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9022635134301155651858717 3383488175362933369447019)
      ·
        refine ⟨5075232263044400054170529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383488175362933369447019 5075232263044400054170529)
        ·
          refine ⟨3806424197283300040627897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5075232263044400054170529 3806424197283300040627897)
          ·
            refine ⟨2854818147962475030470923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3806424197283300040627897 2854818147962475030470923)
            ·
              refine ⟨4282227221943712545706385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854818147962475030470923 4282227221943712545706385)
              ·
                refine ⟨3211670416457784409279789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282227221943712545706385 3211670416457784409279789)
                ·
                  refine ⟨1204376406171669153479921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3211670416457784409279789 1204376406171669153479921)
                  ·
                    refine ⟨903282304628751865109941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1204376406171669153479921 903282304628751865109941)
                    ·
                      refine ⟨84682716058945487354057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 903282304628751865109941 84682716058945487354057)
                      ·
                        rfl

theorem cell23_164919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_164919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164919 prefixEnd_164919 := by exact prefixLift 164919
  have htrace : WordTrace (prefixWord ++ tailWord_164919) baseStart_164919 baseEnd_164919 := by
    simpa [prefixWord, tailWord_164919, baseEnd_164919] using wordTrace_append hprefix tailTrace_164919
  have hstable : (prefixWord ++ tailWord_164919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164919).length < 2 ^ (prefixWord ++ tailWord_164919).sum := by decide
  have hdescent : baseEnd_164919 < baseStart_164919 := by decide
  rcases family_descends (prefixWord ++ tailWord_164919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164958 : List Nat := [4, 4, 1, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_164958 : Nat := 118140960795 + 164958 * 2 ^ 59
def prefixEnd_164958 : Nat := 4983230072969 + 3 ^ 40 * 164958 * 2
def baseEnd_164958 : Nat := 84702741804470834766379

theorem tailTrace_164958 : CollatzResearch.WordTrace tailWord_164958 prefixEnd_164958 84702741804470834766379 := by
  unfold tailWord_164958
  simp only [CollatzResearch.WordTrace]
  refine ⟨752064067049101678571941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4011008357595208952383685 752064067049101678571941)
  ·
    refine ⟨141012012571706564732239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 752064067049101678571941 141012012571706564732239)
    ·
      refine ⟨211518018857559847098359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141012012571706564732239 211518018857559847098359)
      ·
        refine ⟨317277028286339770647539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211518018857559847098359 317277028286339770647539)
        ·
          refine ⟨475915542429509655971309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317277028286339770647539 475915542429509655971309)
          ·
            refine ⟨178468328411066120989241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 475915542429509655971309 178468328411066120989241)
            ·
              refine ⟨133851246308299590741931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178468328411066120989241 133851246308299590741931)
              ·
                refine ⟨200776869462449386112897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133851246308299590741931 200776869462449386112897)
                ·
                  refine ⟨150582652096837039584673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200776869462449386112897 150582652096837039584673)
                  ·
                    refine ⟨112936989072627779688505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150582652096837039584673 112936989072627779688505)
                    ·
                      refine ⟨84702741804470834766379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 112936989072627779688505 84702741804470834766379)
                      ·
                        rfl

theorem cell23_164958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_164958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164958 prefixEnd_164958 := by exact prefixLift 164958
  have htrace : WordTrace (prefixWord ++ tailWord_164958) baseStart_164958 baseEnd_164958 := by
    simpa [prefixWord, tailWord_164958, baseEnd_164958] using wordTrace_append hprefix tailTrace_164958
  have hstable : (prefixWord ++ tailWord_164958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164958).length < 2 ^ (prefixWord ++ tailWord_164958).sum := by decide
  have hdescent : baseEnd_164958 < baseStart_164958 := by decide
  rcases family_descends (prefixWord ++ tailWord_164958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164983 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_164983 : Nat := 118140960795 + 164983 * 2 ^ 59
def prefixEnd_164983 : Nat := 4983230072969 + 3 ^ 40 * 164983 * 2
def baseEnd_164983 : Nat := 84715578820833236953763

theorem tailTrace_164983 : CollatzResearch.WordTrace tailWord_164983 prefixEnd_164983 84715578820833236953763 := by
  unfold tailWord_164983
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017424361302242698235603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4011616240868161798823735 6017424361302242698235603)
  ·
    refine ⟨9026136541953364047353405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6017424361302242698235603 9026136541953364047353405)
    ·
      refine ⟨3384801203232511517757527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9026136541953364047353405 3384801203232511517757527)
      ·
        refine ⟨5077201804848767276636291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3384801203232511517757527 5077201804848767276636291)
        ·
          refine ⟨7615802707273150914954437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077201804848767276636291 7615802707273150914954437)
          ·
            refine ⟨1427963007613715796553957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7615802707273150914954437 1427963007613715796553957)
            ·
              refine ⟨267743063927571711853867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1427963007613715796553957 267743063927571711853867)
              ·
                refine ⟨401614595891357567780801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267743063927571711853867 401614595891357567780801)
                ·
                  refine ⟨301210946918518175835601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401614595891357567780801 301210946918518175835601)
                  ·
                    refine ⟨225908210188888631876701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301210946918518175835601 225908210188888631876701)
                    ·
                      refine ⟨84715578820833236953763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225908210188888631876701 84715578820833236953763)
                      ·
                        rfl

theorem cell23_164983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_164983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_164983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_164983 prefixEnd_164983 := by exact prefixLift 164983
  have htrace : WordTrace (prefixWord ++ tailWord_164983) baseStart_164983 baseEnd_164983 := by
    simpa [prefixWord, tailWord_164983, baseEnd_164983] using wordTrace_append hprefix tailTrace_164983
  have hstable : (prefixWord ++ tailWord_164983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164983).length < 2 ^ (prefixWord ++ tailWord_164983).sum := by decide
  have hdescent : baseEnd_164983 < baseStart_164983 := by decide
  rcases family_descends (prefixWord ++ tailWord_164983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165047 : List Nat := [1, 1, 3, 1, 4, 1, 4, 3, 1, 1, 3]
def baseStart_165047 : Nat := 118140960795 + 165047 * 2 ^ 59
def prefixEnd_165047 : Nat := 4983230072969 + 3 ^ 40 * 165047 * 2
def baseEnd_165047 : Nat := 84748441582720986553469

theorem tailTrace_165047 : CollatzResearch.WordTrace tailWord_165047 prefixEnd_165047 84748441582720986553469 := by
  unfold tailWord_165047
  simp only [CollatzResearch.WordTrace]
  refine ⟨6019758633070381628565395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4013172422046921085710263 6019758633070381628565395)
  ·
    refine ⟨9029637949605572442848093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6019758633070381628565395 9029637949605572442848093)
    ·
      refine ⟨3386114231102089666068035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9029637949605572442848093 3386114231102089666068035)
      ·
        refine ⟨5079171346653134499102053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3386114231102089666068035 5079171346653134499102053)
        ·
          refine ⟨952344627497462718581635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5079171346653134499102053 952344627497462718581635)
          ·
            refine ⟨1428516941246194077872453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952344627497462718581635 1428516941246194077872453)
            ·
              refine ⟨267846926483661389601085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1428516941246194077872453 267846926483661389601085)
              ·
                refine ⟨100442597431373021100407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267846926483661389601085 100442597431373021100407)
                ·
                  refine ⟨150663896147059531650611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100442597431373021100407 150663896147059531650611)
                  ·
                    refine ⟨225995844220589297475917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150663896147059531650611 225995844220589297475917)
                    ·
                      refine ⟨84748441582720986553469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 225995844220589297475917 84748441582720986553469)
                      ·
                        rfl

theorem cell23_165047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_165047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165047 prefixEnd_165047 := by exact prefixLift 165047
  have htrace : WordTrace (prefixWord ++ tailWord_165047) baseStart_165047 baseEnd_165047 := by
    simpa [prefixWord, tailWord_165047, baseEnd_165047] using wordTrace_append hprefix tailTrace_165047
  have hstable : (prefixWord ++ tailWord_165047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165047).length < 2 ^ (prefixWord ++ tailWord_165047).sum := by decide
  have hdescent : baseEnd_165047 < baseStart_165047 := by decide
  rcases family_descends (prefixWord ++ tailWord_165047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165080 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 1, 6]
def baseStart_165080 : Nat := 118140960795 + 165080 * 2 ^ 59
def prefixEnd_165080 : Nat := 4983230072969 + 3 ^ 40 * 165080 * 2
def baseEnd_165080 : Nat := 28255128814773119146939

theorem tailTrace_165080 : CollatzResearch.WordTrace tailWord_165080 prefixEnd_165080 28255128814773119146939 := by
  unfold tailWord_165080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010481120975414132258347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4013974827967218843011129 3010481120975414132258347)
  ·
    refine ⟨4515721681463121198387521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010481120975414132258347 4515721681463121198387521)
    ·
      refine ⟨3386791261097340898790641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4515721681463121198387521 3386791261097340898790641)
      ·
        refine ⟨2540093445823005674092981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3386791261097340898790641 2540093445823005674092981)
        ·
          refine ⟨238133760545906781946217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2540093445823005674092981 238133760545906781946217)
          ·
            refine ⟨178600320409430086459663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238133760545906781946217 178600320409430086459663)
            ·
              refine ⟨267900480614145129689495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178600320409430086459663 267900480614145129689495)
              ·
                refine ⟨401850720921217694534243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267900480614145129689495 401850720921217694534243)
                ·
                  refine ⟨602776081381826541801365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401850720921217694534243 602776081381826541801365)
                  ·
                    refine ⟨28255128814773119146939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 602776081381826541801365 28255128814773119146939)
                    ·
                      rfl

theorem cell23_165080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_165080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165080 prefixEnd_165080 := by exact prefixLift 165080
  have htrace : WordTrace (prefixWord ++ tailWord_165080) baseStart_165080 baseEnd_165080 := by
    simpa [prefixWord, tailWord_165080, baseEnd_165080] using wordTrace_append hprefix tailTrace_165080
  have hstable : (prefixWord ++ tailWord_165080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165080).length < 2 ^ (prefixWord ++ tailWord_165080).sum := by decide
  have hdescent : baseEnd_165080 < baseStart_165080 := by decide
  rcases family_descends (prefixWord ++ tailWord_165080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165093 : List Nat := [1, 3, 1, 4, 3, 1, 1, 9]
def baseStart_165093 : Nat := 118140960795 + 165093 * 2 ^ 59
def prefixEnd_165093 : Nat := 4983230072969 + 3 ^ 40 * 165093 * 2
def baseEnd_165093 : Nat := 3139705988623252095491

theorem tailTrace_165093 : CollatzResearch.WordTrace tailWord_165093 prefixEnd_165093 3139705988623252095491 := by
  unfold tailWord_165093
  simp only [CollatzResearch.WordTrace]
  refine ⟨6021436390903731484739933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4014290927269154323159955 6021436390903731484739933)
  ·
    refine ⟨2258038646588899306777475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6021436390903731484739933 2258038646588899306777475)
    ·
      refine ⟨3387057969883348960166213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258038646588899306777475 3387057969883348960166213)
      ·
        refine ⟨635073369353127930031165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3387057969883348960166213 635073369353127930031165)
        ·
          refine ⟨238152513507422973761687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 635073369353127930031165 238152513507422973761687)
          ·
            refine ⟨357228770261134460642531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238152513507422973761687 357228770261134460642531)
            ·
              refine ⟨535843155391701690963797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357228770261134460642531 535843155391701690963797)
              ·
                refine ⟨3139705988623252095491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 535843155391701690963797 3139705988623252095491)
                ·
                  rfl

theorem cell23_165093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 9].length) (baseStart_165093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165093 prefixEnd_165093 := by exact prefixLift 165093
  have htrace : WordTrace (prefixWord ++ tailWord_165093) baseStart_165093 baseEnd_165093 := by
    simpa [prefixWord, tailWord_165093, baseEnd_165093] using wordTrace_append hprefix tailTrace_165093
  have hstable : (prefixWord ++ tailWord_165093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165093).length < 2 ^ (prefixWord ++ tailWord_165093).sum := by decide
  have hdescent : baseEnd_165093 < baseStart_165093 := by decide
  rcases family_descends (prefixWord ++ tailWord_165093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165120 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 2, 1, 3]
def baseStart_165120 : Nat := 118140960795 + 165120 * 2 ^ 59
def prefixEnd_165120 : Nat := 4983230072969 + 3 ^ 40 * 165120 * 2
def baseEnd_165120 : Nat := 84785925670499200940633

theorem tailTrace_165120 : CollatzResearch.WordTrace tailWord_165120 prefixEnd_165120 84785925670499200940633 := by
  unfold tailWord_165120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011210580902957547986407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4014947441203943397315209 3011210580902957547986407)
  ·
    refine ⟨4516815871354436321979611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3011210580902957547986407 4516815871354436321979611)
    ·
      refine ⟨6775223807031654482969417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4516815871354436321979611 6775223807031654482969417)
      ·
        refine ⟨5081417855273740862227063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6775223807031654482969417 5081417855273740862227063)
        ·
          refine ⟨7622126782910611293340595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081417855273740862227063 7622126782910611293340595)
          ·
            refine ⟨11433190174365916940010893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7622126782910611293340595 11433190174365916940010893)
            ·
              refine ⟨4287446315387218852504085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11433190174365916940010893 4287446315387218852504085)
              ·
                refine ⟨200974046033775883711129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4287446315387218852504085 200974046033775883711129)
                ·
                  refine ⟨150730534525331912783347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200974046033775883711129 150730534525331912783347)
                  ·
                    refine ⟨226095801787997869175021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150730534525331912783347 226095801787997869175021)
                    ·
                      refine ⟨84785925670499200940633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 226095801787997869175021 84785925670499200940633)
                      ·
                        rfl

theorem cell23_165120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_165120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165120 prefixEnd_165120 := by exact prefixLift 165120
  have htrace : WordTrace (prefixWord ++ tailWord_165120) baseStart_165120 baseEnd_165120 := by
    simpa [prefixWord, tailWord_165120, baseEnd_165120] using wordTrace_append hprefix tailTrace_165120
  have hstable : (prefixWord ++ tailWord_165120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165120).length < 2 ^ (prefixWord ++ tailWord_165120).sum := by decide
  have hdescent : baseEnd_165120 < baseStart_165120 := by decide
  rcases family_descends (prefixWord ++ tailWord_165120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165121 : List Nat := [1, 2, 4, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_165121 : Nat := 118140960795 + 165121 * 2 ^ 59
def prefixEnd_165121 : Nat := 4983230072969 + 3 ^ 40 * 165121 * 2
def baseEnd_165121 : Nat := 84786439151153697028129

theorem tailTrace_165121 : CollatzResearch.WordTrace tailWord_165121 prefixEnd_165121 84786439151153697028129 := by
  unfold tailWord_165121
  simp only [CollatzResearch.WordTrace]
  refine ⟨6022457634802292266759217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4014971756534861511172811 6022457634802292266759217)
  ·
    refine ⟨4516843226101719200069413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6022457634802292266759217 4516843226101719200069413)
    ·
      refine ⟨846908104894072350013015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4516843226101719200069413 846908104894072350013015)
      ·
        refine ⟨1270362157341108525019523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846908104894072350013015 1270362157341108525019523)
        ·
          refine ⟨1905543236011662787529285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270362157341108525019523 1905543236011662787529285)
          ·
            refine ⟨357289356752186772661741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1905543236011662787529285 357289356752186772661741)
            ·
              refine ⟨133983508782070039748153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357289356752186772661741 133983508782070039748153)
              ·
                refine ⟨100487631586552529811115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133983508782070039748153 100487631586552529811115)
                ·
                  refine ⟨150731447379828794716673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100487631586552529811115 150731447379828794716673)
                  ·
                    refine ⟨113048585534871596037505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150731447379828794716673 113048585534871596037505)
                    ·
                      refine ⟨84786439151153697028129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113048585534871596037505 84786439151153697028129)
                      ·
                        rfl

theorem cell23_165121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_165121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165121 prefixEnd_165121 := by exact prefixLift 165121
  have htrace : WordTrace (prefixWord ++ tailWord_165121) baseStart_165121 baseEnd_165121 := by
    simpa [prefixWord, tailWord_165121, baseEnd_165121] using wordTrace_append hprefix tailTrace_165121
  have hstable : (prefixWord ++ tailWord_165121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165121).length < 2 ^ (prefixWord ++ tailWord_165121).sum := by decide
  have hdescent : baseEnd_165121 < baseStart_165121 := by decide
  rcases family_descends (prefixWord ++ tailWord_165121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165130 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_165130 : Nat := 118140960795 + 165130 * 2 ^ 59
def prefixEnd_165130 : Nat := 4983230072969 + 3 ^ 40 * 165130 * 2
def baseEnd_165130 : Nat := 84791060477044161815587

theorem tailTrace_165130 : CollatzResearch.WordTrace tailWord_165130 prefixEnd_165130 84791060477044161815587 := by
  unfold tailWord_165130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505696472942421700959211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4015190594513124535891229 1505696472942421700959211)
  ·
    refine ⟨2258544709413632551438817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1505696472942421700959211 2258544709413632551438817)
    ·
      refine ⟨1693908532060224413579113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2258544709413632551438817 1693908532060224413579113)
      ·
        refine ⟨1270431399045168310184335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1693908532060224413579113 1270431399045168310184335)
        ·
          refine ⟨1905647098567752465276503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270431399045168310184335 1905647098567752465276503)
          ·
            refine ⟨2858470647851628697914755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905647098567752465276503 2858470647851628697914755)
            ·
              refine ⟨4287705971777443046872133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858470647851628697914755 4287705971777443046872133)
              ·
                refine ⟨803944869708270571288525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4287705971777443046872133 803944869708270571288525)
                ·
                  refine ⟨301479326140601464233197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803944869708270571288525 301479326140601464233197)
                  ·
                    refine ⟨113054747302725549087449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301479326140601464233197 113054747302725549087449)
                    ·
                      refine ⟨84791060477044161815587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113054747302725549087449 84791060477044161815587)
                      ·
                        rfl

theorem cell23_165130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_165130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165130 prefixEnd_165130 := by exact prefixLift 165130
  have htrace : WordTrace (prefixWord ++ tailWord_165130) baseStart_165130 baseEnd_165130 := by
    simpa [prefixWord, tailWord_165130, baseEnd_165130] using wordTrace_append hprefix tailTrace_165130
  have hstable : (prefixWord ++ tailWord_165130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165130).length < 2 ^ (prefixWord ++ tailWord_165130).sum := by decide
  have hdescent : baseEnd_165130 < baseStart_165130 := by decide
  rcases family_descends (prefixWord ++ tailWord_165130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165136 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 8, 6]
def baseStart_165136 : Nat := 118140960795 + 165136 * 2 ^ 59
def prefixEnd_165136 : Nat := 4983230072969 + 3 ^ 40 * 165136 * 2
def baseEnd_165136 : Nat := 28264713786990379446853

theorem tailTrace_165136 : CollatzResearch.WordTrace tailWord_165136 prefixEnd_165136 28264713786990379446853 := by
  unfold tailWord_165136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011502364873974914277631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4015336486498633219036841 3011502364873974914277631)
  ·
    refine ⟨4517253547310962371416447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3011502364873974914277631 4517253547310962371416447)
    ·
      refine ⟨6775880320966443557124671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4517253547310962371416447 6775880320966443557124671)
      ·
        refine ⟨10163820481449665335687007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6775880320966443557124671 10163820481449665335687007)
        ·
          refine ⟨15245730722174498003530511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10163820481449665335687007 15245730722174498003530511)
          ·
            refine ⟨22868596083261747005295767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15245730722174498003530511 22868596083261747005295767)
            ·
              refine ⟨34302894124892620507943651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22868596083261747005295767 34302894124892620507943651)
              ·
                refine ⟨51454341187338930761915477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34302894124892620507943651 51454341187338930761915477)
                ·
                  refine ⟨602980560789128094866197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 51454341187338930761915477 602980560789128094866197)
                  ·
                    refine ⟨28264713786990379446853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 602980560789128094866197 28264713786990379446853)
                    ·
                      rfl

theorem cell23_165136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_165136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165136 prefixEnd_165136 := by exact prefixLift 165136
  have htrace : WordTrace (prefixWord ++ tailWord_165136) baseStart_165136 baseEnd_165136 := by
    simpa [prefixWord, tailWord_165136, baseEnd_165136] using wordTrace_append hprefix tailTrace_165136
  have hstable : (prefixWord ++ tailWord_165136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165136).length < 2 ^ (prefixWord ++ tailWord_165136).sum := by decide
  have hdescent : baseEnd_165136 < baseStart_165136 := by decide
  rcases family_descends (prefixWord ++ tailWord_165136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165193 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 3]
def baseStart_165193 : Nat := 118140960795 + 165193 * 2 ^ 59
def prefixEnd_165193 : Nat := 4983230072969 + 3 ^ 40 * 165193 * 2
def baseEnd_165193 : Nat := 84823409758277415327797

theorem tailTrace_165193 : CollatzResearch.WordTrace tailWord_165193 prefixEnd_165193 84823409758277415327797 := by
  unfold tailWord_165193
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025083690541448563380233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4016722460360965708920155 6025083690541448563380233)
  ·
    refine ⟨4518812767906086422535175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6025083690541448563380233 4518812767906086422535175)
    ·
      refine ⟨6778219151859129633802763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518812767906086422535175 6778219151859129633802763)
      ·
        refine ⟨10167328727788694450704145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6778219151859129633802763 10167328727788694450704145)
        ·
          refine ⟨7625496545841520838028109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10167328727788694450704145 7625496545841520838028109)
          ·
            refine ⟨2859561204690570314260541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7625496545841520838028109 2859561204690570314260541)
            ·
              refine ⟨1072335451758963867847703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859561204690570314260541 1072335451758963867847703)
              ·
                refine ⟨1608503177638445801771555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072335451758963867847703 1608503177638445801771555)
                ·
                  refine ⟨2412754766457668702657333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608503177638445801771555 2412754766457668702657333)
                  ·
                    refine ⟨226195759355406440874125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2412754766457668702657333 226195759355406440874125)
                    ·
                      refine ⟨84823409758277415327797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 226195759355406440874125 84823409758277415327797)
                      ·
                        rfl

theorem cell23_165193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_165193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165193 prefixEnd_165193 := by exact prefixLift 165193
  have htrace : WordTrace (prefixWord ++ tailWord_165193) baseStart_165193 baseEnd_165193 := by
    simpa [prefixWord, tailWord_165193, baseEnd_165193] using wordTrace_append hprefix tailTrace_165193
  have hstable : (prefixWord ++ tailWord_165193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165193).length < 2 ^ (prefixWord ++ tailWord_165193).sum := by decide
  have hdescent : baseEnd_165193 < baseStart_165193 := by decide
  rcases family_descends (prefixWord ++ tailWord_165193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165260 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_165260 : Nat := 118140960795 + 165260 * 2 ^ 59
def prefixEnd_165260 : Nat := 4983230072969 + 3 ^ 40 * 165260 * 2
def baseEnd_165260 : Nat := 28285937654042884396663

theorem tailTrace_165260 : CollatzResearch.WordTrace tailWord_165260 prefixEnd_165260 28285937654042884396663 := by
  unfold tailWord_165260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013763690649359503034617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4018351587532479337379489 3013763690649359503034617)
  ·
    refine ⟨2260322767987019627275963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3013763690649359503034617 2260322767987019627275963)
    ·
      refine ⟨3390484151980529440913945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260322767987019627275963 3390484151980529440913945)
      ·
        refine ⟨2542863113985397080685459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3390484151980529440913945 2542863113985397080685459)
        ·
          refine ⟨3814294670978095621028189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542863113985397080685459 3814294670978095621028189)
          ·
            refine ⟨1430360501616785857885571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3814294670978095621028189 1430360501616785857885571)
            ·
              refine ⟨2145540752425178786828357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430360501616785857885571 2145540752425178786828357)
              ·
                refine ⟨402288891079721022530317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2145540752425178786828357 402288891079721022530317)
                ·
                  refine ⟨150858334154895383448869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402288891079721022530317 150858334154895383448869)
                  ·
                    refine ⟨28285937654042884396663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150858334154895383448869 28285937654042884396663)
                    ·
                      rfl

theorem cell23_165260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_165260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165260 prefixEnd_165260 := by exact prefixLift 165260
  have htrace : WordTrace (prefixWord ++ tailWord_165260) baseStart_165260 baseEnd_165260 := by
    simpa [prefixWord, tailWord_165260, baseEnd_165260] using wordTrace_append hprefix tailTrace_165260
  have hstable : (prefixWord ++ tailWord_165260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165260).length < 2 ^ (prefixWord ++ tailWord_165260).sum := by decide
  have hdescent : baseEnd_165260 < baseStart_165260 := by decide
  rcases family_descends (prefixWord ++ tailWord_165260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165273 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 8]
def baseStart_165273 : Nat := 118140960795 + 165273 * 2 ^ 59
def prefixEnd_165273 : Nat := 4983230072969 + 3 ^ 40 * 165273 * 2
def baseEnd_165273 : Nat := 9429387578959678036381

theorem tailTrace_165273 : CollatzResearch.WordTrace tailWord_165273 prefixEnd_165273 9429387578959678036381 := by
  unfold tailWord_165273
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028001530251622226292473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4018667686834414817528315 6028001530251622226292473)
  ·
    refine ⟨4521001147688716669719355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6028001530251622226292473 4521001147688716669719355)
    ·
      refine ⟨6781501721533075004579033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4521001147688716669719355 6781501721533075004579033)
      ·
        refine ⟨5086126291149806253434275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6781501721533075004579033 5086126291149806253434275)
        ·
          refine ⟨7629189436724709380151413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5086126291149806253434275 7629189436724709380151413)
          ·
            refine ⟨715236509692941504389195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7629189436724709380151413 715236509692941504389195)
            ·
              refine ⟨1072854764539412256583793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715236509692941504389195 1072854764539412256583793)
              ·
                refine ⟨804641073404559192437845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072854764539412256583793 804641073404559192437845)
                ·
                  refine ⟨9429387578959678036381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 804641073404559192437845 9429387578959678036381)
                  ·
                    rfl

theorem cell23_165273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_165273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165273 prefixEnd_165273 := by exact prefixLift 165273
  have htrace : WordTrace (prefixWord ++ tailWord_165273) baseStart_165273 baseEnd_165273 := by
    simpa [prefixWord, tailWord_165273, baseEnd_165273] using wordTrace_append hprefix tailTrace_165273
  have hstable : (prefixWord ++ tailWord_165273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165273).length < 2 ^ (prefixWord ++ tailWord_165273).sum := by decide
  have hdescent : baseEnd_165273 < baseStart_165273 := by decide
  rcases family_descends (prefixWord ++ tailWord_165273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165287 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_165287 : Nat := 118140960795 + 165287 * 2 ^ 59
def prefixEnd_165287 : Nat := 4983230072969 + 3 ^ 40 * 165287 * 2
def baseEnd_165287 : Nat := 84871676939800047552365

theorem tailTrace_165287 : CollatzResearch.WordTrace tailWord_165287 prefixEnd_165287 84871676939800047552365 := by
  unfold tailWord_165287
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028512152200902617302115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4019008101467268411534743 6028512152200902617302115)
  ·
    refine ⟨9042768228301353925953173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6028512152200902617302115 9042768228301353925953173)
    ·
      refine ⟨423879760701625965279055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9042768228301353925953173 423879760701625965279055)
      ·
        refine ⟨635819641052438947918583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423879760701625965279055 635819641052438947918583)
        ·
          refine ⟨953729461578658421877875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635819641052438947918583 953729461578658421877875)
          ·
            refine ⟨1430594192367987632816813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953729461578658421877875 1430594192367987632816813)
            ·
              refine ⟨536472822137995362306305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1430594192367987632816813 536472822137995362306305)
              ·
                refine ⟨402354616603496521729729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536472822137995362306305 402354616603496521729729)
                ·
                  refine ⟨301765962452622391297297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402354616603496521729729 301765962452622391297297)
                  ·
                    refine ⟨226324471839466793472973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301765962452622391297297 226324471839466793472973)
                    ·
                      refine ⟨84871676939800047552365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 226324471839466793472973 84871676939800047552365)
                      ·
                        rfl

theorem cell23_165287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_165287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165287 prefixEnd_165287 := by exact prefixLift 165287
  have htrace : WordTrace (prefixWord ++ tailWord_165287) baseStart_165287 baseEnd_165287 := by
    simpa [prefixWord, tailWord_165287, baseEnd_165287] using wordTrace_append hprefix tailTrace_165287
  have hstable : (prefixWord ++ tailWord_165287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165287).length < 2 ^ (prefixWord ++ tailWord_165287).sum := by decide
  have hdescent : baseEnd_165287 < baseStart_165287 := by decide
  rcases family_descends (prefixWord ++ tailWord_165287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165320 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 3, 5]
def baseStart_165320 : Nat := 118140960795 + 165320 * 2 ^ 59
def prefixEnd_165320 : Nat := 4983230072969 + 3 ^ 40 * 165320 * 2
def baseEnd_165320 : Nat := 28296207267132806146571

theorem tailTrace_165320 : CollatzResearch.WordTrace tailWord_165320 prefixEnd_165320 28296207267132806146571 := by
  unfold tailWord_165320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014857880540674626626707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4019810507387566168835609 3014857880540674626626707)
  ·
    refine ⟨4522286820811011939940061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3014857880540674626626707 4522286820811011939940061)
    ·
      refine ⟨1695857557804129477477523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4522286820811011939940061 1695857557804129477477523)
      ·
        refine ⟨2543786336706194216216285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695857557804129477477523 2543786336706194216216285)
        ·
          refine ⟨953919876264822831081107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2543786336706194216216285 953919876264822831081107)
          ·
            refine ⟨1430879814397234246621661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953919876264822831081107 1430879814397234246621661)
            ·
              refine ⟨536579930398962842483123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1430879814397234246621661 536579930398962842483123)
              ·
                refine ⟨804869895598444263724685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536579930398962842483123 804869895598444263724685)
                ·
                  refine ⟨301826210849416598896757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804869895598444263724685 301826210849416598896757)
                  ·
                    refine ⟨28296207267132806146571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 301826210849416598896757 28296207267132806146571)
                    ·
                      rfl

theorem cell23_165320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_165320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165320 prefixEnd_165320 := by exact prefixLift 165320
  have htrace : WordTrace (prefixWord ++ tailWord_165320) baseStart_165320 baseEnd_165320 := by
    simpa [prefixWord, tailWord_165320, baseEnd_165320] using wordTrace_append hprefix tailTrace_165320
  have hstable : (prefixWord ++ tailWord_165320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165320).length < 2 ^ (prefixWord ++ tailWord_165320).sum := by decide
  have hdescent : baseEnd_165320 < baseStart_165320 := by decide
  rcases family_descends (prefixWord ++ tailWord_165320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165327 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 2, 3, 2]
def baseStart_165327 : Nat := 118140960795 + 165327 * 2 ^ 59
def prefixEnd_165327 : Nat := 4983230072969 + 3 ^ 40 * 165327 * 2
def baseEnd_165327 : Nat := 84892216165979891052181

theorem tailTrace_165327 : CollatzResearch.WordTrace tailWord_165327 prefixEnd_165327 84892216165979891052181 := by
  unfold tailWord_165327
  simp only [CollatzResearch.WordTrace]
  refine ⟨6029971072055989448758235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4019980714703992965838823 6029971072055989448758235)
  ·
    refine ⟨9044956608083984173137353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6029971072055989448758235 9044956608083984173137353)
    ·
      refine ⟨6783717456062988129853015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9044956608083984173137353 6783717456062988129853015)
      ·
        refine ⟨10175576184094482194779523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6783717456062988129853015 10175576184094482194779523)
        ·
          refine ⟨15263364276141723292169285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10175576184094482194779523 15263364276141723292169285)
          ·
            refine ⟨2861880801776573117281741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15263364276141723292169285 2861880801776573117281741)
            ·
              refine ⟨1073205300666214918980653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2861880801776573117281741 1073205300666214918980653)
              ·
                refine ⟨402451987749830594617745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1073205300666214918980653 402451987749830594617745)
                ·
                  refine ⟨301838990812372945963309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402451987749830594617745 301838990812372945963309)
                  ·
                    refine ⟨113189621554639854736241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301838990812372945963309 113189621554639854736241)
                    ·
                      refine ⟨84892216165979891052181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113189621554639854736241 84892216165979891052181)
                      ·
                        rfl

theorem cell23_165327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 3, 2].length) (baseStart_165327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165327 prefixEnd_165327 := by exact prefixLift 165327
  have htrace : WordTrace (prefixWord ++ tailWord_165327) baseStart_165327 baseEnd_165327 := by
    simpa [prefixWord, tailWord_165327, baseEnd_165327] using wordTrace_append hprefix tailTrace_165327
  have hstable : (prefixWord ++ tailWord_165327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165327).length < 2 ^ (prefixWord ++ tailWord_165327).sum := by decide
  have hdescent : baseEnd_165327 < baseStart_165327 := by decide
  rcases family_descends (prefixWord ++ tailWord_165327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165351 : List Nat := [1, 1, 5, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_165351 : Nat := 118140960795 + 165351 * 2 ^ 59
def prefixEnd_165351 : Nat := 4983230072969 + 3 ^ 40 * 165351 * 2
def baseEnd_165351 : Nat := 84904539701687797152071

theorem tailTrace_165351 : CollatzResearch.WordTrace tailWord_165351 prefixEnd_165351 84904539701687797152071 := by
  unfold tailWord_165351
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030846423969041547631907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4020564282646027698421271 6030846423969041547631907)
  ·
    refine ⟨9046269635953562321447861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6030846423969041547631907 9046269635953562321447861)
    ·
      refine ⟨848087778370646467635737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9046269635953562321447861 848087778370646467635737)
      ·
        refine ⟨636065833777984850726803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848087778370646467635737 636065833777984850726803)
        ·
          refine ⟨954098750666977276090205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636065833777984850726803 954098750666977276090205)
          ·
            refine ⟨357787031500116478533827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 954098750666977276090205 357787031500116478533827)
            ·
              refine ⟨536680547250174717800741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357787031500116478533827 536680547250174717800741)
              ·
                refine ⟨100627602609407759587639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 536680547250174717800741 100627602609407759587639)
                ·
                  refine ⟨150941403914111639381459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100627602609407759587639 150941403914111639381459)
                  ·
                    refine ⟨226412105871167459072189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150941403914111639381459 226412105871167459072189)
                    ·
                      refine ⟨84904539701687797152071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 226412105871167459072189 84904539701687797152071)
                      ·
                        rfl

theorem cell23_165351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_165351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165351 prefixEnd_165351 := by exact prefixLift 165351
  have htrace : WordTrace (prefixWord ++ tailWord_165351) baseStart_165351 baseEnd_165351 := by
    simpa [prefixWord, tailWord_165351, baseEnd_165351] using wordTrace_append hprefix tailTrace_165351
  have hstable : (prefixWord ++ tailWord_165351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165351).length < 2 ^ (prefixWord ++ tailWord_165351).sum := by decide
  have hdescent : baseEnd_165351 < baseStart_165351 := by decide
  rcases family_descends (prefixWord ++ tailWord_165351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165363 : List Nat := [1, 1, 1, 2, 2, 2, 2, 12]
def baseStart_165363 : Nat := 118140960795 + 165363 * 2 ^ 59
def prefixEnd_165363 : Nat := 4983230072969 + 3 ^ 40 * 165363 * 2
def baseEnd_165363 : Nat := 3144840795168212970445

theorem tailTrace_165363 : CollatzResearch.WordTrace tailWord_165363 prefixEnd_165363 3144840795168212970445 := by
  unfold tailWord_165363
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031284099925567597068743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4020856066617045064712495 6031284099925567597068743)
  ·
    refine ⟨9046926149888351395603115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6031284099925567597068743 9046926149888351395603115)
    ·
      refine ⟨13570389224832527093404673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9046926149888351395603115 13570389224832527093404673)
      ·
        refine ⟨10177791918624395320053505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13570389224832527093404673 10177791918624395320053505)
        ·
          refine ⟨7633343938968296490040129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10177791918624395320053505 7633343938968296490040129)
          ·
            refine ⟨5725007954226222367530097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7633343938968296490040129 5725007954226222367530097)
            ·
              refine ⟨4293755965669666775647573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5725007954226222367530097 4293755965669666775647573)
              ·
                refine ⟨3144840795168212970445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 4293755965669666775647573 3144840795168212970445)
                ·
                  rfl

theorem cell23_165363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 12].length) (baseStart_165363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165363 prefixEnd_165363 := by exact prefixLift 165363
  have htrace : WordTrace (prefixWord ++ tailWord_165363) baseStart_165363 baseEnd_165363 := by
    simpa [prefixWord, tailWord_165363, baseEnd_165363] using wordTrace_append hprefix tailTrace_165363
  have hstable : (prefixWord ++ tailWord_165363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165363).length < 2 ^ (prefixWord ++ tailWord_165363).sum := by decide
  have hdescent : baseEnd_165363 < baseStart_165363 := by decide
  rcases family_descends (prefixWord ++ tailWord_165363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165378 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_165378 : Nat := 118140960795 + 165378 * 2 ^ 59
def prefixEnd_165378 : Nat := 4983230072969 + 3 ^ 40 * 165378 * 2
def baseEnd_165378 : Nat := 84918403679359191514447

theorem tailTrace_165378 : CollatzResearch.WordTrace tailWord_165378 prefixEnd_165378 84918403679359191514447 := by
  unfold tailWord_165378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507957798717806289716197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4021220796580816772576525 1507957798717806289716197)
  ·
    refine ⟨282742087259588679321787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1507957798717806289716197 282742087259588679321787)
    ·
      refine ⟨424113130889383018982681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282742087259588679321787 424113130889383018982681)
      ·
        refine ⟨318084848167037264237011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424113130889383018982681 318084848167037264237011)
        ·
          refine ⟨477127272250555896355517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318084848167037264237011 477127272250555896355517)
          ·
            refine ⟨178922727093958461133319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 477127272250555896355517 178922727093958461133319)
            ·
              refine ⟨268384090640937691699979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178922727093958461133319 268384090640937691699979)
              ·
                refine ⟨402576135961406537549969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268384090640937691699979 402576135961406537549969)
                ·
                  refine ⟨301932101971054903162477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402576135961406537549969 301932101971054903162477)
                  ·
                    refine ⟨113224538239145588685929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301932101971054903162477 113224538239145588685929)
                    ·
                      refine ⟨84918403679359191514447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113224538239145588685929 84918403679359191514447)
                      ·
                        rfl

theorem cell23_165378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_165378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165378 prefixEnd_165378 := by exact prefixLift 165378
  have htrace : WordTrace (prefixWord ++ tailWord_165378) baseStart_165378 baseEnd_165378 := by
    simpa [prefixWord, tailWord_165378, baseEnd_165378] using wordTrace_append hprefix tailTrace_165378
  have hstable : (prefixWord ++ tailWord_165378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165378).length < 2 ^ (prefixWord ++ tailWord_165378).sum := by decide
  have hdescent : baseEnd_165378 < baseStart_165378 := by decide
  rcases family_descends (prefixWord ++ tailWord_165378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165408 : List Nat := [2, 1, 1, 6, 1, 1, 2, 4, 1, 2, 2]
def baseStart_165408 : Nat := 118140960795 + 165408 * 2 ^ 59
def prefixEnd_165408 : Nat := 4983230072969 + 3 ^ 40 * 165408 * 2
def baseEnd_165408 : Nat := 84933808098994074139309

theorem tailTrace_165408 : CollatzResearch.WordTrace tailWord_165408 prefixEnd_165408 84933808098994074139309 := by
  unfold tailWord_165408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016462692381270141228439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4021950256508360188304585 3016462692381270141228439)
  ·
    refine ⟨4524694038571905211842659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3016462692381270141228439 4524694038571905211842659)
    ·
      refine ⟨6787041057857857817763989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4524694038571905211842659 6787041057857857817763989)
      ·
        refine ⟨318142549587087085207687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6787041057857857817763989 318142549587087085207687)
        ·
          refine ⟨477213824380630627811531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318142549587087085207687 477213824380630627811531)
          ·
            refine ⟨715820736570945941717297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477213824380630627811531 715820736570945941717297)
            ·
              refine ⟨536865552428209456287973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715820736570945941717297 536865552428209456287973)
              ·
                refine ⟨100662291080289273053995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 536865552428209456287973 100662291080289273053995)
                ·
                  refine ⟨150993436620433909580993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100662291080289273053995 150993436620433909580993)
                  ·
                    refine ⟨113245077465325432185745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 150993436620433909580993 113245077465325432185745)
                    ·
                      refine ⟨84933808098994074139309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113245077465325432185745 84933808098994074139309)
                      ·
                        rfl

theorem cell23_165408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_165408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165408 prefixEnd_165408 := by exact prefixLift 165408
  have htrace : WordTrace (prefixWord ++ tailWord_165408) baseStart_165408 baseEnd_165408 := by
    simpa [prefixWord, tailWord_165408, baseEnd_165408] using wordTrace_append hprefix tailTrace_165408
  have hstable : (prefixWord ++ tailWord_165408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165408).length < 2 ^ (prefixWord ++ tailWord_165408).sum := by decide
  have hdescent : baseEnd_165408 < baseStart_165408 := by decide
  rcases family_descends (prefixWord ++ tailWord_165408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165410 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_165410 : Nat := 118140960795 + 165410 * 2 ^ 59
def prefixEnd_165410 : Nat := 4983230072969 + 3 ^ 40 * 165410 * 2
def baseEnd_165410 : Nat := 28311611686767688771433

theorem tailTrace_165410 : CollatzResearch.WordTrace tailWord_165410 prefixEnd_165410 28311611686767688771433 := by
  unfold tailWord_165410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508249582688823656007421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4021998887170196416019789 1508249582688823656007421)
  ·
    refine ⟨565593593508308871002783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1508249582688823656007421 565593593508308871002783)
    ·
      refine ⟨848390390262463306504175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565593593508308871002783 848390390262463306504175)
      ·
        refine ⟨1272585585393694959756263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848390390262463306504175 1272585585393694959756263)
        ·
          refine ⟨1908878378090542439634395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272585585393694959756263 1908878378090542439634395)
          ·
            refine ⟨2863317567135813659451593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908878378090542439634395 2863317567135813659451593)
            ·
              refine ⟨2147488175351860244588695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863317567135813659451593 2147488175351860244588695)
              ·
                refine ⟨3221232263027790366883043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147488175351860244588695 3221232263027790366883043)
                ·
                  refine ⟨4831848394541685550324565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221232263027790366883043 4831848394541685550324565)
                  ·
                    refine ⟨28311611686767688771433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 4831848394541685550324565 28311611686767688771433)
                    ·
                      rfl

theorem cell23_165410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_165410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165410 prefixEnd_165410 := by exact prefixLift 165410
  have htrace : WordTrace (prefixWord ++ tailWord_165410) baseStart_165410 baseEnd_165410 := by
    simpa [prefixWord, tailWord_165410, baseEnd_165410] using wordTrace_append hprefix tailTrace_165410
  have hstable : (prefixWord ++ tailWord_165410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165410).length < 2 ^ (prefixWord ++ tailWord_165410).sum := by decide
  have hdescent : baseEnd_165410 < baseStart_165410 := by decide
  rcases family_descends (prefixWord ++ tailWord_165410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165485 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_165485 : Nat := 118140960795 + 165485 * 2 ^ 59
def prefixEnd_165485 : Nat := 4983230072969 + 3 ^ 40 * 165485 * 2
def baseEnd_165485 : Nat := 84973346109390272876455

theorem tailTrace_165485 : CollatzResearch.WordTrace tailWord_165485 prefixEnd_165485 84973346109390272876455 := by
  unfold tailWord_165485
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035733805483582433009909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4023822536989054955339939 6035733805483582433009909)
  ·
    refine ⟨565850044264085853094679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6035733805483582433009909 565850044264085853094679)
    ·
      refine ⟨848775066396128779642019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565850044264085853094679 848775066396128779642019)
      ·
        refine ⟨1273162599594193169463029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848775066396128779642019 1273162599594193169463029)
        ·
          refine ⟨119358993711955609637159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1273162599594193169463029 119358993711955609637159)
          ·
            refine ⟨179038490567933414455739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119358993711955609637159 179038490567933414455739)
            ·
              refine ⟨268557735851900121683609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179038490567933414455739 268557735851900121683609)
              ·
                refine ⟨201418301888925091262707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268557735851900121683609 201418301888925091262707)
                ·
                  refine ⟨302127452833387636894061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201418301888925091262707 302127452833387636894061)
                  ·
                    refine ⟨113297794812520363835273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302127452833387636894061 113297794812520363835273)
                    ·
                      refine ⟨84973346109390272876455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113297794812520363835273 84973346109390272876455)
                      ·
                        rfl

theorem cell23_165485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_165485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165485 prefixEnd_165485 := by exact prefixLift 165485
  have htrace : WordTrace (prefixWord ++ tailWord_165485) baseStart_165485 baseEnd_165485 := by
    simpa [prefixWord, tailWord_165485, baseEnd_165485] using wordTrace_append hprefix tailTrace_165485
  have hstable : (prefixWord ++ tailWord_165485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165485).length < 2 ^ (prefixWord ++ tailWord_165485).sum := by decide
  have hdescent : baseEnd_165485 < baseStart_165485 := by decide
  rcases family_descends (prefixWord ++ tailWord_165485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165527 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_165527 : Nat := 118140960795 + 165527 * 2 ^ 59
def prefixEnd_165527 : Nat := 4983230072969 + 3 ^ 40 * 165527 * 2
def baseEnd_165527 : Nat := 84994912296879108551261

theorem tailTrace_165527 : CollatzResearch.WordTrace tailWord_165527 prefixEnd_165527 84994912296879108551261 := by
  unfold tailWord_165527
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037265671331423606038835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4024843780887615737359223 6037265671331423606038835)
  ·
    refine ⟨9055898506997135409058253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6037265671331423606038835 9055898506997135409058253)
    ·
      refine ⟨3395961940123925778396845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9055898506997135409058253 3395961940123925778396845)
      ·
        refine ⟨1273485727546472166898817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3395961940123925778396845 1273485727546472166898817)
        ·
          refine ⟨955114295659854125174113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1273485727546472166898817 955114295659854125174113)
          ·
            refine ⟨716335721744890593880585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955114295659854125174113 716335721744890593880585)
            ·
              refine ⟨537251791308667945410439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716335721744890593880585 537251791308667945410439)
              ·
                refine ⟨805877686963001918115659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537251791308667945410439 805877686963001918115659)
                ·
                  refine ⟨1208816530444502877173489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805877686963001918115659 1208816530444502877173489)
                  ·
                    refine ⟨906612397833377157880117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1208816530444502877173489 906612397833377157880117)
                    ·
                      refine ⟨84994912296879108551261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 906612397833377157880117 84994912296879108551261)
                      ·
                        rfl

theorem cell23_165527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_165527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165527 prefixEnd_165527 := by exact prefixLift 165527
  have htrace : WordTrace (prefixWord ++ tailWord_165527) baseStart_165527 baseEnd_165527 := by
    simpa [prefixWord, tailWord_165527, baseEnd_165527] using wordTrace_append hprefix tailTrace_165527
  have hstable : (prefixWord ++ tailWord_165527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165527).length < 2 ^ (prefixWord ++ tailWord_165527).sum := by decide
  have hdescent : baseEnd_165527 < baseStart_165527 := by decide
  rcases family_descends (prefixWord ++ tailWord_165527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165554 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_165554 : Nat := 118140960795 + 165554 * 2 ^ 59
def prefixEnd_165554 : Nat := 4983230072969 + 3 ^ 40 * 165554 * 2
def baseEnd_165554 : Nat := 85008776274550502913637

theorem tailTrace_165554 : CollatzResearch.WordTrace tailWord_165554 prefixEnd_165554 85008776274550502913637 := by
  unfold tailWord_165554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509562610558401804317929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4025500294822404811514477 1509562610558401804317929)
  ·
    refine ⟨1132171957918801353238447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1509562610558401804317929 1132171957918801353238447)
    ·
      refine ⟨1698257936878202029857671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1132171957918801353238447 1698257936878202029857671)
      ·
        refine ⟨2547386905317303044786507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698257936878202029857671 2547386905317303044786507)
        ·
          refine ⟨3821080357975954567179761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547386905317303044786507 3821080357975954567179761)
          ·
            refine ⟨2865810268481965925384821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821080357975954567179761 2865810268481965925384821)
            ·
              refine ⟨268669712670184305504827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2865810268481965925384821 268669712670184305504827)
              ·
                refine ⟨403004569005276458257241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268669712670184305504827 403004569005276458257241)
                ·
                  refine ⟨302253426753957343692931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403004569005276458257241 302253426753957343692931)
                  ·
                    refine ⟨453380140130936015539397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302253426753957343692931 453380140130936015539397)
                    ·
                      refine ⟨85008776274550502913637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 453380140130936015539397 85008776274550502913637)
                      ·
                        rfl

theorem cell23_165554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_165554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165554 prefixEnd_165554 := by exact prefixLift 165554
  have htrace : WordTrace (prefixWord ++ tailWord_165554) baseStart_165554 baseEnd_165554 := by
    simpa [prefixWord, tailWord_165554, baseEnd_165554] using wordTrace_append hprefix tailTrace_165554
  have hstable : (prefixWord ++ tailWord_165554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165554).length < 2 ^ (prefixWord ++ tailWord_165554).sum := by decide
  have hdescent : baseEnd_165554 < baseStart_165554 := by decide
  rcases family_descends (prefixWord ++ tailWord_165554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165647 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_165647 : Nat := 118140960795 + 165647 * 2 ^ 59
def prefixEnd_165647 : Nat := 4983230072969 + 3 ^ 40 * 165647 * 2
def baseEnd_165647 : Nat := 85056529975418639050709

theorem tailTrace_165647 : CollatzResearch.WordTrace tailWord_165647 prefixEnd_165647 85056529975418639050709 := by
  unfold tailWord_165647
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041642430896684100407195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4027761620597789400271463 6041642430896684100407195)
  ·
    refine ⟨9062463646345026150610793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6041642430896684100407195 9062463646345026150610793)
    ·
      refine ⟨6796847734758769612958095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9062463646345026150610793 6796847734758769612958095)
      ·
        refine ⟨10195271602138154419437143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796847734758769612958095 10195271602138154419437143)
        ·
          refine ⟨15292907403207231629155715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10195271602138154419437143 15292907403207231629155715)
          ·
            refine ⟨22939361104810847443733573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15292907403207231629155715 22939361104810847443733573)
            ·
              refine ⟨4301130207152033895700045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22939361104810847443733573 4301130207152033895700045)
              ·
                refine ⟨1612923827682012710887517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4301130207152033895700045 1612923827682012710887517)
                ·
                  refine ⟨604846435380754766582819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1612923827682012710887517 604846435380754766582819)
                  ·
                    refine ⟨907269653071132149874229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 604846435380754766582819 907269653071132149874229)
                    ·
                      refine ⟨85056529975418639050709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 907269653071132149874229 85056529975418639050709)
                      ·
                        rfl

theorem cell23_165647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_165647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165647 prefixEnd_165647 := by exact prefixLift 165647
  have htrace : WordTrace (prefixWord ++ tailWord_165647) baseStart_165647 baseEnd_165647 := by
    simpa [prefixWord, tailWord_165647, baseEnd_165647] using wordTrace_append hprefix tailTrace_165647
  have hstable : (prefixWord ++ tailWord_165647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165647).length < 2 ^ (prefixWord ++ tailWord_165647).sum := by decide
  have hdescent : baseEnd_165647 < baseStart_165647 := by decide
  rcases family_descends (prefixWord ++ tailWord_165647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165667 : List Nat := [1, 1, 1, 4, 2, 1, 4, 9]
def baseStart_165667 : Nat := 118140960795 + 165667 * 2 ^ 59
def prefixEnd_165667 : Nat := 4983230072969 + 3 ^ 40 * 165667 * 2
def baseEnd_165667 : Nat := 3150622206981798548171

theorem tailTrace_165667 : CollatzResearch.WordTrace tailWord_165667 prefixEnd_165667 3150622206981798548171 := by
  unfold tailWord_165667
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042371890824227516135255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4028247927216151677423503 6042371890824227516135255)
  ·
    refine ⟨9063557836236341274202883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6042371890824227516135255 9063557836236341274202883)
    ·
      refine ⟨13595336754354511911304325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9063557836236341274202883 13595336754354511911304325)
      ·
        refine ⟨2549125641441470983369561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13595336754354511911304325 2549125641441470983369561)
        ·
          refine ⟨1911844231081103237527171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2549125641441470983369561 1911844231081103237527171)
          ·
            refine ⟨2867766346621654856290757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911844231081103237527171 2867766346621654856290757)
            ·
              refine ⟨537706189991560285554517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2867766346621654856290757 537706189991560285554517)
              ·
                refine ⟨3150622206981798548171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 537706189991560285554517 3150622206981798548171)
                ·
                  rfl

theorem cell23_165667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 9].length) (baseStart_165667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165667 prefixEnd_165667 := by exact prefixLift 165667
  have htrace : WordTrace (prefixWord ++ tailWord_165667) baseStart_165667 baseEnd_165667 := by
    simpa [prefixWord, tailWord_165667, baseEnd_165667] using wordTrace_append hprefix tailTrace_165667
  have hstable : (prefixWord ++ tailWord_165667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165667).length < 2 ^ (prefixWord ++ tailWord_165667).sum := by decide
  have hdescent : baseEnd_165667 < baseStart_165667 := by decide
  rcases family_descends (prefixWord ++ tailWord_165667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165681 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_165681 : Nat := 118140960795 + 165681 * 2 ^ 59
def prefixEnd_165681 : Nat := 4983230072969 + 3 ^ 40 * 165681 * 2
def baseEnd_165681 : Nat := 85073988317671506025553

theorem tailTrace_165681 : CollatzResearch.WordTrace tailWord_165681 prefixEnd_165681 85073988317671506025553 := by
  unfold tailWord_165681
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042882512773507907144897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4028588341849005271429931 6042882512773507907144897)
  ·
    refine ⟨4532161884580130930358673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6042882512773507907144897 4532161884580130930358673)
    ·
      refine ⟨3399121413435098197769005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4532161884580130930358673 3399121413435098197769005)
      ·
        refine ⟨1274670530038161824163377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3399121413435098197769005 1274670530038161824163377)
        ·
          refine ⟨956002897528621368122533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274670530038161824163377 956002897528621368122533)
          ·
            refine ⟨179250543286616506522975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 956002897528621368122533 179250543286616506522975)
            ·
              refine ⟨268875814929924759784463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179250543286616506522975 268875814929924759784463)
              ·
                refine ⟨403313722394887139676695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268875814929924759784463 403313722394887139676695)
                ·
                  refine ⟨604970583592330709515043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403313722394887139676695 604970583592330709515043)
                  ·
                    refine ⟨907455875388496064272565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 604970583592330709515043 907455875388496064272565)
                    ·
                      refine ⟨85073988317671506025553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 907455875388496064272565 85073988317671506025553)
                      ·
                        rfl

theorem cell23_165681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_165681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165681 prefixEnd_165681 := by exact prefixLift 165681
  have htrace : WordTrace (prefixWord ++ tailWord_165681) baseStart_165681 baseEnd_165681 := by
    simpa [prefixWord, tailWord_165681, baseEnd_165681] using wordTrace_append hprefix tailTrace_165681
  have hstable : (prefixWord ++ tailWord_165681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165681).length < 2 ^ (prefixWord ++ tailWord_165681).sum := by decide
  have hdescent : baseEnd_165681 < baseStart_165681 := by decide
  rcases family_descends (prefixWord ++ tailWord_165681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165684 : List Nat := [2, 5, 1, 1, 2, 12]
def baseStart_165684 : Nat := 118140960795 + 165684 * 2 ^ 59
def prefixEnd_165684 : Nat := 4983230072969 + 3 ^ 40 * 165684 * 2
def baseEnd_165684 : Nat := 350105056624012322173

theorem tailTrace_165684 : CollatzResearch.WordTrace tailWord_165684 prefixEnd_165684 350105056624012322173 := by
  unfold tailWord_165684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3021495965881319709752053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4028661287841759613002737 3021495965881319709752053)
  ·
    refine ⟨283265246801373722789255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3021495965881319709752053 283265246801373722789255)
    ·
      refine ⟨424897870202060584183883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283265246801373722789255 424897870202060584183883)
      ·
        refine ⟨637346805303090876275825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424897870202060584183883 637346805303090876275825)
        ·
          refine ⟨478010103977318157206869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637346805303090876275825 478010103977318157206869)
          ·
            refine ⟨350105056624012322173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 478010103977318157206869 350105056624012322173)
            ·
              rfl

theorem cell23_165684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 12].length) (baseStart_165684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165684 prefixEnd_165684 := by exact prefixLift 165684
  have htrace : WordTrace (prefixWord ++ tailWord_165684) baseStart_165684 baseEnd_165684 := by
    simpa [prefixWord, tailWord_165684, baseEnd_165684] using wordTrace_append hprefix tailTrace_165684
  have hstable : (prefixWord ++ tailWord_165684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165684).length < 2 ^ (prefixWord ++ tailWord_165684).sum := by decide
  have hdescent : baseEnd_165684 < baseStart_165684 := by decide
  rcases family_descends (prefixWord ++ tailWord_165684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165687 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_165687 : Nat := 118140960795 + 165687 * 2 ^ 59
def prefixEnd_165687 : Nat := 4983230072969 + 3 ^ 40 * 165687 * 2
def baseEnd_165687 : Nat := 85077069201598482550525

theorem tailTrace_165687 : CollatzResearch.WordTrace tailWord_165687 prefixEnd_165687 85077069201598482550525 := by
  unfold tailWord_165687
  simp only [CollatzResearch.WordTrace]
  refine ⟨6043101350751770931863315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4028734233834513954575543 6043101350751770931863315)
  ·
    refine ⟨9064652026127656397794973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6043101350751770931863315 9064652026127656397794973)
    ·
      refine ⟨3399244509797871149173115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9064652026127656397794973 3399244509797871149173115)
      ·
        refine ⟨5098866764696806723759673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399244509797871149173115 5098866764696806723759673)
        ·
          refine ⟨3824150073522605042819755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5098866764696806723759673 3824150073522605042819755)
          ·
            refine ⟨5736225110283907564229633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3824150073522605042819755 5736225110283907564229633)
            ·
              refine ⟨4302168832712930673172225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5736225110283907564229633 4302168832712930673172225)
              ·
                refine ⟨3226626624534698004879169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4302168832712930673172225 3226626624534698004879169)
                ·
                  refine ⟨2419969968401023503659377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3226626624534698004879169 2419969968401023503659377)
                  ·
                    refine ⟨1814977476300767627744533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419969968401023503659377 1814977476300767627744533)
                    ·
                      refine ⟨85077069201598482550525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1814977476300767627744533 85077069201598482550525)
                      ·
                        rfl

theorem cell23_165687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_165687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165687 prefixEnd_165687 := by exact prefixLift 165687
  have htrace : WordTrace (prefixWord ++ tailWord_165687) baseStart_165687 baseEnd_165687 := by
    simpa [prefixWord, tailWord_165687, baseEnd_165687] using wordTrace_append hprefix tailTrace_165687
  have hstable : (prefixWord ++ tailWord_165687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165687).length < 2 ^ (prefixWord ++ tailWord_165687).sum := by decide
  have hdescent : baseEnd_165687 < baseStart_165687 := by decide
  rcases family_descends (prefixWord ++ tailWord_165687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165689 : List Nat := [1, 2, 1, 7, 1, 2, 2, 2, 1, 1, 3]
def baseStart_165689 : Nat := 118140960795 + 165689 * 2 ^ 59
def prefixEnd_165689 : Nat := 4983230072969 + 3 ^ 40 * 165689 * 2
def baseEnd_165689 : Nat := 85078096162907474725517

theorem tailTrace_165689 : CollatzResearch.WordTrace tailWord_165689 prefixEnd_165689 85078096162907474725517 := by
  unfold tailWord_165689
  simp only [CollatzResearch.WordTrace]
  refine ⟨6043174296744525273436121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4028782864496350182290747 6043174296744525273436121)
  ·
    refine ⟨4532380722558393955077091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6043174296744525273436121 4532380722558393955077091)
    ·
      refine ⟨6798571083837590932615637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4532380722558393955077091 6798571083837590932615637)
      ·
        refine ⟨159341509777443537483179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6798571083837590932615637 159341509777443537483179)
        ·
          refine ⟨239012264666165306224769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159341509777443537483179 239012264666165306224769)
          ·
            refine ⟨179259198499623979668577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239012264666165306224769 179259198499623979668577)
            ·
              refine ⟨134444398874717984751433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179259198499623979668577 134444398874717984751433)
              ·
                refine ⟨100833299156038488563575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134444398874717984751433 100833299156038488563575)
                ·
                  refine ⟨151249948734057732845363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100833299156038488563575 151249948734057732845363)
                  ·
                    refine ⟨226874923101086599268045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151249948734057732845363 226874923101086599268045)
                    ·
                      refine ⟨85078096162907474725517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 226874923101086599268045 85078096162907474725517)
                      ·
                        rfl

theorem cell23_165689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_165689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165689 prefixEnd_165689 := by exact prefixLift 165689
  have htrace : WordTrace (prefixWord ++ tailWord_165689) baseStart_165689 baseEnd_165689 := by
    simpa [prefixWord, tailWord_165689, baseEnd_165689] using wordTrace_append hprefix tailTrace_165689
  have hstable : (prefixWord ++ tailWord_165689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165689).length < 2 ^ (prefixWord ++ tailWord_165689).sum := by decide
  have hdescent : baseEnd_165689 < baseStart_165689 := by decide
  rcases family_descends (prefixWord ++ tailWord_165689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165721 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 3, 3, 2]
def baseStart_165721 : Nat := 118140960795 + 165721 * 2 ^ 59
def prefixEnd_165721 : Nat := 4983230072969 + 3 ^ 40 * 165721 * 2
def baseEnd_165721 : Nat := 85094527543851349525369

theorem tailTrace_165721 : CollatzResearch.WordTrace tailWord_165721 prefixEnd_165721 85094527543851349525369 := by
  unfold tailWord_165721
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044341432628594738601017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4029560955085729825734011 6044341432628594738601017)
  ·
    refine ⟨4533256074471446053950763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6044341432628594738601017 4533256074471446053950763)
    ·
      refine ⟨6799884111707169080926145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4533256074471446053950763 6799884111707169080926145)
      ·
        refine ⟨5099913083780376810694609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6799884111707169080926145 5099913083780376810694609)
        ·
          refine ⟨3824934812835282608020957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5099913083780376810694609 3824934812835282608020957)
          ·
            refine ⟨1434350554813230978007859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3824934812835282608020957 1434350554813230978007859)
            ·
              refine ⟨2151525832219846467011789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434350554813230978007859 2151525832219846467011789)
              ·
                refine ⟨806822187082442425129421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2151525832219846467011789 806822187082442425129421)
                ·
                  refine ⟨302558320155915909423533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806822187082442425129421 302558320155915909423533)
                  ·
                    refine ⟨113459370058468466033825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 302558320155915909423533 113459370058468466033825)
                    ·
                      refine ⟨85094527543851349525369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113459370058468466033825 85094527543851349525369)
                      ·
                        rfl

theorem cell23_165721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_165721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165721 prefixEnd_165721 := by exact prefixLift 165721
  have htrace : WordTrace (prefixWord ++ tailWord_165721) baseStart_165721 baseEnd_165721 := by
    simpa [prefixWord, tailWord_165721, baseEnd_165721] using wordTrace_append hprefix tailTrace_165721
  have hstable : (prefixWord ++ tailWord_165721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165721).length < 2 ^ (prefixWord ++ tailWord_165721).sum := by decide
  have hdescent : baseEnd_165721 < baseStart_165721 := by decide
  rcases family_descends (prefixWord ++ tailWord_165721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165732 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_165732 : Nat := 118140960795 + 165732 * 2 ^ 59
def prefixEnd_165732 : Nat := 4983230072969 + 3 ^ 40 * 165732 * 2
def baseEnd_165732 : Nat := 85100175831050806487819

theorem tailTrace_165732 : CollatzResearch.WordTrace tailWord_165732 prefixEnd_165732 85100175831050806487819 := by
  unfold tailWord_165732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3022371317794371808625725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4029828423725829078167633 3022371317794371808625725)
  ·
    refine ⟨1133389244172889428234647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3022371317794371808625725 1133389244172889428234647)
    ·
      refine ⟨1700083866259334142351971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133389244172889428234647 1700083866259334142351971)
      ·
        refine ⟨2550125799389001213527957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700083866259334142351971 2550125799389001213527957)
        ·
          refine ⟨119537146846359431884123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2550125799389001213527957 119537146846359431884123)
          ·
            refine ⟨179305720269539147826185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119537146846359431884123 179305720269539147826185)
            ·
              refine ⟨134479290202154360869639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179305720269539147826185 134479290202154360869639)
              ·
                refine ⟨201718935303231541304459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134479290202154360869639 201718935303231541304459)
                ·
                  refine ⟨302578402954847311956689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201718935303231541304459 302578402954847311956689)
                  ·
                    refine ⟨226933802216135483967517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302578402954847311956689 226933802216135483967517)
                    ·
                      refine ⟨85100175831050806487819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 226933802216135483967517 85100175831050806487819)
                      ·
                        rfl

theorem cell23_165732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_165732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165732 prefixEnd_165732 := by exact prefixLift 165732
  have htrace : WordTrace (prefixWord ++ tailWord_165732) baseStart_165732 baseEnd_165732 := by
    simpa [prefixWord, tailWord_165732, baseEnd_165732] using wordTrace_append hprefix tailTrace_165732
  have hstable : (prefixWord ++ tailWord_165732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165732).length < 2 ^ (prefixWord ++ tailWord_165732).sum := by decide
  have hdescent : baseEnd_165732 < baseStart_165732 := by decide
  rcases family_descends (prefixWord ++ tailWord_165732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165754 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_165754 : Nat := 118140960795 + 165754 * 2 ^ 59
def prefixEnd_165754 : Nat := 4983230072969 + 3 ^ 40 * 165754 * 2
def baseEnd_165754 : Nat := 85111472405449720412717

theorem tailTrace_165754 : CollatzResearch.WordTrace tailWord_165754 prefixEnd_165754 85111472405449720412717 := by
  unfold tailWord_165754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511386260377260343638079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4030363361006027583034877 1511386260377260343638079)
  ·
    refine ⟨2267079390565890515457119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511386260377260343638079 2267079390565890515457119)
    ·
      refine ⟨3400619085848835773185679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267079390565890515457119 3400619085848835773185679)
      ·
        refine ⟨5100928628773253659778519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400619085848835773185679 5100928628773253659778519)
        ·
          refine ⟨7651392943159880489667779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5100928628773253659778519 7651392943159880489667779)
          ·
            refine ⟨11477089414739820734501669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651392943159880489667779 11477089414739820734501669)
            ·
              refine ⟨2151954265263716387719063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11477089414739820734501669 2151954265263716387719063)
              ·
                refine ⟨3227931397895574581578595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151954265263716387719063 3227931397895574581578595)
                ·
                  refine ⟨4841897096843361872367893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227931397895574581578595 4841897096843361872367893)
                  ·
                    refine ⟨226963926414532587767245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4841897096843361872367893 226963926414532587767245)
                    ·
                      refine ⟨85111472405449720412717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 226963926414532587767245 85111472405449720412717)
                      ·
                        rfl

theorem cell23_165754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_165754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165754 prefixEnd_165754 := by exact prefixLift 165754
  have htrace : WordTrace (prefixWord ++ tailWord_165754) baseStart_165754 baseEnd_165754 := by
    simpa [prefixWord, tailWord_165754, baseEnd_165754] using wordTrace_append hprefix tailTrace_165754
  have hstable : (prefixWord ++ tailWord_165754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165754).length < 2 ^ (prefixWord ++ tailWord_165754).sum := by decide
  have hdescent : baseEnd_165754 < baseStart_165754 := by decide
  rcases family_descends (prefixWord ++ tailWord_165754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165811 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 2, 5, 2]
def baseStart_165811 : Nat := 118140960795 + 165811 * 2 ^ 59
def prefixEnd_165811 : Nat := 4983230072969 + 3 ^ 40 * 165811 * 2
def baseEnd_165811 : Nat := 85140740802755997399955

theorem tailTrace_165811 : CollatzResearch.WordTrace tailWord_165811 prefixEnd_165811 85140740802755997399955 := by
  unfold tailWord_165811
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047624002302540109377287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4031749334868360072918191 6047624002302540109377287)
  ·
    refine ⟨9071436003453810164065931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6047624002302540109377287 9071436003453810164065931)
    ·
      refine ⟨13607154005180715246098897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9071436003453810164065931 13607154005180715246098897)
      ·
        refine ⟨10205365503885536434574173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13607154005180715246098897 10205365503885536434574173)
        ·
          refine ⟨3827012063957076162965315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10205365503885536434574173 3827012063957076162965315)
          ·
            refine ⟨5740518095935614244447973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827012063957076162965315 5740518095935614244447973)
            ·
              refine ⟨1076347142987927670833995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5740518095935614244447973 1076347142987927670833995)
              ·
                refine ⟨1614520714481891506250993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076347142987927670833995 1614520714481891506250993)
                ·
                  refine ⟨1210890535861418629688245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614520714481891506250993 1210890535861418629688245)
                  ·
                    refine ⟨113520987737007996533273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1210890535861418629688245 113520987737007996533273)
                    ·
                      refine ⟨85140740802755997399955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113520987737007996533273 85140740802755997399955)
                      ·
                        rfl

theorem cell23_165811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5, 2].length) (baseStart_165811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165811 prefixEnd_165811 := by exact prefixLift 165811
  have htrace : WordTrace (prefixWord ++ tailWord_165811) baseStart_165811 baseEnd_165811 := by
    simpa [prefixWord, tailWord_165811, baseEnd_165811] using wordTrace_append hprefix tailTrace_165811
  have hstable : (prefixWord ++ tailWord_165811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165811).length < 2 ^ (prefixWord ++ tailWord_165811).sum := by decide
  have hdescent : baseEnd_165811 < baseStart_165811 := by decide
  rcases family_descends (prefixWord ++ tailWord_165811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165834 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_165834 : Nat := 118140960795 + 165834 * 2 ^ 59
def prefixEnd_165834 : Nat := 4983230072969 + 3 ^ 40 * 165834 * 2
def baseEnd_165834 : Nat := 28384183619269802470783

theorem tailTrace_165834 : CollatzResearch.WordTrace tailWord_165834 prefixEnd_165834 28384183619269802470783 := by
  unfold tailWord_165834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512115720304803759366139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4032308587479476691643037 1512115720304803759366139)
  ·
    refine ⟨2268173580457205639049209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512115720304803759366139 2268173580457205639049209)
    ·
      refine ⟨1701130185342904229286907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2268173580457205639049209 1701130185342904229286907)
      ·
        refine ⟨2551695278014356343930361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1701130185342904229286907 2551695278014356343930361)
        ·
          refine ⟨1913771458510767257947771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551695278014356343930361 1913771458510767257947771)
          ·
            refine ⟨2870657187766150886921657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913771458510767257947771 2870657187766150886921657)
            ·
              refine ⟨2152992890824613165191243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870657187766150886921657 2152992890824613165191243)
              ·
                refine ⟨3229489336236919747786865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152992890824613165191243 3229489336236919747786865)
                ·
                  refine ⟨2422117002177689810840149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3229489336236919747786865 2422117002177689810840149)
                  ·
                    refine ⟨28384183619269802470783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2422117002177689810840149 28384183619269802470783)
                    ·
                      rfl

theorem cell23_165834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_165834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165834 prefixEnd_165834 := by exact prefixLift 165834
  have htrace : WordTrace (prefixWord ++ tailWord_165834) baseStart_165834 baseEnd_165834 := by
    simpa [prefixWord, tailWord_165834, baseEnd_165834] using wordTrace_append hprefix tailTrace_165834
  have hstable : (prefixWord ++ tailWord_165834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165834).length < 2 ^ (prefixWord ++ tailWord_165834).sum := by decide
  have hdescent : baseEnd_165834 < baseStart_165834 := by decide
  rcases family_descends (prefixWord ++ tailWord_165834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165841 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 3, 6, 2]
def baseStart_165841 : Nat := 118140960795 + 165841 * 2 ^ 59
def prefixEnd_165841 : Nat := 4983230072969 + 3 ^ 40 * 165841 * 2
def baseEnd_165841 : Nat := 85156145222390880024817

theorem tailTrace_165841 : CollatzResearch.WordTrace tailWord_165841 prefixEnd_165841 85156145222390880024817 := by
  unfold tailWord_165841
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048718192193855232969377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4032478794795903488646251 6048718192193855232969377)
  ·
    refine ⟨4536538644145391424727033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6048718192193855232969377 4536538644145391424727033)
    ·
      refine ⟨3402403983109043568545275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4536538644145391424727033 3402403983109043568545275)
      ·
        refine ⟨5103605974663565352817913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402403983109043568545275 5103605974663565352817913)
        ·
          refine ⟨3827704480997674014613435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5103605974663565352817913 3827704480997674014613435)
          ·
            refine ⟨5741556721496511021920153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827704480997674014613435 5741556721496511021920153)
            ·
              refine ⟨4306167541122383266440115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5741556721496511021920153 4306167541122383266440115)
              ·
                refine ⟨6459251311683574899660173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306167541122383266440115 6459251311683574899660173)
                ·
                  refine ⟨2422219241881340587372565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6459251311683574899660173 2422219241881340587372565)
                  ·
                    refine ⟨113541526963187840033089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2422219241881340587372565 113541526963187840033089)
                    ·
                      refine ⟨85156145222390880024817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113541526963187840033089 85156145222390880024817)
                      ·
                        rfl

theorem cell23_165841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_165841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165841 prefixEnd_165841 := by exact prefixLift 165841
  have htrace : WordTrace (prefixWord ++ tailWord_165841) baseStart_165841 baseEnd_165841 := by
    simpa [prefixWord, tailWord_165841, baseEnd_165841] using wordTrace_append hprefix tailTrace_165841
  have hstable : (prefixWord ++ tailWord_165841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165841).length < 2 ^ (prefixWord ++ tailWord_165841).sum := by decide
  have hdescent : baseEnd_165841 < baseStart_165841 := by decide
  rcases family_descends (prefixWord ++ tailWord_165841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165881 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 6]
def baseStart_165881 : Nat := 118140960795 + 165881 * 2 ^ 59
def prefixEnd_165881 : Nat := 4983230072969 + 3 ^ 40 * 165881 * 2
def baseEnd_165881 : Nat := 9464076049841191502737

theorem tailTrace_165881 : CollatzResearch.WordTrace tailWord_165881 prefixEnd_165881 9464076049841191502737 := by
  unfold tailWord_165881
  simp only [CollatzResearch.WordTrace]
  refine ⟨6050177112048942064425497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4033451408032628042950331 6050177112048942064425497)
  ·
    refine ⟨4537632834036706548319123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6050177112048942064425497 4537632834036706548319123)
    ·
      refine ⟨6806449251055059822478685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4537632834036706548319123 6806449251055059822478685)
      ·
        refine ⟨2552418469145647433429507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6806449251055059822478685 2552418469145647433429507)
        ·
          refine ⟨3828627703718471150144261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552418469145647433429507 3828627703718471150144261)
          ·
            refine ⟨717867694447213340652049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3828627703718471150144261 717867694447213340652049)
            ·
              refine ⟨538400770835410005489037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717867694447213340652049 538400770835410005489037)
              ·
                refine ⟨201900289063278752058389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538400770835410005489037 201900289063278752058389)
                ·
                  refine ⟨9464076049841191502737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 201900289063278752058389 9464076049841191502737)
                  ·
                    rfl

theorem cell23_165881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 6].length) (baseStart_165881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165881 prefixEnd_165881 := by exact prefixLift 165881
  have htrace : WordTrace (prefixWord ++ tailWord_165881) baseStart_165881 baseEnd_165881 := by
    simpa [prefixWord, tailWord_165881, baseEnd_165881] using wordTrace_append hprefix tailTrace_165881
  have hstable : (prefixWord ++ tailWord_165881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165881).length < 2 ^ (prefixWord ++ tailWord_165881).sum := by decide
  have hdescent : baseEnd_165881 < baseStart_165881 := by decide
  rcases family_descends (prefixWord ++ tailWord_165881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165892 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_165892 : Nat := 118140960795 + 165892 * 2 ^ 59
def prefixEnd_165892 : Nat := 4983230072969 + 3 ^ 40 * 165892 * 2
def baseEnd_165892 : Nat := 85182332735770180487083

theorem tailTrace_165892 : CollatzResearch.WordTrace tailWord_165892 prefixEnd_165892 85182332735770180487083 := by
  unfold tailWord_165892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025289157504545471537965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4033718876672727295383953 3025289157504545471537965)
  ·
    refine ⟨1134483434064204551826737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3025289157504545471537965 1134483434064204551826737)
    ·
      refine ⟨850862575548153413870053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1134483434064204551826737 850862575548153413870053)
      ·
        refine ⟨159536732915278765100635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 850862575548153413870053 159536732915278765100635)
        ·
          refine ⟨239305099372918147650953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159536732915278765100635 239305099372918147650953)
          ·
            refine ⟨179478824529688610738215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239305099372918147650953 179478824529688610738215)
            ·
              refine ⟨269218236794532916107323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179478824529688610738215 269218236794532916107323)
              ·
                refine ⟨403827355191799374160985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269218236794532916107323 403827355191799374160985)
                ·
                  refine ⟨302870516393849530620739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403827355191799374160985 302870516393849530620739)
                  ·
                    refine ⟨454305774590774295931109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302870516393849530620739 454305774590774295931109)
                    ·
                      refine ⟨85182332735770180487083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 454305774590774295931109 85182332735770180487083)
                      ·
                        rfl

theorem cell23_165892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_165892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165892 prefixEnd_165892 := by exact prefixLift 165892
  have htrace : WordTrace (prefixWord ++ tailWord_165892) baseStart_165892 baseEnd_165892 := by
    simpa [prefixWord, tailWord_165892, baseEnd_165892] using wordTrace_append hprefix tailTrace_165892
  have hstable : (prefixWord ++ tailWord_165892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165892).length < 2 ^ (prefixWord ++ tailWord_165892).sum := by decide
  have hdescent : baseEnd_165892 < baseStart_165892 := by decide
  rcases family_descends (prefixWord ++ tailWord_165892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165895 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_165895 : Nat := 118140960795 + 165895 * 2 ^ 59
def prefixEnd_165895 : Nat := 4983230072969 + 3 ^ 40 * 165895 * 2
def baseEnd_165895 : Nat := 85183873177733668749569

theorem tailTrace_165895 : CollatzResearch.WordTrace tailWord_165895 prefixEnd_165895 85183873177733668749569 := by
  unfold tailWord_165895
  simp only [CollatzResearch.WordTrace]
  refine ⟨6050687733998222455435139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4033791822665481636956759 6050687733998222455435139)
  ·
    refine ⟨9076031600997333683152709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6050687733998222455435139 9076031600997333683152709)
    ·
      refine ⟨1701755925187000065591133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9076031600997333683152709 1701755925187000065591133)
      ·
        refine ⟨638158471945125024596675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1701755925187000065591133 638158471945125024596675)
        ·
          refine ⟨957237707917687536895013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638158471945125024596675 957237707917687536895013)
          ·
            refine ⟨179482070234566413167815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 957237707917687536895013 179482070234566413167815)
            ·
              refine ⟨269223105351849619751723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179482070234566413167815 269223105351849619751723)
              ·
                refine ⟨403834658027774429627585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269223105351849619751723 403834658027774429627585)
                ·
                  refine ⟨302875993520830822220689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403834658027774429627585 302875993520830822220689)
                  ·
                    refine ⟨227156995140623116665517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 302875993520830822220689 227156995140623116665517)
                    ·
                      refine ⟨85183873177733668749569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 227156995140623116665517 85183873177733668749569)
                      ·
                        rfl

theorem cell23_165895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_165895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165895 prefixEnd_165895 := by exact prefixLift 165895
  have htrace : WordTrace (prefixWord ++ tailWord_165895) baseStart_165895 baseEnd_165895 := by
    simpa [prefixWord, tailWord_165895, baseEnd_165895] using wordTrace_append hprefix tailTrace_165895
  have hstable : (prefixWord ++ tailWord_165895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165895).length < 2 ^ (prefixWord ++ tailWord_165895).sum := by decide
  have hdescent : baseEnd_165895 < baseStart_165895 := by decide
  rcases family_descends (prefixWord ++ tailWord_165895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165904 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_165904 : Nat := 118140960795 + 165904 * 2 ^ 59
def prefixEnd_165904 : Nat := 4983230072969 + 3 ^ 40 * 165904 * 2
def baseEnd_165904 : Nat := 85188494503624133537027

theorem tailTrace_165904 : CollatzResearch.WordTrace tailWord_165904 prefixEnd_165904 85188494503624133537027 := by
  unfold tailWord_165904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025507995482808496256383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4034010660643744661675177 3025507995482808496256383)
  ·
    refine ⟨4538261993224212744384575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3025507995482808496256383 4538261993224212744384575)
    ·
      refine ⟨6807392989836319116576863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4538261993224212744384575 6807392989836319116576863)
      ·
        refine ⟨10211089484754478674865295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807392989836319116576863 10211089484754478674865295)
        ·
          refine ⟨15316634227131718012297943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10211089484754478674865295 15316634227131718012297943)
          ·
            refine ⟨22974951340697577018446915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15316634227131718012297943 22974951340697577018446915)
            ·
              refine ⟨34462427011046365527670373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22974951340697577018446915 34462427011046365527670373)
              ·
                refine ⟨6461705064571193536438195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34462427011046365527670373 6461705064571193536438195)
                ·
                  refine ⟨9692557596856790304657293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461705064571193536438195 9692557596856790304657293)
                  ·
                    refine ⟨3634709098821296364246485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9692557596856790304657293 3634709098821296364246485)
                    ·
                      refine ⟨85188494503624133537027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3634709098821296364246485 85188494503624133537027)
                      ·
                        rfl

theorem cell23_165904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_165904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165904 prefixEnd_165904 := by exact prefixLift 165904
  have htrace : WordTrace (prefixWord ++ tailWord_165904) baseStart_165904 baseEnd_165904 := by
    simpa [prefixWord, tailWord_165904, baseEnd_165904] using wordTrace_append hprefix tailTrace_165904
  have hstable : (prefixWord ++ tailWord_165904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165904).length < 2 ^ (prefixWord ++ tailWord_165904).sum := by decide
  have hdescent : baseEnd_165904 < baseStart_165904 := by decide
  rcases family_descends (prefixWord ++ tailWord_165904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165925 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_165925 : Nat := 118140960795 + 165925 * 2 ^ 59
def prefixEnd_165925 : Nat := 4983230072969 + 3 ^ 40 * 165925 * 2
def baseEnd_165925 : Nat := 85199277597368551374431

theorem tailTrace_165925 : CollatzResearch.WordTrace tailWord_165925 prefixEnd_165925 85199277597368551374431 := by
  unfold tailWord_165925
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051781923889537579027229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4034521282593025052684819 6051781923889537579027229)
  ·
    refine ⟨2269418221458576592135211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6051781923889537579027229 2269418221458576592135211)
    ·
      refine ⟨3404127332187864888202817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269418221458576592135211 3404127332187864888202817)
      ·
        refine ⟨2553095499140898666152113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3404127332187864888202817 2553095499140898666152113)
        ·
          refine ⟨1914821624355673999614085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2553095499140898666152113 1914821624355673999614085)
          ·
            refine ⟨359029054566688874927641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1914821624355673999614085 359029054566688874927641)
            ·
              refine ⟨269271790925016656195731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359029054566688874927641 269271790925016656195731)
              ·
                refine ⟨403907686387524984293597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269271790925016656195731 403907686387524984293597)
                ·
                  refine ⟨151465382395321869110099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403907686387524984293597 151465382395321869110099)
                  ·
                    refine ⟨227198073592982803665149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151465382395321869110099 227198073592982803665149)
                    ·
                      refine ⟨85199277597368551374431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 227198073592982803665149 85199277597368551374431)
                      ·
                        rfl

theorem cell23_165925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_165925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165925 prefixEnd_165925 := by exact prefixLift 165925
  have htrace : WordTrace (prefixWord ++ tailWord_165925) baseStart_165925 baseEnd_165925 := by
    simpa [prefixWord, tailWord_165925, baseEnd_165925] using wordTrace_append hprefix tailTrace_165925
  have hstable : (prefixWord ++ tailWord_165925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165925).length < 2 ^ (prefixWord ++ tailWord_165925).sum := by decide
  have hdescent : baseEnd_165925 < baseStart_165925 := by decide
  rcases family_descends (prefixWord ++ tailWord_165925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165931 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 4]
def baseStart_165931 : Nat := 118140960795 + 165931 * 2 ^ 59
def prefixEnd_165931 : Nat := 4983230072969 + 3 ^ 40 * 165931 * 2
def baseEnd_165931 : Nat := 85202358481295527899403

theorem tailTrace_165931 : CollatzResearch.WordTrace tailWord_165931 prefixEnd_165931 85202358481295527899403 := by
  unfold tailWord_165931
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052000761867800603745647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4034667174578533735830431 6052000761867800603745647)
  ·
    refine ⟨9078001142801700905618471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6052000761867800603745647 9078001142801700905618471)
    ·
      refine ⟨13617001714202551358427707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9078001142801700905618471 13617001714202551358427707)
      ·
        refine ⟨20425502571303827037641561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13617001714202551358427707 20425502571303827037641561)
        ·
          refine ⟨15319126928477870278231171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20425502571303827037641561 15319126928477870278231171)
          ·
            refine ⟨22978690392716805417346757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15319126928477870278231171 22978690392716805417346757)
            ·
              refine ⟨4308504448634401015752517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22978690392716805417346757 4308504448634401015752517)
              ·
                refine ⟨807844584118950190453597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4308504448634401015752517 807844584118950190453597)
                ·
                  refine ⟨302941719044606321420099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807844584118950190453597 302941719044606321420099)
                  ·
                    refine ⟨454412578566909482130149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 302941719044606321420099 454412578566909482130149)
                    ·
                      refine ⟨85202358481295527899403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 454412578566909482130149 85202358481295527899403)
                      ·
                        rfl

theorem cell23_165931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 4].length) (baseStart_165931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165931 prefixEnd_165931 := by exact prefixLift 165931
  have htrace : WordTrace (prefixWord ++ tailWord_165931) baseStart_165931 baseEnd_165931 := by
    simpa [prefixWord, tailWord_165931, baseEnd_165931] using wordTrace_append hprefix tailTrace_165931
  have hstable : (prefixWord ++ tailWord_165931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165931).length < 2 ^ (prefixWord ++ tailWord_165931).sum := by decide
  have hdescent : baseEnd_165931 < baseStart_165931 := by decide
  rcases family_descends (prefixWord ++ tailWord_165931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165945 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 1, 5]
def baseStart_165945 : Nat := 118140960795 + 165945 * 2 ^ 59
def prefixEnd_165945 : Nat := 4983230072969 + 3 ^ 40 * 165945 * 2
def baseEnd_165945 : Nat := 28403182403486157708113

theorem tailTrace_165945 : CollatzResearch.WordTrace tailWord_165945 prefixEnd_165945 28403182403486157708113 := by
  unfold tailWord_165945
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052511383817080994755289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4035007589211387329836859 6052511383817080994755289)
  ·
    refine ⟨4539383537862810746066467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6052511383817080994755289 4539383537862810746066467)
    ·
      refine ⟨6809075306794216119099701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539383537862810746066467 6809075306794216119099701)
      ·
        refine ⟨638350810011957761165597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6809075306794216119099701 638350810011957761165597)
        ·
          refine ⟨239381553754484160437099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638350810011957761165597 239381553754484160437099)
          ·
            refine ⟨359072330631726240655649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239381553754484160437099 359072330631726240655649)
            ·
              refine ⟨269304247973794680491737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359072330631726240655649 269304247973794680491737)
              ·
                refine ⟨201978185980346010368803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269304247973794680491737 201978185980346010368803)
                ·
                  refine ⟨302967278970519015553205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201978185980346010368803 302967278970519015553205)
                  ·
                    refine ⟨28403182403486157708113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 302967278970519015553205 28403182403486157708113)
                    ·
                      rfl

theorem cell23_165945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_165945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165945 prefixEnd_165945 := by exact prefixLift 165945
  have htrace : WordTrace (prefixWord ++ tailWord_165945) baseStart_165945 baseEnd_165945 := by
    simpa [prefixWord, tailWord_165945, baseEnd_165945] using wordTrace_append hprefix tailTrace_165945
  have hstable : (prefixWord ++ tailWord_165945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165945).length < 2 ^ (prefixWord ++ tailWord_165945).sum := by decide
  have hdescent : baseEnd_165945 < baseStart_165945 := by decide
  rcases family_descends (prefixWord ++ tailWord_165945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165948 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_165948 : Nat := 118140960795 + 165948 * 2 ^ 59
def prefixEnd_165948 : Nat := 4983230072969 + 3 ^ 40 * 165948 * 2
def baseEnd_165948 : Nat := 85211087652421961386825

theorem tailTrace_165948 : CollatzResearch.WordTrace tailWord_165948 prefixEnd_165948 85211087652421961386825 := by
  unfold tailWord_165948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026310401403106253557249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4035080535204141671409665 3026310401403106253557249)
  ·
    refine ⟨2269732801052329690167937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3026310401403106253557249 2269732801052329690167937)
    ·
      refine ⟨1702299600789247267625953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2269732801052329690167937 1702299600789247267625953)
      ·
        refine ⟨1276724700591935450719465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1702299600789247267625953 1276724700591935450719465)
        ·
          refine ⟨957543525443951588039599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276724700591935450719465 957543525443951588039599)
          ·
            refine ⟨1436315288165927382059399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957543525443951588039599 1436315288165927382059399)
            ·
              refine ⟨2154472932248891073089099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436315288165927382059399 2154472932248891073089099)
              ·
                refine ⟨3231709398373336609633649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154472932248891073089099 3231709398373336609633649)
                ·
                  refine ⟨2423782048780002457225237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3231709398373336609633649 2423782048780002457225237)
                  ·
                    refine ⟨113614783536562615182433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2423782048780002457225237 113614783536562615182433)
                    ·
                      refine ⟨85211087652421961386825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113614783536562615182433 85211087652421961386825)
                      ·
                        rfl

theorem cell23_165948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_165948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165948 prefixEnd_165948 := by exact prefixLift 165948
  have htrace : WordTrace (prefixWord ++ tailWord_165948) baseStart_165948 baseEnd_165948 := by
    simpa [prefixWord, tailWord_165948, baseEnd_165948] using wordTrace_append hprefix tailTrace_165948
  have hstable : (prefixWord ++ tailWord_165948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165948).length < 2 ^ (prefixWord ++ tailWord_165948).sum := by decide
  have hdescent : baseEnd_165948 < baseStart_165948 := by decide
  rcases family_descends (prefixWord ++ tailWord_165948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165961 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_165961 : Nat := 118140960795 + 165961 * 2 ^ 59
def prefixEnd_165961 : Nat := 4983230072969 + 3 ^ 40 * 165961 * 2
def baseEnd_165961 : Nat := 85217762900930410524265

theorem tailTrace_165961 : CollatzResearch.WordTrace tailWord_165961 prefixEnd_165961 85217762900930410524265 := by
  unfold tailWord_165961
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053094951759115727337737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4035396634506077151558491 6053094951759115727337737)
  ·
    refine ⟨4539821213819336795503303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6053094951759115727337737 4539821213819336795503303)
    ·
      refine ⟨6809731820729005193254955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539821213819336795503303 6809731820729005193254955)
      ·
        refine ⟨10214597731093507789882433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809731820729005193254955 10214597731093507789882433)
        ·
          refine ⟨7660948298320130842411825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10214597731093507789882433 7660948298320130842411825)
          ·
            refine ⟨5745711223740098131808869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660948298320130842411825 5745711223740098131808869)
            ·
              refine ⟨1077320854451268399714163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5745711223740098131808869 1077320854451268399714163)
              ·
                refine ⟨1615981281676902599571245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077320854451268399714163 1615981281676902599571245)
                ·
                  refine ⟨605992980628838474839217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1615981281676902599571245 605992980628838474839217)
                  ·
                    refine ⟨454494735471628856129413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605992980628838474839217 454494735471628856129413)
                    ·
                      refine ⟨85217762900930410524265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 454494735471628856129413 85217762900930410524265)
                      ·
                        rfl

theorem cell23_165961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_165961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165961 prefixEnd_165961 := by exact prefixLift 165961
  have htrace : WordTrace (prefixWord ++ tailWord_165961) baseStart_165961 baseEnd_165961 := by
    simpa [prefixWord, tailWord_165961, baseEnd_165961] using wordTrace_append hprefix tailTrace_165961
  have hstable : (prefixWord ++ tailWord_165961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165961).length < 2 ^ (prefixWord ++ tailWord_165961).sum := by decide
  have hdescent : baseEnd_165961 < baseStart_165961 := by decide
  rcases family_descends (prefixWord ++ tailWord_165961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165965 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_165965 : Nat := 118140960795 + 165965 * 2 ^ 59
def prefixEnd_165965 : Nat := 4983230072969 + 3 ^ 40 * 165965 * 2
def baseEnd_165965 : Nat := 85219816823548394874247

theorem tailTrace_165965 : CollatzResearch.WordTrace tailWord_165965 prefixEnd_165965 85219816823548394874247 := by
  unfold tailWord_165965
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053240843744624410483349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4035493895829749606988899 6053240843744624410483349)
  ·
    refine ⟨283745664550529269241407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6053240843744624410483349 283745664550529269241407)
    ·
      refine ⟨425618496825793903862111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283745664550529269241407 425618496825793903862111)
      ·
        refine ⟨638427745238690855793167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425618496825793903862111 638427745238690855793167)
        ·
          refine ⟨957641617858036283689751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638427745238690855793167 957641617858036283689751)
          ·
            refine ⟨1436462426787054425534627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957641617858036283689751 1436462426787054425534627)
            ·
              refine ⟨2154693640180581638301941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436462426787054425534627 2154693640180581638301941)
              ·
                refine ⟨202002528766929528590807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2154693640180581638301941 202002528766929528590807)
                ·
                  refine ⟨303003793150394292886211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202002528766929528590807 303003793150394292886211)
                  ·
                    refine ⟨454505689725591439329317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 303003793150394292886211 454505689725591439329317)
                    ·
                      refine ⟨85219816823548394874247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 454505689725591439329317 85219816823548394874247)
                      ·
                        rfl

theorem cell23_165965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_165965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165965 prefixEnd_165965 := by exact prefixLift 165965
  have htrace : WordTrace (prefixWord ++ tailWord_165965) baseStart_165965 baseEnd_165965 := by
    simpa [prefixWord, tailWord_165965, baseEnd_165965] using wordTrace_append hprefix tailTrace_165965
  have hstable : (prefixWord ++ tailWord_165965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165965).length < 2 ^ (prefixWord ++ tailWord_165965).sum := by decide
  have hdescent : baseEnd_165965 < baseStart_165965 := by decide
  rcases family_descends (prefixWord ++ tailWord_165965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165991 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_165991 : Nat := 118140960795 + 165991 * 2 ^ 59
def prefixEnd_165991 : Nat := 4983230072969 + 3 ^ 40 * 165991 * 2
def baseEnd_165991 : Nat := 85233167320565293149127

theorem tailTrace_165991 : CollatzResearch.WordTrace tailWord_165991 prefixEnd_165991 85233167320565293149127 := by
  unfold tailWord_165991
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054189141650430850929827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4036126094433620567286551 6054189141650430850929827)
  ·
    refine ⟨9081283712475646276394741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6054189141650430850929827 9081283712475646276394741)
    ·
      refine ⟨851370348044591838412007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9081283712475646276394741 851370348044591838412007)
      ·
        refine ⟨1277055522066887757618011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851370348044591838412007 1277055522066887757618011)
        ·
          refine ⟨1915583283100331636427017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277055522066887757618011 1915583283100331636427017)
          ·
            refine ⟨1436687462325248727320263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915583283100331636427017 1436687462325248727320263)
            ·
              refine ⟨2155031193487873090980395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436687462325248727320263 2155031193487873090980395)
              ·
                refine ⟨3232546790231809636470593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155031193487873090980395 3232546790231809636470593)
                ·
                  refine ⟨2424410092673857227352945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232546790231809636470593 2424410092673857227352945)
                  ·
                    refine ⟨1818307569505392920514709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424410092673857227352945 1818307569505392920514709)
                    ·
                      refine ⟨85233167320565293149127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1818307569505392920514709 85233167320565293149127)
                      ·
                        rfl

theorem cell23_165991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_165991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_165991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_165991 prefixEnd_165991 := by exact prefixLift 165991
  have htrace : WordTrace (prefixWord ++ tailWord_165991) baseStart_165991 baseEnd_165991 := by
    simpa [prefixWord, tailWord_165991, baseEnd_165991] using wordTrace_append hprefix tailTrace_165991
  have hstable : (prefixWord ++ tailWord_165991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165991).length < 2 ^ (prefixWord ++ tailWord_165991).sum := by decide
  have hdescent : baseEnd_165991 < baseStart_165991 := by decide
  rcases family_descends (prefixWord ++ tailWord_165991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166002 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_166002 : Nat := 118140960795 + 166002 * 2 ^ 59
def prefixEnd_166002 : Nat := 4983230072969 + 3 ^ 40 * 166002 * 2
def baseEnd_166002 : Nat := 85238815607764750111577

theorem tailTrace_166002 : CollatzResearch.WordTrace tailWord_166002 prefixEnd_166002 85238815607764750111577 := by
  unfold tailWord_166002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513647586152644932395065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4036393563073719819720173 1513647586152644932395065)
  ·
    refine ⟨1135235689614483699296299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1513647586152644932395065 1135235689614483699296299)
    ·
      refine ⟨1702853534421725548944449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135235689614483699296299 1702853534421725548944449)
      ·
        refine ⟨1277140150816294161708337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1702853534421725548944449 1277140150816294161708337)
        ·
          refine ⟨957855113112220621281253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1277140150816294161708337 957855113112220621281253)
          ·
            refine ⟨179597833708541366490235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 957855113112220621281253 179597833708541366490235)
            ·
              refine ⟨269396750562812049735353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179597833708541366490235 269396750562812049735353)
              ·
                refine ⟨202047562922109037301515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269396750562812049735353 202047562922109037301515)
                ·
                  refine ⟨303071344383163555952273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202047562922109037301515 303071344383163555952273)
                  ·
                    refine ⟨227303508287372666964205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 303071344383163555952273 227303508287372666964205)
                    ·
                      refine ⟨85238815607764750111577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 227303508287372666964205 85238815607764750111577)
                      ·
                        rfl

theorem cell23_166002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_166002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166002 prefixEnd_166002 := by exact prefixLift 166002
  have htrace : WordTrace (prefixWord ++ tailWord_166002) baseStart_166002 baseEnd_166002 := by
    simpa [prefixWord, tailWord_166002, baseEnd_166002] using wordTrace_append hprefix tailTrace_166002
  have hstable : (prefixWord ++ tailWord_166002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166002).length < 2 ^ (prefixWord ++ tailWord_166002).sum := by decide
  have hdescent : baseEnd_166002 < baseStart_166002 := by decide
  rcases family_descends (prefixWord ++ tailWord_166002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166041 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_166041 : Nat := 118140960795 + 166041 * 2 ^ 59
def prefixEnd_166041 : Nat := 4983230072969 + 3 ^ 40 * 166041 * 2
def baseEnd_166041 : Nat := 85258841353290097523897

theorem tailTrace_166041 : CollatzResearch.WordTrace tailWord_166041 prefixEnd_166041 85258841353290097523897 := by
  unfold tailWord_166041
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056012791469289390249977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4037341860979526260166651 6056012791469289390249977)
  ·
    refine ⟨4542009593601967042687483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6056012791469289390249977 4542009593601967042687483)
    ·
      refine ⟨6813014390402950564031225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542009593601967042687483 6813014390402950564031225)
      ·
        refine ⟨5109760792802212923023419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6813014390402950564031225 5109760792802212923023419)
        ·
          refine ⟨7664641189203319384535129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5109760792802212923023419 7664641189203319384535129)
          ·
            refine ⟨5748480891902489538401347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7664641189203319384535129 5748480891902489538401347)
            ·
              refine ⟨8622721337853734307602021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748480891902489538401347 8622721337853734307602021)
              ·
                refine ⟨1616760250847575182675379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8622721337853734307602021 1616760250847575182675379)
                ·
                  refine ⟨2425140376271362774013069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616760250847575182675379 2425140376271362774013069)
                  ·
                    refine ⟨909427641101761040254901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425140376271362774013069 909427641101761040254901)
                    ·
                      refine ⟨85258841353290097523897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 909427641101761040254901 85258841353290097523897)
                      ·
                        rfl

theorem cell23_166041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_166041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166041 prefixEnd_166041 := by exact prefixLift 166041
  have htrace : WordTrace (prefixWord ++ tailWord_166041) baseStart_166041 baseEnd_166041 := by
    simpa [prefixWord, tailWord_166041, baseEnd_166041] using wordTrace_append hprefix tailTrace_166041
  have hstable : (prefixWord ++ tailWord_166041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166041).length < 2 ^ (prefixWord ++ tailWord_166041).sum := by decide
  have hdescent : baseEnd_166041 < baseStart_166041 := by decide
  rcases family_descends (prefixWord ++ tailWord_166041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166048 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 2, 6]
def baseStart_166048 : Nat := 118140960795 + 166048 * 2 ^ 59
def prefixEnd_166048 : Nat := 4983230072969 + 3 ^ 40 * 166048 * 2
def baseEnd_166048 : Nat := 28420811905957190045455

theorem tailTrace_166048 : CollatzResearch.WordTrace tailWord_166048 prefixEnd_166048 28420811905957190045455 := by
  unfold tailWord_166048
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028134051221964792877399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4037512068295953057169865 3028134051221964792877399)
  ·
    refine ⟨4542201076832947189316099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3028134051221964792877399 4542201076832947189316099)
    ·
      refine ⟨6813301615249420783974149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542201076832947189316099 6813301615249420783974149)
      ·
        refine ⟨1277494052859266396995153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6813301615249420783974149 1277494052859266396995153)
        ·
          refine ⟨958120539644449797746365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1277494052859266396995153 958120539644449797746365)
          ·
            refine ⟨359295202366668674154887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 958120539644449797746365 359295202366668674154887)
            ·
              refine ⟨538942803550003011232331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359295202366668674154887 538942803550003011232331)
              ·
                refine ⟨808414205325004516848497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538942803550003011232331 808414205325004516848497)
                ·
                  refine ⟨606310653993753387636373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808414205325004516848497 606310653993753387636373)
                  ·
                    refine ⟨28420811905957190045455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 606310653993753387636373 28420811905957190045455)
                    ·
                      rfl

theorem cell23_166048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_166048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166048 prefixEnd_166048 := by exact prefixLift 166048
  have htrace : WordTrace (prefixWord ++ tailWord_166048) baseStart_166048 baseEnd_166048 := by
    simpa [prefixWord, tailWord_166048, baseEnd_166048] using wordTrace_append hprefix tailTrace_166048
  have hstable : (prefixWord ++ tailWord_166048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166048).length < 2 ^ (prefixWord ++ tailWord_166048).sum := by decide
  have hdescent : baseEnd_166048 < baseStart_166048 := by decide
  rcases family_descends (prefixWord ++ tailWord_166048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166076 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_166076 : Nat := 118140960795 + 166076 * 2 ^ 59
def prefixEnd_166076 : Nat := 4983230072969 + 3 ^ 40 * 166076 * 2
def baseEnd_166076 : Nat := 85276813176197460586237

theorem tailTrace_166076 : CollatzResearch.WordTrace tailWord_166076 prefixEnd_166076 85276813176197460586237 := by
  unfold tailWord_166076
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028644673171245183887041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4038192897561660245182721 3028644673171245183887041)
  ·
    refine ⟨2271483504878433887915281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3028644673171245183887041 2271483504878433887915281)
    ·
      refine ⟨1703612628658825415936461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2271483504878433887915281 1703612628658825415936461)
      ·
        refine ⟨638854735747059530976173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1703612628658825415936461 638854735747059530976173)
        ·
          refine ⟨239570525905147324116065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638854735747059530976173 239570525905147324116065)
          ·
            refine ⟨179677894428860493087049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239570525905147324116065 179677894428860493087049)
            ·
              refine ⟨134758420821645369815287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179677894428860493087049 134758420821645369815287)
              ·
                refine ⟨202137631232468054722931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134758420821645369815287 202137631232468054722931)
                ·
                  refine ⟨303206446848702082084397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202137631232468054722931 303206446848702082084397)
                  ·
                    refine ⟨113702417568263280781649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 303206446848702082084397 113702417568263280781649)
                    ·
                      refine ⟨85276813176197460586237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 113702417568263280781649 85276813176197460586237)
                      ·
                        rfl

theorem cell23_166076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_166076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166076 prefixEnd_166076 := by exact prefixLift 166076
  have htrace : WordTrace (prefixWord ++ tailWord_166076) baseStart_166076 baseEnd_166076 := by
    simpa [prefixWord, tailWord_166076, baseEnd_166076] using wordTrace_append hprefix tailTrace_166076
  have hstable : (prefixWord ++ tailWord_166076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166076).length < 2 ^ (prefixWord ++ tailWord_166076).sum := by decide
  have hdescent : baseEnd_166076 < baseStart_166076 := by decide
  rcases family_descends (prefixWord ++ tailWord_166076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166082 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_166082 : Nat := 118140960795 + 166082 * 2 ^ 59
def prefixEnd_166082 : Nat := 4983230072969 + 3 ^ 40 * 166082 * 2
def baseEnd_166082 : Nat := 28426631353374812370403

theorem tailTrace_166082 : CollatzResearch.WordTrace tailWord_166082 prefixEnd_166082 28426631353374812370403 := by
  unfold tailWord_166082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514377046080188348123125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4038338789547168928328333 1514377046080188348123125)
  ·
    refine ⟨141972848070017657636543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1514377046080188348123125 141972848070017657636543)
    ·
      refine ⟨212959272105026486454815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141972848070017657636543 212959272105026486454815)
      ·
        refine ⟨319438908157539729682223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212959272105026486454815 319438908157539729682223)
        ·
          refine ⟨479158362236309594523335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319438908157539729682223 479158362236309594523335)
          ·
            refine ⟨718737543354464391785003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479158362236309594523335 718737543354464391785003)
            ·
              refine ⟨1078106315031696587677505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718737543354464391785003 1078106315031696587677505)
              ·
                refine ⟨808579736273772440758129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078106315031696587677505 808579736273772440758129)
                ·
                  refine ⟨606434802205329330568597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808579736273772440758129 606434802205329330568597)
                  ·
                    refine ⟨28426631353374812370403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 606434802205329330568597 28426631353374812370403)
                    ·
                      rfl

theorem cell23_166082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_166082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166082 prefixEnd_166082 := by exact prefixLift 166082
  have htrace : WordTrace (prefixWord ++ tailWord_166082) baseStart_166082 baseEnd_166082 := by
    simpa [prefixWord, tailWord_166082, baseEnd_166082] using wordTrace_append hprefix tailTrace_166082
  have hstable : (prefixWord ++ tailWord_166082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166082).length < 2 ^ (prefixWord ++ tailWord_166082).sum := by decide
  have hdescent : baseEnd_166082 < baseStart_166082 := by decide
  rcases family_descends (prefixWord ++ tailWord_166082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166102 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_166102 : Nat := 118140960795 + 166102 * 2 ^ 59
def prefixEnd_166102 : Nat := 4983230072969 + 3 ^ 40 * 166102 * 2
def baseEnd_166102 : Nat := 85290163673214358861117

theorem tailTrace_166102 : CollatzResearch.WordTrace tailWord_166102 prefixEnd_166102 85290163673214358861117 := by
  unfold tailWord_166102
  simp only [CollatzResearch.WordTrace]
  refine ⟨378639852765518550513785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4038825096165531205480373 378639852765518550513785)
  ·
    refine ⟨283979889574138912885339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 378639852765518550513785 283979889574138912885339)
    ·
      refine ⟨425969834361208369328009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283979889574138912885339 425969834361208369328009)
      ·
        refine ⟨319477375770906276996007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425969834361208369328009 319477375770906276996007)
        ·
          refine ⟨479216063656359415494011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319477375770906276996007 479216063656359415494011)
          ·
            refine ⟨718824095484539123241017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479216063656359415494011 718824095484539123241017)
            ·
              refine ⟨539118071613404342430763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718824095484539123241017 539118071613404342430763)
              ·
                refine ⟨808677107420106513646145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539118071613404342430763 808677107420106513646145)
                ·
                  refine ⟨606507830565079885234609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808677107420106513646145 606507830565079885234609)
                  ·
                    refine ⟨454880872923809913925957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 606507830565079885234609 454880872923809913925957)
                    ·
                      refine ⟨85290163673214358861117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 454880872923809913925957 85290163673214358861117)
                      ·
                        rfl

theorem cell23_166102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_166102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_166102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_166102 prefixEnd_166102 := by exact prefixLift 166102
  have htrace : WordTrace (prefixWord ++ tailWord_166102) baseStart_166102 baseEnd_166102 := by
    simpa [prefixWord, tailWord_166102, baseEnd_166102] using wordTrace_append hprefix tailTrace_166102
  have hstable : (prefixWord ++ tailWord_166102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166102).length < 2 ^ (prefixWord ++ tailWord_166102).sum := by decide
  have hdescent : baseEnd_166102 < baseStart_166102 := by decide
  rcases family_descends (prefixWord ++ tailWord_166102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
