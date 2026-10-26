import V185TrunkScan23Chunk0225

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1336453 : List Nat := [1, 3, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_1336453 : Nat := 118140960795 + 1336453 * 2 ^ 59
def prefixEnd_1336453 : Nat := 4983230072969 + 3 ^ 40 * 1336453 * 2
def baseEnd_1336453 : Nat := 228747587047788285063757

theorem tailTrace_1336453 : CollatzResearch.WordTrace tailWord_1336453 prefixEnd_1336453 228747587047788285063757 := by
  unfold tailWord_1336453
  simp only [CollatzResearch.WordTrace]
  refine ⟨48744445427266503845758013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32496296951511002563838675 48744445427266503845758013)
  ·
    refine ⟨18279167035224938942159255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48744445427266503845758013 18279167035224938942159255)
    ·
      refine ⟨27418750552837408413238883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18279167035224938942159255 27418750552837408413238883)
      ·
        refine ⟨41128125829256112619858325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27418750552837408413238883 41128125829256112619858325)
        ·
          refine ⟨1927880898246380279055859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41128125829256112619858325 1927880898246380279055859)
          ·
            refine ⟨2891821347369570418583789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927880898246380279055859 2891821347369570418583789)
            ·
              refine ⟨1084433005263588906968921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2891821347369570418583789 1084433005263588906968921)
              ·
                refine ⟨813324753947691680226691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084433005263588906968921 813324753947691680226691)
                ·
                  refine ⟨1219987130921537520340037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813324753947691680226691 1219987130921537520340037)
                  ·
                    refine ⟨228747587047788285063757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1219987130921537520340037 228747587047788285063757)
                    ·
                      rfl

theorem cell23_1336453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_1336453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336453 prefixEnd_1336453 := by exact prefixLift 1336453
  have htrace : WordTrace (prefixWord ++ tailWord_1336453) baseStart_1336453 baseEnd_1336453 := by
    simpa [prefixWord, tailWord_1336453, baseEnd_1336453] using wordTrace_append hprefix tailTrace_1336453
  have hstable : (prefixWord ++ tailWord_1336453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336453).length < 2 ^ (prefixWord ++ tailWord_1336453).sum := by decide
  have hdescent : baseEnd_1336453 < baseStart_1336453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336455 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1336455 : Nat := 118140960795 + 1336455 * 2 ^ 59
def prefixEnd_1336455 : Nat := 4983230072969 + 3 ^ 40 * 1336455 * 2
def baseEnd_1336455 : Nat := 686243788104673847366261

theorem tailTrace_1336455 : CollatzResearch.WordTrace tailWord_1336455 prefixEnd_1336455 686243788104673847366261 := by
  unfold tailWord_1336455
  simp only [CollatzResearch.WordTrace]
  refine ⟨48744518373259258187330819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32496345582172838791553879 48744518373259258187330819)
  ·
    refine ⟨73116777559888887280996229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48744518373259258187330819 73116777559888887280996229)
    ·
      refine ⟨13709395792479166365186793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73116777559888887280996229 13709395792479166365186793)
      ·
        refine ⟨10282046844359374773890095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13709395792479166365186793 10282046844359374773890095)
        ·
          refine ⟨15423070266539062160835143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10282046844359374773890095 15423070266539062160835143)
          ·
            refine ⟨23134605399808593241252715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15423070266539062160835143 23134605399808593241252715)
            ·
              refine ⟨34701908099712889861879073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23134605399808593241252715 34701908099712889861879073)
              ·
                refine ⟨26026431074784667396409305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34701908099712889861879073 26026431074784667396409305)
                ·
                  refine ⟨19519823306088500547306979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26026431074784667396409305 19519823306088500547306979)
                  ·
                    refine ⟨29279734959132750820960469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19519823306088500547306979 29279734959132750820960469)
                    ·
                      refine ⟨686243788104673847366261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29279734959132750820960469 686243788104673847366261)
                      ·
                        rfl

theorem cell23_1336455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1336455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336455 prefixEnd_1336455 := by exact prefixLift 1336455
  have htrace : WordTrace (prefixWord ++ tailWord_1336455) baseStart_1336455 baseEnd_1336455 := by
    simpa [prefixWord, tailWord_1336455, baseEnd_1336455] using wordTrace_append hprefix tailTrace_1336455
  have hstable : (prefixWord ++ tailWord_1336455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336455).length < 2 ^ (prefixWord ++ tailWord_1336455).sum := by decide
  have hdescent : baseEnd_1336455 < baseStart_1336455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336466 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 6]
def baseStart_1336466 : Nat := 118140960795 + 1336466 * 2 ^ 59
def prefixEnd_1336466 : Nat := 4983230072969 + 3 ^ 40 * 1336466 * 2
def baseEnd_1336466 : Nat := 76249937376874811592079

theorem tailTrace_1336466 : CollatzResearch.WordTrace tailWord_1336466 prefixEnd_1336466 76249937376874811592079 := by
  unfold tailWord_1336466
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186229894054851766495313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32496613050812938043987501 12186229894054851766495313)
  ·
    refine ⟨9139672420541138824871485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12186229894054851766495313 9139672420541138824871485)
    ·
      refine ⟨3427377157702927059326807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9139672420541138824871485 3427377157702927059326807)
      ·
        refine ⟨5141065736554390588990211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427377157702927059326807 5141065736554390588990211)
        ·
          refine ⟨7711598604831585883485317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5141065736554390588990211 7711598604831585883485317)
          ·
            refine ⟨1445924738405922353153497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7711598604831585883485317 1445924738405922353153497)
            ·
              refine ⟨1084443553804441764865123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445924738405922353153497 1084443553804441764865123)
              ·
                refine ⟨1626665330706662647297685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084443553804441764865123 1626665330706662647297685)
                ·
                  refine ⟨76249937376874811592079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1626665330706662647297685 76249937376874811592079)
                  ·
                    rfl

theorem cell23_1336466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_1336466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336466 prefixEnd_1336466 := by exact prefixLift 1336466
  have htrace : WordTrace (prefixWord ++ tailWord_1336466) baseStart_1336466 baseEnd_1336466 := by
    simpa [prefixWord, tailWord_1336466, baseEnd_1336466] using wordTrace_append hprefix tailTrace_1336466
  have hstable : (prefixWord ++ tailWord_1336466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336466).length < 2 ^ (prefixWord ++ tailWord_1336466).sum := by decide
  have hdescent : baseEnd_1336466 < baseStart_1336466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336479 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 3, 5]
def baseStart_1336479 : Nat := 118140960795 + 1336479 * 2 ^ 59
def prefixEnd_1336479 : Nat := 4983230072969 + 3 ^ 40 * 1336479 * 2
def baseEnd_1336479 : Nat := 228752037213460584488717

theorem tailTrace_1336479 : CollatzResearch.WordTrace tailWord_1336479 prefixEnd_1336479 228752037213460584488717 := by
  unfold tailWord_1336479
  simp only [CollatzResearch.WordTrace]
  refine ⟨48745393725172310286204491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32496929150114873524136327 48745393725172310286204491)
  ·
    refine ⟨73118090587758465429306737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48745393725172310286204491 73118090587758465429306737)
    ·
      refine ⟨54838567940818849071980053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73118090587758465429306737 54838567940818849071980053)
      ·
        refine ⟨2570557872225883550249065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54838567940818849071980053 2570557872225883550249065)
        ·
          refine ⟨1927918404169412662686799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2570557872225883550249065 1927918404169412662686799)
          ·
            refine ⟨2891877606254118994030199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927918404169412662686799 2891877606254118994030199)
            ·
              refine ⟨4337816409381178491045299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891877606254118994030199 4337816409381178491045299)
              ·
                refine ⟨6506724614071767736567949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337816409381178491045299 6506724614071767736567949)
                ·
                  refine ⟨2440021730276912901212981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6506724614071767736567949 2440021730276912901212981)
                  ·
                    refine ⟨228752037213460584488717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2440021730276912901212981 228752037213460584488717)
                    ·
                      rfl

theorem cell23_1336479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_1336479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336479 prefixEnd_1336479 := by exact prefixLift 1336479
  have htrace : WordTrace (prefixWord ++ tailWord_1336479) baseStart_1336479 baseEnd_1336479 := by
    simpa [prefixWord, tailWord_1336479, baseEnd_1336479] using wordTrace_append hprefix tailTrace_1336479
  have hstable : (prefixWord ++ tailWord_1336479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336479).length < 2 ^ (prefixWord ++ tailWord_1336479).sum := by decide
  have hdescent : baseEnd_1336479 < baseStart_1336479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336492 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_1336492 : Nat := 118140960795 + 1336492 * 2 ^ 59
def prefixEnd_1336492 : Nat := 4983230072969 + 3 ^ 40 * 1336492 * 2
def baseEnd_1336492 : Nat := 228754262296296734201197

theorem tailTrace_1336492 : CollatzResearch.WordTrace tailWord_1336492 prefixEnd_1336492 228754262296296734201197 := by
  unfold tailWord_1336492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24372933937062606753213865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32497245249416809004285153 24372933937062606753213865)
  ·
    refine ⟨18279700452796955064910399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24372933937062606753213865 18279700452796955064910399)
    ·
      refine ⟨27419550679195432597365599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18279700452796955064910399 27419550679195432597365599)
      ·
        refine ⟨41129326018793148896048399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27419550679195432597365599 41129326018793148896048399)
        ·
          refine ⟨61693989028189723344072599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41129326018793148896048399 61693989028189723344072599)
          ·
            refine ⟨92540983542284585016108899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61693989028189723344072599 92540983542284585016108899)
            ·
              refine ⟨138811475313426877524163349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92540983542284585016108899 138811475313426877524163349)
              ·
                refine ⟨6506787905316884883945157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138811475313426877524163349 6506787905316884883945157)
                ·
                  refine ⟨1220022732246915915739717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6506787905316884883945157 1220022732246915915739717)
                  ·
                    refine ⟨228754262296296734201197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220022732246915915739717 228754262296296734201197)
                    ·
                      rfl

theorem cell23_1336492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_1336492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336492 prefixEnd_1336492 := by exact prefixLift 1336492
  have htrace : WordTrace (prefixWord ++ tailWord_1336492) baseStart_1336492 baseEnd_1336492 := by
    simpa [prefixWord, tailWord_1336492, baseEnd_1336492] using wordTrace_append hprefix tailTrace_1336492
  have hstable : (prefixWord ++ tailWord_1336492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336492).length < 2 ^ (prefixWord ++ tailWord_1336492).sum := by decide
  have hdescent : baseEnd_1336492 < baseStart_1336492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336505 : List Nat := [1, 2, 1, 4, 1, 14]
def baseStart_1336505 : Nat := 118140960795 + 1336505 * 2 ^ 59
def prefixEnd_1336505 : Nat := 4983230072969 + 3 ^ 40 * 1336505 * 2
def baseEnd_1336505 : Nat := 2824154165174480048317

theorem tailTrace_1336505 : CollatzResearch.WordTrace tailWord_1336505 prefixEnd_1336505 2824154165174480048317 := by
  unfold tailWord_1336505
  simp only [CollatzResearch.WordTrace]
  refine ⟨48746342023078116726650969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32497561348718744484433979 48746342023078116726650969)
  ·
    refine ⟨36559756517308587544988227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48746342023078116726650969 36559756517308587544988227)
    ·
      refine ⟨54839634775962881317482341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36559756517308587544988227 54839634775962881317482341)
      ·
        refine ⟨10282431520493040247027939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54839634775962881317482341 10282431520493040247027939)
        ·
          refine ⟨15423647280739560370541909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10282431520493040247027939 15423647280739560370541909)
          ·
            refine ⟨2824154165174480048317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 15423647280739560370541909 2824154165174480048317)
            ·
              rfl

theorem cell23_1336505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 14].length) (baseStart_1336505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336505 prefixEnd_1336505 := by exact prefixLift 1336505
  have htrace : WordTrace (prefixWord ++ tailWord_1336505) baseStart_1336505 baseEnd_1336505 := by
    simpa [prefixWord, tailWord_1336505, baseEnd_1336505] using wordTrace_append hprefix tailTrace_1336505
  have hstable : (prefixWord ++ tailWord_1336505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336505).length < 2 ^ (prefixWord ++ tailWord_1336505).sum := by decide
  have hdescent : baseEnd_1336505 < baseStart_1336505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336509 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1336509 : Nat := 118140960795 + 1336509 * 2 ^ 59
def prefixEnd_1336509 : Nat := 4983230072969 + 3 ^ 40 * 1336509 * 2
def baseEnd_1336509 : Nat := 228757172020005545363671

theorem tailTrace_1336509 : CollatzResearch.WordTrace tailWord_1336509 prefixEnd_1336509 228757172020005545363671 := by
  unfold tailWord_1336509
  simp only [CollatzResearch.WordTrace]
  refine ⟨48746487915063625409796581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32497658610042416939864387 48746487915063625409796581)
  ·
    refine ⟨9139966484074429764336859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48746487915063625409796581 9139966484074429764336859)
    ·
      refine ⟨13709949726111644646505289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9139966484074429764336859 13709949726111644646505289)
      ·
        refine ⟨10282462294583733484878967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13709949726111644646505289 10282462294583733484878967)
        ·
          refine ⟨15423693441875600227318451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10282462294583733484878967 15423693441875600227318451)
          ·
            refine ⟨23135540162813400340977677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15423693441875600227318451 23135540162813400340977677)
            ·
              refine ⟨8675827561055025127866629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23135540162813400340977677 8675827561055025127866629)
              ·
                refine ⟨1626717667697817211474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8675827561055025127866629 1626717667697817211474993)
                ·
                  refine ⟨1220038250773362908606245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1626717667697817211474993 1220038250773362908606245)
                  ·
                    refine ⟨228757172020005545363671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220038250773362908606245 228757172020005545363671)
                    ·
                      rfl

theorem cell23_1336509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1336509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336509 prefixEnd_1336509 := by exact prefixLift 1336509
  have htrace : WordTrace (prefixWord ++ tailWord_1336509) baseStart_1336509 baseEnd_1336509 := by
    simpa [prefixWord, tailWord_1336509, baseEnd_1336509] using wordTrace_append hprefix tailTrace_1336509
  have hstable : (prefixWord ++ tailWord_1336509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336509).length < 2 ^ (prefixWord ++ tailWord_1336509).sum := by decide
  have hdescent : baseEnd_1336509 < baseStart_1336509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336510 : List Nat := [4, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_1336510 : Nat := 118140960795 + 1336510 * 2 ^ 59
def prefixEnd_1336510 : Nat := 4983230072969 + 3 ^ 40 * 1336510 * 2
def baseEnd_1336510 : Nat := 686272029540671132178509

theorem tailTrace_1336510 : CollatzResearch.WordTrace tailWord_1336510 prefixEnd_1336510 686272029540671132178509 := by
  unfold tailWord_1336510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6093315548507500322572873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32497682925373335053721989 6093315548507500322572873)
  ·
    refine ⟨4569986661380625241929655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6093315548507500322572873 4569986661380625241929655)
    ·
      refine ⟨6854979992070937862894483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4569986661380625241929655 6854979992070937862894483)
      ·
        refine ⟨10282469988106406794341725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854979992070937862894483 10282469988106406794341725)
        ·
          refine ⟨3855926245539902547878147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10282469988106406794341725 3855926245539902547878147)
          ·
            refine ⟨5783889368309853821817221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855926245539902547878147 5783889368309853821817221)
            ·
              refine ⟨1084479256558097591590729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5783889368309853821817221 1084479256558097591590729)
              ·
                refine ⟨813359442418573193693047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084479256558097591590729 813359442418573193693047)
                ·
                  refine ⟨1220039163627859790539571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813359442418573193693047 1220039163627859790539571)
                  ·
                    refine ⟨1830058745441789685809357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220039163627859790539571 1830058745441789685809357)
                    ·
                      refine ⟨686272029540671132178509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1830058745441789685809357 686272029540671132178509)
                      ·
                        rfl

theorem cell23_1336510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_1336510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336510 prefixEnd_1336510 := by exact prefixLift 1336510
  have htrace : WordTrace (prefixWord ++ tailWord_1336510) baseStart_1336510 baseEnd_1336510 := by
    simpa [prefixWord, tailWord_1336510, baseEnd_1336510] using wordTrace_append hprefix tailTrace_1336510
  have hstable : (prefixWord ++ tailWord_1336510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336510).length < 2 ^ (prefixWord ++ tailWord_1336510).sum := by decide
  have hdescent : baseEnd_1336510 < baseStart_1336510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336515 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1336515 : Nat := 118140960795 + 1336515 * 2 ^ 59
def prefixEnd_1336515 : Nat := 4983230072969 + 3 ^ 40 * 1336515 * 2
def baseEnd_1336515 : Nat := 686274596943943612615985

theorem tailTrace_1336515 : CollatzResearch.WordTrace tailWord_1336515 prefixEnd_1336515 686274596943943612615985 := by
  unfold tailWord_1336515
  simp only [CollatzResearch.WordTrace]
  refine ⟨48746706753041888434514999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32497804502027925623009999 48746706753041888434514999)
  ·
    refine ⟨73120060129562832651772499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48746706753041888434514999 73120060129562832651772499)
    ·
      refine ⟨109680090194344248977658749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73120060129562832651772499 109680090194344248977658749)
      ·
        refine ⟨41130033822879093366622031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109680090194344248977658749 41130033822879093366622031)
        ·
          refine ⟨61695050734318640049933047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41130033822879093366622031 61695050734318640049933047)
          ·
            refine ⟨92542576101477960074899571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61695050734318640049933047 92542576101477960074899571)
            ·
              refine ⟨138813864152216940112349357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92542576101477960074899571 138813864152216940112349357)
              ·
                refine ⟨52055199057081352542131009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138813864152216940112349357 52055199057081352542131009)
                ·
                  refine ⟨39041399292811014406598257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52055199057081352542131009 39041399292811014406598257)
                  ·
                    refine ⟨29281049469608260804948693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39041399292811014406598257 29281049469608260804948693)
                    ·
                      refine ⟨686274596943943612615985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29281049469608260804948693 686274596943943612615985)
                      ·
                        rfl

theorem cell23_1336515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1336515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336515 prefixEnd_1336515 := by exact prefixLift 1336515
  have htrace : WordTrace (prefixWord ++ tailWord_1336515) baseStart_1336515 baseEnd_1336515 := by
    simpa [prefixWord, tailWord_1336515, baseEnd_1336515] using wordTrace_append hprefix tailTrace_1336515
  have hstable : (prefixWord ++ tailWord_1336515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336515).length < 2 ^ (prefixWord ++ tailWord_1336515).sum := by decide
  have hdescent : baseEnd_1336515 < baseStart_1336515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336522 : List Nat := [3, 1, 2, 1, 3, 2, 3, 8]
def baseStart_1336522 : Nat := 118140960795 + 1336522 * 2 ^ 59
def prefixEnd_1336522 : Nat := 4983230072969 + 3 ^ 40 * 1336522 * 2
def baseEnd_1336522 : Nat := 25417710789204632786239

theorem tailTrace_1336522 : CollatzResearch.WordTrace tailWord_1336522 prefixEnd_1336522 25417710789204632786239 := by
  unfold tailWord_1336522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186740516004132157504955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32497974709344352420013213 12186740516004132157504955)
  ·
    refine ⟨18280110774006198236257433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12186740516004132157504955 18280110774006198236257433)
    ·
      refine ⟨13710083080504648677193075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18280110774006198236257433 13710083080504648677193075)
      ·
        refine ⟨20565124620756973015789613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13710083080504648677193075 20565124620756973015789613)
        ·
          refine ⟨7711921732783864880921105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20565124620756973015789613 7711921732783864880921105)
          ·
            refine ⟨5783941299587898660690829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711921732783864880921105 5783941299587898660690829)
            ·
              refine ⟨2168977987345461997759061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5783941299587898660690829 2168977987345461997759061)
              ·
                refine ⟨25417710789204632786239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2168977987345461997759061 25417710789204632786239)
                ·
                  rfl

theorem cell23_1336522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_1336522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336522 prefixEnd_1336522 := by exact prefixLift 1336522
  have htrace : WordTrace (prefixWord ++ tailWord_1336522) baseStart_1336522 baseEnd_1336522 := by
    simpa [prefixWord, tailWord_1336522, baseEnd_1336522] using wordTrace_append hprefix tailTrace_1336522
  have hstable : (prefixWord ++ tailWord_1336522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336522).length < 2 ^ (prefixWord ++ tailWord_1336522).sum := by decide
  have hdescent : baseEnd_1336522 < baseStart_1336522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336533 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1336533 : Nat := 118140960795 + 1336533 * 2 ^ 59
def prefixEnd_1336533 : Nat := 4983230072969 + 3 ^ 40 * 1336533 * 2
def baseEnd_1336533 : Nat := 686283839595724542190903

theorem tailTrace_1336533 : CollatzResearch.WordTrace tailWord_1336533 prefixEnd_1336533 686283839595724542190903 := by
  unfold tailWord_1336533
  simp only [CollatzResearch.WordTrace]
  refine ⟨48747363266976677508670253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32498242177984451672446835 48747363266976677508670253)
  ·
    refine ⟨18280261225116254065751345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48747363266976677508670253 18280261225116254065751345)
    ·
      refine ⟨13710195918837190549313509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18280261225116254065751345 13710195918837190549313509)
      ·
        refine ⟨2570661734781973227996283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13710195918837190549313509 2570661734781973227996283)
        ·
          refine ⟨3855992602172959841994425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570661734781973227996283 3855992602172959841994425)
          ·
            refine ⟨2891994451629719881495819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855992602172959841994425 2891994451629719881495819)
            ·
              refine ⟨4337991677444579822243729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891994451629719881495819 4337991677444579822243729)
              ·
                refine ⟨3253493758083434866682797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4337991677444579822243729 3253493758083434866682797)
                ·
                  refine ⟨1220060159281288075006049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3253493758083434866682797 1220060159281288075006049)
                  ·
                    refine ⟨915045119460966056254537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1220060159281288075006049 915045119460966056254537)
                    ·
                      refine ⟨686283839595724542190903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915045119460966056254537 686283839595724542190903)
                      ·
                        rfl

theorem cell23_1336533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1336533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336533 prefixEnd_1336533 := by exact prefixLift 1336533
  have htrace : WordTrace (prefixWord ++ tailWord_1336533) baseStart_1336533 baseEnd_1336533 := by
    simpa [prefixWord, tailWord_1336533, baseEnd_1336533] using wordTrace_append hprefix tailTrace_1336533
  have hstable : (prefixWord ++ tailWord_1336533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336533).length < 2 ^ (prefixWord ++ tailWord_1336533).sum := by decide
  have hdescent : baseEnd_1336533 < baseStart_1336533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336592 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3]
def baseStart_1336592 : Nat := 118140960795 + 1336592 * 2 ^ 59
def prefixEnd_1336592 : Nat := 4983230072969 + 3 ^ 40 * 1336592 * 2
def baseEnd_1336592 : Nat := 686314134954339811353131

theorem tailTrace_1336592 : CollatzResearch.WordTrace tailWord_1336592 prefixEnd_1336592 686314134954339811353131 := by
  unfold tailWord_1336592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24374757586881465292534015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32499676782508620390045353 24374757586881465292534015)
  ·
    refine ⟨36562136380322197938801023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24374757586881465292534015 36562136380322197938801023)
    ·
      refine ⟨54843204570483296908201535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36562136380322197938801023 54843204570483296908201535)
      ·
        refine ⟨82264806855724945362302303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54843204570483296908201535 82264806855724945362302303)
        ·
          refine ⟨123397210283587418043453455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82264806855724945362302303 123397210283587418043453455)
          ·
            refine ⟨185095815425381127065180183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123397210283587418043453455 185095815425381127065180183)
            ·
              refine ⟨277643723138071690597770275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185095815425381127065180183 277643723138071690597770275)
              ·
                refine ⟨416465584707107535896655413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277643723138071690597770275 416465584707107535896655413)
                ·
                  refine ⟨39043648566291331490311445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416465584707107535896655413 39043648566291331490311445)
                  ·
                    refine ⟨1830171026544906163608349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39043648566291331490311445 1830171026544906163608349)
                    ·
                      refine ⟨686314134954339811353131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1830171026544906163608349 686314134954339811353131)
                      ·
                        rfl

theorem cell23_1336592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_1336592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336592 prefixEnd_1336592 := by exact prefixLift 1336592
  have htrace : WordTrace (prefixWord ++ tailWord_1336592) baseStart_1336592 baseEnd_1336592 := by
    simpa [prefixWord, tailWord_1336592, baseEnd_1336592] using wordTrace_append hprefix tailTrace_1336592
  have hstable : (prefixWord ++ tailWord_1336592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336592).length < 2 ^ (prefixWord ++ tailWord_1336592).sum := by decide
  have hdescent : baseEnd_1336592 < baseStart_1336592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336629 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 7]
def baseStart_1336629 : Nat := 118140960795 + 1336629 * 2 ^ 59
def prefixEnd_1336629 : Nat := 4983230072969 + 3 ^ 40 * 1336629 * 2
def baseEnd_1336629 : Nat := 76259237082061796287829

theorem tailTrace_1336629 : CollatzResearch.WordTrace tailWord_1336629 prefixEnd_1336629 76259237082061796287829 := by
  unfold tailWord_1336629
  simp only [CollatzResearch.WordTrace]
  refine ⟨48750864674628885904164941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32500576449752590602776627 48750864674628885904164941)
  ·
    refine ⟨18281574252985832214061853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48750864674628885904164941 18281574252985832214061853)
    ·
      refine ⟨6855590344869687080273195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18281574252985832214061853 6855590344869687080273195)
      ·
        refine ⟨10283385517304530620409793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6855590344869687080273195 10283385517304530620409793)
        ·
          refine ⟨7712539137978397965307345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10283385517304530620409793 7712539137978397965307345)
          ·
            refine ⟨5784404353483798473980509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7712539137978397965307345 5784404353483798473980509)
            ·
              refine ⟨2169151632556424427742691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5784404353483798473980509 2169151632556424427742691)
              ·
                refine ⟨3253727448834636641614037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169151632556424427742691 3253727448834636641614037)
                ·
                  refine ⟨76259237082061796287829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3253727448834636641614037 76259237082061796287829)
                  ·
                    rfl

theorem cell23_1336629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_1336629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336629 prefixEnd_1336629 := by exact prefixLift 1336629
  have htrace : WordTrace (prefixWord ++ tailWord_1336629) baseStart_1336629 baseEnd_1336629 := by
    simpa [prefixWord, tailWord_1336629, baseEnd_1336629] using wordTrace_append hprefix tailTrace_1336629
  have hstable : (prefixWord ++ tailWord_1336629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336629).length < 2 ^ (prefixWord ++ tailWord_1336629).sum := by decide
  have hdescent : baseEnd_1336629 < baseStart_1336629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336659 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 2, 5]
def baseStart_1336659 : Nat := 118140960795 + 1336659 * 2 ^ 59
def prefixEnd_1336659 : Nat := 4983230072969 + 3 ^ 40 * 1336659 * 2
def baseEnd_1336659 : Nat := 228782846052730349738441

theorem tailTrace_1336659 : CollatzResearch.WordTrace tailWord_1336659 prefixEnd_1336659 228782846052730349738441 := by
  unfold tailWord_1336659
  simp only [CollatzResearch.WordTrace]
  refine ⟨48751958864520201027757031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32501305909680134018504687 48751958864520201027757031)
  ·
    refine ⟨73127938296780301541635547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48751958864520201027757031 73127938296780301541635547)
    ·
      refine ⟨109691907445170452312453321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73127938296780301541635547 109691907445170452312453321)
      ·
        refine ⟨82268930583877839234339991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109691907445170452312453321 82268930583877839234339991)
        ·
          refine ⟨123403395875816758851509987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82268930583877839234339991 123403395875816758851509987)
          ·
            refine ⟨185105093813725138277264981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123403395875816758851509987 185105093813725138277264981)
            ·
              refine ⟨2169200318129591464186699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 185105093813725138277264981 2169200318129591464186699)
              ·
                refine ⟨3253800477194387196280049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169200318129591464186699 3253800477194387196280049)
                ·
                  refine ⟨2440350357895790397210037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253800477194387196280049 2440350357895790397210037)
                  ·
                    refine ⟨228782846052730349738441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2440350357895790397210037 228782846052730349738441)
                    ·
                      rfl

theorem cell23_1336659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 5].length) (baseStart_1336659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336659 prefixEnd_1336659 := by exact prefixLift 1336659
  have htrace : WordTrace (prefixWord ++ tailWord_1336659) baseStart_1336659 baseEnd_1336659 := by
    simpa [prefixWord, tailWord_1336659, baseEnd_1336659] using wordTrace_append hprefix tailTrace_1336659
  have hstable : (prefixWord ++ tailWord_1336659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336659).length < 2 ^ (prefixWord ++ tailWord_1336659).sum := by decide
  have hdescent : baseEnd_1336659 < baseStart_1336659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336680 : List Nat := [2, 1, 4, 2, 3, 2, 2, 2, 5]
def baseStart_1336680 : Nat := 118140960795 + 1336680 * 2 ^ 59
def prefixEnd_1336680 : Nat := 4983230072969 + 3 ^ 40 * 1336680 * 2
def baseEnd_1336680 : Nat := 76262146805770607450303

theorem tailTrace_1336680 : CollatzResearch.WordTrace tailWord_1336680 prefixEnd_1336680 76262146805770607450303 := by
  unfold tailWord_1336680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24376362398722060807135747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32501816531629414409514329 24376362398722060807135747)
  ·
    refine ⟨36564543598083091210703621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24376362398722060807135747 36564543598083091210703621)
    ·
      refine ⟨6855851924640579602006929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36564543598083091210703621 6855851924640579602006929)
      ·
        refine ⟨5141888943480434701505197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6855851924640579602006929 5141888943480434701505197)
        ·
          refine ⟨1928208353805163013064449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5141888943480434701505197 1928208353805163013064449)
          ·
            refine ⟨1446156265353872259798337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928208353805163013064449 1446156265353872259798337)
            ·
              refine ⟨1084617199015404194848753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446156265353872259798337 1084617199015404194848753)
              ·
                refine ⟨813462899261553146136565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084617199015404194848753 813462899261553146136565)
                ·
                  refine ⟨76262146805770607450303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 813462899261553146136565 76262146805770607450303)
                  ·
                    rfl

theorem cell23_1336680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 5].length) (baseStart_1336680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336680 prefixEnd_1336680 := by exact prefixLift 1336680
  have htrace : WordTrace (prefixWord ++ tailWord_1336680) baseStart_1336680 baseEnd_1336680 := by
    simpa [prefixWord, tailWord_1336680, baseEnd_1336680] using wordTrace_append hprefix tailTrace_1336680
  have hstable : (prefixWord ++ tailWord_1336680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336680).length < 2 ^ (prefixWord ++ tailWord_1336680).sum := by decide
  have hdescent : baseEnd_1336680 < baseStart_1336680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336699 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 3]
def baseStart_1336699 : Nat := 118140960795 + 1336699 * 2 ^ 59
def prefixEnd_1336699 : Nat := 4983230072969 + 3 ^ 40 * 1336699 * 2
def baseEnd_1336699 : Nat := 686369077384370892715139

theorem tailTrace_1336699 : CollatzResearch.WordTrace tailWord_1336699 prefixEnd_1336699 686369077384370892715139 := by
  unfold tailWord_1336699
  simp only [CollatzResearch.WordTrace]
  refine ⟨48753417784375287859213151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32502278522916858572808767 48753417784375287859213151)
  ·
    refine ⟨73130126676562931788819727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48753417784375287859213151 73130126676562931788819727)
    ·
      refine ⟨109695190014844397683229591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73130126676562931788819727 109695190014844397683229591)
      ·
        refine ⟨164542785022266596524844387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109695190014844397683229591 164542785022266596524844387)
        ·
          refine ⟨246814177533399894787266581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164542785022266596524844387 246814177533399894787266581)
          ·
            refine ⟨11569414571878120068153121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 246814177533399894787266581 11569414571878120068153121)
            ·
              refine ⟨8677060928908590051114841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11569414571878120068153121 8677060928908590051114841)
              ·
                refine ⟨6507795696681442538336131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8677060928908590051114841 6507795696681442538336131)
                ·
                  refine ⟨9761693545022163807504197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6507795696681442538336131 9761693545022163807504197)
                  ·
                    refine ⟨1830317539691655713907037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9761693545022163807504197 1830317539691655713907037)
                    ·
                      refine ⟨686369077384370892715139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1830317539691655713907037 686369077384370892715139)
                      ·
                        rfl

theorem cell23_1336699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 3].length) (baseStart_1336699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336699 prefixEnd_1336699 := by exact prefixLift 1336699
  have htrace : WordTrace (prefixWord ++ tailWord_1336699) baseStart_1336699 baseEnd_1336699 := by
    simpa [prefixWord, tailWord_1336699, baseEnd_1336699] using wordTrace_append hprefix tailTrace_1336699
  have hstable : (prefixWord ++ tailWord_1336699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336699).length < 2 ^ (prefixWord ++ tailWord_1336699).sum := by decide
  have hdescent : baseEnd_1336699 < baseStart_1336699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336713 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 4]
def baseStart_1336713 : Nat := 118140960795 + 1336713 * 2 ^ 59
def prefixEnd_1336713 : Nat := 4983230072969 + 3 ^ 40 * 1336713 * 2
def baseEnd_1336713 : Nat := 686376266113533837940075

theorem tailTrace_1336713 : CollatzResearch.WordTrace tailWord_1336713 prefixEnd_1336713 686376266113533837940075 := by
  unfold tailWord_1336713
  simp only [CollatzResearch.WordTrace]
  refine ⟨48753928406324568250222793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32502618937549712166815195 48753928406324568250222793)
  ·
    refine ⟨36565446304743426187667095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48753928406324568250222793 36565446304743426187667095)
    ·
      refine ⟨54848169457115139281500643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36565446304743426187667095 54848169457115139281500643)
      ·
        refine ⟨82272254185672708922250965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54848169457115139281500643 82272254185672708922250965)
        ·
          refine ⟨1928255957476704115365257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82272254185672708922250965 1928255957476704115365257)
          ·
            refine ⟨1446191968107528086523943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928255957476704115365257 1446191968107528086523943)
            ·
              refine ⟨2169287952161292129785915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446191968107528086523943 2169287952161292129785915)
              ·
                refine ⟨3253931928241938194678873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169287952161292129785915 3253931928241938194678873)
                ·
                  refine ⟨2440448946181453646009155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3253931928241938194678873 2440448946181453646009155)
                  ·
                    refine ⟨3660673419272180469013733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2440448946181453646009155 3660673419272180469013733)
                    ·
                      refine ⟨686376266113533837940075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3660673419272180469013733 686376266113533837940075)
                      ·
                        rfl

theorem cell23_1336713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_1336713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336713 prefixEnd_1336713 := by exact prefixLift 1336713
  have htrace : WordTrace (prefixWord ++ tailWord_1336713) baseStart_1336713 baseEnd_1336713 := by
    simpa [prefixWord, tailWord_1336713, baseEnd_1336713] using wordTrace_append hprefix tailTrace_1336713
  have hstable : (prefixWord ++ tailWord_1336713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336713).length < 2 ^ (prefixWord ++ tailWord_1336713).sum := by decide
  have hdescent : baseEnd_1336713 < baseStart_1336713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336779 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 1, 6]
def baseStart_1336779 : Nat := 118140960795 + 1336779 * 2 ^ 59
def prefixEnd_1336779 : Nat := 4983230072969 + 3 ^ 40 * 1336779 * 2
def baseEnd_1336779 : Nat := 228803385278910193238257

theorem tailTrace_1336779 : CollatzResearch.WordTrace tailWord_1336779 prefixEnd_1336779 228803385278910193238257 := by
  unfold tailWord_1336779
  simp only [CollatzResearch.WordTrace]
  refine ⟨48756335624085461522125391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32504223749390307681416927 48756335624085461522125391)
  ·
    refine ⟨73134503436128192283188087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48756335624085461522125391 73134503436128192283188087)
    ·
      refine ⟨109701755154192288424782131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73134503436128192283188087 109701755154192288424782131)
      ·
        refine ⟨164552632731288432637173197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109701755154192288424782131 164552632731288432637173197)
        ·
          refine ⟨61707237274233162238939949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164552632731288432637173197 61707237274233162238939949)
          ·
            refine ⟨23140213977837435839602481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61707237274233162238939949 23140213977837435839602481)
            ·
              refine ⟨17355160483378076879701861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23140213977837435839602481 17355160483378076879701861)
              ·
                refine ⟨3254092590633389414944099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17355160483378076879701861 3254092590633389414944099)
                ·
                  refine ⟨4881138885950084122416149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254092590633389414944099 4881138885950084122416149)
                  ·
                    refine ⟨228803385278910193238257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4881138885950084122416149 228803385278910193238257)
                    ·
                      rfl

theorem cell23_1336779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 6].length) (baseStart_1336779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336779 prefixEnd_1336779 := by exact prefixLift 1336779
  have htrace : WordTrace (prefixWord ++ tailWord_1336779) baseStart_1336779 baseEnd_1336779 := by
    simpa [prefixWord, tailWord_1336779, baseEnd_1336779] using wordTrace_append hprefix tailTrace_1336779
  have hstable : (prefixWord ++ tailWord_1336779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336779).length < 2 ^ (prefixWord ++ tailWord_1336779).sum := by decide
  have hdescent : baseEnd_1336779 < baseStart_1336779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336790 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_1336790 : Nat := 118140960795 + 1336790 * 2 ^ 59
def prefixEnd_1336790 : Nat := 4983230072969 + 3 ^ 40 * 1336790 * 2
def baseEnd_1336790 : Nat := 686415804123930036677221

theorem tailTrace_1336790 : CollatzResearch.WordTrace tailWord_1336790 prefixEnd_1336790 686415804123930036677221 := by
  unfold tailWord_1336790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047296051690350650048489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32504491218030406933850549 3047296051690350650048489)
  ·
    refine ⟨2285472038767762987536367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3047296051690350650048489 2285472038767762987536367)
    ·
      refine ⟨3428208058151644481304551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2285472038767762987536367 3428208058151644481304551)
      ·
        refine ⟨5142312087227466721956827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428208058151644481304551 5142312087227466721956827)
        ·
          refine ⟨7713468130841200082935241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142312087227466721956827 7713468130841200082935241)
          ·
            refine ⟨5785101098130900062201431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7713468130841200082935241 5785101098130900062201431)
            ·
              refine ⟨8677651647196350093302147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785101098130900062201431 8677651647196350093302147)
              ·
                refine ⟨13016477470794525139953221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8677651647196350093302147 13016477470794525139953221)
                ·
                  refine ⟨2440589525773973463741229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13016477470794525139953221 2440589525773973463741229)
                  ·
                    refine ⟨915221072165240048902961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440589525773973463741229 915221072165240048902961)
                    ·
                      refine ⟨686415804123930036677221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915221072165240048902961 686415804123930036677221)
                      ·
                        rfl

theorem cell23_1336790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_1336790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336790 prefixEnd_1336790 := by exact prefixLift 1336790
  have htrace : WordTrace (prefixWord ++ tailWord_1336790) baseStart_1336790 baseEnd_1336790 := by
    simpa [prefixWord, tailWord_1336790, baseEnd_1336790] using wordTrace_append hprefix tailTrace_1336790
  have hstable : (prefixWord ++ tailWord_1336790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336790).length < 2 ^ (prefixWord ++ tailWord_1336790).sum := by decide
  have hdescent : baseEnd_1336790 < baseStart_1336790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336799 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1336799 : Nat := 118140960795 + 1336799 * 2 ^ 59
def prefixEnd_1336799 : Nat := 4983230072969 + 3 ^ 40 * 1336799 * 2
def baseEnd_1336799 : Nat := 686420425449820501464679

theorem tailTrace_1336799 : CollatzResearch.WordTrace tailWord_1336799 prefixEnd_1336799 686420425449820501464679 := by
  unfold tailWord_1336799
  simp only [CollatzResearch.WordTrace]
  refine ⟨48757065084013004937853451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32504710056008669958568967 48757065084013004937853451)
  ·
    refine ⟨73135597626019507406780177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48757065084013004937853451 73135597626019507406780177)
    ·
      refine ⟨54851698219514630555085133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73135597626019507406780177 54851698219514630555085133)
      ·
        refine ⟨20569386832317986458156925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54851698219514630555085133 20569386832317986458156925)
        ·
          refine ⟨7713520062119244921808847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20569386832317986458156925 7713520062119244921808847)
          ·
            refine ⟨11570280093178867382713271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713520062119244921808847 11570280093178867382713271)
            ·
              refine ⟨17355420139768301074069907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11570280093178867382713271 17355420139768301074069907)
              ·
                refine ⟨26033130209652451611104861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17355420139768301074069907 26033130209652451611104861)
                ·
                  refine ⟨9762423828619669354164323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26033130209652451611104861 9762423828619669354164323)
                  ·
                    refine ⟨14643635742929504031246485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9762423828619669354164323 14643635742929504031246485)
                    ·
                      refine ⟨686420425449820501464679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14643635742929504031246485 686420425449820501464679)
                      ·
                        rfl

theorem cell23_1336799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1336799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336799 prefixEnd_1336799 := by exact prefixLift 1336799
  have htrace : WordTrace (prefixWord ++ tailWord_1336799) baseStart_1336799 baseEnd_1336799 := by
    simpa [prefixWord, tailWord_1336799, baseEnd_1336799] using wordTrace_append hprefix tailTrace_1336799
  have hstable : (prefixWord ++ tailWord_1336799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336799).length < 2 ^ (prefixWord ++ tailWord_1336799).sum := by decide
  have hdescent : baseEnd_1336799 < baseStart_1336799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336830 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1336830 : Nat := 118140960795 + 1336830 * 2 ^ 59
def prefixEnd_1336830 : Nat := 4983230072969 + 3 ^ 40 * 1336830 * 2
def baseEnd_1336830 : Nat := 228812114450036626725679

theorem tailTrace_1336830 : CollatzResearch.WordTrace tailWord_1336830 prefixEnd_1336830 228812114450036626725679 := by
  unfold tailWord_1336830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094774468362587154028993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32505463831267131488154629 6094774468362587154028993)
  ·
    refine ⟨4571080851271940365521745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6094774468362587154028993 4571080851271940365521745)
    ·
      refine ⟨3428310638453955274141309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4571080851271940365521745 3428310638453955274141309)
      ·
        refine ⟨1285616489420233227802991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3428310638453955274141309 1285616489420233227802991)
        ·
          refine ⟨1928424734130349841704487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285616489420233227802991 1928424734130349841704487)
          ·
            refine ⟨2892637101195524762556731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928424734130349841704487 2892637101195524762556731)
            ·
              refine ⟨4338955651793287143835097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892637101195524762556731 4338955651793287143835097)
              ·
                refine ⟨3254216738844965357876323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4338955651793287143835097 3254216738844965357876323)
                ·
                  refine ⟨4881325108267448036814485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254216738844965357876323 4881325108267448036814485)
                  ·
                    refine ⟨228812114450036626725679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4881325108267448036814485 228812114450036626725679)
                    ·
                      rfl

theorem cell23_1336830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1336830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336830 prefixEnd_1336830 := by exact prefixLift 1336830
  have htrace : WordTrace (prefixWord ++ tailWord_1336830) baseStart_1336830 baseEnd_1336830 := by
    simpa [prefixWord, tailWord_1336830, baseEnd_1336830] using wordTrace_append hprefix tailTrace_1336830
  have hstable : (prefixWord ++ tailWord_1336830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336830).length < 2 ^ (prefixWord ++ tailWord_1336830).sum := by decide
  have hdescent : baseEnd_1336830 < baseStart_1336830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336833 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1336833 : Nat := 118140960795 + 1336833 * 2 ^ 59
def prefixEnd_1336833 : Nat := 4983230072969 + 3 ^ 40 * 1336833 * 2
def baseEnd_1336833 : Nat := 686437883792073368439523

theorem tailTrace_1336833 : CollatzResearch.WordTrace tailWord_1336833 prefixEnd_1336833 686437883792073368439523 := by
  unfold tailWord_1336833
  simp only [CollatzResearch.WordTrace]
  refine ⟨48758305165889828744591153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32505536777259885829727435 48758305165889828744591153)
  ·
    refine ⟨36568728874417371558443365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48758305165889828744591153 36568728874417371558443365)
    ·
      refine ⟨6856636663953257167208131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36568728874417371558443365 6856636663953257167208131)
      ·
        refine ⟨10284954995929885750812197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6856636663953257167208131 10284954995929885750812197)
        ·
          refine ⟨1928429061736853578277287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10284954995929885750812197 1928429061736853578277287)
          ·
            refine ⟨2892643592605280367415931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928429061736853578277287 2892643592605280367415931)
            ·
              refine ⟨4338965388907920551123897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892643592605280367415931 4338965388907920551123897)
              ·
                refine ⟨3254224041680940413342923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4338965388907920551123897 3254224041680940413342923)
                ·
                  refine ⟨4881336062521410620014385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254224041680940413342923 4881336062521410620014385)
                  ·
                    refine ⟨3661002046891057965010789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4881336062521410620014385 3661002046891057965010789)
                    ·
                      refine ⟨686437883792073368439523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3661002046891057965010789 686437883792073368439523)
                      ·
                        rfl

theorem cell23_1336833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1336833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336833 prefixEnd_1336833 := by exact prefixLift 1336833
  have htrace : WordTrace (prefixWord ++ tailWord_1336833) baseStart_1336833 baseEnd_1336833 := by
    simpa [prefixWord, tailWord_1336833, baseEnd_1336833] using wordTrace_append hprefix tailTrace_1336833
  have hstable : (prefixWord ++ tailWord_1336833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336833).length < 2 ^ (prefixWord ++ tailWord_1336833).sum := by decide
  have hdescent : baseEnd_1336833 < baseStart_1336833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336863 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 3, 3, 2]
def baseStart_1336863 : Nat := 118140960795 + 1336863 * 2 ^ 59
def prefixEnd_1336863 : Nat := 4983230072969 + 3 ^ 40 * 1336863 * 2
def baseEnd_1336863 : Nat := 686453288211708251064385

theorem tailTrace_1336863 : CollatzResearch.WordTrace tailWord_1336863 prefixEnd_1336863 686453288211708251064385 := by
  unfold tailWord_1336863
  simp only [CollatzResearch.WordTrace]
  refine ⟨48759399355781143868183243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32506266237187429245455495 48759399355781143868183243)
  ·
    refine ⟨73139099033671715802274865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48759399355781143868183243 73139099033671715802274865)
    ·
      refine ⟨54854324275253786851706149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73139099033671715802274865 54854324275253786851706149)
      ·
        refine ⟨10285185801610085034694903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54854324275253786851706149 10285185801610085034694903)
        ·
          refine ⟨15427778702415127552042355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10285185801610085034694903 15427778702415127552042355)
          ·
            refine ⟨23141668053622691328063533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15427778702415127552042355 23141668053622691328063533)
            ·
              refine ⟨8678125520108509248023825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23141668053622691328063533 8678125520108509248023825)
              ·
                refine ⟨6508594140081381936017869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8678125520108509248023825 6508594140081381936017869)
                ·
                  refine ⟨2440722802530518226006701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6508594140081381936017869 2440722802530518226006701)
                  ·
                    refine ⟨915271050948944334752513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2440722802530518226006701 915271050948944334752513)
                    ·
                      refine ⟨686453288211708251064385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915271050948944334752513 686453288211708251064385)
                      ·
                        rfl

theorem cell23_1336863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_1336863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336863 prefixEnd_1336863 := by exact prefixLift 1336863
  have htrace : WordTrace (prefixWord ++ tailWord_1336863) baseStart_1336863 baseEnd_1336863 := by
    simpa [prefixWord, tailWord_1336863, baseEnd_1336863] using wordTrace_append hprefix tailTrace_1336863
  have hstable : (prefixWord ++ tailWord_1336863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336863).length < 2 ^ (prefixWord ++ tailWord_1336863).sum := by decide
  have hdescent : baseEnd_1336863 < baseStart_1336863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336906 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1336906 : Nat := 118140960795 + 1336906 * 2 ^ 59
def prefixEnd_1336906 : Nat := 4983230072969 + 3 ^ 40 * 1336906 * 2
def baseEnd_1336906 : Nat := 686475367879851582826687

theorem tailTrace_1336906 : CollatzResearch.WordTrace tailWord_1336906 prefixEnd_1336906 686475367879851582826687 := by
  unfold tailWord_1336906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190241923656340552999643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32507311796416908141332381 12190241923656340552999643)
  ·
    refine ⟨18285362885484510829499465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12190241923656340552999643 18285362885484510829499465)
    ·
      refine ⟨13714022164113383122124599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18285362885484510829499465 13714022164113383122124599)
      ·
        refine ⟨20571033246170074683186899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13714022164113383122124599 20571033246170074683186899)
        ·
          refine ⟨30856549869255112024780349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20571033246170074683186899 30856549869255112024780349)
          ·
            refine ⟨11571206200970667009292631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30856549869255112024780349 11571206200970667009292631)
            ·
              refine ⟨17356809301456000513938947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11571206200970667009292631 17356809301456000513938947)
              ·
                refine ⟨26035213952184000770908421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17356809301456000513938947 26035213952184000770908421)
                ·
                  refine ⟨4881602616034500144545329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26035213952184000770908421 4881602616034500144545329)
                  ·
                    refine ⟨3661201962025875108408997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4881602616034500144545329 3661201962025875108408997)
                    ·
                      refine ⟨686475367879851582826687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3661201962025875108408997 686475367879851582826687)
                      ·
                        rfl

theorem cell23_1336906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1336906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336906 prefixEnd_1336906 := by exact prefixLift 1336906
  have htrace : WordTrace (prefixWord ++ tailWord_1336906) baseStart_1336906 baseEnd_1336906 := by
    simpa [prefixWord, tailWord_1336906, baseEnd_1336906] using wordTrace_append hprefix tailTrace_1336906
  have hstable : (prefixWord ++ tailWord_1336906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336906).length < 2 ^ (prefixWord ++ tailWord_1336906).sum := by decide
  have hdescent : baseEnd_1336906 < baseStart_1336906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336956 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1336956 : Nat := 118140960795 + 1336956 * 2 ^ 59
def prefixEnd_1336956 : Nat := 4983230072969 + 3 ^ 40 * 1336956 * 2
def baseEnd_1336956 : Nat := 686501041912576387201457

theorem tailTrace_1336956 : CollatzResearch.WordTrace tailWord_1336956 prefixEnd_1336956 686501041912576387201457 := by
  unfold tailWord_1336956
  simp only [CollatzResearch.WordTrace]
  refine ⟨24381395672222110375659361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32508527562962813834212481 24381395672222110375659361)
  ·
    refine ⟨18286046754166582781744521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24381395672222110375659361 18286046754166582781744521)
    ·
      refine ⟨13714535065624937086308391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18286046754166582781744521 13714535065624937086308391)
      ·
        refine ⟨20571802598437405629462587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13714535065624937086308391 20571802598437405629462587)
        ·
          refine ⟨30857703897656108444193881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20571802598437405629462587 30857703897656108444193881)
          ·
            refine ⟨23143277923242081333145411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30857703897656108444193881 23143277923242081333145411)
            ·
              refine ⟨34714916884863121999718117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23143277923242081333145411 34714916884863121999718117)
              ·
                refine ⟨6509046915911835374947147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34714916884863121999718117 6509046915911835374947147)
                ·
                  refine ⟨9763570373867753062420721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6509046915911835374947147 9763570373867753062420721)
                  ·
                    refine ⟨7322677780400814796815541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9763570373867753062420721 7322677780400814796815541)
                    ·
                      refine ⟨686501041912576387201457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7322677780400814796815541 686501041912576387201457)
                      ·
                        rfl

theorem cell23_1336956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1336956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336956 prefixEnd_1336956 := by exact prefixLift 1336956
  have htrace : WordTrace (prefixWord ++ tailWord_1336956) baseStart_1336956 baseEnd_1336956 := by
    simpa [prefixWord, tailWord_1336956, baseEnd_1336956] using wordTrace_append hprefix tailTrace_1336956
  have hstable : (prefixWord ++ tailWord_1336956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336956).length < 2 ^ (prefixWord ++ tailWord_1336956).sum := by decide
  have hdescent : baseEnd_1336956 < baseStart_1336956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336978 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_1336978 : Nat := 118140960795 + 1336978 * 2 ^ 59
def prefixEnd_1336978 : Nat := 4983230072969 + 3 ^ 40 * 1336978 * 2
def baseEnd_1336978 : Nat := 686512338486975301126357

theorem tailTrace_1336978 : CollatzResearch.WordTrace tailWord_1336978 prefixEnd_1336978 686512338486975301126357 := by
  unfold tailWord_1336978
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190898437591129627154897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32509062500243012339079725 12190898437591129627154897)
  ·
    refine ⟨9143173828193347220366173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12190898437591129627154897 9143173828193347220366173)
    ·
      refine ⟨3428690185572505207637315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9143173828193347220366173 3428690185572505207637315)
      ·
        refine ⟨5143035278358757811455973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428690185572505207637315 5143035278358757811455973)
        ·
          refine ⟨964319114692267089647995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5143035278358757811455973 964319114692267089647995)
          ·
            refine ⟨1446478672038400634471993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964319114692267089647995 1446478672038400634471993)
            ·
              refine ⟨1084859004028800475853995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446478672038400634471993 1084859004028800475853995)
              ·
                refine ⟨1627288506043200713780993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084859004028800475853995 1627288506043200713780993)
                ·
                  refine ⟨1220466379532400535335745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1627288506043200713780993 1220466379532400535335745)
                  ·
                    refine ⟨915349784649300401501809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1220466379532400535335745 915349784649300401501809)
                    ·
                      refine ⟨686512338486975301126357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915349784649300401501809 686512338486975301126357)
                      ·
                        rfl

theorem cell23_1336978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_1336978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1336978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1336978 prefixEnd_1336978 := by exact prefixLift 1336978
  have htrace : WordTrace (prefixWord ++ tailWord_1336978) baseStart_1336978 baseEnd_1336978 := by
    simpa [prefixWord, tailWord_1336978, baseEnd_1336978] using wordTrace_append hprefix tailTrace_1336978
  have hstable : (prefixWord ++ tailWord_1336978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336978).length < 2 ^ (prefixWord ++ tailWord_1336978).sum := by decide
  have hdescent : baseEnd_1336978 < baseStart_1336978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337020 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1337020 : Nat := 118140960795 + 1337020 * 2 ^ 59
def prefixEnd_1337020 : Nat := 4983230072969 + 3 ^ 40 * 1337020 * 2
def baseEnd_1337020 : Nat := 686533904674464136801163

theorem tailTrace_1337020 : CollatzResearch.WordTrace tailWord_1337020 prefixEnd_1337020 686533904674464136801163 := by
  unfold tailWord_1337020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24382562808106179840824257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32510083744141573121099009 24382562808106179840824257)
  ·
    refine ⟨18286922106079634880618193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24382562808106179840824257 18286922106079634880618193)
    ·
      refine ⟨13715191579559726160463645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18286922106079634880618193 13715191579559726160463645)
      ·
        refine ⟨5143196842334897310173867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13715191579559726160463645 5143196842334897310173867)
        ·
          refine ⟨7714795263502345965260801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143196842334897310173867 7714795263502345965260801)
          ·
            refine ⟨5786096447626759473945601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7714795263502345965260801 5786096447626759473945601)
            ·
              refine ⟨4339572335720069605459201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5786096447626759473945601 4339572335720069605459201)
              ·
                refine ⟨3254679251790052204094401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339572335720069605459201 3254679251790052204094401)
                ·
                  refine ⟨2441009438842539153070801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3254679251790052204094401 2441009438842539153070801)
                  ·
                    refine ⟨1830757079131904364803101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2441009438842539153070801 1830757079131904364803101)
                    ·
                      refine ⟨686533904674464136801163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1830757079131904364803101 686533904674464136801163)
                      ·
                        rfl

theorem cell23_1337020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1337020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337020 prefixEnd_1337020 := by exact prefixLift 1337020
  have htrace : WordTrace (prefixWord ++ tailWord_1337020) baseStart_1337020 baseEnd_1337020 := by
    simpa [prefixWord, tailWord_1337020, baseEnd_1337020] using wordTrace_append hprefix tailTrace_1337020
  have hstable : (prefixWord ++ tailWord_1337020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337020).length < 2 ^ (prefixWord ++ tailWord_1337020).sum := by decide
  have hdescent : baseEnd_1337020 < baseStart_1337020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337023 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 6]
def baseStart_1337023 : Nat := 118140960795 + 1337023 * 2 ^ 59
def prefixEnd_1337023 : Nat := 4983230072969 + 3 ^ 40 * 1337023 * 2
def baseEnd_1337023 : Nat := 76281716124047513895961

theorem tailTrace_1337023 : CollatzResearch.WordTrace tailWord_1337023 prefixEnd_1337023 76281716124047513895961 := by
  unfold tailWord_1337023
  simp only [CollatzResearch.WordTrace]
  refine ⟨48765235035201491194007723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32510156690134327462671815 48765235035201491194007723)
  ·
    refine ⟨73147852552802236791011585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48765235035201491194007723 73147852552802236791011585)
    ·
      refine ⟨54860889414601677593258689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73147852552802236791011585 54860889414601677593258689)
      ·
        refine ⟨41145667060951258194944017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54860889414601677593258689 41145667060951258194944017)
        ·
          refine ⟨30859250295713443646208013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41145667060951258194944017 30859250295713443646208013)
          ·
            refine ⟨11572218860892541367328005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30859250295713443646208013 11572218860892541367328005)
            ·
              refine ⟨2169791036417351506374001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11572218860892541367328005 2169791036417351506374001)
              ·
                refine ⟨1627343277313013629780501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169791036417351506374001 1627343277313013629780501)
                ·
                  refine ⟨76281716124047513895961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1627343277313013629780501 76281716124047513895961)
                  ·
                    rfl

theorem cell23_1337023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 6].length) (baseStart_1337023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337023 prefixEnd_1337023 := by exact prefixLift 1337023
  have htrace : WordTrace (prefixWord ++ tailWord_1337023) baseStart_1337023 baseEnd_1337023 := by
    simpa [prefixWord, tailWord_1337023, baseEnd_1337023] using wordTrace_append hprefix tailTrace_1337023
  have hstable : (prefixWord ++ tailWord_1337023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337023).length < 2 ^ (prefixWord ++ tailWord_1337023).sum := by decide
  have hdescent : baseEnd_1337023 < baseStart_1337023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337043 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 9, 2]
def baseStart_1337043 : Nat := 118140960795 + 1337043 * 2 ^ 59
def prefixEnd_1337043 : Nat := 4983230072969 + 3 ^ 40 * 1337043 * 2
def baseEnd_1337043 : Nat := 686545714729517546813557

theorem tailTrace_1337043 : CollatzResearch.WordTrace tailWord_1337043 prefixEnd_1337043 686545714729517546813557 := by
  unfold tailWord_1337043
  simp only [CollatzResearch.WordTrace]
  refine ⟨48765964495129034609735783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32510642996752689739823855 48765964495129034609735783)
  ·
    refine ⟨73148946742693551914603675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48765964495129034609735783 73148946742693551914603675)
    ·
      refine ⟨109723420114040327871905513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73148946742693551914603675 109723420114040327871905513)
      ·
        refine ⟨82292565085530245903929135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109723420114040327871905513 82292565085530245903929135)
        ·
          refine ⟨123438847628295368855893703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82292565085530245903929135 123438847628295368855893703)
          ·
            refine ⟨185158271442443053283840555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123438847628295368855893703 185158271442443053283840555)
            ·
              refine ⟨277737407163664579925760833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185158271442443053283840555 277737407163664579925760833)
              ·
                refine ⟨208303055372748434944320625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277737407163664579925760833 208303055372748434944320625)
                ·
                  refine ⟨156227291529561326208240469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208303055372748434944320625 156227291529561326208240469)
                  ·
                    refine ⟨915394286306023395751409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156227291529561326208240469 915394286306023395751409)
                    ·
                      refine ⟨686545714729517546813557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915394286306023395751409 686545714729517546813557)
                      ·
                        rfl

theorem cell23_1337043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9, 2].length) (baseStart_1337043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337043 prefixEnd_1337043 := by exact prefixLift 1337043
  have htrace : WordTrace (prefixWord ++ tailWord_1337043) baseStart_1337043 baseEnd_1337043 := by
    simpa [prefixWord, tailWord_1337043, baseEnd_1337043] using wordTrace_append hprefix tailTrace_1337043
  have hstable : (prefixWord ++ tailWord_1337043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337043).length < 2 ^ (prefixWord ++ tailWord_1337043).sum := by decide
  have hdescent : baseEnd_1337043 < baseStart_1337043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337050 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_1337050 : Nat := 118140960795 + 1337050 * 2 ^ 59
def prefixEnd_1337050 : Nat := 4983230072969 + 3 ^ 40 * 1337050 * 2
def baseEnd_1337050 : Nat := 686549309094099019426025

theorem tailTrace_1337050 : CollatzResearch.WordTrace tailWord_1337050 prefixEnd_1337050 686549309094099019426025 := by
  unfold tailWord_1337050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191554951525918701310151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32510813204069116536827069 12191554951525918701310151)
  ·
    refine ⟨18287332427288878051965227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12191554951525918701310151 18287332427288878051965227)
    ·
      refine ⟨27430998640933317077947841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18287332427288878051965227 27430998640933317077947841)
      ·
        refine ⟨20573248980699987808460881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27430998640933317077947841 20573248980699987808460881)
        ·
          refine ⟨15429936735524990856345661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20573248980699987808460881 15429936735524990856345661)
          ·
            refine ⟨5786226275821871571129623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15429936735524990856345661 5786226275821871571129623)
            ·
              refine ⟨8679339413732807356694435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5786226275821871571129623 8679339413732807356694435)
              ·
                refine ⟨13019009120599211035041653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8679339413732807356694435 13019009120599211035041653)
                ·
                  refine ⟨1220532105056176034535155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13019009120599211035041653 1220532105056176034535155)
                  ·
                    refine ⟨1830798157584264051802733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220532105056176034535155 1830798157584264051802733)
                    ·
                      refine ⟨686549309094099019426025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1830798157584264051802733 686549309094099019426025)
                      ·
                        rfl

theorem cell23_1337050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_1337050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337050 prefixEnd_1337050 := by exact prefixLift 1337050
  have htrace : WordTrace (prefixWord ++ tailWord_1337050) baseStart_1337050 baseEnd_1337050 := by
    simpa [prefixWord, tailWord_1337050, baseEnd_1337050] using wordTrace_append hprefix tailTrace_1337050
  have hstable : (prefixWord ++ tailWord_1337050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337050).length < 2 ^ (prefixWord ++ tailWord_1337050).sum := by decide
  have hdescent : baseEnd_1337050 < baseStart_1337050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337060 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_1337060 : Nat := 118140960795 + 1337060 * 2 ^ 59
def prefixEnd_1337060 : Nat := 4983230072969 + 3 ^ 40 * 1337060 * 2
def baseEnd_1337060 : Nat := 686554443900643980300979

theorem tailTrace_1337060 : CollatzResearch.WordTrace tailWord_1337060 prefixEnd_1337060 686554443900643980300979 := by
  unfold tailWord_1337060
  simp only [CollatzResearch.WordTrace]
  refine ⟨24383292268033723256552317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32511056357378297675403089 24383292268033723256552317)
  ·
    refine ⟨9143734600512646221207119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24383292268033723256552317 9143734600512646221207119)
    ·
      refine ⟨13715601900768969331810679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9143734600512646221207119 13715601900768969331810679)
      ·
        refine ⟨20573402851153453997716019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13715601900768969331810679 20573402851153453997716019)
        ·
          refine ⟨30860104276730180996574029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20573402851153453997716019 30860104276730180996574029)
          ·
            refine ⟨11572539103773817873715261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30860104276730180996574029 11572539103773817873715261)
            ·
              refine ⟨4339702163915181702643223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11572539103773817873715261 4339702163915181702643223)
              ·
                refine ⟨6509553245872772553964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4339702163915181702643223 6509553245872772553964835)
                ·
                  refine ⟨9764329868809158830947253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6509553245872772553964835 9764329868809158830947253)
                  ·
                    refine ⟨915405925200858640401305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9764329868809158830947253 915405925200858640401305)
                    ·
                      refine ⟨686554443900643980300979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915405925200858640401305 686554443900643980300979)
                      ·
                        rfl

theorem cell23_1337060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_1337060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337060 prefixEnd_1337060 := by exact prefixLift 1337060
  have htrace : WordTrace (prefixWord ++ tailWord_1337060) baseStart_1337060 baseEnd_1337060 := by
    simpa [prefixWord, tailWord_1337060, baseEnd_1337060] using wordTrace_append hprefix tailTrace_1337060
  have hstable : (prefixWord ++ tailWord_1337060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337060).length < 2 ^ (prefixWord ++ tailWord_1337060).sum := by decide
  have hdescent : baseEnd_1337060 < baseStart_1337060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337067 : List Nat := [1, 1, 1, 1, 2, 4, 3, 5, 1, 1, 3]
def baseStart_1337067 : Nat := 118140960795 + 1337067 * 2 ^ 59
def prefixEnd_1337067 : Nat := 4983230072969 + 3 ^ 40 * 1337067 * 2
def baseEnd_1337067 : Nat := 686558038265225452913447

theorem tailTrace_1337067 : CollatzResearch.WordTrace tailWord_1337067 prefixEnd_1337067 686558038265225452913447 := by
  unfold tailWord_1337067
  simp only [CollatzResearch.WordTrace]
  refine ⟨48766839847042086708609455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32511226564694724472406303 48766839847042086708609455)
  ·
    refine ⟨73150259770563130062914183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48766839847042086708609455 73150259770563130062914183)
    ·
      refine ⟨109725389655844695094371275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73150259770563130062914183 109725389655844695094371275)
      ·
        refine ⟨164588084483767042641556913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109725389655844695094371275 164588084483767042641556913)
        ·
          refine ⟨123441063362825281981167685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164588084483767042641556913 123441063362825281981167685)
          ·
            refine ⟨23145199380529740371468941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123441063362825281981167685 23145199380529740371468941)
            ·
              refine ⟨8679449767698652639300853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23145199380529740371468941 8679449767698652639300853)
              ·
                refine ⟨813698415721748684934455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8679449767698652639300853 813698415721748684934455)
                ·
                  refine ⟨1220547623582623027401683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813698415721748684934455 1220547623582623027401683)
                  ·
                    refine ⟨1830821435373934541102525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220547623582623027401683 1830821435373934541102525)
                    ·
                      refine ⟨686558038265225452913447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1830821435373934541102525 686558038265225452913447)
                      ·
                        rfl

theorem cell23_1337067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 1, 3].length) (baseStart_1337067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337067 prefixEnd_1337067 := by exact prefixLift 1337067
  have htrace : WordTrace (prefixWord ++ tailWord_1337067) baseStart_1337067 baseEnd_1337067 := by
    simpa [prefixWord, tailWord_1337067, baseEnd_1337067] using wordTrace_append hprefix tailTrace_1337067
  have hstable : (prefixWord ++ tailWord_1337067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337067).length < 2 ^ (prefixWord ++ tailWord_1337067).sum := by decide
  have hdescent : baseEnd_1337067 < baseStart_1337067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337070 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1337070 : Nat := 118140960795 + 1337070 * 2 ^ 59
def prefixEnd_1337070 : Nat := 4983230072969 + 3 ^ 40 * 1337070 * 2
def baseEnd_1337070 : Nat := 228853192902396313725311

theorem tailTrace_1337070 : CollatzResearch.WordTrace tailWord_1337070 prefixEnd_1337070 228853192902396313725311 := by
  unfold tailWord_1337070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6095868658253902277621083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32511299510687478813979109 6095868658253902277621083)
  ·
    refine ⟨9143802987380853416431625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6095868658253902277621083 9143802987380853416431625)
    ·
      refine ⟨6857852240535640062323719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9143802987380853416431625 6857852240535640062323719)
      ·
        refine ⟨10286778360803460093485579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857852240535640062323719 10286778360803460093485579)
        ·
          refine ⟨15430167541205190140228369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10286778360803460093485579 15430167541205190140228369)
          ·
            refine ⟨11572625655903892605171277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15430167541205190140228369 11572625655903892605171277)
            ·
              refine ⟨4339734620963959726939229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11572625655903892605171277 4339734620963959726939229)
              ·
                refine ⟨1627400482861484897602211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4339734620963959726939229 1627400482861484897602211)
                ·
                  refine ⟨2441100724292227346403317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627400482861484897602211 2441100724292227346403317)
                  ·
                    refine ⟨228853192902396313725311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2441100724292227346403317 228853192902396313725311)
                    ·
                      rfl

theorem cell23_1337070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1337070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337070 prefixEnd_1337070 := by exact prefixLift 1337070
  have htrace : WordTrace (prefixWord ++ tailWord_1337070) baseStart_1337070 baseEnd_1337070 := by
    simpa [prefixWord, tailWord_1337070, baseEnd_1337070] using wordTrace_append hprefix tailTrace_1337070
  have hstable : (prefixWord ++ tailWord_1337070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337070).length < 2 ^ (prefixWord ++ tailWord_1337070).sum := by decide
  have hdescent : baseEnd_1337070 < baseStart_1337070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337100 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_1337100 : Nat := 118140960795 + 1337100 * 2 ^ 59
def prefixEnd_1337100 : Nat := 4983230072969 + 3 ^ 40 * 1337100 * 2
def baseEnd_1337100 : Nat := 228858327708941274600265

theorem tailTrace_1337100 : CollatzResearch.WordTrace tailWord_1337100 prefixEnd_1337100 228858327708941274600265 := by
  unfold tailWord_1337100
  simp only [CollatzResearch.WordTrace]
  refine ⟨24384021727961266672280377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32512028970615022229707169 24384021727961266672280377)
  ·
    refine ⟨18288016295970950004210283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24384021727961266672280377 18288016295970950004210283)
    ·
      refine ⟨27432024443956425006315425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18288016295970950004210283 27432024443956425006315425)
      ·
        refine ⟨20574018332967318754736569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27432024443956425006315425 20574018332967318754736569)
        ·
          refine ⟨15430513749725489066052427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20574018332967318754736569 15430513749725489066052427)
          ·
            refine ⟨23145770624588233599078641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15430513749725489066052427 23145770624588233599078641)
            ·
              refine ⟨17359327968441175199308981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23145770624588233599078641 17359327968441175199308981)
              ·
                refine ⟨1627436997041360174935217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17359327968441175199308981 1627436997041360174935217)
                ·
                  refine ⟨1220577747781020131201413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1627436997041360174935217 1220577747781020131201413)
                  ·
                    refine ⟨228858327708941274600265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220577747781020131201413 228858327708941274600265)
                    ·
                      rfl

theorem cell23_1337100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_1337100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337100 prefixEnd_1337100 := by exact prefixLift 1337100
  have htrace : WordTrace (prefixWord ++ tailWord_1337100) baseStart_1337100 baseEnd_1337100 := by
    simpa [prefixWord, tailWord_1337100, baseEnd_1337100] using wordTrace_append hprefix tailTrace_1337100
  have hstable : (prefixWord ++ tailWord_1337100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337100).length < 2 ^ (prefixWord ++ tailWord_1337100).sum := by decide
  have hdescent : baseEnd_1337100 < baseStart_1337100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337103 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_1337103 : Nat := 118140960795 + 1337103 * 2 ^ 59
def prefixEnd_1337103 : Nat := 4983230072969 + 3 ^ 40 * 1337103 * 2
def baseEnd_1337103 : Nat := 686576523568787312063281

theorem tailTrace_1337103 : CollatzResearch.WordTrace tailWord_1337103 prefixEnd_1337103 686576523568787312063281 := by
  unfold tailWord_1337103
  simp only [CollatzResearch.WordTrace]
  refine ⟨48768152874911664856919963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32512101916607776571279975 48768152874911664856919963)
  ·
    refine ⟨73152229312367497285379945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48768152874911664856919963 73152229312367497285379945)
    ·
      refine ⟨54864171984275622964034959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73152229312367497285379945 54864171984275622964034959)
      ·
        refine ⟨82296257976413434446052439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54864171984275622964034959 82296257976413434446052439)
        ·
          refine ⟨123444386964620151669078659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82296257976413434446052439 123444386964620151669078659)
          ·
            refine ⟨185166580446930227503617989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123444386964620151669078659 185166580446930227503617989)
            ·
              refine ⟨34718733833799417656928373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185166580446930227503617989 34718733833799417656928373)
              ·
                refine ⟨3254881296918695405337035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34718733833799417656928373 3254881296918695405337035)
                ·
                  refine ⟨4882321945378043108005553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254881296918695405337035 4882321945378043108005553)
                  ·
                    refine ⟨3661741459033532331004165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4882321945378043108005553 3661741459033532331004165)
                    ·
                      refine ⟨686576523568787312063281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3661741459033532331004165 686576523568787312063281)
                      ·
                        rfl

theorem cell23_1337103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_1337103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337103 prefixEnd_1337103 := by exact prefixLift 1337103
  have htrace : WordTrace (prefixWord ++ tailWord_1337103) baseStart_1337103 baseEnd_1337103 := by
    simpa [prefixWord, tailWord_1337103, baseEnd_1337103] using wordTrace_append hprefix tailTrace_1337103
  have hstable : (prefixWord ++ tailWord_1337103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337103).length < 2 ^ (prefixWord ++ tailWord_1337103).sum := by decide
  have hdescent : baseEnd_1337103 < baseStart_1337103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337141 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_1337141 : Nat := 118140960795 + 1337141 * 2 ^ 59
def prefixEnd_1337141 : Nat := 4983230072969 + 3 ^ 40 * 1337141 * 2
def baseEnd_1337141 : Nat := 686596035833658163388107

theorem tailTrace_1337141 : CollatzResearch.WordTrace tailWord_1337141 prefixEnd_1337141 686596035833658163388107 := by
  unfold tailWord_1337141
  simp only [CollatzResearch.WordTrace]
  refine ⟨48769538848773997346803277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32513025899182664897868851 48769538848773997346803277)
  ·
    refine ⟨18288577068290249005051229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48769538848773997346803277 18288577068290249005051229)
    ·
      refine ⟨6858216400608843376894211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18288577068290249005051229 6858216400608843376894211)
      ·
        refine ⟨10287324600913265065341317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6858216400608843376894211 10287324600913265065341317)
        ·
          refine ⟨1928873362671237199751497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10287324600913265065341317 1928873362671237199751497)
          ·
            refine ⟨1446655022003427899813623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928873362671237199751497 1446655022003427899813623)
            ·
              refine ⟨2169982533005141849720435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446655022003427899813623 2169982533005141849720435)
              ·
                refine ⟨3254973799507712774580653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169982533005141849720435 3254973799507712774580653)
                ·
                  refine ⟨1220615174815392290467745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3254973799507712774580653 1220615174815392290467745)
                  ·
                    refine ⟨915461381111544217850809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1220615174815392290467745 915461381111544217850809)
                    ·
                      refine ⟨686596035833658163388107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915461381111544217850809 686596035833658163388107)
                      ·
                        rfl

theorem cell23_1337141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_1337141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337141 prefixEnd_1337141 := by exact prefixLift 1337141
  have htrace : WordTrace (prefixWord ++ tailWord_1337141) baseStart_1337141 baseEnd_1337141 := by
    simpa [prefixWord, tailWord_1337141, baseEnd_1337141] using wordTrace_append hprefix tailTrace_1337141
  have hstable : (prefixWord ++ tailWord_1337141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337141).length < 2 ^ (prefixWord ++ tailWord_1337141).sum := by decide
  have hdescent : baseEnd_1337141 < baseStart_1337141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337151 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 2, 4]
def baseStart_1337151 : Nat := 118140960795 + 1337151 * 2 ^ 59
def prefixEnd_1337151 : Nat := 4983230072969 + 3 ^ 40 * 1337151 * 2
def baseEnd_1337151 : Nat := 228867056880067708087687

theorem tailTrace_1337151 : CollatzResearch.WordTrace tailWord_1337151 prefixEnd_1337151 228867056880067708087687 := by
  unfold tailWord_1337151
  simp only [CollatzResearch.WordTrace]
  refine ⟨48769903578737769054667307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32513269052491846036444871 48769903578737769054667307)
  ·
    refine ⟨73154855368106653582000961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48769903578737769054667307 73154855368106653582000961)
    ·
      refine ⟨54866141526079990186500721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73154855368106653582000961 54866141526079990186500721)
      ·
        refine ⟨41149606144559992639875541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54866141526079990186500721 41149606144559992639875541)
        ·
          refine ⟨964443894013124827497083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 41149606144559992639875541 964443894013124827497083)
          ·
            refine ⟨1446665841019687241245625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964443894013124827497083 1446665841019687241245625)
            ·
              refine ⟨1084999380764765430934219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446665841019687241245625 1084999380764765430934219)
              ·
                refine ⟨1627499071147148146401329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084999380764765430934219 1627499071147148146401329)
                ·
                  refine ⟨1220624303360361109800997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1627499071147148146401329 1220624303360361109800997)
                  ·
                    refine ⟨228867056880067708087687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220624303360361109800997 228867056880067708087687)
                    ·
                      rfl

theorem cell23_1337151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 4].length) (baseStart_1337151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337151 prefixEnd_1337151 := by exact prefixLift 1337151
  have htrace : WordTrace (prefixWord ++ tailWord_1337151) baseStart_1337151 baseEnd_1337151 := by
    simpa [prefixWord, tailWord_1337151, baseEnd_1337151] using wordTrace_append hprefix tailTrace_1337151
  have hstable : (prefixWord ++ tailWord_1337151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337151).length < 2 ^ (prefixWord ++ tailWord_1337151).sum := by decide
  have hdescent : baseEnd_1337151 < baseStart_1337151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337157 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_1337157 : Nat := 118140960795 + 1337157 * 2 ^ 59
def prefixEnd_1337157 : Nat := 4983230072969 + 3 ^ 40 * 1337157 * 2
def baseEnd_1337157 : Nat := 686604251524130100788033

theorem tailTrace_1337157 : CollatzResearch.WordTrace tailWord_1337157 prefixEnd_1337157 686604251524130100788033 := by
  unfold tailWord_1337157
  simp only [CollatzResearch.WordTrace]
  refine ⟨48770122416716032079385725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32513414944477354719590483 48770122416716032079385725)
  ·
    refine ⟨18288795906268512029769647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48770122416716032079385725 18288795906268512029769647)
    ·
      refine ⟨27433193859402768044654471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18288795906268512029769647 27433193859402768044654471)
      ·
        refine ⟨41149790789104152066981707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27433193859402768044654471 41149790789104152066981707)
        ·
          refine ⟨61724686183656228100472561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41149790789104152066981707 61724686183656228100472561)
          ·
            refine ⟨46293514637742171075354421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61724686183656228100472561 46293514637742171075354421)
            ·
              refine ⟨4340016997288328538314477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46293514637742171075354421 4340016997288328538314477)
              ·
                refine ⟨1627506373983123201867929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4340016997288328538314477 1627506373983123201867929)
                ·
                  refine ⟨1220629780487342401400947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1627506373983123201867929 1220629780487342401400947)
                  ·
                    refine ⟨1830944670731013602101421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220629780487342401400947 1830944670731013602101421)
                    ·
                      refine ⟨686604251524130100788033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1830944670731013602101421 686604251524130100788033)
                      ·
                        rfl

theorem cell23_1337157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_1337157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337157 prefixEnd_1337157 := by exact prefixLift 1337157
  have htrace : WordTrace (prefixWord ++ tailWord_1337157) baseStart_1337157 baseEnd_1337157 := by
    simpa [prefixWord, tailWord_1337157, baseEnd_1337157] using wordTrace_append hprefix tailTrace_1337157
  have hstable : (prefixWord ++ tailWord_1337157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337157).length < 2 ^ (prefixWord ++ tailWord_1337157).sum := by decide
  have hdescent : baseEnd_1337157 < baseStart_1337157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337193 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_1337193 : Nat := 118140960795 + 1337193 * 2 ^ 59
def prefixEnd_1337193 : Nat := 4983230072969 + 3 ^ 40 * 1337193 * 2
def baseEnd_1337193 : Nat := 686622736827691959937867

theorem tailTrace_1337193 : CollatzResearch.WordTrace tailWord_1337193 prefixEnd_1337193 686622736827691959937867 := by
  unfold tailWord_1337193
  simp only [CollatzResearch.WordTrace]
  refine ⟨48771435444585610227696233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32514290296390406818464155 48771435444585610227696233)
  ·
    refine ⟨36578576583439207670772175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48771435444585610227696233 36578576583439207670772175)
    ·
      refine ⟨54867864875158811506158263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36578576583439207670772175 54867864875158811506158263)
      ·
        refine ⟨82301797312738217259237395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54867864875158811506158263 82301797312738217259237395)
        ·
          refine ⟨123452695969107325888856093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82301797312738217259237395 123452695969107325888856093)
          ·
            refine ⟨46294760988415247208321035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123452695969107325888856093 46294760988415247208321035)
            ·
              refine ⟨69442141482622870812481553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46294760988415247208321035 69442141482622870812481553)
              ·
                refine ⟨52081606111967153109361165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69442141482622870812481553 52081606111967153109361165)
                ·
                  refine ⟨19530602291987682416010437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52081606111967153109361165 19530602291987682416010437)
                  ·
                    refine ⟨3661987929747690453001957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19530602291987682416010437 3661987929747690453001957)
                    ·
                      refine ⟨686622736827691959937867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3661987929747690453001957 686622736827691959937867)
                      ·
                        rfl

theorem cell23_1337193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_1337193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337193 prefixEnd_1337193 := by exact prefixLift 1337193
  have htrace : WordTrace (prefixWord ++ tailWord_1337193) baseStart_1337193 baseEnd_1337193 := by
    simpa [prefixWord, tailWord_1337193, baseEnd_1337193] using wordTrace_append hprefix tailTrace_1337193
  have hstable : (prefixWord ++ tailWord_1337193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337193).length < 2 ^ (prefixWord ++ tailWord_1337193).sum := by decide
  have hdescent : baseEnd_1337193 < baseStart_1337193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337203 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 7]
def baseStart_1337203 : Nat := 118140960795 + 1337203 * 2 ^ 59
def prefixEnd_1337203 : Nat := 4983230072969 + 3 ^ 40 * 1337203 * 2
def baseEnd_1337203 : Nat := 76291985737137435645869

theorem tailTrace_1337203 : CollatzResearch.WordTrace tailWord_1337203 prefixEnd_1337203 76291985737137435645869 := by
  unfold tailWord_1337203
  simp only [CollatzResearch.WordTrace]
  refine ⟨48771800174549381935560263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32514533449699587957040175 48771800174549381935560263)
  ·
    refine ⟨73157700261824072903340395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48771800174549381935560263 73157700261824072903340395)
    ·
      refine ⟨109736550392736109355010593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73157700261824072903340395 109736550392736109355010593)
      ·
        refine ⟨82302412794552082016257945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109736550392736109355010593 82302412794552082016257945)
        ·
          refine ⟨61726809595914061512193459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82302412794552082016257945 61726809595914061512193459)
          ·
            refine ⟨92590214393871092268290189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61726809595914061512193459 92590214393871092268290189)
            ·
              refine ⟨34721330397701659600608821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92590214393871092268290189 34721330397701659600608821)
              ·
                refine ⟨3255124724784530587557077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34721330397701659600608821 3255124724784530587557077)
                ·
                  refine ⟨76291985737137435645869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3255124724784530587557077 76291985737137435645869)
                  ·
                    rfl

theorem cell23_1337203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 7].length) (baseStart_1337203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337203 prefixEnd_1337203 := by exact prefixLift 1337203
  have htrace : WordTrace (prefixWord ++ tailWord_1337203) baseStart_1337203 baseEnd_1337203 := by
    simpa [prefixWord, tailWord_1337203, baseEnd_1337203] using wordTrace_append hprefix tailTrace_1337203
  have hstable : (prefixWord ++ tailWord_1337203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337203).length < 2 ^ (prefixWord ++ tailWord_1337203).sum := by decide
  have hdescent : baseEnd_1337203 < baseStart_1337203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337237 : List Nat := [1, 3, 2, 1, 1, 3, 4, 3, 5]
def baseStart_1337237 : Nat := 118140960795 + 1337237 * 2 ^ 59
def prefixEnd_1337237 : Nat := 4983230072969 + 3 ^ 40 * 1337237 * 2
def baseEnd_1337237 : Nat := 76293925552943309754185

theorem tailTrace_1337237 : CollatzResearch.WordTrace tailWord_1337237 prefixEnd_1337237 76293925552943309754185 := by
  unfold tailWord_1337237
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773040256426205742297965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32515360170950803828198643 48773040256426205742297965)
  ·
    refine ⟨18289890096159827153361737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48773040256426205742297965 18289890096159827153361737)
    ·
      refine ⟨13717417572119870365021303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18289890096159827153361737 13717417572119870365021303)
      ·
        refine ⟨20576126358179805547531955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13717417572119870365021303 20576126358179805547531955)
        ·
          refine ⟨30864189537269708321297933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20576126358179805547531955 30864189537269708321297933)
          ·
            refine ⟨11574071076476140620486725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30864189537269708321297933 11574071076476140620486725)
            ·
              refine ⟨2170138326839276366341261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11574071076476140620486725 2170138326839276366341261)
              ·
                refine ⟨813801872564728637377973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170138326839276366341261 813801872564728637377973)
                ·
                  refine ⟨76293925552943309754185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 813801872564728637377973 76293925552943309754185)
                  ·
                    rfl

theorem cell23_1337237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_1337237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337237 prefixEnd_1337237 := by exact prefixLift 1337237
  have htrace : WordTrace (prefixWord ++ tailWord_1337237) baseStart_1337237 baseEnd_1337237 := by
    simpa [prefixWord, tailWord_1337237, baseEnd_1337237] using wordTrace_append hprefix tailTrace_1337237
  have hstable : (prefixWord ++ tailWord_1337237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337237).length < 2 ^ (prefixWord ++ tailWord_1337237).sum := by decide
  have hdescent : baseEnd_1337237 < baseStart_1337237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337347 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 1, 5, 2]
def baseStart_1337347 : Nat := 118140960795 + 1337347 * 2 ^ 59
def prefixEnd_1337347 : Nat := 4983230072969 + 3 ^ 40 * 1337347 * 2
def baseEnd_1337347 : Nat := 686701812848484357412159

theorem tailTrace_1337347 : CollatzResearch.WordTrace tailWord_1337347 prefixEnd_1337347 686701812848484357412159 := by
  unfold tailWord_1337347
  simp only [CollatzResearch.WordTrace]
  refine ⟨48777052286027694528802295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32518034857351796352534863 48777052286027694528802295)
  ·
    refine ⟨73165578429041541793203443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48777052286027694528802295 73165578429041541793203443)
    ·
      refine ⟨109748367643562312689805165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73165578429041541793203443 109748367643562312689805165)
      ·
        refine ⟨41155637866335867258676937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109748367643562312689805165 41155637866335867258676937)
        ·
          refine ⟨30866728399751900444007703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41155637866335867258676937 30866728399751900444007703)
          ·
            refine ⟨46300092599627850666011555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30866728399751900444007703 46300092599627850666011555)
            ·
              refine ⟨69450138899441775999017333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46300092599627850666011555 69450138899441775999017333)
              ·
                refine ⟨6510950521822666499907875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69450138899441775999017333 6510950521822666499907875)
                ·
                  refine ⟨9766425782733999749861813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6510950521822666499907875 9766425782733999749861813)
                  ·
                    refine ⟨915602417131312476549545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9766425782733999749861813 915602417131312476549545)
                    ·
                      refine ⟨686701812848484357412159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915602417131312476549545 686701812848484357412159)
                      ·
                        rfl

theorem cell23_1337347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_1337347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337347 prefixEnd_1337347 := by exact prefixLift 1337347
  have htrace : WordTrace (prefixWord ++ tailWord_1337347) baseStart_1337347 baseEnd_1337347 := by
    simpa [prefixWord, tailWord_1337347, baseEnd_1337347] using wordTrace_append hprefix tailTrace_1337347
  have hstable : (prefixWord ++ tailWord_1337347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337347).length < 2 ^ (prefixWord ++ tailWord_1337347).sum := by decide
  have hdescent : baseEnd_1337347 < baseStart_1337347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337365 : List Nat := [1, 3, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1337365 : Nat := 118140960795 + 1337365 * 2 ^ 59
def prefixEnd_1337365 : Nat := 4983230072969 + 3 ^ 40 * 1337365 * 2
def baseEnd_1337365 : Nat := 228903685166755095662359

theorem tailTrace_1337365 : CollatzResearch.WordTrace tailWord_1337365 prefixEnd_1337365 228903685166755095662359 := by
  unfold tailWord_1337365
  simp only [CollatzResearch.WordTrace]
  refine ⟨48777708799962483602957549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32518472533308322401971699 48777708799962483602957549)
  ·
    refine ⟨18291640799985931351109081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48777708799962483602957549 18291640799985931351109081)
    ·
      refine ⟨13718730599989448513331811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18291640799985931351109081 13718730599989448513331811)
      ·
        refine ⟨20578095899984172769997717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13718730599989448513331811 20578095899984172769997717)
        ·
          refine ⟨964598245311758098593643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20578095899984172769997717 964598245311758098593643)
          ·
            refine ⟨1446897367967637147890465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964598245311758098593643 1446897367967637147890465)
            ·
              refine ⟨1085173025975727860917849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446897367967637147890465 1085173025975727860917849)
              ·
                refine ⟨813879769481795895688387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085173025975727860917849 813879769481795895688387)
                ·
                  refine ⟨1220819654222693843532581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813879769481795895688387 1220819654222693843532581)
                  ·
                    refine ⟨228903685166755095662359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220819654222693843532581 228903685166755095662359)
                    ·
                      rfl

theorem cell23_1337365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1337365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337365 prefixEnd_1337365 := by exact prefixLift 1337365
  have htrace : WordTrace (prefixWord ++ tailWord_1337365) baseStart_1337365 baseEnd_1337365 := by
    simpa [prefixWord, tailWord_1337365, baseEnd_1337365] using wordTrace_append hprefix tailTrace_1337365
  have hstable : (prefixWord ++ tailWord_1337365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337365).length < 2 ^ (prefixWord ++ tailWord_1337365).sum := by decide
  have hdescent : baseEnd_1337365 < baseStart_1337365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337407 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_1337407 : Nat := 118140960795 + 1337407 * 2 ^ 59
def prefixEnd_1337407 : Nat := 4983230072969 + 3 ^ 40 * 1337407 * 2
def baseEnd_1337407 : Nat := 686732621687754122661883

theorem tailTrace_1337407 : CollatzResearch.WordTrace tailWord_1337407 prefixEnd_1337407 686732621687754122661883 := by
  unfold tailWord_1337407
  simp only [CollatzResearch.WordTrace]
  refine ⟨48779240665810324775986475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32519493777206883183990983 48779240665810324775986475)
  ·
    refine ⟨73168860998715487163979713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48779240665810324775986475 73168860998715487163979713)
    ·
      refine ⟨54876645749036615372984785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73168860998715487163979713 54876645749036615372984785)
      ·
        refine ⟨41157484311777461529738589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54876645749036615372984785 41157484311777461529738589)
        ·
          refine ⟨15434056616916548073651971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41157484311777461529738589 15434056616916548073651971)
          ·
            refine ⟨23151084925374822110477957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15434056616916548073651971 23151084925374822110477957)
            ·
              refine ⟨4340828423507779145714617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23151084925374822110477957 4340828423507779145714617)
              ·
                refine ⟨3255621317630834359285963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4340828423507779145714617 3255621317630834359285963)
                ·
                  refine ⟨4883431976446251538928945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255621317630834359285963 4883431976446251538928945)
                  ·
                    refine ⟨3662573982334688654196709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883431976446251538928945 3662573982334688654196709)
                    ·
                      refine ⟨686732621687754122661883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3662573982334688654196709 686732621687754122661883)
                      ·
                        rfl

theorem cell23_1337407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_1337407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337407 prefixEnd_1337407 := by exact prefixLift 1337407
  have htrace : WordTrace (prefixWord ++ tailWord_1337407) baseStart_1337407 baseEnd_1337407 := by
    simpa [prefixWord, tailWord_1337407, baseEnd_1337407] using wordTrace_append hprefix tailTrace_1337407
  have hstable : (prefixWord ++ tailWord_1337407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337407).length < 2 ^ (prefixWord ++ tailWord_1337407).sum := by decide
  have hdescent : baseEnd_1337407 < baseStart_1337407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337444 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_1337444 : Nat := 118140960795 + 1337444 * 2 ^ 59
def prefixEnd_1337444 : Nat := 4983230072969 + 3 ^ 40 * 1337444 * 2
def baseEnd_1337444 : Nat := 686751620471970477899213

theorem tailTrace_1337444 : CollatzResearch.WordTrace tailWord_1337444 prefixEnd_1337444 686751620471970477899213 := by
  unfold tailWord_1337444
  simp only [CollatzResearch.WordTrace]
  refine ⟨24390295083338140047541693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32520393444450853396722257 24390295083338140047541693)
  ·
    refine ⟨9146360656251802517828135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24390295083338140047541693 9146360656251802517828135)
    ·
      refine ⟨13719540984377703776742203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9146360656251802517828135 13719540984377703776742203)
      ·
        refine ⟨20579311476566555665113305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13719540984377703776742203 20579311476566555665113305)
        ·
          refine ⟨15434483607424916748834979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20579311476566555665113305 15434483607424916748834979)
          ·
            refine ⟨23151725411137375123252469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15434483607424916748834979 23151725411137375123252469)
            ·
              refine ⟨2170474257294128917804919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23151725411137375123252469 2170474257294128917804919)
              ·
                refine ⟨3255711385941193376707379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170474257294128917804919 3255711385941193376707379)
                ·
                  refine ⟨4883567078911790065061069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255711385941193376707379 4883567078911790065061069)
                  ·
                    refine ⟨1831337654591921274397901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4883567078911790065061069 1831337654591921274397901)
                    ·
                      refine ⟨686751620471970477899213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1831337654591921274397901 686751620471970477899213)
                      ·
                        rfl

theorem cell23_1337444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_1337444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337444 prefixEnd_1337444 := by exact prefixLift 1337444
  have htrace : WordTrace (prefixWord ++ tailWord_1337444) baseStart_1337444 baseEnd_1337444 := by
    simpa [prefixWord, tailWord_1337444, baseEnd_1337444] using wordTrace_append hprefix tailTrace_1337444
  have hstable : (prefixWord ++ tailWord_1337444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337444).length < 2 ^ (prefixWord ++ tailWord_1337444).sum := by decide
  have hdescent : baseEnd_1337444 < baseStart_1337444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337462 : List Nat := [5, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1337462 : Nat := 118140960795 + 1337462 * 2 ^ 59
def prefixEnd_1337462 : Nat := 4983230072969 + 3 ^ 40 * 1337462 * 2
def baseEnd_1337462 : Nat := 686760863123751407474131

theorem tailTrace_1337462 : CollatzResearch.WordTrace tailWord_1337462 prefixEnd_1337462 686760863123751407474131 := by
  unfold tailWord_1337462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048827917538191823077415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32520831120407379446159093 3048827917538191823077415)
  ·
    refine ⟨4573241876307287734616123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3048827917538191823077415 4573241876307287734616123)
    ·
      refine ⟨6859862814460931601924185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4573241876307287734616123 6859862814460931601924185)
      ·
        refine ⟨5144897110845698701443139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6859862814460931601924185 5144897110845698701443139)
        ·
          refine ⟨7717345666268548052164709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144897110845698701443139 7717345666268548052164709)
          ·
            refine ⟨1447002312425352759780883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7717345666268548052164709 1447002312425352759780883)
            ·
              refine ⟨2170503468638029139671325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447002312425352759780883 2170503468638029139671325)
              ·
                refine ⟨813938800739260927376747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170503468638029139671325 813938800739260927376747)
                ·
                  refine ⟨1220908201108891391065121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813938800739260927376747 1220908201108891391065121)
                  ·
                    refine ⟨915681150831668543298841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1220908201108891391065121 915681150831668543298841)
                    ·
                      refine ⟨686760863123751407474131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915681150831668543298841 686760863123751407474131)
                      ·
                        rfl

theorem cell23_1337462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1337462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337462 prefixEnd_1337462 := by exact prefixLift 1337462
  have htrace : WordTrace (prefixWord ++ tailWord_1337462) baseStart_1337462 baseEnd_1337462 := by
    simpa [prefixWord, tailWord_1337462, baseEnd_1337462] using wordTrace_append hprefix tailTrace_1337462
  have hstable : (prefixWord ++ tailWord_1337462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337462).length < 2 ^ (prefixWord ++ tailWord_1337462).sum := by decide
  have hdescent : baseEnd_1337462 < baseStart_1337462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337495 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 2, 1, 3]
def baseStart_1337495 : Nat := 118140960795 + 1337495 * 2 ^ 59
def prefixEnd_1337495 : Nat := 4983230072969 + 3 ^ 40 * 1337495 * 2
def baseEnd_1337495 : Nat := 686777807985349778361479

theorem tailTrace_1337495 : CollatzResearch.WordTrace tailWord_1337495 prefixEnd_1337495 686777807985349778361479 := by
  unfold tailWord_1337495
  simp only [CollatzResearch.WordTrace]
  refine ⟨48782450289491515805189939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32521633526327677203459959 48782450289491515805189939)
  ·
    refine ⟨73173675434237273707784909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48782450289491515805189939 73173675434237273707784909)
    ·
      refine ⟨27440128287838977640419341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73173675434237273707784909 27440128287838977640419341)
      ·
        refine ⟨10290048107939616615157253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27440128287838977640419341 10290048107939616615157253)
        ·
          refine ⟨1929384020238678115341985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10290048107939616615157253 1929384020238678115341985)
          ·
            refine ⟨1447038015179008586506489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1929384020238678115341985 1447038015179008586506489)
            ·
              refine ⟨1085278511384256439879867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447038015179008586506489 1085278511384256439879867)
              ·
                refine ⟨1627917767076384659819801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085278511384256439879867 1627917767076384659819801)
                ·
                  refine ⟨1220938325307288494864851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1627917767076384659819801 1220938325307288494864851)
                  ·
                    refine ⟨1831407487960932742297277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220938325307288494864851 1831407487960932742297277)
                    ·
                      refine ⟨686777807985349778361479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1831407487960932742297277 686777807985349778361479)
                      ·
                        rfl

theorem cell23_1337495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_1337495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337495 prefixEnd_1337495 := by exact prefixLift 1337495
  have htrace : WordTrace (prefixWord ++ tailWord_1337495) baseStart_1337495 baseEnd_1337495 := by
    simpa [prefixWord, tailWord_1337495, baseEnd_1337495] using wordTrace_append hprefix tailTrace_1337495
  have hstable : (prefixWord ++ tailWord_1337495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337495).length < 2 ^ (prefixWord ++ tailWord_1337495).sum := by decide
  have hdescent : baseEnd_1337495 < baseStart_1337495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337497 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_1337497 : Nat := 118140960795 + 1337497 * 2 ^ 59
def prefixEnd_1337497 : Nat := 4983230072969 + 3 ^ 40 * 1337497 * 2
def baseEnd_1337497 : Nat := 686778834946658770536469

theorem tailTrace_1337497 : CollatzResearch.WordTrace tailWord_1337497 prefixEnd_1337497 686778834946658770536469 := by
  unfold tailWord_1337497
  simp only [CollatzResearch.WordTrace]
  refine ⟨48782523235484270146762745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32521682156989513431175163 48782523235484270146762745)
  ·
    refine ⟨36586892426613202610072059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48782523235484270146762745 36586892426613202610072059)
    ·
      refine ⟨54880338639919803915108089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36586892426613202610072059 54880338639919803915108089)
      ·
        refine ⟨41160253979939852936331067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54880338639919803915108089 41160253979939852936331067)
        ·
          refine ⟨61740380969909779404496601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41160253979939852936331067 61740380969909779404496601)
          ·
            refine ⟨46305285727432334553372451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61740380969909779404496601 46305285727432334553372451)
            ·
              refine ⟨69457928591148501830058677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46305285727432334553372451 69457928591148501830058677)
              ·
                refine ⟨6511680805420172046568001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69457928591148501830058677 6511680805420172046568001)
                ·
                  refine ⟨4883760604065129034926001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511680805420172046568001 4883760604065129034926001)
                  ·
                    refine ⟨3662820453048846776194501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883760604065129034926001 3662820453048846776194501)
                    ·
                      refine ⟨686778834946658770536469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3662820453048846776194501 686778834946658770536469)
                      ·
                        rfl

theorem cell23_1337497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_1337497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337497 prefixEnd_1337497 := by exact prefixLift 1337497
  have htrace : WordTrace (prefixWord ++ tailWord_1337497) baseStart_1337497 baseEnd_1337497 := by
    simpa [prefixWord, tailWord_1337497, baseEnd_1337497] using wordTrace_append hprefix tailTrace_1337497
  have hstable : (prefixWord ++ tailWord_1337497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337497).length < 2 ^ (prefixWord ++ tailWord_1337497).sum := by decide
  have hdescent : baseEnd_1337497 < baseStart_1337497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337538 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1337538 : Nat := 118140960795 + 1337538 * 2 ^ 59
def prefixEnd_1337538 : Nat := 4983230072969 + 3 ^ 40 * 1337538 * 2
def baseEnd_1337538 : Nat := 686799887653493110123781

theorem tailTrace_1337538 : CollatzResearch.WordTrace tailWord_1337538 prefixEnd_1337538 686799887653493110123781 := by
  unfold tailWord_1337538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12196004657083933537251317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32522679085557156099336845 12196004657083933537251317)
  ·
    refine ⟨1143375436601618769117311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12196004657083933537251317 1143375436601618769117311)
    ·
      refine ⟨1715063154902428153675967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143375436601618769117311 1715063154902428153675967)
      ·
        refine ⟨2572594732353642230513951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715063154902428153675967 2572594732353642230513951)
        ·
          refine ⟨3858892098530463345770927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572594732353642230513951 3858892098530463345770927)
          ·
            refine ⟨5788338147795695018656391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858892098530463345770927 5788338147795695018656391)
            ·
              refine ⟨8682507221693542527984587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788338147795695018656391 8682507221693542527984587)
              ·
                refine ⟨13023760832540313791976881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8682507221693542527984587 13023760832540313791976881)
                ·
                  refine ⟨9767820624405235343982661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13023760832540313791976881 9767820624405235343982661)
                  ·
                    refine ⟨1831466367075981626996749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9767820624405235343982661 1831466367075981626996749)
                    ·
                      refine ⟨686799887653493110123781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1831466367075981626996749 686799887653493110123781)
                      ·
                        rfl

theorem cell23_1337538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1337538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337538 prefixEnd_1337538 := by exact prefixLift 1337538
  have htrace : WordTrace (prefixWord ++ tailWord_1337538) baseStart_1337538 baseEnd_1337538 := by
    simpa [prefixWord, tailWord_1337538, baseEnd_1337538] using wordTrace_append hprefix tailTrace_1337538
  have hstable : (prefixWord ++ tailWord_1337538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337538).length < 2 ^ (prefixWord ++ tailWord_1337538).sum := by decide
  have hdescent : baseEnd_1337538 < baseStart_1337538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337541 : List Nat := [1, 3, 1, 1, 1, 1, 8, 2, 5]
def baseStart_1337541 : Nat := 118140960795 + 1337541 * 2 ^ 59
def prefixEnd_1337541 : Nat := 4983230072969 + 3 ^ 40 * 1337541 * 2
def baseEnd_1337541 : Nat := 76311269788384066487363

theorem tailTrace_1337541 : CollatzResearch.WordTrace tailWord_1337541 prefixEnd_1337541 76311269788384066487363 := by
  unfold tailWord_1337541
  simp only [CollatzResearch.WordTrace]
  refine ⟨48784128047324865661364477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32522752031549910440909651 48784128047324865661364477)
  ·
    refine ⟨18294048017746824623011679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48784128047324865661364477 18294048017746824623011679)
    ·
      refine ⟨27441072026620236934517519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18294048017746824623011679 27441072026620236934517519)
      ·
        refine ⟨41161608039930355401776279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27441072026620236934517519 41161608039930355401776279)
        ·
          refine ⟨61742412059895533102664419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41161608039930355401776279 61742412059895533102664419)
          ·
            refine ⟨92613618089843299653996629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61742412059895533102664419 92613618089843299653996629)
            ·
              refine ⟨1085315836990351167820273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 92613618089843299653996629 1085315836990351167820273)
              ·
                refine ⟨813986877742763375865205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085315836990351167820273 813986877742763375865205)
                ·
                  refine ⟨76311269788384066487363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 813986877742763375865205 76311269788384066487363)
                  ·
                    rfl

theorem cell23_1337541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_1337541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337541 prefixEnd_1337541 := by exact prefixLift 1337541
  have htrace : WordTrace (prefixWord ++ tailWord_1337541) baseStart_1337541 baseEnd_1337541 := by
    simpa [prefixWord, tailWord_1337541, baseEnd_1337541] using wordTrace_append hprefix tailTrace_1337541
  have hstable : (prefixWord ++ tailWord_1337541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337541).length < 2 ^ (prefixWord ++ tailWord_1337541).sum := by decide
  have hdescent : baseEnd_1337541 < baseStart_1337541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337547 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5]
def baseStart_1337547 : Nat := 118140960795 + 1337547 * 2 ^ 59
def prefixEnd_1337547 : Nat := 4983230072969 + 3 ^ 40 * 1337547 * 2
def baseEnd_1337547 : Nat := 686804508979383574911239

theorem tailTrace_1337547 : CollatzResearch.WordTrace tailWord_1337547 prefixEnd_1337547 686804508979383574911239 := by
  unfold tailWord_1337547
  simp only [CollatzResearch.WordTrace]
  refine ⟨48784346885303128686082895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32522897923535419124055263 48784346885303128686082895)
  ·
    refine ⟨73176520327954693029124343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48784346885303128686082895 73176520327954693029124343)
    ·
      refine ⟨109764780491932039543686515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73176520327954693029124343 109764780491932039543686515)
      ·
        refine ⟨164647170737898059315529773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109764780491932039543686515 164647170737898059315529773)
        ·
          refine ⟨61742689026711772243323665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164647170737898059315529773 61742689026711772243323665)
          ·
            refine ⟨46307016770033829182492749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61742689026711772243323665 46307016770033829182492749)
            ·
              refine ⟨17365131288762685943434781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46307016770033829182492749 17365131288762685943434781)
              ·
                refine ⟨6511924233286007228788043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17365131288762685943434781 6511924233286007228788043)
                ·
                  refine ⟨9767886349929010843182065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6511924233286007228788043 9767886349929010843182065)
                  ·
                    refine ⟨7325914762446758132386549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9767886349929010843182065 7325914762446758132386549)
                    ·
                      refine ⟨686804508979383574911239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7325914762446758132386549 686804508979383574911239)
                      ·
                        rfl

theorem cell23_1337547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_1337547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337547 prefixEnd_1337547 := by exact prefixLift 1337547
  have htrace : WordTrace (prefixWord ++ tailWord_1337547) baseStart_1337547 baseEnd_1337547 := by
    simpa [prefixWord, tailWord_1337547, baseEnd_1337547] using wordTrace_append hprefix tailTrace_1337547
  have hstable : (prefixWord ++ tailWord_1337547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337547).length < 2 ^ (prefixWord ++ tailWord_1337547).sum := by decide
  have hdescent : baseEnd_1337547 < baseStart_1337547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337571 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 1, 7]
def baseStart_1337571 : Nat := 118140960795 + 1337571 * 2 ^ 59
def prefixEnd_1337571 : Nat := 4983230072969 + 3 ^ 40 * 1337571 * 2
def baseEnd_1337571 : Nat := 228938944171697160337043

theorem tailTrace_1337571 : CollatzResearch.WordTrace tailWord_1337571 prefixEnd_1337571 228938944171697160337043 := by
  unfold tailWord_1337571
  simp only [CollatzResearch.WordTrace]
  refine ⟨48785222237216180784956567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32523481491477453856637711 48785222237216180784956567)
  ·
    refine ⟨73177833355824271177434851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48785222237216180784956567 73177833355824271177434851)
    ·
      refine ⟨109766750033736406766152277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73177833355824271177434851 109766750033736406766152277)
      ·
        refine ⟨1286329101957848516790847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 109766750033736406766152277 1286329101957848516790847)
        ·
          refine ⟨1929493652936772775186271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286329101957848516790847 1929493652936772775186271)
          ·
            refine ⟨2894240479405159162779407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929493652936772775186271 2894240479405159162779407)
            ·
              refine ⟨4341360719107738744169111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894240479405159162779407 4341360719107738744169111)
              ·
                refine ⟨6512041078661608116253667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341360719107738744169111 6512041078661608116253667)
                ·
                  refine ⟨9768061617992412174380501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512041078661608116253667 9768061617992412174380501)
                  ·
                    refine ⟨228938944171697160337043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9768061617992412174380501 228938944171697160337043)
                    ·
                      rfl

theorem cell23_1337571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 7].length) (baseStart_1337571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337571 prefixEnd_1337571 := by exact prefixLift 1337571
  have htrace : WordTrace (prefixWord ++ tailWord_1337571) baseStart_1337571 baseEnd_1337571 := by
    simpa [prefixWord, tailWord_1337571, baseEnd_1337571] using wordTrace_append hprefix tailTrace_1337571
  have hstable : (prefixWord ++ tailWord_1337571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337571).length < 2 ^ (prefixWord ++ tailWord_1337571).sum := by decide
  have hdescent : baseEnd_1337571 < baseStart_1337571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337587 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6]
def baseStart_1337587 : Nat := 118140960795 + 1337587 * 2 ^ 59
def prefixEnd_1337587 : Nat := 4983230072969 + 3 ^ 40 * 1337587 * 2
def baseEnd_1337587 : Nat := 686825048205563418411055

theorem tailTrace_1337587 : CollatzResearch.WordTrace tailWord_1337587 prefixEnd_1337587 686825048205563418411055 := by
  unfold tailWord_1337587
  simp only [CollatzResearch.WordTrace]
  refine ⟨48785805805158215517539015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32523870536772143678359343 48785805805158215517539015)
  ·
    refine ⟨73178708707737323276308523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48785805805158215517539015 73178708707737323276308523)
    ·
      refine ⟨109768063061605984914462785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73178708707737323276308523 109768063061605984914462785)
      ·
        refine ⟨82326047296204488685847089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109768063061605984914462785 82326047296204488685847089)
        ·
          refine ⟨61744535472153366514385317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82326047296204488685847089 61744535472153366514385317)
          ·
            refine ⟨11577100401028756221447247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61744535472153366514385317 11577100401028756221447247)
            ·
              refine ⟨17365650601543134332170871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11577100401028756221447247 17365650601543134332170871)
              ·
                refine ⟨26048475902314701498256307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17365650601543134332170871 26048475902314701498256307)
                ·
                  refine ⟨39072713853472052247384461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26048475902314701498256307 39072713853472052247384461)
                  ·
                    refine ⟨14652267695052019592769173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39072713853472052247384461 14652267695052019592769173)
                    ·
                      refine ⟨686825048205563418411055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14652267695052019592769173 686825048205563418411055)
                      ·
                        rfl

theorem cell23_1337587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_1337587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337587 prefixEnd_1337587 := by exact prefixLift 1337587
  have htrace : WordTrace (prefixWord ++ tailWord_1337587) baseStart_1337587 baseEnd_1337587 := by
    simpa [prefixWord, tailWord_1337587, baseEnd_1337587] using wordTrace_append hprefix tailTrace_1337587
  have hstable : (prefixWord ++ tailWord_1337587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337587).length < 2 ^ (prefixWord ++ tailWord_1337587).sum := by decide
  have hdescent : baseEnd_1337587 < baseStart_1337587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337601 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1337601 : Nat := 118140960795 + 1337601 * 2 ^ 59
def prefixEnd_1337601 : Nat := 4983230072969 + 3 ^ 40 * 1337601 * 2
def baseEnd_1337601 : Nat := 228944078978242121211997

theorem tailTrace_1337601 : CollatzResearch.WordTrace tailWord_1337601 prefixEnd_1337601 228944078978242121211997 := by
  unfold tailWord_1337601
  simp only [CollatzResearch.WordTrace]
  refine ⟨48786316427107495908548657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32524210951404997272365771 48786316427107495908548657)
  ·
    refine ⟨36589737320330621931411493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48786316427107495908548657 36589737320330621931411493)
    ·
      refine ⟨6860575747561991612139655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36589737320330621931411493 6860575747561991612139655)
      ·
        refine ⟨10290863621342987418209483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6860575747561991612139655 10290863621342987418209483)
        ·
          refine ⟨15436295432014481127314225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290863621342987418209483 15436295432014481127314225)
          ·
            refine ⟨11577221574010860845485669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15436295432014481127314225 11577221574010860845485669)
            ·
              refine ⟨2170729045127036408528563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11577221574010860845485669 2170729045127036408528563)
              ·
                refine ⟨3256093567690554612792845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170729045127036408528563 3256093567690554612792845)
                ·
                  refine ⟨1221035087883957979797317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3256093567690554612792845 1221035087883957979797317)
                  ·
                    refine ⟨228944078978242121211997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221035087883957979797317 228944078978242121211997)
                    ·
                      rfl

theorem cell23_1337601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1337601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337601 prefixEnd_1337601 := by exact prefixLift 1337601
  have htrace : WordTrace (prefixWord ++ tailWord_1337601) baseStart_1337601 baseEnd_1337601 := by
    simpa [prefixWord, tailWord_1337601, baseEnd_1337601] using wordTrace_append hprefix tailTrace_1337601
  have hstable : (prefixWord ++ tailWord_1337601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337601).length < 2 ^ (prefixWord ++ tailWord_1337601).sum := by decide
  have hdescent : baseEnd_1337601 < baseStart_1337601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337624 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1337624 : Nat := 118140960795 + 1337624 * 2 ^ 59
def prefixEnd_1337624 : Nat := 4983230072969 + 3 ^ 40 * 1337624 * 2
def baseEnd_1337624 : Nat := 686844046989779773648385

theorem tailTrace_1337624 : CollatzResearch.WordTrace tailWord_1337624 prefixEnd_1337624 686844046989779773648385 := by
  unfold tailWord_1337624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24393577653012085418317963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32524770204016113891090617 24393577653012085418317963)
  ·
    refine ⟨36590366479518128127476945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24393577653012085418317963 36590366479518128127476945)
    ·
      refine ⟨27442774859638596095607709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36590366479518128127476945 27442774859638596095607709)
      ·
        refine ⟨10291040572364473535852891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27442774859638596095607709 10291040572364473535852891)
        ·
          refine ⟨15436560858546710303779337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10291040572364473535852891 15436560858546710303779337)
          ·
            refine ⟨11577420643910032727834503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15436560858546710303779337 11577420643910032727834503)
            ·
              refine ⟨17366130965865049091751755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11577420643910032727834503 17366130965865049091751755)
              ·
                refine ⟨26049196448797573637627633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17366130965865049091751755 26049196448797573637627633)
                ·
                  refine ⟨19536897336598180228220725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26049196448797573637627633 19536897336598180228220725)
                  ·
                    refine ⟨1831584125306079396395693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19536897336598180228220725 1831584125306079396395693)
                    ·
                      refine ⟨686844046989779773648385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1831584125306079396395693 686844046989779773648385)
                      ·
                        rfl

theorem cell23_1337624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1337624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337624 prefixEnd_1337624 := by exact prefixLift 1337624
  have htrace : WordTrace (prefixWord ++ tailWord_1337624) baseStart_1337624 baseEnd_1337624 := by
    simpa [prefixWord, tailWord_1337624, baseEnd_1337624] using wordTrace_append hprefix tailTrace_1337624
  have hstable : (prefixWord ++ tailWord_1337624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337624).length < 2 ^ (prefixWord ++ tailWord_1337624).sum := by decide
  have hdescent : baseEnd_1337624 < baseStart_1337624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337645 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1337645 : Nat := 118140960795 + 1337645 * 2 ^ 59
def prefixEnd_1337645 : Nat := 4983230072969 + 3 ^ 40 * 1337645 * 2
def baseEnd_1337645 : Nat := 686854830083524191485789

theorem tailTrace_1337645 : CollatzResearch.WordTrace tailWord_1337645 prefixEnd_1337645 686854830083524191485789 := by
  unfold tailWord_1337645
  simp only [CollatzResearch.WordTrace]
  refine ⟨48787921238948091423150389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32525280825965394282100259 48787921238948091423150389)
  ·
    refine ⟨4573867616151383570920349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48787921238948091423150389 4573867616151383570920349)
    ·
      refine ⟨1715200356056768839095131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4573867616151383570920349 1715200356056768839095131)
      ·
        refine ⟨2572800534085153258642697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715200356056768839095131 2572800534085153258642697)
        ·
          refine ⟨1929600400563864943982023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2572800534085153258642697 1929600400563864943982023)
          ·
            refine ⟨2894400600845797415973035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929600400563864943982023 2894400600845797415973035)
            ·
              refine ⟨4341600901268696123959553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894400600845797415973035 4341600901268696123959553)
              ·
                refine ⟨3256200675951522092969665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4341600901268696123959553 3256200675951522092969665)
                ·
                  refine ⟨2442150506963641569727249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3256200675951522092969665 2442150506963641569727249)
                  ·
                    refine ⟨1831612880222731177295437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2442150506963641569727249 1831612880222731177295437)
                    ·
                      refine ⟨686854830083524191485789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1831612880222731177295437 686854830083524191485789)
                      ·
                        rfl

theorem cell23_1337645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1337645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337645 prefixEnd_1337645 := by exact prefixLift 1337645
  have htrace : WordTrace (prefixWord ++ tailWord_1337645) baseStart_1337645 baseEnd_1337645 := by
    simpa [prefixWord, tailWord_1337645, baseEnd_1337645] using wordTrace_append hprefix tailTrace_1337645
  have hstable : (prefixWord ++ tailWord_1337645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337645).length < 2 ^ (prefixWord ++ tailWord_1337645).sum := by decide
  have hdescent : baseEnd_1337645 < baseStart_1337645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337652 : List Nat := [2, 5, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1337652 : Nat := 118140960795 + 1337652 * 2 ^ 59
def prefixEnd_1337652 : Nat := 4983230072969 + 3 ^ 40 * 1337652 * 2
def baseEnd_1337652 : Nat := 228952808149368554699419

theorem tailTrace_1337652 : CollatzResearch.WordTrace tailWord_1337652 prefixEnd_1337652 228952808149368554699419 := by
  unfold tailWord_1337652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24394088274961365809327605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32525451033281821079103473 24394088274961365809327605)
  ·
    refine ⟨2286945775777628044624463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24394088274961365809327605 2286945775777628044624463)
    ·
      refine ⟨3430418663666442066936695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2286945775777628044624463 3430418663666442066936695)
      ·
        refine ⟨5145627995499663100405043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3430418663666442066936695 5145627995499663100405043)
        ·
          refine ⟨7718441993249494650607565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5145627995499663100405043 7718441993249494650607565)
          ·
            refine ⟨2894415747468560493977837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7718441993249494650607565 2894415747468560493977837)
            ·
              refine ⟨1085405905300710185241689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2894415747468560493977837 1085405905300710185241689)
              ·
                refine ⟨814054428975532638931267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085405905300710185241689 814054428975532638931267)
                ·
                  refine ⟨1221081643463298958396901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814054428975532638931267 1221081643463298958396901)
                  ·
                    refine ⟨228952808149368554699419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221081643463298958396901 228952808149368554699419)
                    ·
                      rfl

theorem cell23_1337652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1337652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337652 prefixEnd_1337652 := by exact prefixLift 1337652
  have htrace : WordTrace (prefixWord ++ tailWord_1337652) baseStart_1337652 baseEnd_1337652 := by
    simpa [prefixWord, tailWord_1337652, baseEnd_1337652] using wordTrace_append hprefix tailTrace_1337652
  have hstable : (prefixWord ++ tailWord_1337652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337652).length < 2 ^ (prefixWord ++ tailWord_1337652).sum := by decide
  have hdescent : baseEnd_1337652 < baseStart_1337652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337658 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_1337658 : Nat := 118140960795 + 1337658 * 2 ^ 59
def prefixEnd_1337658 : Nat := 4983230072969 + 3 ^ 40 * 1337658 * 2
def baseEnd_1337658 : Nat := 686861505332032640623229

theorem tailTrace_1337658 : CollatzResearch.WordTrace tailWord_1337658 prefixEnd_1337658 686861505332032640623229 := by
  unfold tailWord_1337658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12197098846975248660843407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32525596925267329762249085 12197098846975248660843407)
  ·
    refine ⟨18295648270462872991265111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12197098846975248660843407 18295648270462872991265111)
    ·
      refine ⟨27443472405694309486897667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18295648270462872991265111 27443472405694309486897667)
      ·
        refine ⟨41165208608541464230346501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27443472405694309486897667 41165208608541464230346501)
        ·
          refine ⟨7718476614101524543189969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41165208608541464230346501 7718476614101524543189969)
          ·
            refine ⟨5788857460576143407392477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7718476614101524543189969 5788857460576143407392477)
            ·
              refine ⟨2170821547716053777772179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5788857460576143407392477 2170821547716053777772179)
              ·
                refine ⟨3256232321574080666658269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170821547716053777772179 3256232321574080666658269)
                ·
                  refine ⟨1221087120590280249996851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3256232321574080666658269 1221087120590280249996851)
                  ·
                    refine ⟨1831630680885420374995277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1221087120590280249996851 1831630680885420374995277)
                    ·
                      refine ⟨686861505332032640623229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1831630680885420374995277 686861505332032640623229)
                      ·
                        rfl

theorem cell23_1337658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_1337658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337658 prefixEnd_1337658 := by exact prefixLift 1337658
  have htrace : WordTrace (prefixWord ++ tailWord_1337658) baseStart_1337658 baseEnd_1337658 := by
    simpa [prefixWord, tailWord_1337658, baseEnd_1337658] using wordTrace_append hprefix tailTrace_1337658
  have hstable : (prefixWord ++ tailWord_1337658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337658).length < 2 ^ (prefixWord ++ tailWord_1337658).sum := by decide
  have hdescent : baseEnd_1337658 < baseStart_1337658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337665 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 6]
def baseStart_1337665 : Nat := 118140960795 + 1337665 * 2 ^ 59
def prefixEnd_1337665 : Nat := 4983230072969 + 3 ^ 40 * 1337665 * 2
def baseEnd_1337665 : Nat := 76318344410734901470633

theorem tailTrace_1337665 : CollatzResearch.WordTrace tailWord_1337665 prefixEnd_1337665 76318344410734901470633 := by
  unfold tailWord_1337665
  simp only [CollatzResearch.WordTrace]
  refine ⟨48788650698875634838878449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32525767132583756559252299 48788650698875634838878449)
  ·
    refine ⟨36591488024156726129158837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48788650698875634838878449 36591488024156726129158837)
    ·
      refine ⟨3430452002264693074608641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36591488024156726129158837 3430452002264693074608641)
      ·
        refine ⟨2572839001698519805956481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3430452002264693074608641 2572839001698519805956481)
        ·
          refine ⟨1929629251273889854467361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2572839001698519805956481 1929629251273889854467361)
          ·
            refine ⟨1447221938455417390850521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1929629251273889854467361 1447221938455417390850521)
            ·
              refine ⟨1085416453841563043137891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447221938455417390850521 1085416453841563043137891)
              ·
                refine ⟨1628124680762344564706837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085416453841563043137891 1628124680762344564706837)
                ·
                  refine ⟨76318344410734901470633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1628124680762344564706837 76318344410734901470633)
                  ·
                    rfl

theorem cell23_1337665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 6].length) (baseStart_1337665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337665 prefixEnd_1337665 := by exact prefixLift 1337665
  have htrace : WordTrace (prefixWord ++ tailWord_1337665) baseStart_1337665 baseEnd_1337665 := by
    simpa [prefixWord, tailWord_1337665, baseEnd_1337665] using wordTrace_append hprefix tailTrace_1337665
  have hstable : (prefixWord ++ tailWord_1337665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337665).length < 2 ^ (prefixWord ++ tailWord_1337665).sum := by decide
  have hdescent : baseEnd_1337665 < baseStart_1337665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337681 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_1337681 : Nat := 118140960795 + 1337681 * 2 ^ 59
def prefixEnd_1337681 : Nat := 4983230072969 + 3 ^ 40 * 1337681 * 2
def baseEnd_1337681 : Nat := 686873315387086050635623

theorem tailTrace_1337681 : CollatzResearch.WordTrace tailWord_1337681 prefixEnd_1337681 686873315387086050635623 := by
  unfold tailWord_1337681
  simp only [CollatzResearch.WordTrace]
  refine ⟨48789234266817669571460897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32526156177878446380973931 48789234266817669571460897)
  ·
    refine ⟨36591925700113252178595673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48789234266817669571460897 36591925700113252178595673)
    ·
      refine ⟨27443944275084939133946755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36591925700113252178595673 27443944275084939133946755)
      ·
        refine ⟨41165916412627408700920133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27443944275084939133946755 41165916412627408700920133)
        ·
          refine ⟨7718609327367639131422525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41165916412627408700920133 7718609327367639131422525)
          ·
            refine ⟨2894478497762864674283447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7718609327367639131422525 2894478497762864674283447)
            ·
              refine ⟨4341717746644297011425171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894478497762864674283447 4341717746644297011425171)
              ·
                refine ⟨6512576619966445517137757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341717746644297011425171 6512576619966445517137757)
                ·
                  refine ⟨2442216232487417068926659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6512576619966445517137757 2442216232487417068926659)
                  ·
                    refine ⟨3663324348731125603389989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2442216232487417068926659 3663324348731125603389989)
                    ·
                      refine ⟨686873315387086050635623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3663324348731125603389989 686873315387086050635623)
                      ·
                        rfl

theorem cell23_1337681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_1337681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337681 prefixEnd_1337681 := by exact prefixLift 1337681
  have htrace : WordTrace (prefixWord ++ tailWord_1337681) baseStart_1337681 baseEnd_1337681 := by
    simpa [prefixWord, tailWord_1337681, baseEnd_1337681] using wordTrace_append hprefix tailTrace_1337681
  have hstable : (prefixWord ++ tailWord_1337681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337681).length < 2 ^ (prefixWord ++ tailWord_1337681).sum := by decide
  have hdescent : baseEnd_1337681 < baseStart_1337681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337685 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_1337685 : Nat := 118140960795 + 1337685 * 2 ^ 59
def prefixEnd_1337685 : Nat := 4983230072969 + 3 ^ 40 * 1337685 * 2
def baseEnd_1337685 : Nat := 686875369309704034985605

theorem tailTrace_1337685 : CollatzResearch.WordTrace tailWord_1337685 prefixEnd_1337685 686875369309704034985605 := by
  unfold tailWord_1337685
  simp only [CollatzResearch.WordTrace]
  refine ⟨48789380158803178254606509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32526253439202118836404339 48789380158803178254606509)
  ·
    refine ⟨18296017559551191845477441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48789380158803178254606509 18296017559551191845477441)
    ·
      refine ⟨13722013169663393884108081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18296017559551191845477441 13722013169663393884108081)
      ·
        refine ⟨10291509877247545413081061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13722013169663393884108081 10291509877247545413081061)
        ·
          refine ⟨1929658101983914764952699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10291509877247545413081061 1929658101983914764952699)
          ·
            refine ⟨2894487152975872147429049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929658101983914764952699 2894487152975872147429049)
            ·
              refine ⟨2170865364731904110571787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894487152975872147429049 2170865364731904110571787)
              ·
                refine ⟨3256298047097856165857681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170865364731904110571787 3256298047097856165857681)
                ·
                  refine ⟨2442223535323392124393261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3256298047097856165857681 2442223535323392124393261)
                  ·
                    refine ⟨915833825746272046647473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442223535323392124393261 915833825746272046647473)
                    ·
                      refine ⟨686875369309704034985605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915833825746272046647473 686875369309704034985605)
                      ·
                        rfl

theorem cell23_1337685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_1337685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337685 prefixEnd_1337685 := by exact prefixLift 1337685
  have htrace : WordTrace (prefixWord ++ tailWord_1337685) baseStart_1337685 baseEnd_1337685 := by
    simpa [prefixWord, tailWord_1337685, baseEnd_1337685] using wordTrace_append hprefix tailTrace_1337685
  have hstable : (prefixWord ++ tailWord_1337685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337685).length < 2 ^ (prefixWord ++ tailWord_1337685).sum := by decide
  have hdescent : baseEnd_1337685 < baseStart_1337685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337701 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1337701 : Nat := 118140960795 + 1337701 * 2 ^ 59
def prefixEnd_1337701 : Nat := 4983230072969 + 3 ^ 40 * 1337701 * 2
def baseEnd_1337701 : Nat := 686883585000175972385531

theorem tailTrace_1337701 : CollatzResearch.WordTrace tailWord_1337701 prefixEnd_1337701 686883585000175972385531 := by
  unfold tailWord_1337701
  simp only [CollatzResearch.WordTrace]
  refine ⟨48789963726745212987188957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32526642484496808658125971 48789963726745212987188957)
  ·
    refine ⟨18296236397529454870195859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48789963726745212987188957 18296236397529454870195859)
    ·
      refine ⟨27444354596294182305293789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18296236397529454870195859 27444354596294182305293789)
      ·
        refine ⟨10291632973610318364485171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27444354596294182305293789 10291632973610318364485171)
        ·
          refine ⟨15437449460415477546727757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10291632973610318364485171 15437449460415477546727757)
          ·
            refine ⟨5789043547655804080022909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15437449460415477546727757 5789043547655804080022909)
            ·
              refine ⟨2170891330370926530008591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5789043547655804080022909 2170891330370926530008591)
              ·
                refine ⟨3256336995556389795012887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170891330370926530008591 3256336995556389795012887)
                ·
                  refine ⟨4884505493334584692519331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256336995556389795012887 4884505493334584692519331)
                  ·
                    refine ⟨7326758240001877038778997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4884505493334584692519331 7326758240001877038778997)
                    ·
                      refine ⟨686883585000175972385531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7326758240001877038778997 686883585000175972385531)
                      ·
                        rfl

theorem cell23_1337701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1337701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337701 prefixEnd_1337701 := by exact prefixLift 1337701
  have htrace : WordTrace (prefixWord ++ tailWord_1337701) baseStart_1337701 baseEnd_1337701 := by
    simpa [prefixWord, tailWord_1337701, baseEnd_1337701] using wordTrace_append hprefix tailTrace_1337701
  have hstable : (prefixWord ++ tailWord_1337701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337701).length < 2 ^ (prefixWord ++ tailWord_1337701).sum := by decide
  have hdescent : baseEnd_1337701 < baseStart_1337701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337704 : List Nat := [2, 1, 4, 2, 2, 12]
def baseStart_1337704 : Nat := 118140960795 + 1337704 * 2 ^ 59
def prefixEnd_1337704 : Nat := 4983230072969 + 3 ^ 40 * 1337704 * 2
def baseEnd_1337704 : Nat := 2826687759021150043819

theorem tailTrace_1337704 : CollatzResearch.WordTrace tailWord_1337704 prefixEnd_1337704 2826687759021150043819 := by
  unfold tailWord_1337704
  simp only [CollatzResearch.WordTrace]
  refine ⟨24395036572867172249774083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32526715430489562999698777 24395036572867172249774083)
  ·
    refine ⟨36592554859300758374661125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24395036572867172249774083 36592554859300758374661125)
    ·
      refine ⟨6861104036118892195248961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36592554859300758374661125 6861104036118892195248961)
      ·
        refine ⟨5145828027089169146436721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6861104036118892195248961 5145828027089169146436721)
        ·
          refine ⟨3859371020316876859827541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5145828027089169146436721 3859371020316876859827541)
          ·
            refine ⟨2826687759021150043819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3859371020316876859827541 2826687759021150043819)
            ·
              rfl

theorem cell23_1337704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 12].length) (baseStart_1337704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337704 prefixEnd_1337704 := by exact prefixLift 1337704
  have htrace : WordTrace (prefixWord ++ tailWord_1337704) baseStart_1337704 baseEnd_1337704 := by
    simpa [prefixWord, tailWord_1337704, baseEnd_1337704] using wordTrace_append hprefix tailTrace_1337704
  have hstable : (prefixWord ++ tailWord_1337704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337704).length < 2 ^ (prefixWord ++ tailWord_1337704).sum := by decide
  have hdescent : baseEnd_1337704 < baseStart_1337704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337715 : List Nat := [1, 1, 1, 2, 2, 1, 2, 8, 1, 2, 2]
def baseStart_1337715 : Nat := 118140960795 + 1337715 * 2 ^ 59
def prefixEnd_1337715 : Nat := 4983230072969 + 3 ^ 40 * 1337715 * 2
def baseEnd_1337715 : Nat := 686890773729338917610467

theorem tailTrace_1337715 : CollatzResearch.WordTrace tailWord_1337715 prefixEnd_1337715 686890773729338917610467 := by
  unfold tailWord_1337715
  simp only [CollatzResearch.WordTrace]
  refine ⟨48790474348694493378198599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32526982899129662252132399 48790474348694493378198599)
  ·
    refine ⟨73185711523041740067297899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48790474348694493378198599 73185711523041740067297899)
    ·
      refine ⟨109778567284562610100946849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73185711523041740067297899 109778567284562610100946849)
      ·
        refine ⟨82333925463421957575710137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109778567284562610100946849 82333925463421957575710137)
        ·
          refine ⟨61750444097566468181782603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82333925463421957575710137 61750444097566468181782603)
          ·
            refine ⟨92625666146349702272673905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61750444097566468181782603 92625666146349702272673905)
            ·
              refine ⟨69469249609762276704505429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92625666146349702272673905 69469249609762276704505429)
              ·
                refine ⟨814092768864401680130923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 69469249609762276704505429 814092768864401680130923)
                ·
                  refine ⟨1221139153296602520196385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814092768864401680130923 1221139153296602520196385)
                  ·
                    refine ⟨915854364972451890147289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1221139153296602520196385 915854364972451890147289)
                    ·
                      refine ⟨686890773729338917610467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 915854364972451890147289 686890773729338917610467)
                      ·
                        rfl

theorem cell23_1337715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 2, 2].length) (baseStart_1337715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337715 prefixEnd_1337715 := by exact prefixLift 1337715
  have htrace : WordTrace (prefixWord ++ tailWord_1337715) baseStart_1337715 baseEnd_1337715 := by
    simpa [prefixWord, tailWord_1337715, baseEnd_1337715] using wordTrace_append hprefix tailTrace_1337715
  have hstable : (prefixWord ++ tailWord_1337715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337715).length < 2 ^ (prefixWord ++ tailWord_1337715).sum := by decide
  have hdescent : baseEnd_1337715 < baseStart_1337715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337752 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1337752 : Nat := 118140960795 + 1337752 * 2 ^ 59
def prefixEnd_1337752 : Nat := 4983230072969 + 3 ^ 40 * 1337752 * 2
def baseEnd_1337752 : Nat := 686909772513555272847797

theorem tailTrace_1337752 : CollatzResearch.WordTrace tailWord_1337752 prefixEnd_1337752 686909772513555272847797 := by
  unfold tailWord_1337752
  simp only [CollatzResearch.WordTrace]
  refine ⟨24395911924780224348647755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32527882566373632464863673 24395911924780224348647755)
  ·
    refine ⟨36593867887170336522971633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24395911924780224348647755 36593867887170336522971633)
    ·
      refine ⟨27445400915377752392228725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36593867887170336522971633 27445400915377752392228725)
      ·
        refine ⟨2573006335816664286771443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27445400915377752392228725 2573006335816664286771443)
        ·
          refine ⟨3859509503724996430157165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2573006335816664286771443 3859509503724996430157165)
          ·
            refine ⟨1447316063896873661308937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3859509503724996430157165 1447316063896873661308937)
            ·
              refine ⟨1085487047922655245981703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447316063896873661308937 1085487047922655245981703)
              ·
                refine ⟨1628230571883982868972555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085487047922655245981703 1628230571883982868972555)
                ·
                  refine ⟨2442345857825974303458833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628230571883982868972555 2442345857825974303458833)
                  ·
                    refine ⟨1831759393369480727594125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2442345857825974303458833 1831759393369480727594125)
                    ·
                      refine ⟨686909772513555272847797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1831759393369480727594125 686909772513555272847797)
                      ·
                        rfl

theorem cell23_1337752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1337752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337752 prefixEnd_1337752 := by exact prefixLift 1337752
  have htrace : WordTrace (prefixWord ++ tailWord_1337752) baseStart_1337752 baseEnd_1337752 := by
    simpa [prefixWord, tailWord_1337752, baseEnd_1337752] using wordTrace_append hprefix tailTrace_1337752
  have hstable : (prefixWord ++ tailWord_1337752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337752).length < 2 ^ (prefixWord ++ tailWord_1337752).sum := by decide
  have hdescent : baseEnd_1337752 < baseStart_1337752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337821 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1337821 : Nat := 118140960795 + 1337821 * 2 ^ 59
def prefixEnd_1337821 : Nat := 4983230072969 + 3 ^ 40 * 1337821 * 2
def baseEnd_1337821 : Nat := 686945202678715502884979

theorem tailTrace_1337821 : CollatzResearch.WordTrace tailWord_1337821 prefixEnd_1337821 686945202678715502884979 := by
  unfold tailWord_1337821
  simp only [CollatzResearch.WordTrace]
  refine ⟨48794340486310473481557317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32529560324206982321038211 48794340486310473481557317)
  ·
    refine ⟨9148938841183213777791997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48794340486310473481557317 9148938841183213777791997)
    ·
      refine ⟨3430852065443705166671999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9148938841183213777791997 3430852065443705166671999)
      ·
        refine ⟨5146278098165557750007999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3430852065443705166671999 5146278098165557750007999)
        ·
          refine ⟨7719417147248336625011999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146278098165557750007999 7719417147248336625011999)
          ·
            refine ⟨11579125720872504937517999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7719417147248336625011999 11579125720872504937517999)
            ·
              refine ⟨17368688581308757406276999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11579125720872504937517999 17368688581308757406276999)
              ·
                refine ⟨26053032871963136109415499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17368688581308757406276999 26053032871963136109415499)
                ·
                  refine ⟨39079549307944704164123249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26053032871963136109415499 39079549307944704164123249)
                  ·
                    refine ⟨29309661980958528123092437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39079549307944704164123249 29309661980958528123092437)
                    ·
                      refine ⟨686945202678715502884979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29309661980958528123092437 686945202678715502884979)
                      ·
                        rfl

theorem cell23_1337821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1337821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337821 prefixEnd_1337821 := by exact prefixLift 1337821
  have htrace : WordTrace (prefixWord ++ tailWord_1337821) baseStart_1337821 baseEnd_1337821 := by
    simpa [prefixWord, tailWord_1337821, baseEnd_1337821] using wordTrace_append hprefix tailTrace_1337821
  have hstable : (prefixWord ++ tailWord_1337821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337821).length < 2 ^ (prefixWord ++ tailWord_1337821).sum := by decide
  have hdescent : baseEnd_1337821 < baseStart_1337821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337841 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 4, 5]
def baseStart_1337841 : Nat := 118140960795 + 1337841 * 2 ^ 59
def prefixEnd_1337841 : Nat := 4983230072969 + 3 ^ 40 * 1337841 * 2
def baseEnd_1337841 : Nat := 228985157430601808211629

theorem tailTrace_1337841 : CollatzResearch.WordTrace tailWord_1337841 prefixEnd_1337841 228985157430601808211629 := by
  unfold tailWord_1337841
  simp only [CollatzResearch.WordTrace]
  refine ⟨48795069946238016897285377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32530046630825344598190251 48795069946238016897285377)
  ·
    refine ⟨36596302459678512672964033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48795069946238016897285377 36596302459678512672964033)
    ·
      refine ⟨27447226844758884504723025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36596302459678512672964033 27447226844758884504723025)
      ·
        refine ⟨20585420133569163378542269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27447226844758884504723025 20585420133569163378542269)
        ·
          refine ⟨7719532550088436266953351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20585420133569163378542269 7719532550088436266953351)
          ·
            refine ⟨11579298825132654400430027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7719532550088436266953351 11579298825132654400430027)
            ·
              refine ⟨17368948237698981600645041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11579298825132654400430027 17368948237698981600645041)
              ·
                refine ⟨13026711178274236200483781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17368948237698981600645041 13026711178274236200483781)
                ·
                  refine ⟨2442508345926419287590709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13026711178274236200483781 2442508345926419287590709)
                  ·
                    refine ⟨228985157430601808211629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2442508345926419287590709 228985157430601808211629)
                    ·
                      rfl

theorem cell23_1337841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_1337841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337841 prefixEnd_1337841 := by exact prefixLift 1337841
  have htrace : WordTrace (prefixWord ++ tailWord_1337841) baseStart_1337841 baseEnd_1337841 := by
    simpa [prefixWord, tailWord_1337841, baseEnd_1337841] using wordTrace_append hprefix tailTrace_1337841
  have hstable : (prefixWord ++ tailWord_1337841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337841).length < 2 ^ (prefixWord ++ tailWord_1337841).sum := by decide
  have hdescent : baseEnd_1337841 < baseStart_1337841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337861 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_1337861 : Nat := 118140960795 + 1337861 * 2 ^ 59
def prefixEnd_1337861 : Nat := 4983230072969 + 3 ^ 40 * 1337861 * 2
def baseEnd_1337861 : Nat := 686965741904895346384795

theorem tailTrace_1337861 : CollatzResearch.WordTrace tailWord_1337861 prefixEnd_1337861 686965741904895346384795 := by
  unfold tailWord_1337861
  simp only [CollatzResearch.WordTrace]
  refine ⟨48795799406165560313013437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32530532937443706875342291 48795799406165560313013437)
  ·
    refine ⟨18298424777312085117380039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48795799406165560313013437 18298424777312085117380039)
    ·
      refine ⟨27447637165968127676070059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18298424777312085117380039 27447637165968127676070059)
      ·
        refine ⟨41171455748952191514105089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27447637165968127676070059 41171455748952191514105089)
        ·
          refine ⟨30878591811714143635578817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41171455748952191514105089 30878591811714143635578817)
          ·
            refine ⟨23158943858785607726684113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30878591811714143635578817 23158943858785607726684113)
            ·
              refine ⟨17369207894089205795013085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23158943858785607726684113 17369207894089205795013085)
              ·
                refine ⟨6513452960283452173129907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17369207894089205795013085 6513452960283452173129907)
                ·
                  refine ⟨9770179440425178259694861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6513452960283452173129907 9770179440425178259694861)
                  ·
                    refine ⟨3663817290159441847385573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9770179440425178259694861 3663817290159441847385573)
                    ·
                      refine ⟨686965741904895346384795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3663817290159441847385573 686965741904895346384795)
                      ·
                        rfl

theorem cell23_1337861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_1337861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337861 prefixEnd_1337861 := by exact prefixLift 1337861
  have htrace : WordTrace (prefixWord ++ tailWord_1337861) baseStart_1337861 baseEnd_1337861 := by
    simpa [prefixWord, tailWord_1337861, baseEnd_1337861] using wordTrace_append hprefix tailTrace_1337861
  have hstable : (prefixWord ++ tailWord_1337861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337861).length < 2 ^ (prefixWord ++ tailWord_1337861).sum := by decide
  have hdescent : baseEnd_1337861 < baseStart_1337861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337879 : List Nat := [1, 1, 3, 6, 1, 2, 2, 2, 5]
def baseStart_1337879 : Nat := 118140960795 + 1337879 * 2 ^ 59
def prefixEnd_1337879 : Nat := 4983230072969 + 3 ^ 40 * 1337879 * 2
def baseEnd_1337879 : Nat := 76330553839630697328857

theorem tailTrace_1337879 : CollatzResearch.WordTrace tailWord_1337879 prefixEnd_1337879 76330553839630697328857 := by
  unfold tailWord_1337879
  simp only [CollatzResearch.WordTrace]
  refine ⟨48796455920100349387168691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32530970613400232924779127 48796455920100349387168691)
  ·
    refine ⟨73194683880150524080753037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48796455920100349387168691 73194683880150524080753037)
    ·
      refine ⟨27448006455056446530282389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73194683880150524080753037 27448006455056446530282389)
      ·
        refine ⟨1286625302580770931106987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27448006455056446530282389 1286625302580770931106987)
        ·
          refine ⟨1929937953871156396660481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286625302580770931106987 1929937953871156396660481)
          ·
            refine ⟨1447453465403367297495361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1929937953871156396660481 1447453465403367297495361)
            ·
              refine ⟨1085590099052525473121521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447453465403367297495361 1085590099052525473121521)
              ·
                refine ⟨814192574289394104841141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085590099052525473121521 814192574289394104841141)
                ·
                  refine ⟨76330553839630697328857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 814192574289394104841141 76330553839630697328857)
                  ·
                    rfl

theorem cell23_1337879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 5].length) (baseStart_1337879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337879 prefixEnd_1337879 := by exact prefixLift 1337879
  have htrace : WordTrace (prefixWord ++ tailWord_1337879) baseStart_1337879 baseEnd_1337879 := by
    simpa [prefixWord, tailWord_1337879, baseEnd_1337879] using wordTrace_append hprefix tailTrace_1337879
  have hstable : (prefixWord ++ tailWord_1337879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337879).length < 2 ^ (prefixWord ++ tailWord_1337879).sum := by decide
  have hdescent : baseEnd_1337879 < baseStart_1337879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337965 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1337965 : Nat := 118140960795 + 1337965 * 2 ^ 59
def prefixEnd_1337965 : Nat := 4983230072969 + 3 ^ 40 * 1337965 * 2
def baseEnd_1337965 : Nat := 229006381297654313161439

theorem tailTrace_1337965 : CollatzResearch.WordTrace tailWord_1337965 prefixEnd_1337965 229006381297654313161439 := by
  unfold tailWord_1337965
  simp only [CollatzResearch.WordTrace]
  refine ⟨48799592597788786074799349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32533061731859190716532899 48799592597788786074799349)
  ·
    refine ⟨4574961806042698694512439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48799592597788786074799349 4574961806042698694512439)
    ·
      refine ⟨6862442709064048041768659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574961806042698694512439 6862442709064048041768659)
      ·
        refine ⟨10293664063596072062652989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6862442709064048041768659 10293664063596072062652989)
        ·
          refine ⟨3860124023848527023494871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10293664063596072062652989 3860124023848527023494871)
          ·
            refine ⟨5790186035772790535242307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860124023848527023494871 5790186035772790535242307)
            ·
              refine ⟨8685279053659185802863461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790186035772790535242307 8685279053659185802863461)
              ·
                refine ⟨1628489822561097338036899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8685279053659185802863461 1628489822561097338036899)
                ·
                  refine ⟨2442734733841646007055349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628489822561097338036899 2442734733841646007055349)
                  ·
                    refine ⟨229006381297654313161439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2442734733841646007055349 229006381297654313161439)
                    ·
                      rfl

theorem cell23_1337965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1337965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337965 prefixEnd_1337965 := by exact prefixLift 1337965
  have htrace : WordTrace (prefixWord ++ tailWord_1337965) baseStart_1337965 baseEnd_1337965 := by
    simpa [prefixWord, tailWord_1337965, baseEnd_1337965] using wordTrace_append hprefix tailTrace_1337965
  have hstable : (prefixWord ++ tailWord_1337965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337965).length < 2 ^ (prefixWord ++ tailWord_1337965).sum := by decide
  have hdescent : baseEnd_1337965 < baseStart_1337965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337985 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1337985 : Nat := 118140960795 + 1337985 * 2 ^ 59
def prefixEnd_1337985 : Nat := 4983230072969 + 3 ^ 40 * 1337985 * 2
def baseEnd_1337985 : Nat := 687029413506052861234225

theorem tailTrace_1337985 : CollatzResearch.WordTrace tailWord_1337985 prefixEnd_1337985 687029413506052861234225 := by
  unfold tailWord_1337985
  simp only [CollatzResearch.WordTrace]
  refine ⟨48800322057716329490527409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32533548038477552993684939 48800322057716329490527409)
  ·
    refine ⟨36600241543287247117895557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48800322057716329490527409 36600241543287247117895557)
    ·
      refine ⟨6862545289366358834605417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36600241543287247117895557 6862545289366358834605417)
      ·
        refine ⟨5146908967024769125954063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862545289366358834605417 5146908967024769125954063)
        ·
          refine ⟨7720363450537153688931095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146908967024769125954063 7720363450537153688931095)
          ·
            refine ⟨11580545175805730533396643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720363450537153688931095 11580545175805730533396643)
            ·
              refine ⟨17370817763708595800094965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11580545175805730533396643 17370817763708595800094965)
              ·
                refine ⟨1628514165347680856258903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17370817763708595800094965 1628514165347680856258903)
                ·
                  refine ⟨2442771248021521284388355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628514165347680856258903 2442771248021521284388355)
                  ·
                    refine ⟨3664156872032281926582533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2442771248021521284388355 3664156872032281926582533)
                    ·
                      refine ⟨687029413506052861234225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3664156872032281926582533 687029413506052861234225)
                      ·
                        rfl

theorem cell23_1337985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1337985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337985 prefixEnd_1337985 := by exact prefixLift 1337985
  have htrace : WordTrace (prefixWord ++ tailWord_1337985) baseStart_1337985 baseEnd_1337985 := by
    simpa [prefixWord, tailWord_1337985, baseEnd_1337985] using wordTrace_append hprefix tailTrace_1337985
  have hstable : (prefixWord ++ tailWord_1337985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337985).length < 2 ^ (prefixWord ++ tailWord_1337985).sum := by decide
  have hdescent : baseEnd_1337985 < baseStart_1337985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337998 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1337998 : Nat := 118140960795 + 1337998 * 2 ^ 59
def prefixEnd_1337998 : Nat := 4983230072969 + 3 ^ 40 * 1337998 * 2
def baseEnd_1337998 : Nat := 687036088754561310371665

theorem tailTrace_1337998 : CollatzResearch.WordTrace tailWord_1337998 prefixEnd_1337998 687036088754561310371665 := by
  unfold tailWord_1337998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100099525833654088843831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32533864137779488473833765 6100099525833654088843831)
  ·
    refine ⟨9150149288750481133265747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6100099525833654088843831 9150149288750481133265747)
    ·
      refine ⟨13725223933125721699898621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9150149288750481133265747 13725223933125721699898621)
      ·
        refine ⟨5146958974922145637461983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13725223933125721699898621 5146958974922145637461983)
        ·
          refine ⟨7720438462383218456192975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146958974922145637461983 7720438462383218456192975)
          ·
            refine ⟨11580657693574827684289463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720438462383218456192975 11580657693574827684289463)
            ·
              refine ⟨17370986540362241526434195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11580657693574827684289463 17370986540362241526434195)
              ·
                refine ⟨26056479810543362289651293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17370986540362241526434195 26056479810543362289651293)
                ·
                  refine ⟨9771179928953760858619235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26056479810543362289651293 9771179928953760858619235)
                  ·
                    refine ⟨14656769893430641287928853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9771179928953760858619235 14656769893430641287928853)
                    ·
                      refine ⟨687036088754561310371665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14656769893430641287928853 687036088754561310371665)
                      ·
                        rfl

theorem cell23_1337998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1337998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1337998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1337998 prefixEnd_1337998 := by exact prefixLift 1337998
  have htrace : WordTrace (prefixWord ++ tailWord_1337998) baseStart_1337998 baseEnd_1337998 := by
    simpa [prefixWord, tailWord_1337998, baseEnd_1337998] using wordTrace_append hprefix tailTrace_1337998
  have hstable : (prefixWord ++ tailWord_1337998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337998).length < 2 ^ (prefixWord ++ tailWord_1337998).sum := by decide
  have hdescent : baseEnd_1337998 < baseStart_1337998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338008 : List Nat := [2, 1, 2, 4, 1, 1, 4, 8]
def baseStart_1338008 : Nat := 118140960795 + 1338008 * 2 ^ 59
def prefixEnd_1338008 : Nat := 4983230072969 + 3 ^ 40 * 1338008 * 2
def baseEnd_1338008 : Nat := 25445971243003935972097

theorem tailTrace_1338008 : CollatzResearch.WordTrace tailWord_1338008 prefixEnd_1338008 25445971243003935972097 := by
  unfold tailWord_1338008
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400580468316502209307339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32534107291088669612409785 24400580468316502209307339)
  ·
    refine ⟨36600870702474753313961009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24400580468316502209307339 36600870702474753313961009)
    ·
      refine ⟨27450653026856064985470757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36600870702474753313961009 27450653026856064985470757)
      ·
        refine ⟨5146997442535512184775767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27450653026856064985470757 5146997442535512184775767)
        ·
          refine ⟨7720496163803268277163651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146997442535512184775767 7720496163803268277163651)
          ·
            refine ⟨11580744245704902415745477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7720496163803268277163651 11580744245704902415745477)
            ·
              refine ⟨2171389546069669202952277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11580744245704902415745477 2171389546069669202952277)
              ·
                refine ⟨25445971243003935972097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2171389546069669202952277 25445971243003935972097)
                ·
                  rfl

theorem cell23_1338008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 8].length) (baseStart_1338008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338008 prefixEnd_1338008 := by exact prefixLift 1338008
  have htrace : WordTrace (prefixWord ++ tailWord_1338008) baseStart_1338008 baseEnd_1338008 := by
    simpa [prefixWord, tailWord_1338008, baseEnd_1338008] using wordTrace_append hprefix tailTrace_1338008
  have hstable : (prefixWord ++ tailWord_1338008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338008).length < 2 ^ (prefixWord ++ tailWord_1338008).sum := by decide
  have hdescent : baseEnd_1338008 < baseStart_1338008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338011 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8]
def baseStart_1338011 : Nat := 118140960795 + 1338011 * 2 ^ 59
def prefixEnd_1338011 : Nat := 4983230072969 + 3 ^ 40 * 1338011 * 2
def baseEnd_1338011 : Nat := 687042764003069759509105

theorem tailTrace_1338011 : CollatzResearch.WordTrace tailWord_1338011 prefixEnd_1338011 687042764003069759509105 := by
  unfold tailWord_1338011
  simp only [CollatzResearch.WordTrace]
  refine ⟨48801270355622135930973887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32534180237081423953982591 48801270355622135930973887)
  ·
    refine ⟨73201905533433203896460831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48801270355622135930973887 73201905533433203896460831)
    ·
      refine ⟨109802858300149805844691247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73201905533433203896460831 109802858300149805844691247)
      ·
        refine ⟨164704287450224708767036871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109802858300149805844691247 164704287450224708767036871)
        ·
          refine ⟨247056431175337063150555307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164704287450224708767036871 247056431175337063150555307)
          ·
            refine ⟨370584646763005594725832961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247056431175337063150555307 370584646763005594725832961)
            ·
              refine ⟨277938485072254196044374721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370584646763005594725832961 277938485072254196044374721)
              ·
                refine ⟨208453863804190647033281041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277938485072254196044374721 208453863804190647033281041)
                ·
                  refine ⟨156340397853142985274960781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208453863804190647033281041 156340397853142985274960781)
                  ·
                    refine ⟨58627649194928619478110293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156340397853142985274960781 58627649194928619478110293)
                    ·
                      refine ⟨687042764003069759509105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58627649194928619478110293 687042764003069759509105)
                      ·
                        rfl

theorem cell23_1338011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_1338011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338011 prefixEnd_1338011 := by exact prefixLift 1338011
  have htrace : WordTrace (prefixWord ++ tailWord_1338011) baseStart_1338011 baseEnd_1338011 := by
    simpa [prefixWord, tailWord_1338011, baseEnd_1338011] using wordTrace_append hprefix tailTrace_1338011
  have hstable : (prefixWord ++ tailWord_1338011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338011).length < 2 ^ (prefixWord ++ tailWord_1338011).sum := by decide
  have hdescent : baseEnd_1338011 < baseStart_1338011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338012 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1338012 : Nat := 118140960795 + 1338012 * 2 ^ 59
def prefixEnd_1338012 : Nat := 4983230072969 + 3 ^ 40 * 1338012 * 2
def baseEnd_1338012 : Nat := 229014425827908085198867

theorem tailTrace_1338012 : CollatzResearch.WordTrace tailWord_1338012 prefixEnd_1338012 229014425827908085198867 := by
  unfold tailWord_1338012
  simp only [CollatzResearch.WordTrace]
  refine ⟨24400653414309256550880145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32534204552412342067840193 24400653414309256550880145)
  ·
    refine ⟨18300490060731942413160109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24400653414309256550880145 18300490060731942413160109)
    ·
      refine ⟨6862683772774478404935041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18300490060731942413160109 6862683772774478404935041)
      ·
        refine ⟨5147012829580858803701281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862683772774478404935041 5147012829580858803701281)
        ·
          refine ⟨3860259622185644102775961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5147012829580858803701281 3860259622185644102775961)
          ·
            refine ⟨2895194716639233077081971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3860259622185644102775961 2895194716639233077081971)
            ·
              refine ⟨4342792074958849615622957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895194716639233077081971 4342792074958849615622957)
              ·
                refine ⟨1628547028109568605858609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4342792074958849615622957 1628547028109568605858609)
                ·
                  refine ⟨1221410271082176454393957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1628547028109568605858609 1221410271082176454393957)
                  ·
                    refine ⟨229014425827908085198867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221410271082176454393957 229014425827908085198867)
                    ·
                      rfl

theorem cell23_1338012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1338012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338012 prefixEnd_1338012 := by exact prefixLift 1338012
  have htrace : WordTrace (prefixWord ++ tailWord_1338012) baseStart_1338012 baseEnd_1338012 := by
    simpa [prefixWord, tailWord_1338012, baseEnd_1338012] using wordTrace_append hprefix tailTrace_1338012
  have hstable : (prefixWord ++ tailWord_1338012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338012).length < 2 ^ (prefixWord ++ tailWord_1338012).sum := by decide
  have hdescent : baseEnd_1338012 < baseStart_1338012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338035 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 3]
def baseStart_1338035 : Nat := 118140960795 + 1338035 * 2 ^ 59
def prefixEnd_1338035 : Nat := 4983230072969 + 3 ^ 40 * 1338035 * 2
def baseEnd_1338035 : Nat := 687055087538777665608995

theorem tailTrace_1338035 : CollatzResearch.WordTrace tailWord_1338035 prefixEnd_1338035 687055087538777665608995 := by
  unfold tailWord_1338035
  simp only [CollatzResearch.WordTrace]
  refine ⟨48802145707535188029847559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32534763805023458686565039 48802145707535188029847559)
  ·
    refine ⟨73203218561302782044771339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48802145707535188029847559 73203218561302782044771339)
    ·
      refine ⟨109804827841954173067157009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73203218561302782044771339 109804827841954173067157009)
      ·
        refine ⟨82353620881465629800367757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109804827841954173067157009 82353620881465629800367757)
        ·
          refine ⟨30882607830549611175137909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82353620881465629800367757 30882607830549611175137909)
          ·
            refine ⟨2895244484114026047669179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30882607830549611175137909 2895244484114026047669179)
            ·
              refine ⟨4342866726171039071503769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895244484114026047669179 4342866726171039071503769)
              ·
                refine ⟨3257150044628279303627827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4342866726171039071503769 3257150044628279303627827)
                ·
                  refine ⟨4885725066942418955441741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257150044628279303627827 4885725066942418955441741)
                  ·
                    refine ⟨1832146900103407108290653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4885725066942418955441741 1832146900103407108290653)
                    ·
                      refine ⟨687055087538777665608995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832146900103407108290653 687055087538777665608995)
                      ·
                        rfl

theorem cell23_1338035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_1338035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338035 prefixEnd_1338035 := by exact prefixLift 1338035
  have htrace : WordTrace (prefixWord ++ tailWord_1338035) baseStart_1338035 baseEnd_1338035 := by
    simpa [prefixWord, tailWord_1338035, baseEnd_1338035] using wordTrace_append hprefix tailTrace_1338035
  have hstable : (prefixWord ++ tailWord_1338035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338035).length < 2 ^ (prefixWord ++ tailWord_1338035).sum := by decide
  have hdescent : baseEnd_1338035 < baseStart_1338035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338039 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 1, 2, 3]
def baseStart_1338039 : Nat := 118140960795 + 1338039 * 2 ^ 59
def prefixEnd_1338039 : Nat := 4983230072969 + 3 ^ 40 * 1338039 * 2
def baseEnd_1338039 : Nat := 687057141461395649958977

theorem tailTrace_1338039 : CollatzResearch.WordTrace tailWord_1338039 prefixEnd_1338039 687057141461395649958977 := by
  unfold tailWord_1338039
  simp only [CollatzResearch.WordTrace]
  refine ⟨48802291599520696712993171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32534861066347131141995447 48802291599520696712993171)
  ·
    refine ⟨73203437399281045069489757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48802291599520696712993171 73203437399281045069489757)
    ·
      refine ⟨27451289024730391901058659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73203437399281045069489757 27451289024730391901058659)
      ·
        refine ⟨41176933537095587851587989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27451289024730391901058659 41176933537095587851587989)
        ·
          refine ⟨1930168759551355680543187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41176933537095587851587989 1930168759551355680543187)
          ·
            refine ⟨2895253139327033520814781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930168759551355680543187 2895253139327033520814781)
            ·
              refine ⟨1085719927247637570305543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2895253139327033520814781 1085719927247637570305543)
              ·
                refine ⟨1628579890871456355458315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085719927247637570305543 1628579890871456355458315)
                ·
                  refine ⟨2442869836307184533187473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1628579890871456355458315 2442869836307184533187473)
                  ·
                    refine ⟨1832152377230388399890605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2442869836307184533187473 1832152377230388399890605)
                    ·
                      refine ⟨687057141461395649958977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832152377230388399890605 687057141461395649958977)
                      ·
                        rfl

theorem cell23_1338039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_1338039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338039 prefixEnd_1338039 := by exact prefixLift 1338039
  have htrace : WordTrace (prefixWord ++ tailWord_1338039) baseStart_1338039 baseEnd_1338039 := by
    simpa [prefixWord, tailWord_1338039, baseEnd_1338039] using wordTrace_append hprefix tailTrace_1338039
  have hstable : (prefixWord ++ tailWord_1338039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338039).length < 2 ^ (prefixWord ++ tailWord_1338039).sum := by decide
  have hdescent : baseEnd_1338039 < baseStart_1338039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338062 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_1338062 : Nat := 118140960795 + 1338062 * 2 ^ 59
def prefixEnd_1338062 : Nat := 4983230072969 + 3 ^ 40 * 1338062 * 2
def baseEnd_1338062 : Nat := 687068951516449059971371

theorem tailTrace_1338062 : CollatzResearch.WordTrace tailWord_1338062 prefixEnd_1338062 687068951516449059971371 := by
  unfold tailWord_1338062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100391309804671455135055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32535420318958247760720293 6100391309804671455135055)
  ·
    refine ⟨9150586964707007182702583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6100391309804671455135055 9150586964707007182702583)
    ·
      refine ⟨13725880447060510774053875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9150586964707007182702583 13725880447060510774053875)
      ·
        refine ⟨20588820670590766161080813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13725880447060510774053875 20588820670590766161080813)
        ·
          refine ⟨7720807751471537310405305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20588820670590766161080813 7720807751471537310405305)
          ·
            refine ⟨5790605813603652982803979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7720807751471537310405305 5790605813603652982803979)
            ·
              refine ⟨8685908720405479474205969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790605813603652982803979 8685908720405479474205969)
              ·
                refine ⟨6514431540304109605654477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8685908720405479474205969 6514431540304109605654477)
                ·
                  refine ⟨2442911827614041102120429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6514431540304109605654477 2442911827614041102120429)
                  ·
                    refine ⟨916091935355265413295161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2442911827614041102120429 916091935355265413295161)
                    ·
                      refine ⟨687068951516449059971371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916091935355265413295161 687068951516449059971371)
                      ·
                        rfl

theorem cell23_1338062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_1338062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338062 prefixEnd_1338062 := by exact prefixLift 1338062
  have htrace : WordTrace (prefixWord ++ tailWord_1338062) baseStart_1338062 baseEnd_1338062 := by
    simpa [prefixWord, tailWord_1338062, baseEnd_1338062] using wordTrace_append hprefix tailTrace_1338062
  have hstable : (prefixWord ++ tailWord_1338062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338062).length < 2 ^ (prefixWord ++ tailWord_1338062).sum := by decide
  have hdescent : baseEnd_1338062 < baseStart_1338062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338069 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1338069 : Nat := 118140960795 + 1338069 * 2 ^ 59
def prefixEnd_1338069 : Nat := 4983230072969 + 3 ^ 40 * 1338069 * 2
def baseEnd_1338069 : Nat := 687072545881030532583839

theorem tailTrace_1338069 : CollatzResearch.WordTrace tailWord_1338069 prefixEnd_1338069 687072545881030532583839 := by
  unfold tailWord_1338069
  simp only [CollatzResearch.WordTrace]
  refine ⟨48803385789412011836585261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32535590526274674557723507 48803385789412011836585261)
  ·
    refine ⟨18301269671029504438719473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48803385789412011836585261 18301269671029504438719473)
    ·
      refine ⟨13725952253272128329039605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18301269671029504438719473 13725952253272128329039605)
      ·
        refine ⟨1286808023744262030847463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13725952253272128329039605 1286808023744262030847463)
        ·
          refine ⟨1930212035616393046271195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286808023744262030847463 1930212035616393046271195)
          ·
            refine ⟨2895318053424589569406793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930212035616393046271195 2895318053424589569406793)
            ·
              refine ⟨2171488540068442177055095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895318053424589569406793 2171488540068442177055095)
              ·
                refine ⟨3257232810102663265582643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171488540068442177055095 3257232810102663265582643)
                ·
                  refine ⟨4885849215153994898373965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257232810102663265582643 4885849215153994898373965)
                  ·
                    refine ⟨1832193455682748086890237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4885849215153994898373965 1832193455682748086890237)
                    ·
                      refine ⟨687072545881030532583839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832193455682748086890237 687072545881030532583839)
                      ·
                        rfl

theorem cell23_1338069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1338069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338069 prefixEnd_1338069 := by exact prefixLift 1338069
  have htrace : WordTrace (prefixWord ++ tailWord_1338069) baseStart_1338069 baseEnd_1338069 := by
    simpa [prefixWord, tailWord_1338069, baseEnd_1338069] using wordTrace_append hprefix tailTrace_1338069
  have hstable : (prefixWord ++ tailWord_1338069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338069).length < 2 ^ (prefixWord ++ tailWord_1338069).sum := by decide
  have hdescent : baseEnd_1338069 < baseStart_1338069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338092 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 4, 2, 2]
def baseStart_1338092 : Nat := 118140960795 + 1338092 * 2 ^ 59
def prefixEnd_1338092 : Nat := 4983230072969 + 3 ^ 40 * 1338092 * 2
def baseEnd_1338092 : Nat := 687084355936083942596233

theorem tailTrace_1338092 : CollatzResearch.WordTrace tailWord_1338092 prefixEnd_1338092 687084355936083942596233 := by
  unfold tailWord_1338092
  simp only [CollatzResearch.WordTrace]
  refine ⟨24402112334164343382336265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32536149778885791176448353 24402112334164343382336265)
  ·
    refine ⟨18301584250623257536752199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24402112334164343382336265 18301584250623257536752199)
    ·
      refine ⟨27452376375934886305128299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18301584250623257536752199 27452376375934886305128299)
      ·
        refine ⟨41178564563902329457692449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27452376375934886305128299 41178564563902329457692449)
        ·
          refine ⟨30883923422926747093269337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41178564563902329457692449 30883923422926747093269337)
          ·
            refine ⟨23162942567195060319952003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30883923422926747093269337 23162942567195060319952003)
            ·
              refine ⟨34744413850792590479928005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23162942567195060319952003 34744413850792590479928005)
              ·
                refine ⟨6514577597023610714986501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34744413850792590479928005 6514577597023610714986501)
                ·
                  refine ⟨1221483299441927009059969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6514577597023610714986501 1221483299441927009059969)
                  ·
                    refine ⟨916112474581445256794977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1221483299441927009059969 916112474581445256794977)
                    ·
                      refine ⟨687084355936083942596233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916112474581445256794977 687084355936083942596233)
                      ·
                        rfl

theorem cell23_1338092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_1338092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338092 prefixEnd_1338092 := by exact prefixLift 1338092
  have htrace : WordTrace (prefixWord ++ tailWord_1338092) baseStart_1338092 baseEnd_1338092 := by
    simpa [prefixWord, tailWord_1338092, baseEnd_1338092] using wordTrace_append hprefix tailTrace_1338092
  have hstable : (prefixWord ++ tailWord_1338092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338092).length < 2 ^ (prefixWord ++ tailWord_1338092).sum := by decide
  have hdescent : baseEnd_1338092 < baseStart_1338092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338145 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1338145 : Nat := 118140960795 + 1338145 * 2 ^ 59
def prefixEnd_1338145 : Nat := 4983230072969 + 3 ^ 40 * 1338145 * 2
def baseEnd_1338145 : Nat := 229037190136924078411163

theorem tailTrace_1338145 : CollatzResearch.WordTrace tailWord_1338145 prefixEnd_1338145 229037190136924078411163 := by
  unfold tailWord_1338145
  simp only [CollatzResearch.WordTrace]
  refine ⟨48806157737136676816351889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32537438491424451210901259 48806157737136676816351889)
  ·
    refine ⟨36604618302852507612263917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48806157737136676816351889 36604618302852507612263917)
    ·
      refine ⟨13726731863569690354598969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36604618302852507612263917 13726731863569690354598969)
      ·
        refine ⟨10295048897677267765949227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13726731863569690354598969 10295048897677267765949227)
        ·
          refine ⟨15442573346515901648923841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10295048897677267765949227 15442573346515901648923841)
          ·
            refine ⟨11581930009886926236692881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15442573346515901648923841 11581930009886926236692881)
            ·
              refine ⟨8686447507415194677519661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11581930009886926236692881 8686447507415194677519661)
              ·
                refine ⟨3257417815280698004069873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8686447507415194677519661 3257417815280698004069873)
                ·
                  refine ⟨2443063361460523503052405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3257417815280698004069873 2443063361460523503052405)
                  ·
                    refine ⟨229037190136924078411163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2443063361460523503052405 229037190136924078411163)
                    ·
                      rfl

theorem cell23_1338145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1338145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338145 prefixEnd_1338145 := by exact prefixLift 1338145
  have htrace : WordTrace (prefixWord ++ tailWord_1338145) baseStart_1338145 baseEnd_1338145 := by
    simpa [prefixWord, tailWord_1338145, baseEnd_1338145] using wordTrace_append hprefix tailTrace_1338145
  have hstable : (prefixWord ++ tailWord_1338145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338145).length < 2 ^ (prefixWord ++ tailWord_1338145).sum := by decide
  have hdescent : baseEnd_1338145 < baseStart_1338145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338166 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_1338166 : Nat := 118140960795 + 1338166 * 2 ^ 59
def prefixEnd_1338166 : Nat := 4983230072969 + 3 ^ 40 * 1338166 * 2
def baseEnd_1338166 : Nat := 76346928167168517007877

theorem tailTrace_1338166 : CollatzResearch.WordTrace tailWord_1338166 prefixEnd_1338166 76346928167168517007877 := by
  unfold tailWord_1338166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050432729378787337679147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32537949113373731601910901 3050432729378787337679147)
  ·
    refine ⟨4575649094068181006518721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3050432729378787337679147 4575649094068181006518721)
    ·
      refine ⟨3431736820551135754889041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4575649094068181006518721 3431736820551135754889041)
      ·
        refine ⟨2573802615413351816166781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3431736820551135754889041 2573802615413351816166781)
        ·
          refine ⟨965175980780006931062543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2573802615413351816166781 965175980780006931062543)
          ·
            refine ⟨1447763971170010396593815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965175980780006931062543 1447763971170010396593815)
            ·
              refine ⟨2171645956755015594890723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447763971170010396593815 2171645956755015594890723)
              ·
                refine ⟨3257468935132523392336085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171645956755015594890723 3257468935132523392336085)
                ·
                  refine ⟨76346928167168517007877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3257468935132523392336085 76346928167168517007877)
                  ·
                    rfl

theorem cell23_1338166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_1338166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338166 prefixEnd_1338166 := by exact prefixLift 1338166
  have htrace : WordTrace (prefixWord ++ tailWord_1338166) baseStart_1338166 baseEnd_1338166 := by
    simpa [prefixWord, tailWord_1338166, baseEnd_1338166] using wordTrace_append hprefix tailTrace_1338166
  have hstable : (prefixWord ++ tailWord_1338166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338166).length < 2 ^ (prefixWord ++ tailWord_1338166).sum := by decide
  have hdescent : baseEnd_1338166 < baseStart_1338166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338177 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1338177 : Nat := 118140960795 + 1338177 * 2 ^ 59
def prefixEnd_1338177 : Nat := 4983230072969 + 3 ^ 40 * 1338177 * 2
def baseEnd_1338177 : Nat := 687128001791716110033343

theorem tailTrace_1338177 : CollatzResearch.WordTrace tailWord_1338177 prefixEnd_1338177 687128001791716110033343 := by
  unfold tailWord_1338177
  simp only [CollatzResearch.WordTrace]
  refine ⟨48807324873020746281516785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32538216582013830854344523 48807324873020746281516785)
  ·
    refine ⟨36605493654765559711137589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48807324873020746281516785 36605493654765559711137589)
    ·
      refine ⟨3431765030134271222919149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36605493654765559711137589 3431765030134271222919149)
      ·
        refine ⟨1286911886300351708594681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3431765030134271222919149 1286911886300351708594681)
        ·
          refine ⟨965183914725263781446011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1286911886300351708594681 965183914725263781446011)
          ·
            refine ⟨1447775872087895672169017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965183914725263781446011 1447775872087895672169017)
            ·
              refine ⟨1085831904065921754126763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447775872087895672169017 1085831904065921754126763)
              ·
                refine ⟨1628747856098882631190145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085831904065921754126763 1628747856098882631190145)
                ·
                  refine ⟨1221560892074161973392609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1628747856098882631190145 1221560892074161973392609)
                  ·
                    refine ⟨916170669055621480044457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1221560892074161973392609 916170669055621480044457)
                    ·
                      refine ⟨687128001791716110033343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916170669055621480044457 687128001791716110033343)
                      ·
                        rfl

theorem cell23_1338177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1338177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338177 prefixEnd_1338177 := by exact prefixLift 1338177
  have htrace : WordTrace (prefixWord ++ tailWord_1338177) baseStart_1338177 baseEnd_1338177 := by
    simpa [prefixWord, tailWord_1338177, baseEnd_1338177] using wordTrace_append hprefix tailTrace_1338177
  have hstable : (prefixWord ++ tailWord_1338177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338177).length < 2 ^ (prefixWord ++ tailWord_1338177).sum := by decide
  have hdescent : baseEnd_1338177 < baseStart_1338177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338202 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_1338202 : Nat := 118140960795 + 1338202 * 2 ^ 59
def prefixEnd_1338202 : Nat := 4983230072969 + 3 ^ 40 * 1338202 * 2
def baseEnd_1338202 : Nat := 687140838808078512220727

theorem tailTrace_1338202 : CollatzResearch.WordTrace tailWord_1338202 prefixEnd_1338202 687140838808078512220727 := by
  unfold tailWord_1338202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202059174482543887794215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32538824465286783700784573 12202059174482543887794215)
  ·
    refine ⟨18303088761723815831691323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12202059174482543887794215 18303088761723815831691323)
    ·
      refine ⟨27454633142585723747536985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18303088761723815831691323 27454633142585723747536985)
      ·
        refine ⟨20590974856939292810652739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27454633142585723747536985 20590974856939292810652739)
        ·
          refine ⟨30886462285408939215979109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20590974856939292810652739 30886462285408939215979109)
          ·
            refine ⟨5791211678514176102996083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30886462285408939215979109 5791211678514176102996083)
            ·
              refine ⟨8686817517771264154494125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791211678514176102996083 8686817517771264154494125)
              ·
                refine ⟨3257556569164224057935297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8686817517771264154494125 3257556569164224057935297)
                ·
                  refine ⟨2443167426873168043451473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3257556569164224057935297 2443167426873168043451473)
                  ·
                    refine ⟨1832375570154876032588605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2443167426873168043451473 1832375570154876032588605)
                    ·
                      refine ⟨687140838808078512220727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832375570154876032588605 687140838808078512220727)
                      ·
                        rfl

theorem cell23_1338202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_1338202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338202 prefixEnd_1338202 := by exact prefixLift 1338202
  have htrace : WordTrace (prefixWord ++ tailWord_1338202) baseStart_1338202 baseEnd_1338202 := by
    simpa [prefixWord, tailWord_1338202, baseEnd_1338202] using wordTrace_append hprefix tailTrace_1338202
  have hstable : (prefixWord ++ tailWord_1338202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338202).length < 2 ^ (prefixWord ++ tailWord_1338202).sum := by decide
  have hdescent : baseEnd_1338202 < baseStart_1338202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338226 : List Nat := [3, 2, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_1338226 : Nat := 118140960795 + 1338226 * 2 ^ 59
def prefixEnd_1338226 : Nat := 4983230072969 + 3 ^ 40 * 1338226 * 2
def baseEnd_1338226 : Nat := 229051054114595472773539

theorem tailTrace_1338226 : CollatzResearch.WordTrace tailWord_1338226 prefixEnd_1338226 229051054114595472773539 := by
  unfold tailWord_1338226
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202278012460806912512633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32539408033228818433367021 12202278012460806912512633)
  ·
    refine ⟨9151708509345605184384475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12202278012460806912512633 9151708509345605184384475)
    ·
      refine ⟨13727562764018407776576713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9151708509345605184384475 13727562764018407776576713)
      ·
        refine ⟨10295672073013805832432535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13727562764018407776576713 10295672073013805832432535)
        ·
          refine ⟨15443508109520708748648803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10295672073013805832432535 15443508109520708748648803)
          ·
            refine ⟨23165262164281063122973205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15443508109520708748648803 23165262164281063122973205)
            ·
              refine ⟨1085871663950674833889369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23165262164281063122973205 1085871663950674833889369)
              ·
                refine ⟨814403747963006125417027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085871663950674833889369 814403747963006125417027)
                ·
                  refine ⟨1221605621944509188125541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814403747963006125417027 1221605621944509188125541)
                  ·
                    refine ⟨229051054114595472773539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221605621944509188125541 229051054114595472773539)
                    ·
                      rfl

theorem cell23_1338226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_1338226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338226 prefixEnd_1338226 := by exact prefixLift 1338226
  have htrace : WordTrace (prefixWord ++ tailWord_1338226) baseStart_1338226 baseEnd_1338226 := by
    simpa [prefixWord, tailWord_1338226, baseEnd_1338226] using wordTrace_append hprefix tailTrace_1338226
  have hstable : (prefixWord ++ tailWord_1338226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338226).length < 2 ^ (prefixWord ++ tailWord_1338226).sum := by decide
  have hdescent : baseEnd_1338226 < baseStart_1338226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338235 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 3, 5]
def baseStart_1338235 : Nat := 118140960795 + 1338235 * 2 ^ 59
def prefixEnd_1338235 : Nat := 4983230072969 + 3 ^ 40 * 1338235 * 2
def baseEnd_1338235 : Nat := 229052594556558961036025

theorem tailTrace_1338235 : CollatzResearch.WordTrace tailWord_1338235 prefixEnd_1338235 229052594556558961036025 := by
  unfold tailWord_1338235
  simp only [CollatzResearch.WordTrace]
  refine ⟨48809440306810622187128159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32539626871207081458085439 48809440306810622187128159)
  ·
    refine ⟨73214160460215933280692239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48809440306810622187128159 73214160460215933280692239)
    ·
      refine ⟨109821240690323899921038359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73214160460215933280692239 109821240690323899921038359)
      ·
        refine ⟨164731861035485849881557539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109821240690323899921038359 164731861035485849881557539)
        ·
          refine ⟨247097791553228774822336309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164731861035485849881557539 247097791553228774822336309)
          ·
            refine ⟨23165417958115197639594029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247097791553228774822336309 23165417958115197639594029)
            ·
              refine ⟨8687031734293199114847761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23165417958115197639594029 8687031734293199114847761)
              ·
                refine ⟨6515273800719899336135821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8687031734293199114847761 6515273800719899336135821)
                ·
                  refine ⟨2443227675269962251050933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6515273800719899336135821 2443227675269962251050933)
                  ·
                    refine ⟨229052594556558961036025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2443227675269962251050933 229052594556558961036025)
                    ·
                      rfl

theorem cell23_1338235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 5].length) (baseStart_1338235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338235 prefixEnd_1338235 := by exact prefixLift 1338235
  have htrace : WordTrace (prefixWord ++ tailWord_1338235) baseStart_1338235 baseEnd_1338235 := by
    simpa [prefixWord, tailWord_1338235, baseEnd_1338235] using wordTrace_append hprefix tailTrace_1338235
  have hstable : (prefixWord ++ tailWord_1338235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338235).length < 2 ^ (prefixWord ++ tailWord_1338235).sum := by decide
  have hdescent : baseEnd_1338235 < baseStart_1338235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338249 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 3]
def baseStart_1338249 : Nat := 118140960795 + 1338249 * 2 ^ 59
def prefixEnd_1338249 : Nat := 4983230072969 + 3 ^ 40 * 1338249 * 2
def baseEnd_1338249 : Nat := 687164972398839828333011

theorem tailTrace_1338249 : CollatzResearch.WordTrace tailWord_1338249 prefixEnd_1338249 687164972398839828333011 := by
  unfold tailWord_1338249
  simp only [CollatzResearch.WordTrace]
  refine ⟨48809950928759902578137801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32539967285839935052091867 48809950928759902578137801)
  ·
    refine ⟨36607463196569926933603351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48809950928759902578137801 36607463196569926933603351)
    ·
      refine ⟨54911194794854890400405027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36607463196569926933603351 54911194794854890400405027)
      ·
        refine ⟨82366792192282335600607541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54911194794854890400405027 82366792192282335600607541)
        ·
          refine ⟨7721886768026468962556957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82366792192282335600607541 7721886768026468962556957)
          ·
            refine ⟨2895707538009925860958859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7721886768026468962556957 2895707538009925860958859)
            ·
              refine ⟨4343561307014888791438289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895707538009925860958859 4343561307014888791438289)
              ·
                refine ⟨3257670980261166593578717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4343561307014888791438289 3257670980261166593578717)
                ·
                  refine ⟨1221626617597937472592019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3257670980261166593578717 1221626617597937472592019)
                  ·
                    refine ⟨1832439926396906208888029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1221626617597937472592019 1832439926396906208888029)
                    ·
                      refine ⟨687164972398839828333011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832439926396906208888029 687164972398839828333011)
                      ·
                        rfl

theorem cell23_1338249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 3].length) (baseStart_1338249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338249 prefixEnd_1338249 := by exact prefixLift 1338249
  have htrace : WordTrace (prefixWord ++ tailWord_1338249) baseStart_1338249 baseEnd_1338249 := by
    simpa [prefixWord, tailWord_1338249, baseEnd_1338249] using wordTrace_append hprefix tailTrace_1338249
  have hstable : (prefixWord ++ tailWord_1338249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338249).length < 2 ^ (prefixWord ++ tailWord_1338249).sum := by decide
  have hdescent : baseEnd_1338249 < baseStart_1338249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338302 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1338302 : Nat := 118140960795 + 1338302 * 2 ^ 59
def prefixEnd_1338302 : Nat := 4983230072969 + 3 ^ 40 * 1338302 * 2
def baseEnd_1338302 : Nat := 687192186873528120970267

theorem tailTrace_1338302 : CollatzResearch.WordTrace tailWord_1338302 prefixEnd_1338302 687192186873528120970267 := by
  unfold tailWord_1338302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101485499695986578727145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32541255998378595086544773 6101485499695986578727145)
  ·
    refine ⟨4576114124771989934045359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6101485499695986578727145 4576114124771989934045359)
    ·
      refine ⟨6864171187157984901068039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4576114124771989934045359 6864171187157984901068039)
      ·
        refine ⟨10296256780736977351602059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6864171187157984901068039 10296256780736977351602059)
        ·
          refine ⟨15444385171105466027403089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10296256780736977351602059 15444385171105466027403089)
          ·
            refine ⟨11583288878329099520552317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15444385171105466027403089 11583288878329099520552317)
            ·
              refine ⟨4343733329373412320207119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11583288878329099520552317 4343733329373412320207119)
              ·
                refine ⟨6515599994060118480310679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4343733329373412320207119 6515599994060118480310679)
                ·
                  refine ⟨9773399991090177720466019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6515599994060118480310679 9773399991090177720466019)
                  ·
                    refine ⟨14660099986635266580699029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9773399991090177720466019 14660099986635266580699029)
                    ·
                      refine ⟨687192186873528120970267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14660099986635266580699029 687192186873528120970267)
                      ·
                        rfl

theorem cell23_1338302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1338302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338302 prefixEnd_1338302 := by exact prefixLift 1338302
  have htrace : WordTrace (prefixWord ++ tailWord_1338302) baseStart_1338302 baseEnd_1338302 := by
    simpa [prefixWord, tailWord_1338302, baseEnd_1338302] using wordTrace_append hprefix tailTrace_1338302
  have hstable : (prefixWord ++ tailWord_1338302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338302).length < 2 ^ (prefixWord ++ tailWord_1338302).sum := by decide
  have hdescent : baseEnd_1338302 < baseStart_1338302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338312 : List Nat := [2, 1, 3, 1, 5, 1, 1, 9]
def baseStart_1338312 : Nat := 118140960795 + 1338312 * 2 ^ 59
def prefixEnd_1338312 : Nat := 4983230072969 + 3 ^ 40 * 1338312 * 2
def baseEnd_1338312 : Nat := 25451752654817521549823

theorem tailTrace_1338312 : CollatzResearch.WordTrace tailWord_1338312 prefixEnd_1338312 25451752654817521549823 := by
  unfold tailWord_1338312
  simp only [CollatzResearch.WordTrace]
  refine ⟨24406124363765832168840595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32541499151687776225120793 24406124363765832168840595)
  ·
    refine ⟨36609186545648748253260893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24406124363765832168840595 36609186545648748253260893)
    ·
      refine ⟨13728444954618280594972835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36609186545648748253260893 13728444954618280594972835)
      ·
        refine ⟨20592667431927420892459253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13728444954618280594972835 20592667431927420892459253)
        ·
          refine ⟨1930562571743195708668055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20592667431927420892459253 1930562571743195708668055)
          ·
            refine ⟨2895843857614793563002083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930562571743195708668055 2895843857614793563002083)
            ·
              refine ⟨4343765786422190344503125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2895843857614793563002083 4343765786422190344503125)
              ·
                refine ⟨25451752654817521549823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4343765786422190344503125 25451752654817521549823)
                ·
                  rfl

theorem cell23_1338312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 9].length) (baseStart_1338312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338312 prefixEnd_1338312 := by exact prefixLift 1338312
  have htrace : WordTrace (prefixWord ++ tailWord_1338312) baseStart_1338312 baseEnd_1338312 := by
    simpa [prefixWord, tailWord_1338312, baseEnd_1338312] using wordTrace_append hprefix tailTrace_1338312
  have hstable : (prefixWord ++ tailWord_1338312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338312).length < 2 ^ (prefixWord ++ tailWord_1338312).sum := by decide
  have hdescent : baseEnd_1338312 < baseStart_1338312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338326 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1338326 : Nat := 118140960795 + 1338326 * 2 ^ 59
def prefixEnd_1338326 : Nat := 4983230072969 + 3 ^ 40 * 1338326 * 2
def baseEnd_1338326 : Nat := 687204510409236027070157

theorem tailTrace_1338326 : CollatzResearch.WordTrace tailWord_1338326 prefixEnd_1338326 687204510409236027070157 := by
  unfold tailWord_1338326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3050797459342559045543177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32541839566320629819127221 3050797459342559045543177)
  ·
    refine ⟨2288098094506919284157383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3050797459342559045543177 2288098094506919284157383)
    ·
      refine ⟨3432147141760378926236075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288098094506919284157383 3432147141760378926236075)
      ·
        refine ⟨5148220712640568389354113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432147141760378926236075 5148220712640568389354113)
        ·
          refine ⟨3861165534480426292015585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5148220712640568389354113 3861165534480426292015585)
          ·
            refine ⟨2895874150860319719011689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861165534480426292015585 2895874150860319719011689)
            ·
              refine ⟨2171905613145239789258767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895874150860319719011689 2171905613145239789258767)
              ·
                refine ⟨3257858419717859683888151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171905613145239789258767 3257858419717859683888151)
                ·
                  refine ⟨4886787629576789525832227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3257858419717859683888151 4886787629576789525832227)
                  ·
                    refine ⟨7330181444365184288748341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4886787629576789525832227 7330181444365184288748341)
                    ·
                      refine ⟨687204510409236027070157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7330181444365184288748341 687204510409236027070157)
                      ·
                        rfl

theorem cell23_1338326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1338326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338326 prefixEnd_1338326 := by exact prefixLift 1338326
  have htrace : WordTrace (prefixWord ++ tailWord_1338326) baseStart_1338326 baseEnd_1338326 := by
    simpa [prefixWord, tailWord_1338326, baseEnd_1338326] using wordTrace_append hprefix tailTrace_1338326
  have hstable : (prefixWord ++ tailWord_1338326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338326).length < 2 ^ (prefixWord ++ tailWord_1338326).sum := by decide
  have hdescent : baseEnd_1338326 < baseStart_1338326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338339 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1338339 : Nat := 118140960795 + 1338339 * 2 ^ 59
def prefixEnd_1338339 : Nat := 4983230072969 + 3 ^ 40 * 1338339 * 2
def baseEnd_1338339 : Nat := 687211185657744476207597

theorem tailTrace_1338339 : CollatzResearch.WordTrace tailWord_1338339 prefixEnd_1338339 687211185657744476207597 := by
  unfold tailWord_1338339
  simp only [CollatzResearch.WordTrace]
  refine ⟨48813233498433847948914071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32542155665622565299276047 48813233498433847948914071)
  ·
    refine ⟨73219850247650771923371107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48813233498433847948914071 73219850247650771923371107)
    ·
      refine ⟨109829775371476157885056661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73219850247650771923371107 109829775371476157885056661)
      ·
        refine ⟨5148270720537944900862031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109829775371476157885056661 5148270720537944900862031)
        ·
          refine ⟨7722406080806917351293047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148270720537944900862031 7722406080806917351293047)
          ·
            refine ⟨11583609121210376026939571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7722406080806917351293047 11583609121210376026939571)
            ·
              refine ⟨17375413681815564040409357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11583609121210376026939571 17375413681815564040409357)
              ·
                refine ⟨6515780130680836515153509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17375413681815564040409357 6515780130680836515153509)
                ·
                  refine ⟨1221708774502656846591283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6515780130680836515153509 1221708774502656846591283)
                  ·
                    refine ⟨1832563161753985269886925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1221708774502656846591283 1832563161753985269886925)
                    ·
                      refine ⟨687211185657744476207597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832563161753985269886925 687211185657744476207597)
                      ·
                        rfl

theorem cell23_1338339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1338339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338339 prefixEnd_1338339 := by exact prefixLift 1338339
  have htrace : WordTrace (prefixWord ++ tailWord_1338339) baseStart_1338339 baseEnd_1338339 := by
    simpa [prefixWord, tailWord_1338339, baseEnd_1338339] using wordTrace_append hprefix tailTrace_1338339
  have hstable : (prefixWord ++ tailWord_1338339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338339).length < 2 ^ (prefixWord ++ tailWord_1338339).sum := by decide
  have hdescent : baseEnd_1338339 < baseStart_1338339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338350 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1338350 : Nat := 118140960795 + 1338350 * 2 ^ 59
def prefixEnd_1338350 : Nat := 4983230072969 + 3 ^ 40 * 1338350 * 2
def baseEnd_1338350 : Nat := 229072277981647977723349

theorem tailTrace_1338350 : CollatzResearch.WordTrace tailWord_1338350 prefixEnd_1338350 229072277981647977723349 := by
  unfold tailWord_1338350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101704337674249603445563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32542423134262664551709669 6101704337674249603445563)
  ·
    refine ⟨9152556506511374405168345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6101704337674249603445563 9152556506511374405168345)
    ·
      refine ⟨6864417379883530803876259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9152556506511374405168345 6864417379883530803876259)
      ·
        refine ⟨10296626069825296205814389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6864417379883530803876259 10296626069825296205814389)
        ·
          refine ⟨965308694046121519295099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10296626069825296205814389 965308694046121519295099)
          ·
            refine ⟨1447963041069182278942649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965308694046121519295099 1447963041069182278942649)
            ·
              refine ⟨1085972280801886709206987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447963041069182278942649 1085972280801886709206987)
              ·
                refine ⟨1628958421202830063810481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085972280801886709206987 1628958421202830063810481)
                ·
                  refine ⟨1221718815902122547857861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1628958421202830063810481 1221718815902122547857861)
                  ·
                    refine ⟨229072277981647977723349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221718815902122547857861 229072277981647977723349)
                    ·
                      rfl

theorem cell23_1338350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1338350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338350 prefixEnd_1338350 := by exact prefixLift 1338350
  have htrace : WordTrace (prefixWord ++ tailWord_1338350) baseStart_1338350 baseEnd_1338350 := by
    simpa [prefixWord, tailWord_1338350, baseEnd_1338350] using wordTrace_append hprefix tailTrace_1338350
  have hstable : (prefixWord ++ tailWord_1338350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338350).length < 2 ^ (prefixWord ++ tailWord_1338350).sum := by decide
  have hdescent : baseEnd_1338350 < baseStart_1338350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338379 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 3, 4, 2]
def baseStart_1338379 : Nat := 118140960795 + 1338379 * 2 ^ 59
def prefixEnd_1338379 : Nat := 4983230072969 + 3 ^ 40 * 1338379 * 2
def baseEnd_1338379 : Nat := 687231724883924319707413

theorem tailTrace_1338379 : CollatzResearch.WordTrace tailWord_1338379 prefixEnd_1338379 687231724883924319707413 := by
  unfold tailWord_1338379
  simp only [CollatzResearch.WordTrace]
  refine ⟨48814692418288934780370191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32543128278859289853580127 48814692418288934780370191)
  ·
    refine ⟨73222038627433402170555287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48814692418288934780370191 73222038627433402170555287)
    ·
      refine ⟨109833057941150103255832931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73222038627433402170555287 109833057941150103255832931)
      ·
        refine ⟨164749586911725154883749397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109833057941150103255832931 164749586911725154883749397)
        ·
          refine ⟨7722636886487116635175753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164749586911725154883749397 7722636886487116635175753)
          ·
            refine ⟨5791977664865337476381815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7722636886487116635175753 5791977664865337476381815)
            ·
              refine ⟨8687966497298006214572723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5791977664865337476381815 8687966497298006214572723)
              ·
                refine ⟨13031949745947009321859085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8687966497298006214572723 13031949745947009321859085)
                ·
                  refine ⟨4886981154730128495697157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13031949745947009321859085 4886981154730128495697157)
                  ·
                    refine ⟨916308966511899092943217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4886981154730128495697157 916308966511899092943217)
                    ·
                      refine ⟨687231724883924319707413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916308966511899092943217 687231724883924319707413)
                      ·
                        rfl

theorem cell23_1338379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4, 2].length) (baseStart_1338379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338379 prefixEnd_1338379 := by exact prefixLift 1338379
  have htrace : WordTrace (prefixWord ++ tailWord_1338379) baseStart_1338379 baseEnd_1338379 := by
    simpa [prefixWord, tailWord_1338379, baseEnd_1338379] using wordTrace_append hprefix tailTrace_1338379
  have hstable : (prefixWord ++ tailWord_1338379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338379).length < 2 ^ (prefixWord ++ tailWord_1338379).sum := by decide
  have hdescent : baseEnd_1338379 < baseStart_1338379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338432 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 1, 7]
def baseStart_1338432 : Nat := 118140960795 + 1338432 * 2 ^ 59
def prefixEnd_1338432 : Nat := 4983230072969 + 3 ^ 40 * 1338432 * 2
def baseEnd_1338432 : Nat := 229086313119537537448223

theorem tailTrace_1338432 : CollatzResearch.WordTrace tailWord_1338432 prefixEnd_1338432 229086313119537537448223 := by
  unfold tailWord_1338432
  simp only [CollatzResearch.WordTrace]
  refine ⟨24408312743548462416024775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32544416991397949888033033 24408312743548462416024775)
  ·
    refine ⟨36612469115322693624037163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24408312743548462416024775 36612469115322693624037163)
    ·
      refine ⟨54918703672984040436055745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36612469115322693624037163 54918703672984040436055745)
      ·
        refine ⟨41189027754738030327041809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54918703672984040436055745 41189027754738030327041809)
        ·
          refine ⟨30891770816053522745281357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41189027754738030327041809 30891770816053522745281357)
          ·
            refine ⟨11584414056020071029480509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30891770816053522745281357 11584414056020071029480509)
            ·
              refine ⟨4344155271007526636055191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11584414056020071029480509 4344155271007526636055191)
              ·
                refine ⟨6516232906511289954082787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344155271007526636055191 6516232906511289954082787)
                ·
                  refine ⟨9774349359766934931124181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6516232906511289954082787 9774349359766934931124181)
                  ·
                    refine ⟨229086313119537537448223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9774349359766934931124181 229086313119537537448223)
                    ·
                      rfl

theorem cell23_1338432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_1338432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338432 prefixEnd_1338432 := by exact prefixLift 1338432
  have htrace : WordTrace (prefixWord ++ tailWord_1338432) baseStart_1338432 baseEnd_1338432 := by
    simpa [prefixWord, tailWord_1338432, baseEnd_1338432] using wordTrace_append hprefix tailTrace_1338432
  have hstable : (prefixWord ++ tailWord_1338432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338432).length < 2 ^ (prefixWord ++ tailWord_1338432).sum := by decide
  have hdescent : baseEnd_1338432 < baseStart_1338432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338442 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1338442 : Nat := 118140960795 + 1338442 * 2 ^ 59
def prefixEnd_1338442 : Nat := 4983230072969 + 3 ^ 40 * 1338442 * 2
def baseEnd_1338442 : Nat := 687264074165157573219623

theorem tailTrace_1338442 : CollatzResearch.WordTrace tailWord_1338442 prefixEnd_1338442 687264074165157573219623 := by
  unfold tailWord_1338442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204247554265174134978395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32544660144707131026609053 12204247554265174134978395)
  ·
    refine ⟨18306371331397761202467593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12204247554265174134978395 18306371331397761202467593)
    ·
      refine ⟨13729778498548320901850695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18306371331397761202467593 13729778498548320901850695)
      ·
        refine ⟨20594667747822481352776043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13729778498548320901850695 20594667747822481352776043)
        ·
          refine ⟨30892001621733722029164065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20594667747822481352776043 30892001621733722029164065)
          ·
            refine ⟨23169001216300291521873049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30892001621733722029164065 23169001216300291521873049)
            ·
              refine ⟨17376750912225218641404787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23169001216300291521873049 17376750912225218641404787)
              ·
                refine ⟨26065126368337827962107181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17376750912225218641404787 26065126368337827962107181)
                ·
                  refine ⟨9774422388126685485790193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26065126368337827962107181 9774422388126685485790193)
                  ·
                    refine ⟨7330816791095014114342645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9774422388126685485790193 7330816791095014114342645)
                    ·
                      refine ⟨687264074165157573219623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7330816791095014114342645 687264074165157573219623)
                      ·
                        rfl

theorem cell23_1338442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1338442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338442 prefixEnd_1338442 := by exact prefixLift 1338442
  have htrace : WordTrace (prefixWord ++ tailWord_1338442) baseStart_1338442 baseEnd_1338442 := by
    simpa [prefixWord, tailWord_1338442, baseEnd_1338442] using wordTrace_append hprefix tailTrace_1338442
  have hstable : (prefixWord ++ tailWord_1338442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338442).length < 2 ^ (prefixWord ++ tailWord_1338442).sum := by decide
  have hdescent : baseEnd_1338442 < baseStart_1338442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338479 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 3, 4]
def baseStart_1338479 : Nat := 118140960795 + 1338479 * 2 ^ 59
def prefixEnd_1338479 : Nat := 4983230072969 + 3 ^ 40 * 1338479 * 2
def baseEnd_1338479 : Nat := 229094357649791309485651

theorem tailTrace_1338479 : CollatzResearch.WordTrace tailWord_1338479 prefixEnd_1338479 229094357649791309485651 := by
  unfold tailWord_1338479
  simp only [CollatzResearch.WordTrace]
  refine ⟨48818339717926651859010491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32545559811951101239340327 48818339717926651859010491)
  ·
    refine ⟨73227509576889977788515737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48818339717926651859010491 73227509576889977788515737)
    ·
      refine ⟨54920632182667483341386803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73227509576889977788515737 54920632182667483341386803)
      ·
        refine ⟨82380948274001225012080205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54920632182667483341386803 82380948274001225012080205)
        ·
          refine ⟨30892855602750459379530077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82380948274001225012080205 30892855602750459379530077)
          ·
            refine ⟨11584820851031422267323779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30892855602750459379530077 11584820851031422267323779)
            ·
              refine ⟨17377231276547133400985669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11584820851031422267323779 17377231276547133400985669)
              ·
                refine ⟨3258230864352587512684813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17377231276547133400985669 3258230864352587512684813)
                ·
                  refine ⟨1221836574132220317256805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3258230864352587512684813 1221836574132220317256805)
                  ·
                    refine ⟨229094357649791309485651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221836574132220317256805 229094357649791309485651)
                    ·
                      rfl

theorem cell23_1338479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 4].length) (baseStart_1338479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338479 prefixEnd_1338479 := by exact prefixLift 1338479
  have htrace : WordTrace (prefixWord ++ tailWord_1338479) baseStart_1338479 baseEnd_1338479 := by
    simpa [prefixWord, tailWord_1338479, baseEnd_1338479] using wordTrace_append hprefix tailTrace_1338479
  have hstable : (prefixWord ++ tailWord_1338479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338479).length < 2 ^ (prefixWord ++ tailWord_1338479).sum := by decide
  have hdescent : baseEnd_1338479 < baseStart_1338479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338486 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1338486 : Nat := 118140960795 + 1338486 * 2 ^ 59
def prefixEnd_1338486 : Nat := 4983230072969 + 3 ^ 40 * 1338486 * 2
def baseEnd_1338486 : Nat := 687286667313955401069421

theorem tailTrace_1338486 : CollatzResearch.WordTrace tailWord_1338486 prefixEnd_1338486 687286667313955401069421 := by
  unfold tailWord_1338486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051162189306330753407207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32545730019267528036343541 3051162189306330753407207)
  ·
    refine ⟨4576743283959496130110811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3051162189306330753407207 4576743283959496130110811)
    ·
      refine ⟨6865114925939244195166217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4576743283959496130110811 6865114925939244195166217)
      ·
        refine ⟨5148836194454433146374663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6865114925939244195166217 5148836194454433146374663)
        ·
          refine ⟨7723254291681649719561995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148836194454433146374663 7723254291681649719561995)
          ·
            refine ⟨11584881437522474579342993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723254291681649719561995 11584881437522474579342993)
            ·
              refine ⟨8688661078141855934507245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11584881437522474579342993 8688661078141855934507245)
              ·
                refine ⟨3258247904303195975440217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8688661078141855934507245 3258247904303195975440217)
                ·
                  refine ⟨2443685928227396981580163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258247904303195975440217 2443685928227396981580163)
                  ·
                    refine ⟨3665528892341095472370245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2443685928227396981580163 3665528892341095472370245)
                    ·
                      refine ⟨687286667313955401069421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3665528892341095472370245 687286667313955401069421)
                      ·
                        rfl

theorem cell23_1338486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1338486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338486 prefixEnd_1338486 := by exact prefixLift 1338486
  have htrace : WordTrace (prefixWord ++ tailWord_1338486) baseStart_1338486 baseEnd_1338486 := by
    simpa [prefixWord, tailWord_1338486, baseEnd_1338486] using wordTrace_append hprefix tailTrace_1338486
  have hstable : (prefixWord ++ tailWord_1338486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338486).length < 2 ^ (prefixWord ++ tailWord_1338486).sum := by decide
  have hdescent : baseEnd_1338486 < baseStart_1338486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338492 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 10]
def baseStart_1338492 : Nat := 118140960795 + 1338492 * 2 ^ 59
def prefixEnd_1338492 : Nat := 4983230072969 + 3 ^ 40 * 1338492 * 2
def baseEnd_1338492 : Nat := 76365527577542486399377

theorem tailTrace_1338492 : CollatzResearch.WordTrace tailWord_1338492 prefixEnd_1338492 76365527577542486399377 := by
  unfold tailWord_1338492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409406933439777539616865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32545875911253036719489153 24409406933439777539616865)
  ·
    refine ⟨18307055200079833154712649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24409406933439777539616865 18307055200079833154712649)
    ·
      refine ⟨13730291400059874866034487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18307055200079833154712649 13730291400059874866034487)
      ·
        refine ⟨20595437100089812299051731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13730291400059874866034487 20595437100089812299051731)
        ·
          refine ⟨30893155650134718448577597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20595437100089812299051731 30893155650134718448577597)
          ·
            refine ⟨11584933368800519418216599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30893155650134718448577597 11584933368800519418216599)
            ·
              refine ⟨17377400053200779127324899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11584933368800519418216599 17377400053200779127324899)
              ·
                refine ⟨26066100079801168690987349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17377400053200779127324899 26066100079801168690987349)
                ·
                  refine ⟨76365527577542486399377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 26066100079801168690987349 76365527577542486399377)
                  ·
                    rfl

theorem cell23_1338492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_1338492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338492 prefixEnd_1338492 := by exact prefixLift 1338492
  have htrace : WordTrace (prefixWord ++ tailWord_1338492) baseStart_1338492 baseEnd_1338492 := by
    simpa [prefixWord, tailWord_1338492, baseEnd_1338492] using wordTrace_append hprefix tailTrace_1338492
  have hstable : (prefixWord ++ tailWord_1338492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338492).length < 2 ^ (prefixWord ++ tailWord_1338492).sum := by decide
  have hdescent : baseEnd_1338492 < baseStart_1338492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338506 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1338506 : Nat := 118140960795 + 1338506 * 2 ^ 59
def prefixEnd_1338506 : Nat := 4983230072969 + 3 ^ 40 * 1338506 * 2
def baseEnd_1338506 : Nat := 687296936927045322819329

theorem tailTrace_1338506 : CollatzResearch.WordTrace tailWord_1338506 prefixEnd_1338506 687296936927045322819329 := by
  unfold tailWord_1338506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204831122207208867560843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32546216325885890313495581 12204831122207208867560843)
  ·
    refine ⟨18307246683310813301341265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12204831122207208867560843 18307246683310813301341265)
    ·
      refine ⟨13730435012483109976005949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18307246683310813301341265 13730435012483109976005949)
      ·
        refine ⟨5148913129681166241002231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13730435012483109976005949 5148913129681166241002231)
        ·
          refine ⟨7723369694521749361503347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5148913129681166241002231 7723369694521749361503347)
          ·
            refine ⟨11585054541782624042255021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7723369694521749361503347 11585054541782624042255021)
            ·
              refine ⟨4344395453168484015845633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11585054541782624042255021 4344395453168484015845633)
              ·
                refine ⟨3258296589876363011884225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344395453168484015845633 3258296589876363011884225)
                ·
                  refine ⟨2443722442407272258913169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258296589876363011884225 2443722442407272258913169)
                  ·
                    refine ⟨1832791831805454194184877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2443722442407272258913169 1832791831805454194184877)
                    ·
                      refine ⟨687296936927045322819329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832791831805454194184877 687296936927045322819329)
                      ·
                        rfl

theorem cell23_1338506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1338506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338506 prefixEnd_1338506 := by exact prefixLift 1338506
  have htrace : WordTrace (prefixWord ++ tailWord_1338506) baseStart_1338506 baseEnd_1338506 := by
    simpa [prefixWord, tailWord_1338506, baseEnd_1338506] using wordTrace_append hprefix tailTrace_1338506
  have hstable : (prefixWord ++ tailWord_1338506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338506).length < 2 ^ (prefixWord ++ tailWord_1338506).sum := by decide
  have hdescent : baseEnd_1338506 < baseStart_1338506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338512 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_1338512 : Nat := 118140960795 + 1338512 * 2 ^ 59
def prefixEnd_1338512 : Nat := 4983230072969 + 3 ^ 40 * 1338512 * 2
def baseEnd_1338512 : Nat := 687300017810972299344301

theorem tailTrace_1338512 : CollatzResearch.WordTrace tailWord_1338512 prefixEnd_1338512 687300017810972299344301 := by
  unfold tailWord_1338512
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409771663403549247480895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32546362217871398996641193 24409771663403549247480895)
  ·
    refine ⟨36614657495105323871221343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24409771663403549247480895 36614657495105323871221343)
    ·
      refine ⟨54921986242657985806832015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36614657495105323871221343 54921986242657985806832015)
      ·
        refine ⟨82382979363986978710248023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54921986242657985806832015 82382979363986978710248023)
        ·
          refine ⟨123574469045980468065372035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82382979363986978710248023 123574469045980468065372035)
          ·
            refine ⟨185361703568970702098058053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123574469045980468065372035 185361703568970702098058053)
            ·
              refine ⟨34755319419182006643385885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185361703568970702098058053 34755319419182006643385885)
              ·
                refine ⟨13033244782193252491269707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34755319419182006643385885 13033244782193252491269707)
                ·
                  refine ⟨19549867173289878736904561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13033244782193252491269707 19549867173289878736904561)
                  ·
                    refine ⟨14662400379967409052678421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19549867173289878736904561 14662400379967409052678421)
                    ·
                      refine ⟨687300017810972299344301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14662400379967409052678421 687300017810972299344301)
                      ·
                        rfl

theorem cell23_1338512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_1338512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338512 prefixEnd_1338512 := by exact prefixLift 1338512
  have htrace : WordTrace (prefixWord ++ tailWord_1338512) baseStart_1338512 baseEnd_1338512 := by
    simpa [prefixWord, tailWord_1338512, baseEnd_1338512] using wordTrace_append hprefix tailTrace_1338512
  have hstable : (prefixWord ++ tailWord_1338512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338512).length < 2 ^ (prefixWord ++ tailWord_1338512).sum := by decide
  have hdescent : baseEnd_1338512 < baseStart_1338512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338564 : List Nat := [2, 3, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1338564 : Nat := 118140960795 + 1338564 * 2 ^ 59
def prefixEnd_1338564 : Nat := 4983230072969 + 3 ^ 40 * 1338564 * 2
def baseEnd_1338564 : Nat := 229108906268335365298021

theorem tailTrace_1338564 : CollatzResearch.WordTrace tailWord_1338564 prefixEnd_1338564 229108906268335365298021 := by
  unfold tailWord_1338564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24410719961309355687927373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32547626615079140917236497 24410719961309355687927373)
  ·
    refine ⟨9154019985491008382972765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24410719961309355687927373 9154019985491008382972765)
    ·
      refine ⟨3432757494559128143614787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9154019985491008382972765 3432757494559128143614787)
      ·
        refine ⟨5149136241838692215422181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432757494559128143614787 5149136241838692215422181)
        ·
          refine ⟨965463045344754790391659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5149136241838692215422181 965463045344754790391659)
          ·
            refine ⟨1448194568017132185587489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965463045344754790391659 1448194568017132185587489)
            ·
              refine ⟨1086145926012849139190617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448194568017132185587489 1086145926012849139190617)
              ·
                refine ⟨814609444509636854392963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086145926012849139190617 814609444509636854392963)
                ·
                  refine ⟨1221914166764455281589445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814609444509636854392963 1221914166764455281589445)
                  ·
                    refine ⟨229108906268335365298021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221914166764455281589445 229108906268335365298021)
                    ·
                      rfl

theorem cell23_1338564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1338564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338564 prefixEnd_1338564 := by exact prefixLift 1338564
  have htrace : WordTrace (prefixWord ++ tailWord_1338564) baseStart_1338564 baseEnd_1338564 := by
    simpa [prefixWord, tailWord_1338564, baseEnd_1338564] using wordTrace_append hprefix tailTrace_1338564
  have hstable : (prefixWord ++ tailWord_1338564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338564).length < 2 ^ (prefixWord ++ tailWord_1338564).sum := by decide
  have hdescent : baseEnd_1338564 < baseStart_1338564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338569 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 8, 4]
def baseStart_1338569 : Nat := 118140960795 + 1338569 * 2 ^ 59
def prefixEnd_1338569 : Nat := 4983230072969 + 3 ^ 40 * 1338569 * 2
def baseEnd_1338569 : Nat := 229109762069426192110513

theorem tailTrace_1338569 : CollatzResearch.WordTrace tailWord_1338569 prefixEnd_1338569 229109762069426192110513 := by
  unfold tailWord_1338569
  simp only [CollatzResearch.WordTrace]
  refine ⟨48821622287600597229786761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32547748191733731486524507 48821622287600597229786761)
  ·
    refine ⟨36616216715700447922340071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48821622287600597229786761 36616216715700447922340071)
    ·
      refine ⟨54924325073550671883510107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36616216715700447922340071 54924325073550671883510107)
      ·
        refine ⟨82386487610326007825265161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54924325073550671883510107 82386487610326007825265161)
        ·
          refine ⟨61789865707744505868948871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82386487610326007825265161 61789865707744505868948871)
          ·
            refine ⟨92684798561616758803423307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61789865707744505868948871 92684798561616758803423307)
            ·
              refine ⟨139027197842425138205134961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92684798561616758803423307 139027197842425138205134961)
              ·
                refine ⟨104270398381818853653851221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139027197842425138205134961 104270398381818853653851221)
                ·
                  refine ⟨1221918731036939691256069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 104270398381818853653851221 1221918731036939691256069)
                  ·
                    refine ⟨229109762069426192110513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221918731036939691256069 229109762069426192110513)
                    ·
                      rfl

theorem cell23_1338569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_1338569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338569 prefixEnd_1338569 := by exact prefixLift 1338569
  have htrace : WordTrace (prefixWord ++ tailWord_1338569) baseStart_1338569 baseEnd_1338569 := by
    simpa [prefixWord, tailWord_1338569, baseEnd_1338569] using wordTrace_append hprefix tailTrace_1338569
  have hstable : (prefixWord ++ tailWord_1338569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338569).length < 2 ^ (prefixWord ++ tailWord_1338569).sum := by decide
  have hdescent : baseEnd_1338569 < baseStart_1338569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338570 : List Nat := [3, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_1338570 : Nat := 118140960795 + 1338570 * 2 ^ 59
def prefixEnd_1338570 : Nat := 4983230072969 + 3 ^ 40 * 1338570 * 2
def baseEnd_1338570 : Nat := 687329799688933072419035

theorem tailTrace_1338570 : CollatzResearch.WordTrace tailWord_1338570 prefixEnd_1338570 687329799688933072419035 := by
  unfold tailWord_1338570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12205414690149243600143291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32547772507064649600382109 12205414690149243600143291)
  ·
    refine ⟨18308122035223865400214937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12205414690149243600143291 18308122035223865400214937)
    ·
      refine ⟨13731091526417899050161203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18308122035223865400214937 13731091526417899050161203)
      ·
        refine ⟨20596637289626848575241805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13731091526417899050161203 20596637289626848575241805)
        ·
          refine ⟨7723738983610068215715677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20596637289626848575241805 7723738983610068215715677)
          ·
            refine ⟨2896402118853775580893379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7723738983610068215715677 2896402118853775580893379)
            ·
              refine ⟨4344603178280663371340069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896402118853775580893379 4344603178280663371340069)
              ·
                refine ⟨814613095927624382126263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4344603178280663371340069 814613095927624382126263)
                ·
                  refine ⟨1221919643891436573189395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814613095927624382126263 1221919643891436573189395)
                  ·
                    refine ⟨1832879465837154859784093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1221919643891436573189395 1832879465837154859784093)
                    ·
                      refine ⟨687329799688933072419035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832879465837154859784093 687329799688933072419035)
                      ·
                        rfl

theorem cell23_1338570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_1338570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338570 prefixEnd_1338570 := by exact prefixLift 1338570
  have htrace : WordTrace (prefixWord ++ tailWord_1338570) baseStart_1338570 baseEnd_1338570 := by
    simpa [prefixWord, tailWord_1338570, baseEnd_1338570] using wordTrace_append hprefix tailTrace_1338570
  have hstable : (prefixWord ++ tailWord_1338570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338570).length < 2 ^ (prefixWord ++ tailWord_1338570).sum := by decide
  have hdescent : baseEnd_1338570 < baseStart_1338570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338593 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_1338593 : Nat := 118140960795 + 1338593 * 2 ^ 59
def prefixEnd_1338593 : Nat := 4983230072969 + 3 ^ 40 * 1338593 * 2
def baseEnd_1338593 : Nat := 687341609743986482431429

theorem tailTrace_1338593 : CollatzResearch.WordTrace tailWord_1338593 prefixEnd_1338593 687341609743986482431429 := by
  unfold tailWord_1338593
  simp only [CollatzResearch.WordTrace]
  refine ⟨48822497639513649328660433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32548331759675766219106955 48822497639513649328660433)
  ·
    refine ⟨36616873229635236996495325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48822497639513649328660433 36616873229635236996495325)
    ·
      refine ⟨13731327461113213873685747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36616873229635236996495325 13731327461113213873685747)
      ·
        refine ⟨20596991191669820810528621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13731327461113213873685747 20596991191669820810528621)
        ·
          refine ⟨7723871696876182803948233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20596991191669820810528621 7723871696876182803948233)
          ·
            refine ⟨5792903772657137102961175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7723871696876182803948233 5792903772657137102961175)
            ·
              refine ⟨8689355658985705654441763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5792903772657137102961175 8689355658985705654441763)
              ·
                refine ⟨13034033488478558481662645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8689355658985705654441763 13034033488478558481662645)
                ·
                  refine ⟨1221940639544864857655873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13034033488478558481662645 1221940639544864857655873)
                  ·
                    refine ⟨916455479658648643241905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1221940639544864857655873 916455479658648643241905)
                    ·
                      refine ⟨687341609743986482431429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916455479658648643241905 687341609743986482431429)
                      ·
                        rfl

theorem cell23_1338593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_1338593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338593 prefixEnd_1338593 := by exact prefixLift 1338593
  have htrace : WordTrace (prefixWord ++ tailWord_1338593) baseStart_1338593 baseEnd_1338593 := by
    simpa [prefixWord, tailWord_1338593, baseEnd_1338593] using wordTrace_append hprefix tailTrace_1338593
  have hstable : (prefixWord ++ tailWord_1338593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338593).length < 2 ^ (prefixWord ++ tailWord_1338593).sum := by decide
  have hdescent : baseEnd_1338593 < baseStart_1338593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338596 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_1338596 : Nat := 118140960795 + 1338596 * 2 ^ 59
def prefixEnd_1338596 : Nat := 4983230072969 + 3 ^ 40 * 1338596 * 2
def baseEnd_1338596 : Nat := 687343150185949970693915

theorem tailTrace_1338596 : CollatzResearch.WordTrace tailWord_1338596 prefixEnd_1338596 687343150185949970693915 := by
  unfold tailWord_1338596
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411303529251390420509821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32548404705668520560679761 24411303529251390420509821)
  ·
    refine ⟨9154238823469271407691183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24411303529251390420509821 9154238823469271407691183)
    ·
      refine ⟨13731358235203907111536775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9154238823469271407691183 13731358235203907111536775)
      ·
        refine ⟨20597037352805860667305163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13731358235203907111536775 20597037352805860667305163)
        ·
          refine ⟨30895556029208791000957745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20597037352805860667305163 30895556029208791000957745)
          ·
            refine ⟨23171667021906593250718309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30895556029208791000957745 23171667021906593250718309)
            ·
              refine ⟨4344687566607486234509683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23171667021906593250718309 4344687566607486234509683)
              ·
                refine ⟨6517031349911229351764525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344687566607486234509683 6517031349911229351764525)
                ·
                  refine ⟨2443886756216711006911697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6517031349911229351764525 2443886756216711006911697)
                  ·
                    refine ⟨1832915067162533255183773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2443886756216711006911697 1832915067162533255183773)
                    ·
                      refine ⟨687343150185949970693915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1832915067162533255183773 687343150185949970693915)
                      ·
                        rfl

theorem cell23_1338596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_1338596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338596 prefixEnd_1338596 := by exact prefixLift 1338596
  have htrace : WordTrace (prefixWord ++ tailWord_1338596) baseStart_1338596 baseEnd_1338596 := by
    simpa [prefixWord, tailWord_1338596, baseEnd_1338596] using wordTrace_append hprefix tailTrace_1338596
  have hstable : (prefixWord ++ tailWord_1338596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338596).length < 2 ^ (prefixWord ++ tailWord_1338596).sum := by decide
  have hdescent : baseEnd_1338596 < baseStart_1338596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338597 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1338597 : Nat := 118140960795 + 1338597 * 2 ^ 59
def prefixEnd_1338597 : Nat := 4983230072969 + 3 ^ 40 * 1338597 * 2
def baseEnd_1338597 : Nat := 687343663666604466781411

theorem tailTrace_1338597 : CollatzResearch.WordTrace tailWord_1338597 prefixEnd_1338597 687343663666604466781411 := by
  unfold tailWord_1338597
  simp only [CollatzResearch.WordTrace]
  refine ⟨48822643531499158011806045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32548429020999438674537363 48822643531499158011806045)
  ·
    refine ⟨18308491324312184254427267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48822643531499158011806045 18308491324312184254427267)
    ·
      refine ⟨27462736986468276381640901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18308491324312184254427267 27462736986468276381640901)
      ·
        refine ⟨5149263184962801821557669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27462736986468276381640901 5149263184962801821557669)
        ·
          refine ⟨965486847180525341542063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5149263184962801821557669 965486847180525341542063)
          ·
            refine ⟨1448230270770788012313095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965486847180525341542063 1448230270770788012313095)
            ·
              refine ⟨2172345406156182018469643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448230270770788012313095 2172345406156182018469643)
              ·
                refine ⟨3258518109234273027704465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172345406156182018469643 3258518109234273027704465)
                ·
                  refine ⟨2443888581925704770778349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258518109234273027704465 2443888581925704770778349)
                  ·
                    refine ⟨916458218222139289041881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2443888581925704770778349 916458218222139289041881)
                    ·
                      refine ⟨687343663666604466781411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916458218222139289041881 687343663666604466781411)
                      ·
                        rfl

theorem cell23_1338597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1338597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338597 prefixEnd_1338597 := by exact prefixLift 1338597
  have htrace : WordTrace (prefixWord ++ tailWord_1338597) baseStart_1338597 baseEnd_1338597 := by
    simpa [prefixWord, tailWord_1338597, baseEnd_1338597] using wordTrace_append hprefix tailTrace_1338597
  have hstable : (prefixWord ++ tailWord_1338597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338597).length < 2 ^ (prefixWord ++ tailWord_1338597).sum := by decide
  have hdescent : baseEnd_1338597 < baseStart_1338597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338606 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1338606 : Nat := 118140960795 + 1338606 * 2 ^ 59
def prefixEnd_1338606 : Nat := 4983230072969 + 3 ^ 40 * 1338606 * 2
def baseEnd_1338606 : Nat := 687348284992494931568869

theorem tailTrace_1338606 : CollatzResearch.WordTrace tailWord_1338606 prefixEnd_1338606 687348284992494931568869 := by
  unfold tailWord_1338606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6102871473558319068610459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32548647858977701699255781 6102871473558319068610459)
  ·
    refine ⟨9154307210337478602915689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6102871473558319068610459 9154307210337478602915689)
    ·
      refine ⟨6865730407753108952186767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9154307210337478602915689 6865730407753108952186767)
      ·
        refine ⟨10298595611629663428280151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6865730407753108952186767 10298595611629663428280151)
        ·
          refine ⟨15447893417444495142420227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10298595611629663428280151 15447893417444495142420227)
          ·
            refine ⟨23171840126166742713630341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15447893417444495142420227 23171840126166742713630341)
            ·
              refine ⟨4344720023656264258805689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23171840126166742713630341 4344720023656264258805689)
              ·
                refine ⟨3258540017742198194104267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344720023656264258805689 3258540017742198194104267)
                ·
                  refine ⟨4887810026613297291156401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3258540017742198194104267 4887810026613297291156401)
                  ·
                    refine ⟨3665857519959972968367301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4887810026613297291156401 3665857519959972968367301)
                    ·
                      refine ⟨687348284992494931568869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3665857519959972968367301 687348284992494931568869)
                      ·
                        rfl

theorem cell23_1338606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1338606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338606 prefixEnd_1338606 := by exact prefixLift 1338606
  have htrace : WordTrace (prefixWord ++ tailWord_1338606) baseStart_1338606 baseEnd_1338606 := by
    simpa [prefixWord, tailWord_1338606, baseEnd_1338606] using wordTrace_append hprefix tailTrace_1338606
  have hstable : (prefixWord ++ tailWord_1338606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338606).length < 2 ^ (prefixWord ++ tailWord_1338606).sum := by decide
  have hdescent : baseEnd_1338606 < baseStart_1338606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338620 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1338620 : Nat := 118140960795 + 1338620 * 2 ^ 59
def prefixEnd_1338620 : Nat := 4983230072969 + 3 ^ 40 * 1338620 * 2
def baseEnd_1338620 : Nat := 229118491240552625597935

theorem tailTrace_1338620 : CollatzResearch.WordTrace tailWord_1338620 prefixEnd_1338620 229118491240552625597935 := by
  unfold tailWord_1338620
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411741205207916469946657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32548988273610555293262209 24411741205207916469946657)
  ·
    refine ⟨18308805903905937352459993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24411741205207916469946657 18308805903905937352459993)
    ·
      refine ⟨13731604427929453014344995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18308805903905937352459993 13731604427929453014344995)
      ·
        refine ⟨20597406641894179521517493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13731604427929453014344995 20597406641894179521517493)
        ·
          refine ⟨1931006872677579330142265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20597406641894179521517493 1931006872677579330142265)
          ·
            refine ⟨1448255154508184497606699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931006872677579330142265 1448255154508184497606699)
            ·
              refine ⟨2172382731762276746410049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448255154508184497606699 2172382731762276746410049)
              ·
                refine ⟨1629287048821707559807537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172382731762276746410049 1629287048821707559807537)
                ·
                  refine ⟨1221965286616280669855653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1629287048821707559807537 1221965286616280669855653)
                  ·
                    refine ⟨229118491240552625597935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221965286616280669855653 229118491240552625597935)
                    ·
                      rfl

theorem cell23_1338620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1338620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338620 prefixEnd_1338620 := by exact prefixLift 1338620
  have htrace : WordTrace (prefixWord ++ tailWord_1338620) baseStart_1338620 baseEnd_1338620 := by
    simpa [prefixWord, tailWord_1338620, baseEnd_1338620] using wordTrace_append hprefix tailTrace_1338620
  have hstable : (prefixWord ++ tailWord_1338620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338620).length < 2 ^ (prefixWord ++ tailWord_1338620).sum := by decide
  have hdescent : baseEnd_1338620 < baseStart_1338620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338678 : List Nat := [5, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1338678 : Nat := 118140960795 + 1338678 * 2 ^ 59
def prefixEnd_1338678 : Nat := 4983230072969 + 3 ^ 40 * 1338678 * 2
def baseEnd_1338678 : Nat := 687385255599618649868539

theorem tailTrace_1338678 : CollatzResearch.WordTrace tailWord_1338678 prefixEnd_1338678 687385255599618649868539 := by
  unfold tailWord_1338678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051599865262856802844043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32550398562803805897003125 3051599865262856802844043)
  ·
    refine ⟨4577399797894285204266065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3051599865262856802844043 4577399797894285204266065)
    ·
      refine ⟨3433049848420713903199549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4577399797894285204266065 3433049848420713903199549)
      ·
        refine ⟨1287393693157767713699831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3433049848420713903199549 1287393693157767713699831)
        ·
          refine ⟨1931090539736651570549747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287393693157767713699831 1931090539736651570549747)
          ·
            refine ⟨2896635809604977355824621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931090539736651570549747 2896635809604977355824621)
            ·
              refine ⟨1086238428601866508434233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2896635809604977355824621 1086238428601866508434233)
              ·
                refine ⟨814678821451399881325675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086238428601866508434233 814678821451399881325675)
                ·
                  refine ⟨1222018232177099821988513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814678821451399881325675 1222018232177099821988513)
                  ·
                    refine ⟨916513674132824866491385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1222018232177099821988513 916513674132824866491385)
                    ·
                      refine ⟨687385255599618649868539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916513674132824866491385 687385255599618649868539)
                      ·
                        rfl

theorem cell23_1338678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1338678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338678 prefixEnd_1338678 := by exact prefixLift 1338678
  have htrace : WordTrace (prefixWord ++ tailWord_1338678) baseStart_1338678 baseEnd_1338678 := by
    simpa [prefixWord, tailWord_1338678, baseEnd_1338678] using wordTrace_append hprefix tailTrace_1338678
  have hstable : (prefixWord ++ tailWord_1338678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338678).length < 2 ^ (prefixWord ++ tailWord_1338678).sum := by decide
  have hdescent : baseEnd_1338678 < baseStart_1338678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338686 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1338686 : Nat := 118140960795 + 1338686 * 2 ^ 59
def prefixEnd_1338686 : Nat := 4983230072969 + 3 ^ 40 * 1338686 * 2
def baseEnd_1338686 : Nat := 687389363444854618568501

theorem tailTrace_1338686 : CollatzResearch.WordTrace tailWord_1338686 prefixEnd_1338686 687389363444854618568501 := by
  unfold tailWord_1338686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103236203522090776474489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32550593085451150807863941 6103236203522090776474489)
  ·
    refine ⟨4577427152641568082355867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6103236203522090776474489 4577427152641568082355867)
    ·
      refine ⟨6866140728962352123533801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4577427152641568082355867 6866140728962352123533801)
      ·
        refine ⟨5149605546721764092650351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6866140728962352123533801 5149605546721764092650351)
        ·
          refine ⟨7724408320082646138975527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5149605546721764092650351 7724408320082646138975527)
          ·
            refine ⟨11586612480123969208463291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724408320082646138975527 11586612480123969208463291)
            ·
              refine ⟨17379918720185953812694937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11586612480123969208463291 17379918720185953812694937)
              ·
                refine ⟨13034939040139465359521203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17379918720185953812694937 13034939040139465359521203)
                ·
                  refine ⟨19552408560209198039281805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13034939040139465359521203 19552408560209198039281805)
                  ·
                    refine ⟨7332153210078449264730677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19552408560209198039281805 7332153210078449264730677)
                    ·
                      refine ⟨687389363444854618568501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7332153210078449264730677 687389363444854618568501)
                      ·
                        rfl

theorem cell23_1338686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1338686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338686 prefixEnd_1338686 := by exact prefixLift 1338686
  have htrace : WordTrace (prefixWord ++ tailWord_1338686) baseStart_1338686 baseEnd_1338686 := by
    simpa [prefixWord, tailWord_1338686, baseEnd_1338686] using wordTrace_append hprefix tailTrace_1338686
  have hstable : (prefixWord ++ tailWord_1338686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338686).length < 2 ^ (prefixWord ++ tailWord_1338686).sum := by decide
  have hdescent : baseEnd_1338686 < baseStart_1338686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338736 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 2, 5]
def baseStart_1338736 : Nat := 118140960795 + 1338736 * 2 ^ 59
def prefixEnd_1338736 : Nat := 4983230072969 + 3 ^ 40 * 1338736 * 2
def baseEnd_1338736 : Nat := 229138345825859807647757

theorem tailTrace_1338736 : CollatzResearch.WordTrace tailWord_1338736 prefixEnd_1338736 229138345825859807647757 := by
  unfold tailWord_1338736
  simp only [CollatzResearch.WordTrace]
  refine ⟨24413856638997792375558031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32551808851997056500744041 24413856638997792375558031)
  ·
    refine ⟨36620784958496688563337047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24413856638997792375558031 36620784958496688563337047)
    ·
      refine ⟨54931177437745032845005571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36620784958496688563337047 54931177437745032845005571)
      ·
        refine ⟨82396766156617549267508357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54931177437745032845005571 82396766156617549267508357)
        ·
          refine ⟨15449393654365790487657817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82396766156617549267508357 15449393654365790487657817)
          ·
            refine ⟨11587045240774342865743363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15449393654365790487657817 11587045240774342865743363)
            ·
              refine ⟨17380567861161514298615045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11587045240774342865743363 17380567861161514298615045)
              ·
                refine ⟨3258856473967783930990321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17380567861161514298615045 3258856473967783930990321)
                ·
                  refine ⟨2444142355475837948242741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258856473967783930990321 2444142355475837948242741)
                  ·
                    refine ⟨229138345825859807647757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2444142355475837948242741 229138345825859807647757)
                    ·
                      rfl

theorem cell23_1338736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_1338736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338736 prefixEnd_1338736 := by exact prefixLift 1338736
  have htrace : WordTrace (prefixWord ++ tailWord_1338736) baseStart_1338736 baseEnd_1338736 := by
    simpa [prefixWord, tailWord_1338736, baseEnd_1338736] using wordTrace_append hprefix tailTrace_1338736
  have hstable : (prefixWord ++ tailWord_1338736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338736).length < 2 ^ (prefixWord ++ tailWord_1338736).sum := by decide
  have hdescent : baseEnd_1338736 < baseStart_1338736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338739 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8]
def baseStart_1338739 : Nat := 118140960795 + 1338739 * 2 ^ 59
def prefixEnd_1338739 : Nat := 4983230072969 + 3 ^ 40 * 1338739 * 2
def baseEnd_1338739 : Nat := 687416577919542911205757

theorem tailTrace_1338739 : CollatzResearch.WordTrace tailWord_1338739 prefixEnd_1338739 687416577919542911205757 := by
  unfold tailWord_1338739
  simp only [CollatzResearch.WordTrace]
  refine ⟨48827822696984716263475271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32551881797989810842316847 48827822696984716263475271)
  ·
    refine ⟨73241734045477074395212907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48827822696984716263475271 73241734045477074395212907)
    ·
      refine ⟨109862601068215611592819361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73241734045477074395212907 109862601068215611592819361)
      ·
        refine ⟨82396950801161708694614521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109862601068215611592819361 82396950801161708694614521)
        ·
          refine ⟨61797713100871281520960891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82396950801161708694614521 61797713100871281520960891)
          ·
            refine ⟨92696569651306922281441337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61797713100871281520960891 92696569651306922281441337)
            ·
              refine ⟨69522427238480191711081003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92696569651306922281441337 69522427238480191711081003)
              ·
                refine ⟨104283640857720287566621505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69522427238480191711081003 104283640857720287566621505)
                ·
                  refine ⟨78212730643290215674966129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104283640857720287566621505 78212730643290215674966129)
                  ·
                    refine ⟨58659547982467661756224597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78212730643290215674966129 58659547982467661756224597)
                    ·
                      refine ⟨687416577919542911205757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58659547982467661756224597 687416577919542911205757)
                      ·
                        rfl

theorem cell23_1338739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_1338739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338739 prefixEnd_1338739 := by exact prefixLift 1338739
  have htrace : WordTrace (prefixWord ++ tailWord_1338739) baseStart_1338739 baseEnd_1338739 := by
    simpa [prefixWord, tailWord_1338739, baseEnd_1338739] using wordTrace_append hprefix tailTrace_1338739
  have hstable : (prefixWord ++ tailWord_1338739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338739).length < 2 ^ (prefixWord ++ tailWord_1338739).sum := by decide
  have hdescent : baseEnd_1338739 < baseStart_1338739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338770 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1338770 : Nat := 118140960795 + 1338770 * 2 ^ 59
def prefixEnd_1338770 : Nat := 4983230072969 + 3 ^ 40 * 1338770 * 2
def baseEnd_1338770 : Nat := 229144165273277429972705

theorem tailTrace_1338770 : CollatzResearch.WordTrace tailWord_1338770 prefixEnd_1338770 229144165273277429972705 := by
  unfold tailWord_1338770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12207238339968102139463441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32552635573248272371902509 12207238339968102139463441)
  ·
    refine ⟨9155428754976076604597581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12207238339968102139463441 9155428754976076604597581)
    ·
      refine ⟨3433285783116028726724093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9155428754976076604597581 3433285783116028726724093)
      ·
        refine ⟨1287482168668510772521535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3433285783116028726724093 1287482168668510772521535)
        ·
          refine ⟨1931223253002766158782303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287482168668510772521535 1931223253002766158782303)
          ·
            refine ⟨2896834879504149238173455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931223253002766158782303 2896834879504149238173455)
            ·
              refine ⟨4345252319256223857260183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896834879504149238173455 4345252319256223857260183)
              ·
                refine ⟨6517878478884335785890275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4345252319256223857260183 6517878478884335785890275)
                ·
                  refine ⟨9776817718326503678835413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6517878478884335785890275 9776817718326503678835413)
                  ·
                    refine ⟨229144165273277429972705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9776817718326503678835413 229144165273277429972705)
                    ·
                      rfl

theorem cell23_1338770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1338770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338770 prefixEnd_1338770 := by exact prefixLift 1338770
  have htrace : WordTrace (prefixWord ++ tailWord_1338770) baseStart_1338770 baseEnd_1338770 := by
    simpa [prefixWord, tailWord_1338770, baseEnd_1338770] using wordTrace_append hprefix tailTrace_1338770
  have hstable : (prefixWord ++ tailWord_1338770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338770).length < 2 ^ (prefixWord ++ tailWord_1338770).sum := by decide
  have hdescent : baseEnd_1338770 < baseStart_1338770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338773 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_1338773 : Nat := 118140960795 + 1338773 * 2 ^ 59
def prefixEnd_1338773 : Nat := 4983230072969 + 3 ^ 40 * 1338773 * 2
def baseEnd_1338773 : Nat := 687434036261795778180601

theorem tailTrace_1338773 : CollatzResearch.WordTrace tailWord_1338773 prefixEnd_1338773 687434036261795778180601 := by
  unfold tailWord_1338773
  simp only [CollatzResearch.WordTrace]
  refine ⟨48829062778861540070212973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32552708519241026713475315 48829062778861540070212973)
  ·
    refine ⟨18310898542073077526329865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48829062778861540070212973 18310898542073077526329865)
    ·
      refine ⟨13733173906554808144747399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18310898542073077526329865 13733173906554808144747399)
      ·
        refine ⟨20599760859832212217121099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13733173906554808144747399 20599760859832212217121099)
        ·
          refine ⟨30899641289748318325681649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20599760859832212217121099 30899641289748318325681649)
          ·
            refine ⟨23174730967311238744261237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30899641289748318325681649 23174730967311238744261237)
            ·
              refine ⟨2172631028185428632274491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23174730967311238744261237 2172631028185428632274491)
              ·
                refine ⟨3258946542278142948411737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172631028185428632274491 3258946542278142948411737)
                ·
                  refine ⟨2444209906708607211308803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3258946542278142948411737 2444209906708607211308803)
                  ·
                    refine ⟨3666314860062910816963205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2444209906708607211308803 3666314860062910816963205)
                    ·
                      refine ⟨687434036261795778180601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3666314860062910816963205 687434036261795778180601)
                      ·
                        rfl

theorem cell23_1338773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_1338773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338773 prefixEnd_1338773 := by exact prefixLift 1338773
  have htrace : WordTrace (prefixWord ++ tailWord_1338773) baseStart_1338773 baseEnd_1338773 := by
    simpa [prefixWord, tailWord_1338773, baseEnd_1338773] using wordTrace_append hprefix tailTrace_1338773
  have hstable : (prefixWord ++ tailWord_1338773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338773).length < 2 ^ (prefixWord ++ tailWord_1338773).sum := by decide
  have hdescent : baseEnd_1338773 < baseStart_1338773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338884 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1338884 : Nat := 118140960795 + 1338884 * 2 ^ 59
def prefixEnd_1338884 : Nat := 4983230072969 + 3 ^ 40 * 1338884 * 2
def baseEnd_1338884 : Nat := 687491032614444843892591

theorem tailTrace_1338884 : CollatzResearch.WordTrace tailWord_1338884 prefixEnd_1338884 687491032614444843892591 := by
  unfold tailWord_1338884
  simp only [CollatzResearch.WordTrace]
  refine ⟨24416555640729703013751853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32555407520972937351669137 24416555640729703013751853)
  ·
    refine ⟨9156208365273638630156945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24416555640729703013751853 9156208365273638630156945)
    ·
      refine ⟨6867156273955228972617709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9156208365273638630156945 6867156273955228972617709)
      ·
        refine ⟨2575183602733210864731641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6867156273955228972617709 2575183602733210864731641)
        ·
          refine ⟨1931387702049908148548731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2575183602733210864731641 1931387702049908148548731)
          ·
            refine ⟨2897081553074862222823097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931387702049908148548731 2897081553074862222823097)
            ·
              refine ⟨2172811164806146667117323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897081553074862222823097 2172811164806146667117323)
              ·
                refine ⟨3259216747209220000675985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172811164806146667117323 3259216747209220000675985)
                ·
                  refine ⟨2444412560406915000506989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3259216747209220000675985 2444412560406915000506989)
                  ·
                    refine ⟨916654710152593125190121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2444412560406915000506989 916654710152593125190121)
                    ·
                      refine ⟨687491032614444843892591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916654710152593125190121 687491032614444843892591)
                      ·
                        rfl

theorem cell23_1338884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1338884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338884 prefixEnd_1338884 := by exact prefixLift 1338884
  have htrace : WordTrace (prefixWord ++ tailWord_1338884) baseStart_1338884 baseEnd_1338884 := by
    simpa [prefixWord, tailWord_1338884, baseEnd_1338884] using wordTrace_append hprefix tailTrace_1338884
  have hstable : (prefixWord ++ tailWord_1338884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338884).length < 2 ^ (prefixWord ++ tailWord_1338884).sum := by decide
  have hdescent : baseEnd_1338884 < baseStart_1338884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338930 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1338930 : Nat := 118140960795 + 1338930 * 2 ^ 59
def prefixEnd_1338930 : Nat := 4983230072969 + 3 ^ 40 * 1338930 * 2
def baseEnd_1338930 : Nat := 687514652724551663917379

theorem tailTrace_1338930 : CollatzResearch.WordTrace tailWord_1338930 prefixEnd_1338930 687514652724551663917379 := by
  unfold tailWord_1338930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12208697259823188970919561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32556526026195170589118829 12208697259823188970919561)
  ·
    refine ⟨9156522944867391728189671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12208697259823188970919561 9156522944867391728189671)
    ·
      refine ⟨13734784417301087592284507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9156522944867391728189671 13734784417301087592284507)
      ·
        refine ⟨20602176625951631388426761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13734784417301087592284507 20602176625951631388426761)
        ·
          refine ⟨15451632469463723541320071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20602176625951631388426761 15451632469463723541320071)
          ·
            refine ⟨23177448704195585311980107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15451632469463723541320071 23177448704195585311980107)
            ·
              refine ⟨34766173056293377967970161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23177448704195585311980107 34766173056293377967970161)
              ·
                refine ⟨26074629792220033475977621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34766173056293377967970161 26074629792220033475977621)
                ·
                  refine ⟨1222248271510314069186451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26074629792220033475977621 1222248271510314069186451)
                  ·
                    refine ⟨1833372407265471103779677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1222248271510314069186451 1833372407265471103779677)
                    ·
                      refine ⟨687514652724551663917379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1833372407265471103779677 687514652724551663917379)
                      ·
                        rfl

theorem cell23_1338930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1338930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338930 prefixEnd_1338930 := by exact prefixLift 1338930
  have htrace : WordTrace (prefixWord ++ tailWord_1338930) baseStart_1338930 baseEnd_1338930 := by
    simpa [prefixWord, tailWord_1338930, baseEnd_1338930] using wordTrace_append hprefix tailTrace_1338930
  have hstable : (prefixWord ++ tailWord_1338930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338930).length < 2 ^ (prefixWord ++ tailWord_1338930).sum := by decide
  have hdescent : baseEnd_1338930 < baseStart_1338930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338951 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_1338951 : Nat := 118140960795 + 1338951 * 2 ^ 59
def prefixEnd_1338951 : Nat := 4983230072969 + 3 ^ 40 * 1338951 * 2
def baseEnd_1338951 : Nat := 687525435818296081754783

theorem tailTrace_1338951 : CollatzResearch.WordTrace tailWord_1338951 prefixEnd_1338951 687525435818296081754783 := by
  unfold tailWord_1338951
  simp only [CollatzResearch.WordTrace]
  refine ⟨48835554972216676470192707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32557036648144450980128471 48835554972216676470192707)
  ·
    refine ⟨73253332458325014705289061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48835554972216676470192707 73253332458325014705289061)
    ·
      refine ⟨13734999835935940257241699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73253332458325014705289061 13734999835935940257241699)
      ·
        refine ⟨20602499753903910385862549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13734999835935940257241699 20602499753903910385862549)
        ·
          refine ⟨965742175964245799337307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20602499753903910385862549 965742175964245799337307)
          ·
            refine ⟨1448613263946368699005961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965742175964245799337307 1448613263946368699005961)
            ·
              refine ⟨1086459947959776524254471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448613263946368699005961 1086459947959776524254471)
              ·
                refine ⟨1629689921939664786381707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086459947959776524254471 1629689921939664786381707)
                ·
                  refine ⟨2444534882909497179572561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1629689921939664786381707 2444534882909497179572561)
                  ·
                    refine ⟨1833401162182122884679421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2444534882909497179572561 1833401162182122884679421)
                    ·
                      refine ⟨687525435818296081754783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1833401162182122884679421 687525435818296081754783)
                      ·
                        rfl

theorem cell23_1338951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_1338951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338951 prefixEnd_1338951 := by exact prefixLift 1338951
  have htrace : WordTrace (prefixWord ++ tailWord_1338951) baseStart_1338951 baseEnd_1338951 := by
    simpa [prefixWord, tailWord_1338951, baseEnd_1338951] using wordTrace_append hprefix tailTrace_1338951
  have hstable : (prefixWord ++ tailWord_1338951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338951).length < 2 ^ (prefixWord ++ tailWord_1338951).sum := by decide
  have hdescent : baseEnd_1338951 < baseStart_1338951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338970 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2]
def baseStart_1338970 : Nat := 118140960795 + 1338970 * 2 ^ 59
def prefixEnd_1338970 : Nat := 4983230072969 + 3 ^ 40 * 1338970 * 2
def baseEnd_1338970 : Nat := 687535191950731507417195

theorem tailTrace_1338970 : CollatzResearch.WordTrace tailWord_1338970 prefixEnd_1338970 687535191950731507417195 := by
  unfold tailWord_1338970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12209061989786960678783591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32557498639431895143422909 12209061989786960678783591)
  ·
    refine ⟨18313592984680441018175387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12209061989786960678783591 18313592984680441018175387)
    ·
      refine ⟨27470389477020661527263081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18313592984680441018175387 27470389477020661527263081)
      ·
        refine ⟨20602792107765496145447311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27470389477020661527263081 20602792107765496145447311)
        ·
          refine ⟨30904188161648244218170967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20602792107765496145447311 30904188161648244218170967)
          ·
            refine ⟨46356282242472366327256451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30904188161648244218170967 46356282242472366327256451)
            ·
              refine ⟨69534423363708549490884677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46356282242472366327256451 69534423363708549490884677)
              ·
                refine ⟨13037704380695353029540877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69534423363708549490884677 13037704380695353029540877)
                ·
                  refine ⟨4889139142760757386077829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13037704380695353029540877 4889139142760757386077829)
                  ·
                    refine ⟨916713589267642009889593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889139142760757386077829 916713589267642009889593)
                    ·
                      refine ⟨687535191950731507417195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916713589267642009889593 687535191950731507417195)
                      ·
                        rfl

theorem cell23_1338970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_1338970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1338970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1338970 prefixEnd_1338970 := by exact prefixLift 1338970
  have htrace : WordTrace (prefixWord ++ tailWord_1338970) baseStart_1338970 baseEnd_1338970 := by
    simpa [prefixWord, tailWord_1338970, baseEnd_1338970] using wordTrace_append hprefix tailTrace_1338970
  have hstable : (prefixWord ++ tailWord_1338970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338970).length < 2 ^ (prefixWord ++ tailWord_1338970).sum := by decide
  have hdescent : baseEnd_1338970 < baseStart_1338970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339038 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_1339038 : Nat := 118140960795 + 1339038 * 2 ^ 59
def prefixEnd_1339038 : Nat := 4983230072969 + 3 ^ 40 * 1339038 * 2
def baseEnd_1339038 : Nat := 687570108635237241366883

theorem tailTrace_1339038 : CollatzResearch.WordTrace tailWord_1339038 prefixEnd_1339038 687570108635237241366883 := by
  unfold tailWord_1339038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104841015362686291076221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32559152081934326885739845 6104841015362686291076221)
  ·
    refine ⟨2289315380761007359153583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6104841015362686291076221 2289315380761007359153583)
    ·
      refine ⟨3433973071141511038730375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289315380761007359153583 3433973071141511038730375)
      ·
        refine ⟨5150959606712266558095563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433973071141511038730375 5150959606712266558095563)
        ·
          refine ⟨7726439410068399837143345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150959606712266558095563 7726439410068399837143345)
          ·
            refine ⟨5794829557551299877857509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7726439410068399837143345 5794829557551299877857509)
            ·
              refine ⟨1086530542040868727098283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5794829557551299877857509 1086530542040868727098283)
              ·
                refine ⟨1629795813061303090647425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086530542040868727098283 1629795813061303090647425)
                ·
                  refine ⟨1222346859795977317985569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1629795813061303090647425 1222346859795977317985569)
                  ·
                    refine ⟨916760144846982988489177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1222346859795977317985569 916760144846982988489177)
                    ·
                      refine ⟨687570108635237241366883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916760144846982988489177 687570108635237241366883)
                      ·
                        rfl

theorem cell23_1339038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_1339038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339038 prefixEnd_1339038 := by exact prefixLift 1339038
  have htrace : WordTrace (prefixWord ++ tailWord_1339038) baseStart_1339038 baseEnd_1339038 := by
    simpa [prefixWord, tailWord_1339038, baseEnd_1339038] using wordTrace_append hprefix tailTrace_1339038
  have hstable : (prefixWord ++ tailWord_1339038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339038).length < 2 ^ (prefixWord ++ tailWord_1339038).sum := by decide
  have hdescent : baseEnd_1339038 < baseStart_1339038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339078 : List Nat := [6, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1339078 : Nat := 118140960795 + 1339078 * 2 ^ 59
def prefixEnd_1339078 : Nat := 4983230072969 + 3 ^ 40 * 1339078 * 2
def baseEnd_1339078 : Nat := 76398960873490787207411

theorem tailTrace_1339078 : CollatzResearch.WordTrace tailWord_1339078 prefixEnd_1339078 76398960873490787207411 := by
  unfold tailWord_1339078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526255845086143036252059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32560124695171051440043925 1526255845086143036252059)
  ·
    refine ⟨2289383767629214554378089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526255845086143036252059 2289383767629214554378089)
    ·
      refine ⟨1717037825721910915783567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2289383767629214554378089 1717037825721910915783567)
      ·
        refine ⟨2575556738582866373675351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717037825721910915783567 2575556738582866373675351)
        ·
          refine ⟨3863335107874299560513027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575556738582866373675351 3863335107874299560513027)
          ·
            refine ⟨5795002661811449340769541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863335107874299560513027 5795002661811449340769541)
            ·
              refine ⟨1086562999089646751394289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5795002661811449340769541 1086562999089646751394289)
              ·
                refine ⟨814922249317235063545717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086562999089646751394289 814922249317235063545717)
                ·
                  refine ⟨76398960873490787207411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 814922249317235063545717 76398960873490787207411)
                  ·
                    rfl

theorem cell23_1339078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1339078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339078 prefixEnd_1339078 := by exact prefixLift 1339078
  have htrace : WordTrace (prefixWord ++ tailWord_1339078) baseStart_1339078 baseEnd_1339078 := by
    simpa [prefixWord, tailWord_1339078, baseEnd_1339078] using wordTrace_append hprefix tailTrace_1339078
  have hstable : (prefixWord ++ tailWord_1339078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339078).length < 2 ^ (prefixWord ++ tailWord_1339078).sum := by decide
  have hdescent : baseEnd_1339078 < baseStart_1339078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339083 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 8]
def baseStart_1339083 : Nat := 118140960795 + 1339083 * 2 ^ 59
def prefixEnd_1339083 : Nat := 4983230072969 + 3 ^ 40 * 1339083 * 2
def baseEnd_1339083 : Nat := 76399246140521062811575

theorem tailTrace_1339083 : CollatzResearch.WordTrace tailWord_1339083 prefixEnd_1339083 76399246140521062811575 := by
  unfold tailWord_1339083
  simp only [CollatzResearch.WordTrace]
  refine ⟨48840369407738463013997903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32560246271825642009331935 48840369407738463013997903)
  ·
    refine ⟨73260554111607694520996855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48840369407738463013997903 73260554111607694520996855)
    ·
      refine ⟨109890831167411541781495283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73260554111607694520996855 109890831167411541781495283)
      ·
        refine ⟨164836246751117312672242925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109890831167411541781495283 164836246751117312672242925)
        ·
          refine ⟨61813592531668992252091097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164836246751117312672242925 61813592531668992252091097)
          ·
            refine ⟨46360194398751744189068323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61813592531668992252091097 46360194398751744189068323)
            ·
              refine ⟨69540291598127616283602485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46360194398751744189068323 69540291598127616283602485)
              ·
                refine ⟨6519402337324464026587733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69540291598127616283602485 6519402337324464026587733)
                ·
                  refine ⟨76399246140521062811575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6519402337324464026587733 76399246140521062811575)
                  ·
                    rfl

theorem cell23_1339083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 8].length) (baseStart_1339083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339083 prefixEnd_1339083 := by exact prefixLift 1339083
  have htrace : WordTrace (prefixWord ++ tailWord_1339083) baseStart_1339083 baseEnd_1339083 := by
    simpa [prefixWord, tailWord_1339083, baseEnd_1339083] using wordTrace_append hprefix tailTrace_1339083
  have hstable : (prefixWord ++ tailWord_1339083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339083).length < 2 ^ (prefixWord ++ tailWord_1339083).sum := by decide
  have hdescent : baseEnd_1339083 < baseStart_1339083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339111 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1339111 : Nat := 118140960795 + 1339111 * 2 ^ 59
def prefixEnd_1339111 : Nat := 4983230072969 + 3 ^ 40 * 1339111 * 2
def baseEnd_1339111 : Nat := 687607592723015455754047

theorem tailTrace_1339111 : CollatzResearch.WordTrace tailWord_1339111 prefixEnd_1339111 687607592723015455754047 := by
  unfold tailWord_1339111
  simp only [CollatzResearch.WordTrace]
  refine ⟨48841390651637023796017187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32560927101091349197344791 48841390651637023796017187)
  ·
    refine ⟨73262085977455535694025781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48841390651637023796017187 73262085977455535694025781)
    ·
      refine ⟨6868320560386456471314917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73262085977455535694025781 6868320560386456471314917)
      ·
        refine ⟨1287810105072460588371547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6868320560386456471314917 1287810105072460588371547)
        ·
          refine ⟨1931715157608690882557321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287810105072460588371547 1931715157608690882557321)
          ·
            refine ⟨1448786368206518161917991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931715157608690882557321 1448786368206518161917991)
            ·
              refine ⟨2173179552309777242876987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448786368206518161917991 2173179552309777242876987)
              ·
                refine ⟨3259769328464665864315481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173179552309777242876987 3259769328464665864315481)
                ·
                  refine ⟨2444826996348499398236611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3259769328464665864315481 2444826996348499398236611)
                  ·
                    refine ⟨3667240494522749097354917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2444826996348499398236611 3667240494522749097354917)
                    ·
                      refine ⟨687607592723015455754047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3667240494522749097354917 687607592723015455754047)
                      ·
                        rfl

theorem cell23_1339111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1339111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339111 prefixEnd_1339111 := by exact prefixLift 1339111
  have htrace : WordTrace (prefixWord ++ tailWord_1339111) baseStart_1339111 baseEnd_1339111 := by
    simpa [prefixWord, tailWord_1339111, baseEnd_1339111] using wordTrace_append hprefix tailTrace_1339111
  have hstable : (prefixWord ++ tailWord_1339111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339111).length < 2 ^ (prefixWord ++ tailWord_1339111).sum := by decide
  have hdescent : baseEnd_1339111 < baseStart_1339111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339124 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1339124 : Nat := 118140960795 + 1339124 * 2 ^ 59
def prefixEnd_1339124 : Nat := 4983230072969 + 3 ^ 40 * 1339124 * 2
def baseEnd_1339124 : Nat := 687614267971523904891487

theorem tailTrace_1339124 : CollatzResearch.WordTrace tailWord_1339124 prefixEnd_1339124 687614267971523904891487 := by
  unfold tailWord_1339124
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420932400294963508120213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32561243200393284677493617 24420932400294963508120213)
  ·
    refine ⟨1144731206263826414443135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24420932400294963508120213 1144731206263826414443135)
    ·
      refine ⟨1717096809395739621664703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144731206263826414443135 1717096809395739621664703)
      ·
        refine ⟨2575645214093609432497055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717096809395739621664703 2575645214093609432497055)
        ·
          refine ⟨3863467821140414148745583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575645214093609432497055 3863467821140414148745583)
          ·
            refine ⟨5795201731710621223118375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863467821140414148745583 5795201731710621223118375)
            ·
              refine ⟨8692802597565931834677563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795201731710621223118375 8692802597565931834677563)
              ·
                refine ⟨13039203896348897752016345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8692802597565931834677563 13039203896348897752016345)
                ·
                  refine ⟨9779402922261673314012259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13039203896348897752016345 9779402922261673314012259)
                  ·
                    refine ⟨14669104383392509971018389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9779402922261673314012259 14669104383392509971018389)
                    ·
                      refine ⟨687614267971523904891487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14669104383392509971018389 687614267971523904891487)
                      ·
                        rfl

theorem cell23_1339124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1339124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339124 prefixEnd_1339124 := by exact prefixLift 1339124
  have htrace : WordTrace (prefixWord ++ tailWord_1339124) baseStart_1339124 baseEnd_1339124 := by
    simpa [prefixWord, tailWord_1339124, baseEnd_1339124] using wordTrace_append hprefix tailTrace_1339124
  have hstable : (prefixWord ++ tailWord_1339124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339124).length < 2 ^ (prefixWord ++ tailWord_1339124).sum := by decide
  have hdescent : baseEnd_1339124 < baseStart_1339124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339144 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_1339144 : Nat := 118140960795 + 1339144 * 2 ^ 59
def prefixEnd_1339144 : Nat := 4983230072969 + 3 ^ 40 * 1339144 * 2
def baseEnd_1339144 : Nat := 687624537584613826641395

theorem tailTrace_1339144 : CollatzResearch.WordTrace tailWord_1339144 prefixEnd_1339144 687624537584613826641395 := by
  unfold tailWord_1339144
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421297130258735215984243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32561729507011646954645657 24421297130258735215984243)
  ·
    refine ⟨36631945695388102823976365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24421297130258735215984243 36631945695388102823976365)
    ·
      refine ⟨13736979635770538558991137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36631945695388102823976365 13736979635770538558991137)
      ·
        refine ⟨10302734726827903919243353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13736979635770538558991137 10302734726827903919243353)
        ·
          refine ⟨7727051045120927939432515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10302734726827903919243353 7727051045120927939432515)
          ·
            refine ⟨11590576567681391909148773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727051045120927939432515 11590576567681391909148773)
            ·
              refine ⟨2173233106440260982965395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11590576567681391909148773 2173233106440260982965395)
              ·
                refine ⟨3259849659660391474448093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173233106440260982965395 3259849659660391474448093)
                ·
                  refine ⟨1222443622372646802918035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3259849659660391474448093 1222443622372646802918035)
                  ·
                    refine ⟨1833665433558970204377053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1222443622372646802918035 1833665433558970204377053)
                    ·
                      refine ⟨687624537584613826641395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1833665433558970204377053 687624537584613826641395)
                      ·
                        rfl

theorem cell23_1339144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_1339144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339144 prefixEnd_1339144 := by exact prefixLift 1339144
  have htrace : WordTrace (prefixWord ++ tailWord_1339144) baseStart_1339144 baseEnd_1339144 := by
    simpa [prefixWord, tailWord_1339144, baseEnd_1339144] using wordTrace_append hprefix tailTrace_1339144
  have hstable : (prefixWord ++ tailWord_1339144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339144).length < 2 ^ (prefixWord ++ tailWord_1339144).sum := by decide
  have hdescent : baseEnd_1339144 < baseStart_1339144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339167 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 2, 6, 2]
def baseStart_1339167 : Nat := 118140960795 + 1339167 * 2 ^ 59
def prefixEnd_1339167 : Nat := 4983230072969 + 3 ^ 40 * 1339167 * 2
def baseEnd_1339167 : Nat := 687636347639667236653789

theorem tailTrace_1339167 : CollatzResearch.WordTrace tailWord_1339167 prefixEnd_1339167 687636347639667236653789 := by
  unfold tailWord_1339167
  simp only [CollatzResearch.WordTrace]
  refine ⟨48843433139434145360055755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32562288759622763573370503 48843433139434145360055755)
  ·
    refine ⟨73265149709151218040083633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48843433139434145360055755 73265149709151218040083633)
    ·
      refine ⟨54948862281863413530062725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73265149709151218040083633 54948862281863413530062725)
      ·
        refine ⟨10302911677849390036886761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54948862281863413530062725 10302911677849390036886761)
        ·
          refine ⟨7727183758387042527665071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10302911677849390036886761 7727183758387042527665071)
          ·
            refine ⟨11590775637580563791497607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727183758387042527665071 11590775637580563791497607)
            ·
              refine ⟨17386163456370845687246411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11590775637580563791497607 17386163456370845687246411)
              ·
                refine ⟨26079245184556268530869617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17386163456370845687246411 26079245184556268530869617)
                ·
                  refine ⟨19559433888417201398152213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26079245184556268530869617 19559433888417201398152213)
                  ·
                    refine ⟨916848463519556315538385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19559433888417201398152213 916848463519556315538385)
                    ·
                      refine ⟨687636347639667236653789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916848463519556315538385 687636347639667236653789)
                      ·
                        rfl

theorem cell23_1339167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_1339167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339167 prefixEnd_1339167 := by exact prefixLift 1339167
  have htrace : WordTrace (prefixWord ++ tailWord_1339167) baseStart_1339167 baseEnd_1339167 := by
    simpa [prefixWord, tailWord_1339167, baseEnd_1339167] using wordTrace_append hprefix tailTrace_1339167
  have hstable : (prefixWord ++ tailWord_1339167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339167).length < 2 ^ (prefixWord ++ tailWord_1339167).sum := by decide
  have hdescent : baseEnd_1339167 < baseStart_1339167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339197 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1339197 : Nat := 118140960795 + 1339197 * 2 ^ 59
def prefixEnd_1339197 : Nat := 4983230072969 + 3 ^ 40 * 1339197 * 2
def baseEnd_1339197 : Nat := 687651752059302119278651

theorem tailTrace_1339197 : CollatzResearch.WordTrace tailWord_1339197 prefixEnd_1339197 687651752059302119278651 := by
  unfold tailWord_1339197
  simp only [CollatzResearch.WordTrace]
  refine ⟨48844527329325460483647845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32563018219550306989098563 48844527329325460483647845)
  ·
    refine ⟨9158348874248523840683971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48844527329325460483647845 9158348874248523840683971)
    ·
      refine ⟨13737523311372785761025957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9158348874248523840683971 13737523311372785761025957)
      ·
        refine ⟨2575785620882397330192367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13737523311372785761025957 2575785620882397330192367)
        ·
          refine ⟨3863678431323595995288551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575785620882397330192367 3863678431323595995288551)
          ·
            refine ⟨5795517646985393992932827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863678431323595995288551 5795517646985393992932827)
            ·
              refine ⟨8693276470478090989399241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795517646985393992932827 8693276470478090989399241)
              ·
                refine ⟨6519957352858568242049431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8693276470478090989399241 6519957352858568242049431)
                ·
                  refine ⟨9779936029287852363074147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6519957352858568242049431 9779936029287852363074147)
                  ·
                    refine ⟨14669904043931778544611221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9779936029287852363074147 14669904043931778544611221)
                    ·
                      refine ⟨687651752059302119278651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14669904043931778544611221 687651752059302119278651)
                      ·
                        rfl

theorem cell23_1339197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1339197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339197 prefixEnd_1339197 := by exact prefixLift 1339197
  have htrace : WordTrace (prefixWord ++ tailWord_1339197) baseStart_1339197 baseEnd_1339197 := by
    simpa [prefixWord, tailWord_1339197, baseEnd_1339197] using wordTrace_append hprefix tailTrace_1339197
  have hstable : (prefixWord ++ tailWord_1339197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339197).length < 2 ^ (prefixWord ++ tailWord_1339197).sum := by decide
  have hdescent : baseEnd_1339197 < baseStart_1339197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339210 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1339210 : Nat := 118140960795 + 1339210 * 2 ^ 59
def prefixEnd_1339210 : Nat := 4983230072969 + 3 ^ 40 * 1339210 * 2
def baseEnd_1339210 : Nat := 687658427307810568416091

theorem tailTrace_1339210 : CollatzResearch.WordTrace tailWord_1339210 prefixEnd_1339210 687658427307810568416091 := by
  unfold tailWord_1339210
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211250369569590925967771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32563334318852242469247389 12211250369569590925967771)
  ·
    refine ⟨18316875554354386388951657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12211250369569590925967771 18316875554354386388951657)
    ·
      refine ⟨13737656665765789791713743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18316875554354386388951657 13737656665765789791713743)
      ·
        refine ⟨20606484998648684687570615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13737656665765789791713743 20606484998648684687570615)
        ·
          refine ⟨30909727497973027031355923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20606484998648684687570615 30909727497973027031355923)
          ·
            refine ⟨46364591246959540547033885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30909727497973027031355923 46364591246959540547033885)
            ·
              refine ⟨17386721717609827705137707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46364591246959540547033885 17386721717609827705137707)
              ·
                refine ⟨26080082576414741557706561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17386721717609827705137707 26080082576414741557706561)
                ·
                  refine ⟨19560061932311056168279921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26080082576414741557706561 19560061932311056168279921)
                  ·
                    refine ⟨14670046449233292126209941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19560061932311056168279921 14670046449233292126209941)
                    ·
                      refine ⟨687658427307810568416091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14670046449233292126209941 687658427307810568416091)
                      ·
                        rfl

theorem cell23_1339210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1339210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339210 prefixEnd_1339210 := by exact prefixLift 1339210
  have htrace : WordTrace (prefixWord ++ tailWord_1339210) baseStart_1339210 baseEnd_1339210 := by
    simpa [prefixWord, tailWord_1339210, baseEnd_1339210] using wordTrace_append hprefix tailTrace_1339210
  have hstable : (prefixWord ++ tailWord_1339210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339210).length < 2 ^ (prefixWord ++ tailWord_1339210).sum := by decide
  have hdescent : baseEnd_1339210 < baseStart_1339210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339221 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_1339221 : Nat := 118140960795 + 1339221 * 2 ^ 59
def prefixEnd_1339221 : Nat := 4983230072969 + 3 ^ 40 * 1339221 * 2
def baseEnd_1339221 : Nat := 687664075595010025378541

theorem tailTrace_1339221 : CollatzResearch.WordTrace tailWord_1339221 prefixEnd_1339221 687664075595010025378541 := by
  unfold tailWord_1339221
  simp only [CollatzResearch.WordTrace]
  refine ⟨48845402681238512582521517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32563601787492341721681011 48845402681238512582521517)
  ·
    refine ⟨18317026005464442218445569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48845402681238512582521517 18317026005464442218445569)
    ·
      refine ⟨13737769504098331663834177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18317026005464442218445569 13737769504098331663834177)
      ·
        refine ⟨10303327128073748747875633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13737769504098331663834177 10303327128073748747875633)
        ·
          refine ⟨7727495346055311560906725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10303327128073748747875633 7727495346055311560906725)
          ·
            refine ⟨1448905377385370917670011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7727495346055311560906725 1448905377385370917670011)
            ·
              refine ⟨2173358066078056376505017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448905377385370917670011 2173358066078056376505017)
              ·
                refine ⟨1630018549558542282378763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173358066078056376505017 1630018549558542282378763)
                ·
                  refine ⟨2445027824337813423568145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630018549558542282378763 2445027824337813423568145)
                  ·
                    refine ⟨1833770868253360067676109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2445027824337813423568145 1833770868253360067676109)
                    ·
                      refine ⟨687664075595010025378541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1833770868253360067676109 687664075595010025378541)
                      ·
                        rfl

theorem cell23_1339221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_1339221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339221 prefixEnd_1339221 := by exact prefixLift 1339221
  have htrace : WordTrace (prefixWord ++ tailWord_1339221) baseStart_1339221 baseEnd_1339221 := by
    simpa [prefixWord, tailWord_1339221, baseEnd_1339221] using wordTrace_append hprefix tailTrace_1339221
  have hstable : (prefixWord ++ tailWord_1339221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339221).length < 2 ^ (prefixWord ++ tailWord_1339221).sum := by decide
  have hdescent : baseEnd_1339221 < baseStart_1339221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339234 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1339234 : Nat := 118140960795 + 1339234 * 2 ^ 59
def prefixEnd_1339234 : Nat := 4983230072969 + 3 ^ 40 * 1339234 * 2
def baseEnd_1339234 : Nat := 687670750843518474515981

theorem tailTrace_1339234 : CollatzResearch.WordTrace tailWord_1339234 prefixEnd_1339234 687670750843518474515981 := by
  unfold tailWord_1339234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211469207547853950686189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32563917886794277201829837 12211469207547853950686189)
  ·
    refine ⟨4579300952830445231507321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12211469207547853950686189 4579300952830445231507321)
    ·
      refine ⟨3434475714622833923630491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4579300952830445231507321 3434475714622833923630491)
      ·
        refine ⟨5151713571934250885445737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3434475714622833923630491 5151713571934250885445737)
        ·
          refine ⟨3863785178950688164084303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5151713571934250885445737 3863785178950688164084303)
          ·
            refine ⟨5795677768426032246126455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863785178950688164084303 5795677768426032246126455)
            ·
              refine ⟨8693516652639048369189683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795677768426032246126455 8693516652639048369189683)
              ·
                refine ⟨13040274978958572553784525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8693516652639048369189683 13040274978958572553784525)
                ·
                  refine ⟨4890103117109464707669197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13040274978958572553784525 4890103117109464707669197)
                  ·
                    refine ⟨1833788668916049265375949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4890103117109464707669197 1833788668916049265375949)
                    ·
                      refine ⟨687670750843518474515981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1833788668916049265375949 687670750843518474515981)
                      ·
                        rfl

theorem cell23_1339234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1339234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339234 prefixEnd_1339234 := by exact prefixLift 1339234
  have htrace : WordTrace (prefixWord ++ tailWord_1339234) baseStart_1339234 baseEnd_1339234 := by
    simpa [prefixWord, tailWord_1339234, baseEnd_1339234] using wordTrace_append hprefix tailTrace_1339234
  have hstable : (prefixWord ++ tailWord_1339234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339234).length < 2 ^ (prefixWord ++ tailWord_1339234).sum := by decide
  have hdescent : baseEnd_1339234 < baseStart_1339234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339267 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 2, 6]
def baseStart_1339267 : Nat := 118140960795 + 1339267 * 2 ^ 59
def prefixEnd_1339267 : Nat := 4983230072969 + 3 ^ 40 * 1339267 * 2
def baseEnd_1339267 : Nat := 229229231901705615134443

theorem tailTrace_1339267 : CollatzResearch.WordTrace tailWord_1339267 prefixEnd_1339267 229229231901705615134443 := by
  unfold tailWord_1339267
  simp only [CollatzResearch.WordTrace]
  refine ⟨48847080439071862438696055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32564720292714574959130703 48847080439071862438696055)
  ·
    refine ⟨73270620658607793658044083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48847080439071862438696055 73270620658607793658044083)
    ·
      refine ⟨109905930987911690487066125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73270620658607793658044083 109905930987911690487066125)
      ·
        refine ⟨41214724120466883932649797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109905930987911690487066125 41214724120466883932649797)
        ·
          refine ⟨7727760772587540737371837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41214724120466883932649797 7727760772587540737371837)
          ·
            refine ⟨2897910289720327776514439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7727760772587540737371837 2897910289720327776514439)
            ·
              refine ⟨4346865434580491664771659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897910289720327776514439 4346865434580491664771659)
              ·
                refine ⟨6520298151870737497157489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4346865434580491664771659 6520298151870737497157489)
                ·
                  refine ⟨4890223613903053122868117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6520298151870737497157489 4890223613903053122868117)
                  ·
                    refine ⟨229229231901705615134443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4890223613903053122868117 229229231901705615134443)
                    ·
                      rfl

theorem cell23_1339267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 6].length) (baseStart_1339267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339267 prefixEnd_1339267 := by exact prefixLift 1339267
  have htrace : WordTrace (prefixWord ++ tailWord_1339267) baseStart_1339267 baseEnd_1339267 := by
    simpa [prefixWord, tailWord_1339267, baseEnd_1339267] using wordTrace_append hprefix tailTrace_1339267
  have hstable : (prefixWord ++ tailWord_1339267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339267).length < 2 ^ (prefixWord ++ tailWord_1339267).sum := by decide
  have hdescent : baseEnd_1339267 < baseStart_1339267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339280 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 9]
def baseStart_1339280 : Nat := 118140960795 + 1339280 * 2 ^ 59
def prefixEnd_1339280 : Nat := 4983230072969 + 3 ^ 40 * 1339280 * 2
def baseEnd_1339280 : Nat := 76410485661513921615641

theorem tailTrace_1339280 : CollatzResearch.WordTrace tailWord_1339280 prefixEnd_1339280 76410485661513921615641 := by
  unfold tailWord_1339280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24423777294012382829459647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32565036392016510439279529 24423777294012382829459647)
  ·
    refine ⟨36635665941018574244189471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24423777294012382829459647 36635665941018574244189471)
    ·
      refine ⟨54953498911527861366284207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36635665941018574244189471 54953498911527861366284207)
      ·
        refine ⟨82430248367291792049426311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54953498911527861366284207 82430248367291792049426311)
        ·
          refine ⟨123645372550937688074139467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82430248367291792049426311 123645372550937688074139467)
          ·
            refine ⟨185468058826406532111209201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123645372550937688074139467 185468058826406532111209201)
            ·
              refine ⟨139101044119804899083406901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185468058826406532111209201 139101044119804899083406901)
              ·
                refine ⟨13040722886231709289069397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139101044119804899083406901 13040722886231709289069397)
                ·
                  refine ⟨76410485661513921615641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13040722886231709289069397 76410485661513921615641)
                  ·
                    rfl

theorem cell23_1339280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_1339280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339280 prefixEnd_1339280 := by exact prefixLift 1339280
  have htrace : WordTrace (prefixWord ++ tailWord_1339280) baseStart_1339280 baseEnd_1339280 := by
    simpa [prefixWord, tailWord_1339280, baseEnd_1339280] using wordTrace_append hprefix tailTrace_1339280
  have hstable : (prefixWord ++ tailWord_1339280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339280).length < 2 ^ (prefixWord ++ tailWord_1339280).sum := by decide
  have hdescent : baseEnd_1339280 < baseStart_1339280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339295 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 1, 3, 2]
def baseStart_1339295 : Nat := 118140960795 + 1339295 * 2 ^ 59
def prefixEnd_1339295 : Nat := 4983230072969 + 3 ^ 40 * 1339295 * 2
def baseEnd_1339295 : Nat := 687702073163442735853201

theorem tailTrace_1339295 : CollatzResearch.WordTrace tailWord_1339295 prefixEnd_1339295 687702073163442735853201 := by
  unfold tailWord_1339295
  simp only [CollatzResearch.WordTrace]
  refine ⟨48848101682970423220715339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32565401121980282147143559 48848101682970423220715339)
  ·
    refine ⟨73272152524455634831073009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48848101682970423220715339 73272152524455634831073009)
    ·
      refine ⟨54954114393341726123304757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73272152524455634831073009 54954114393341726123304757)
      ·
        refine ⟨5151948224375786824059821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54954114393341726123304757 5151948224375786824059821)
        ·
          refine ⟨1931980584140920059022433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5151948224375786824059821 1931980584140920059022433)
          ·
            refine ⟨1448985438105690044266825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931980584140920059022433 1448985438105690044266825)
            ·
              refine ⟨1086739078579267533200119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448985438105690044266825 1086739078579267533200119)
              ·
                refine ⟨1630108617868901299800179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086739078579267533200119 1630108617868901299800179)
                ·
                  refine ⟨2445162926803351949700269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630108617868901299800179 2445162926803351949700269)
                  ·
                    refine ⟨916936097551256981137601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445162926803351949700269 916936097551256981137601)
                    ·
                      refine ⟨687702073163442735853201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916936097551256981137601 687702073163442735853201)
                      ·
                        rfl

theorem cell23_1339295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_1339295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339295 prefixEnd_1339295 := by exact prefixLift 1339295
  have htrace : WordTrace (prefixWord ++ tailWord_1339295) baseStart_1339295 baseEnd_1339295 := by
    simpa [prefixWord, tailWord_1339295, baseEnd_1339295] using wordTrace_append hprefix tailTrace_1339295
  have hstable : (prefixWord ++ tailWord_1339295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339295).length < 2 ^ (prefixWord ++ tailWord_1339295).sum := by decide
  have hdescent : baseEnd_1339295 < baseStart_1339295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339325 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_1339325 : Nat := 118140960795 + 1339325 * 2 ^ 59
def prefixEnd_1339325 : Nat := 4983230072969 + 3 ^ 40 * 1339325 * 2
def baseEnd_1339325 : Nat := 687717477583077618478063

theorem tailTrace_1339325 : CollatzResearch.WordTrace tailWord_1339325 prefixEnd_1339325 687717477583077618478063 := by
  unfold tailWord_1339325
  simp only [CollatzResearch.WordTrace]
  refine ⟨48849195872861738344307429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32566130581907825562871619 48849195872861738344307429)
  ·
    refine ⟨9159224226161575939557643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48849195872861738344307429 9159224226161575939557643)
    ·
      refine ⟨13738836339242363909336465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9159224226161575939557643 13738836339242363909336465)
      ·
        refine ⟨10304127254431772932002349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13738836339242363909336465 10304127254431772932002349)
        ·
          refine ⟨3864047720411914849500881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10304127254431772932002349 3864047720411914849500881)
          ·
            refine ⟨2898035790308936137125661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3864047720411914849500881 2898035790308936137125661)
            ·
              refine ⟨1086763421365851051422123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2898035790308936137125661 1086763421365851051422123)
              ·
                refine ⟨1630145132048776577133185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086763421365851051422123 1630145132048776577133185)
                ·
                  refine ⟨1222608849036582432849889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1630145132048776577133185 1222608849036582432849889)
                  ·
                    refine ⟨916956636777436824637417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1222608849036582432849889 916956636777436824637417)
                    ·
                      refine ⟨687717477583077618478063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 916956636777436824637417 687717477583077618478063)
                      ·
                        rfl

theorem cell23_1339325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_1339325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339325 prefixEnd_1339325 := by exact prefixLift 1339325
  have htrace : WordTrace (prefixWord ++ tailWord_1339325) baseStart_1339325 baseEnd_1339325 := by
    simpa [prefixWord, tailWord_1339325, baseEnd_1339325] using wordTrace_append hprefix tailTrace_1339325
  have hstable : (prefixWord ++ tailWord_1339325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339325).length < 2 ^ (prefixWord ++ tailWord_1339325).sum := by decide
  have hdescent : baseEnd_1339325 < baseStart_1339325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339364 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_1339364 : Nat := 118140960795 + 1339364 * 2 ^ 59
def prefixEnd_1339364 : Nat := 4983230072969 + 3 ^ 40 * 1339364 * 2
def baseEnd_1339364 : Nat := 687737503328602965890383

theorem tailTrace_1339364 : CollatzResearch.WordTrace tailWord_1339364 prefixEnd_1339364 687737503328602965890383 := by
  unfold tailWord_1339364
  simp only [CollatzResearch.WordTrace]
  refine ⟨24425309159860224002488573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32567078879813632003318097 24425309159860224002488573)
  ·
    refine ⟨9159490934947584000933215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24425309159860224002488573 9159490934947584000933215)
    ·
      refine ⟨13739236402421376001399823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9159490934947584000933215 13739236402421376001399823)
      ·
        refine ⟨20608854603632064002099735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13739236402421376001399823 20608854603632064002099735)
        ·
          refine ⟨30913281905448096003149603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20608854603632064002099735 30913281905448096003149603)
          ·
            refine ⟨46369922858172144004724405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30913281905448096003149603 46369922858172144004724405)
            ·
              refine ⟨4347180267953638500442913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46369922858172144004724405 4347180267953638500442913)
              ·
                refine ⟨3260385200965228875332185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347180267953638500442913 3260385200965228875332185)
                ·
                  refine ⟨2445288900723921656499139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3260385200965228875332185 2445288900723921656499139)
                  ·
                    refine ⟨3667933351085882484748709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2445288900723921656499139 3667933351085882484748709)
                    ·
                      refine ⟨687737503328602965890383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3667933351085882484748709 687737503328602965890383)
                      ·
                        rfl

theorem cell23_1339364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_1339364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339364 prefixEnd_1339364 := by exact prefixLift 1339364
  have htrace : WordTrace (prefixWord ++ tailWord_1339364) baseStart_1339364 baseEnd_1339364 := by
    simpa [prefixWord, tailWord_1339364, baseEnd_1339364] using wordTrace_append hprefix tailTrace_1339364
  have hstable : (prefixWord ++ tailWord_1339364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339364).length < 2 ^ (prefixWord ++ tailWord_1339364).sum := by decide
  have hdescent : baseEnd_1339364 < baseStart_1339364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339421 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 6]
def baseStart_1339421 : Nat := 118140960795 + 1339421 * 2 ^ 59
def prefixEnd_1339421 : Nat := 4983230072969 + 3 ^ 40 * 1339421 * 2
def baseEnd_1339421 : Nat := 76418530191767693653069

theorem tailTrace_1339421 : CollatzResearch.WordTrace tailWord_1339421 prefixEnd_1339421 76418530191767693653069 := by
  unfold tailWord_1339421
  simp only [CollatzResearch.WordTrace]
  refine ⟨48852697280513946739802117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32568464853675964493201411 48852697280513946739802117)
  ·
    refine ⟨9159880740096365013712897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48852697280513946739802117 9159880740096365013712897)
    ·
      refine ⟨6869910555072273760284673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9159880740096365013712897 6869910555072273760284673)
      ·
        refine ⟨5152432916304205320213505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6869910555072273760284673 5152432916304205320213505)
        ·
          refine ⟨3864324687228153990160129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5152432916304205320213505 3864324687228153990160129)
          ·
            refine ⟨2898243515421115492620097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3864324687228153990160129 2898243515421115492620097)
            ·
              refine ⟨2173682636565836619465073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2898243515421115492620097 2173682636565836619465073)
              ·
                refine ⟨1630261977424377464598805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173682636565836619465073 1630261977424377464598805)
                ·
                  refine ⟨76418530191767693653069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1630261977424377464598805 76418530191767693653069)
                  ·
                    rfl

theorem cell23_1339421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_1339421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339421 prefixEnd_1339421 := by exact prefixLift 1339421
  have htrace : WordTrace (prefixWord ++ tailWord_1339421) baseStart_1339421 baseEnd_1339421 := by
    simpa [prefixWord, tailWord_1339421, baseEnd_1339421] using wordTrace_append hprefix tailTrace_1339421
  have hstable : (prefixWord ++ tailWord_1339421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339421).length < 2 ^ (prefixWord ++ tailWord_1339421).sum := by decide
  have hdescent : baseEnd_1339421 < baseStart_1339421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339448 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_1339448 : Nat := 118140960795 + 1339448 * 2 ^ 59
def prefixEnd_1339448 : Nat := 4983230072969 + 3 ^ 40 * 1339448 * 2
def baseEnd_1339448 : Nat := 687780635703580637239997

theorem tailTrace_1339448 : CollatzResearch.WordTrace tailWord_1339448 prefixEnd_1339448 687780635703580637239997 := by
  unfold tailWord_1339448
  simp only [CollatzResearch.WordTrace]
  refine ⟨24426841025708065175517499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32569121367610753567356665 24426841025708065175517499)
  ·
    refine ⟨36640261538562097763276249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24426841025708065175517499 36640261538562097763276249)
    ·
      refine ⟨27480196153921573322457187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36640261538562097763276249 27480196153921573322457187)
      ·
        refine ⟨41220294230882359983685781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27480196153921573322457187 41220294230882359983685781)
        ·
          refine ⟨1932201292072610624235271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41220294230882359983685781 1932201292072610624235271)
          ·
            refine ⟨2898301938108915936352907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932201292072610624235271 2898301938108915936352907)
            ·
              refine ⟨4347452907163373904529361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898301938108915936352907 4347452907163373904529361)
              ·
                refine ⟨3260589680372530428397021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347452907163373904529361 3260589680372530428397021)
                ·
                  refine ⟨1222721130139698910648883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3260589680372530428397021 1222721130139698910648883)
                  ·
                    refine ⟨1834081695209548365973325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1222721130139698910648883 1834081695209548365973325)
                    ·
                      refine ⟨687780635703580637239997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1834081695209548365973325 687780635703580637239997)
                      ·
                        rfl

theorem cell23_1339448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_1339448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339448 prefixEnd_1339448 := by exact prefixLift 1339448
  have htrace : WordTrace (prefixWord ++ tailWord_1339448) baseStart_1339448 baseEnd_1339448 := by
    simpa [prefixWord, tailWord_1339448, baseEnd_1339448] using wordTrace_append hprefix tailTrace_1339448
  have hstable : (prefixWord ++ tailWord_1339448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339448).length < 2 ^ (prefixWord ++ tailWord_1339448).sum := by decide
  have hdescent : baseEnd_1339448 < baseStart_1339448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339488 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 3, 2, 2]
def baseStart_1339488 : Nat := 118140960795 + 1339488 * 2 ^ 59
def prefixEnd_1339488 : Nat := 4983230072969 + 3 ^ 40 * 1339488 * 2
def baseEnd_1339488 : Nat := 687801174929760480739813

theorem tailTrace_1339488 : CollatzResearch.WordTrace tailWord_1339488 prefixEnd_1339488 687801174929760480739813 := by
  unfold tailWord_1339488
  simp only [CollatzResearch.WordTrace]
  refine ⟨24427570485635608591245559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32570093980847478121660745 24427570485635608591245559)
  ·
    refine ⟨36641355728453412886868339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24427570485635608591245559 36641355728453412886868339)
    ·
      refine ⟨54962033592680119330302509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36641355728453412886868339 54962033592680119330302509)
      ·
        refine ⟨20610762597255044748863441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54962033592680119330302509 20610762597255044748863441)
        ·
          refine ⟨15458071947941283561647581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20610762597255044748863441 15458071947941283561647581)
          ·
            refine ⟨5796776980477981335617843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15458071947941283561647581 5796776980477981335617843)
            ·
              refine ⟨8695165470716972003426765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796776980477981335617843 8695165470716972003426765)
              ·
                refine ⟨3260687051518864501285037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8695165470716972003426765 3260687051518864501285037)
                ·
                  refine ⟨1222757644319574187981889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3260687051518864501285037 1222757644319574187981889)
                  ·
                    refine ⟨917068233239680640986417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1222757644319574187981889 917068233239680640986417)
                    ·
                      refine ⟨687801174929760480739813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917068233239680640986417 687801174929760480739813)
                      ·
                        rfl

theorem cell23_1339488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_1339488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339488 prefixEnd_1339488 := by exact prefixLift 1339488
  have htrace : WordTrace (prefixWord ++ tailWord_1339488) baseStart_1339488 baseEnd_1339488 := by
    simpa [prefixWord, tailWord_1339488, baseEnd_1339488] using wordTrace_append hprefix tailTrace_1339488
  have hstable : (prefixWord ++ tailWord_1339488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339488).length < 2 ^ (prefixWord ++ tailWord_1339488).sum := by decide
  have hdescent : baseEnd_1339488 < baseStart_1339488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339498 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_1339498 : Nat := 118140960795 + 1339498 * 2 ^ 59
def prefixEnd_1339498 : Nat := 4983230072969 + 3 ^ 40 * 1339498 * 2
def baseEnd_1339498 : Nat := 229268769912101813871589

theorem tailTrace_1339498 : CollatzResearch.WordTrace tailWord_1339498 prefixEnd_1339498 229268769912101813871589 := by
  unfold tailWord_1339498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213876425308747222588787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32570337134156659260236765 12213876425308747222588787)
  ·
    refine ⟨18320814637963120833883181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12213876425308747222588787 18320814637963120833883181)
    ·
      refine ⟨6870305489236170312706193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18320814637963120833883181 6870305489236170312706193)
      ·
        refine ⟨5152729116927127734529645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6870305489236170312706193 5152729116927127734529645)
        ·
          refine ⟨1932273418847672900448617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5152729116927127734529645 1932273418847672900448617)
          ·
            refine ⟨1449205064135754675336463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1932273418847672900448617 1449205064135754675336463)
            ·
              refine ⟨2173807596203632013004695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449205064135754675336463 2173807596203632013004695)
              ·
                refine ⟨3260711394305448019507043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2173807596203632013004695 3260711394305448019507043)
                ·
                  refine ⟨4891067091458172029260565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260711394305448019507043 4891067091458172029260565)
                  ·
                    refine ⟨229268769912101813871589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4891067091458172029260565 229268769912101813871589)
                    ·
                      rfl

theorem cell23_1339498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_1339498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339498 prefixEnd_1339498 := by exact prefixLift 1339498
  have htrace : WordTrace (prefixWord ++ tailWord_1339498) baseStart_1339498 baseEnd_1339498 := by
    simpa [prefixWord, tailWord_1339498, baseEnd_1339498] using wordTrace_append hprefix tailTrace_1339498
  have hstable : (prefixWord ++ tailWord_1339498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339498).length < 2 ^ (prefixWord ++ tailWord_1339498).sum := by decide
  have hdescent : baseEnd_1339498 < baseStart_1339498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339511 : List Nat := [1, 1, 3, 1, 1, 7, 2, 7]
def baseStart_1339511 : Nat := 118140960795 + 1339511 * 2 ^ 59
def prefixEnd_1339511 : Nat := 4983230072969 + 3 ^ 40 * 1339511 * 2
def baseEnd_1339511 : Nat := 25474554999437551509341

theorem tailTrace_1339511 : CollatzResearch.WordTrace tailWord_1339511 prefixEnd_1339511 25474554999437551509341 := by
  unfold tailWord_1339511
  simp only [CollatzResearch.WordTrace]
  refine ⟨48855979850187892110578387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32570653233458594740385591 48855979850187892110578387)
  ·
    refine ⟨73283969775281838165867581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48855979850187892110578387 73283969775281838165867581)
    ·
      refine ⟨27481488665730689312200343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73283969775281838165867581 27481488665730689312200343)
      ·
        refine ⟨41222232998596033968300515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27481488665730689312200343 41222232998596033968300515)
        ·
          refine ⟨61833349497894050952450773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41222232998596033968300515 61833349497894050952450773)
          ·
            refine ⟨1449219128856891819198065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61833349497894050952450773 1449219128856891819198065)
            ·
              refine ⟨1086914346642668864398549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449219128856891819198065 1086914346642668864398549)
              ·
                refine ⟨25474554999437551509341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1086914346642668864398549 25474554999437551509341)
                ·
                  rfl

theorem cell23_1339511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 7].length) (baseStart_1339511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339511 prefixEnd_1339511 := by exact prefixLift 1339511
  have htrace : WordTrace (prefixWord ++ tailWord_1339511) baseStart_1339511 baseEnd_1339511 := by
    simpa [prefixWord, tailWord_1339511, baseEnd_1339511] using wordTrace_append hprefix tailTrace_1339511
  have hstable : (prefixWord ++ tailWord_1339511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339511).length < 2 ^ (prefixWord ++ tailWord_1339511).sum := by decide
  have hdescent : baseEnd_1339511 < baseStart_1339511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339531 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 7, 3, 2]
def baseStart_1339531 : Nat := 118140960795 + 1339531 * 2 ^ 59
def prefixEnd_1339531 : Nat := 4983230072969 + 3 ^ 40 * 1339531 * 2
def baseEnd_1339531 : Nat := 687823254597903812502115

theorem tailTrace_1339531 : CollatzResearch.WordTrace tailWord_1339531 prefixEnd_1339531 687823254597903812502115 := by
  unfold tailWord_1339531
  simp only [CollatzResearch.WordTrace]
  refine ⟨48856709310115435526306447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32571139540076957017537631 48856709310115435526306447)
  ·
    refine ⟨73285063965173153289459671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48856709310115435526306447 73285063965173153289459671)
    ·
      refine ⟨109927595947759729934189507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73285063965173153289459671 109927595947759729934189507)
      ·
        refine ⟨164891393921639594901284261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109927595947759729934189507 164891393921639594901284261)
        ·
          refine ⟨30917136360307424043990799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164891393921639594901284261 30917136360307424043990799)
          ·
            refine ⟨46375704540461136065986199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30917136360307424043990799 46375704540461136065986199)
            ·
              refine ⟨69563556810691704098979299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46375704540461136065986199 69563556810691704098979299)
              ·
                refine ⟨104345335216037556148468949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69563556810691704098979299 104345335216037556148468949)
                ·
                  refine ⟨2445593794125880222229741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 104345335216037556148468949 2445593794125880222229741)
                  ·
                    refine ⟨917097672797205083336153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445593794125880222229741 917097672797205083336153)
                    ·
                      refine ⟨687823254597903812502115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917097672797205083336153 687823254597903812502115)
                      ·
                        rfl

theorem cell23_1339531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3, 2].length) (baseStart_1339531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339531 prefixEnd_1339531 := by exact prefixLift 1339531
  have htrace : WordTrace (prefixWord ++ tailWord_1339531) baseStart_1339531 baseEnd_1339531 := by
    simpa [prefixWord, tailWord_1339531, baseEnd_1339531] using wordTrace_append hprefix tailTrace_1339531
  have hstable : (prefixWord ++ tailWord_1339531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339531).length < 2 ^ (prefixWord ++ tailWord_1339531).sum := by decide
  have hdescent : baseEnd_1339531 < baseStart_1339531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339538 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1339538 : Nat := 118140960795 + 1339538 * 2 ^ 59
def prefixEnd_1339538 : Nat := 4983230072969 + 3 ^ 40 * 1339538 * 2
def baseEnd_1339538 : Nat := 687826848962485285114583

theorem tailTrace_1339538 : CollatzResearch.WordTrace tailWord_1339538 prefixEnd_1339538 687826848962485285114583 := by
  unfold tailWord_1339538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214241155272518930452817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32571309747393383814540845 12214241155272518930452817)
  ·
    refine ⟨9160680866454389197839613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12214241155272518930452817 9160680866454389197839613)
    ·
      refine ⟨3435255324920395949189855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9160680866454389197839613 3435255324920395949189855)
      ·
        refine ⟨5152882987380593923784783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435255324920395949189855 5152882987380593923784783)
        ·
          refine ⟨7729324481070890885677175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152882987380593923784783 7729324481070890885677175)
          ·
            refine ⟨11593986721606336328515763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729324481070890885677175 11593986721606336328515763)
            ·
              refine ⟨17390980082409504492773645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11593986721606336328515763 17390980082409504492773645)
              ·
                refine ⟨6521617530903564184790117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17390980082409504492773645 6521617530903564184790117)
                ·
                  refine ⟨1222803287044418284648147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6521617530903564184790117 1222803287044418284648147)
                  ·
                    refine ⟨1834204930566627426972221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1222803287044418284648147 1834204930566627426972221)
                    ·
                      refine ⟨687826848962485285114583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1834204930566627426972221 687826848962485285114583)
                      ·
                        rfl

theorem cell23_1339538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1339538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339538 prefixEnd_1339538 := by exact prefixLift 1339538
  have htrace : WordTrace (prefixWord ++ tailWord_1339538) baseStart_1339538 baseEnd_1339538 := by
    simpa [prefixWord, tailWord_1339538, baseEnd_1339538] using wordTrace_append hprefix tailTrace_1339538
  have hstable : (prefixWord ++ tailWord_1339538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339538).length < 2 ^ (prefixWord ++ tailWord_1339538).sum := by decide
  have hdescent : baseEnd_1339538 < baseStart_1339538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339548 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1339548 : Nat := 118140960795 + 1339548 * 2 ^ 59
def prefixEnd_1339548 : Nat := 4983230072969 + 3 ^ 40 * 1339548 * 2
def baseEnd_1339548 : Nat := 687831983769030245989537

theorem tailTrace_1339548 : CollatzResearch.WordTrace tailWord_1339548 prefixEnd_1339548 687831983769030245989537 := by
  unfold tailWord_1339548
  simp only [CollatzResearch.WordTrace]
  refine ⟨24428664675526923714837649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32571552900702564953116865 24428664675526923714837649)
  ·
    refine ⟨18321498506645192786128237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24428664675526923714837649 18321498506645192786128237)
    ·
      refine ⟨6870561939991947294798089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18321498506645192786128237 6870561939991947294798089)
      ·
        refine ⟨5152921454993960471098567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6870561939991947294798089 5152921454993960471098567)
        ·
          refine ⟨7729382182490940706647851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152921454993960471098567 7729382182490940706647851)
          ·
            refine ⟨11594073273736411059971777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729382182490940706647851 11594073273736411059971777)
            ·
              refine ⟨8695554955302308294978833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11594073273736411059971777 8695554955302308294978833)
              ·
                refine ⟨6521666216476731221234125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8695554955302308294978833 6521666216476731221234125)
                ·
                  refine ⟨2445624831178774207962797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6521666216476731221234125 2445624831178774207962797)
                  ·
                    refine ⟨917109311692040327986049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445624831178774207962797 917109311692040327986049)
                    ·
                      refine ⟨687831983769030245989537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917109311692040327986049 687831983769030245989537)
                      ·
                        rfl

theorem cell23_1339548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1339548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339548 prefixEnd_1339548 := by exact prefixLift 1339548
  have htrace : WordTrace (prefixWord ++ tailWord_1339548) baseStart_1339548 baseEnd_1339548 := by
    simpa [prefixWord, tailWord_1339548, baseEnd_1339548] using wordTrace_append hprefix tailTrace_1339548
  have hstable : (prefixWord ++ tailWord_1339548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339548).length < 2 ^ (prefixWord ++ tailWord_1339548).sum := by decide
  have hdescent : baseEnd_1339548 < baseStart_1339548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339565 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_1339565 : Nat := 118140960795 + 1339565 * 2 ^ 59
def prefixEnd_1339565 : Nat := 4983230072969 + 3 ^ 40 * 1339565 * 2
def baseEnd_1339565 : Nat := 687840712940156679476959

theorem tailTrace_1339565 : CollatzResearch.WordTrace tailWord_1339565 prefixEnd_1339565 687840712940156679476959 := by
  unfold tailWord_1339565
  simp only [CollatzResearch.WordTrace]
  refine ⟨48857949391992259333044149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32571966261328172888696099 48857949391992259333044149)
  ·
    refine ⟨4580432755499274312472889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48857949391992259333044149 4580432755499274312472889)
    ·
      refine ⟨3435324566624455734354667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4580432755499274312472889 3435324566624455734354667)
      ·
        refine ⟨5152986849936683601532001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435324566624455734354667 5152986849936683601532001)
        ·
          refine ⟨3864740137452512701149001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5152986849936683601532001 3864740137452512701149001)
          ·
            refine ⟨2898555103089384525861751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3864740137452512701149001 2898555103089384525861751)
            ·
              refine ⟨4347832654634076788792627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898555103089384525861751 4347832654634076788792627)
              ·
                refine ⟨6521748981951115183188941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347832654634076788792627 6521748981951115183188941)
                ·
                  refine ⟨2445655868231668193695853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6521748981951115183188941 2445655868231668193695853)
                  ·
                    refine ⟨917120950586875572635945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2445655868231668193695853 917120950586875572635945)
                    ·
                      refine ⟨687840712940156679476959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917120950586875572635945 687840712940156679476959)
                      ·
                        rfl

theorem cell23_1339565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_1339565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339565 prefixEnd_1339565 := by exact prefixLift 1339565
  have htrace : WordTrace (prefixWord ++ tailWord_1339565) baseStart_1339565 baseEnd_1339565 := by
    simpa [prefixWord, tailWord_1339565, baseEnd_1339565] using wordTrace_append hprefix tailTrace_1339565
  have hstable : (prefixWord ++ tailWord_1339565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339565).length < 2 ^ (prefixWord ++ tailWord_1339565).sum := by decide
  have hdescent : baseEnd_1339565 < baseStart_1339565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339578 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2]
def baseStart_1339578 : Nat := 118140960795 + 1339578 * 2 ^ 59
def prefixEnd_1339578 : Nat := 4983230072969 + 3 ^ 40 * 1339578 * 2
def baseEnd_1339578 : Nat := 687847388188665128614399

theorem tailTrace_1339578 : CollatzResearch.WordTrace tailWord_1339578 prefixEnd_1339578 687847388188665128614399 := by
  unfold tailWord_1339578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214605885236290638316847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32572282360630108368844925 12214605885236290638316847)
  ·
    refine ⟨18321908827854435957475271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12214605885236290638316847 18321908827854435957475271)
    ·
      refine ⟨27482863241781653936212907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18321908827854435957475271 27482863241781653936212907)
      ·
        refine ⟨41224294862672480904319361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27482863241781653936212907 41224294862672480904319361)
        ·
          refine ⟨30918221147004360678239521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41224294862672480904319361 30918221147004360678239521)
          ·
            refine ⟨23188665860253270508679641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30918221147004360678239521 23188665860253270508679641)
            ·
              refine ⟨17391499395189952881509731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23188665860253270508679641 17391499395189952881509731)
              ·
                refine ⟨26087249092784929322264597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17391499395189952881509731 26087249092784929322264597)
                ·
                  refine ⟨1222839801224293561981153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26087249092784929322264597 1222839801224293561981153)
                  ·
                    refine ⟨917129850918220171485865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1222839801224293561981153 917129850918220171485865)
                    ·
                      refine ⟨687847388188665128614399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917129850918220171485865 687847388188665128614399)
                      ·
                        rfl

theorem cell23_1339578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_1339578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339578 prefixEnd_1339578 := by exact prefixLift 1339578
  have htrace : WordTrace (prefixWord ++ tailWord_1339578) baseStart_1339578 baseEnd_1339578 := by
    simpa [prefixWord, tailWord_1339578, baseEnd_1339578] using wordTrace_append hprefix tailTrace_1339578
  have hstable : (prefixWord ++ tailWord_1339578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339578).length < 2 ^ (prefixWord ++ tailWord_1339578).sum := by decide
  have hdescent : baseEnd_1339578 < baseStart_1339578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339595 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 2, 2, 2]
def baseStart_1339595 : Nat := 118140960795 + 1339595 * 2 ^ 59
def prefixEnd_1339595 : Nat := 4983230072969 + 3 ^ 40 * 1339595 * 2
def baseEnd_1339595 : Nat := 687856117359791562101821

theorem tailTrace_1339595 : CollatzResearch.WordTrace tailWord_1339595 prefixEnd_1339595 687856117359791562101821 := by
  unfold tailWord_1339595
  simp only [CollatzResearch.WordTrace]
  refine ⟨48859043581883574456636239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32572695721255716304424159 48859043581883574456636239)
  ·
    refine ⟨73288565372825361684954359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48859043581883574456636239 73288565372825361684954359)
    ·
      refine ⟨109932848059238042527431539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73288565372825361684954359 109932848059238042527431539)
      ·
        refine ⟨164899272088857063791147309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109932848059238042527431539 164899272088857063791147309)
        ·
          refine ⟨61837227033321398921680241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164899272088857063791147309 61837227033321398921680241)
          ·
            refine ⟨46377920274991049191260181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61837227033321398921680241 46377920274991049191260181)
            ·
              refine ⟨2173965012890205430840321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46377920274991049191260181 2173965012890205430840321)
              ·
                refine ⟨1630473759667654073130241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173965012890205430840321 1630473759667654073130241)
                ·
                  refine ⟨1222855319750740554847681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1630473759667654073130241 1222855319750740554847681)
                  ·
                    refine ⟨917141489813055416135761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1222855319750740554847681 917141489813055416135761)
                    ·
                      refine ⟨687856117359791562101821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917141489813055416135761 687856117359791562101821)
                      ·
                        rfl

theorem cell23_1339595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 2, 2].length) (baseStart_1339595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339595 prefixEnd_1339595 := by exact prefixLift 1339595
  have htrace : WordTrace (prefixWord ++ tailWord_1339595) baseStart_1339595 baseEnd_1339595 := by
    simpa [prefixWord, tailWord_1339595, baseEnd_1339595] using wordTrace_append hprefix tailTrace_1339595
  have hstable : (prefixWord ++ tailWord_1339595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339595).length < 2 ^ (prefixWord ++ tailWord_1339595).sum := by decide
  have hdescent : baseEnd_1339595 < baseStart_1339595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339631 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 1, 7]
def baseStart_1339631 : Nat := 118140960795 + 1339631 * 2 ^ 59
def prefixEnd_1339631 : Nat := 4983230072969 + 3 ^ 40 * 1339631 * 2
def baseEnd_1339631 : Nat := 229291534221117807083885

theorem tailTrace_1339631 : CollatzResearch.WordTrace tailWord_1339631 prefixEnd_1339631 229291534221117807083885 := by
  unfold tailWord_1339631
  simp only [CollatzResearch.WordTrace]
  refine ⟨48860356609753152604946747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32573571073168768403297831 48860356609753152604946747)
  ·
    refine ⟨73290534914629728907420121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48860356609753152604946747 73290534914629728907420121)
    ·
      refine ⟨54967901185972296680565091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73290534914629728907420121 54967901185972296680565091)
      ·
        refine ⟨82451851778958445020847637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54967901185972296680565091 82451851778958445020847637)
        ·
          refine ⟨3864930552138677110352233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82451851778958445020847637 3864930552138677110352233)
          ·
            refine ⟨2898697914104007832764175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3864930552138677110352233 2898697914104007832764175)
            ·
              refine ⟨4348046871156011749146263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898697914104007832764175 4348046871156011749146263)
              ·
                refine ⟨6522070306734017623719395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348046871156011749146263 6522070306734017623719395)
                ·
                  refine ⟨9783105460101026435579093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6522070306734017623719395 9783105460101026435579093)
                  ·
                    refine ⟨229291534221117807083885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9783105460101026435579093 229291534221117807083885)
                    ·
                      rfl

theorem cell23_1339631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_1339631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339631 prefixEnd_1339631 := by exact prefixLift 1339631
  have htrace : WordTrace (prefixWord ++ tailWord_1339631) baseStart_1339631 baseEnd_1339631 := by
    simpa [prefixWord, tailWord_1339631, baseEnd_1339631] using wordTrace_append hprefix tailTrace_1339631
  have hstable : (prefixWord ++ tailWord_1339631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339631).length < 2 ^ (prefixWord ++ tailWord_1339631).sum := by decide
  have hdescent : baseEnd_1339631 < baseStart_1339631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339651 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 4]
def baseStart_1339651 : Nat := 118140960795 + 1339651 * 2 ^ 59
def prefixEnd_1339651 : Nat := 4983230072969 + 3 ^ 40 * 1339651 * 2
def baseEnd_1339651 : Nat := 687884872276443343001563

theorem tailTrace_1339651 : CollatzResearch.WordTrace tailWord_1339651 prefixEnd_1339651 687884872276443343001563 := by
  unfold tailWord_1339651
  simp only [CollatzResearch.WordTrace]
  refine ⟨48861086069680696020674807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32574057379787130680449871 48861086069680696020674807)
  ·
    refine ⟨73291629104521044031012211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48861086069680696020674807 73291629104521044031012211)
    ·
      refine ⟨109937443656781566046518317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73291629104521044031012211 109937443656781566046518317)
      ·
        refine ⟨41226541371293087267444369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109937443656781566046518317 41226541371293087267444369)
        ·
          refine ⟨30919906028469815450583277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41226541371293087267444369 30919906028469815450583277)
          ·
            refine ⟨11594964760676180793968729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30919906028469815450583277 11594964760676180793968729)
            ·
              refine ⟨8696223570507135595476547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11594964760676180793968729 8696223570507135595476547)
              ·
                refine ⟨13044335355760703393214821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696223570507135595476547 13044335355760703393214821)
                ·
                  refine ⟨2445812879205131886227779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13044335355760703393214821 2445812879205131886227779)
                  ·
                    refine ⟨3668719318807697829341669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2445812879205131886227779 3668719318807697829341669)
                    ·
                      refine ⟨687884872276443343001563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3668719318807697829341669 687884872276443343001563)
                      ·
                        rfl

theorem cell23_1339651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_1339651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339651 prefixEnd_1339651 := by exact prefixLift 1339651
  have htrace : WordTrace (prefixWord ++ tailWord_1339651) baseStart_1339651 baseEnd_1339651 := by
    simpa [prefixWord, tailWord_1339651, baseEnd_1339651] using wordTrace_append hprefix tailTrace_1339651
  have hstable : (prefixWord ++ tailWord_1339651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339651).length < 2 ^ (prefixWord ++ tailWord_1339651).sum := by decide
  have hdescent : baseEnd_1339651 < baseStart_1339651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339664 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_1339664 : Nat := 118140960795 + 1339664 * 2 ^ 59
def prefixEnd_1339664 : Nat := 4983230072969 + 3 ^ 40 * 1339664 * 2
def baseEnd_1339664 : Nat := 687891547524951792139003

theorem tailTrace_1339664 : CollatzResearch.WordTrace tailWord_1339664 prefixEnd_1339664 687891547524951792139003 := by
  unfold tailWord_1339664
  simp only [CollatzResearch.WordTrace]
  refine ⟨24430780109316799620449023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32574373479089066160598697 24430780109316799620449023)
  ·
    refine ⟨36646170163975199430673535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24430780109316799620449023 36646170163975199430673535)
    ·
      refine ⟨54969255245962799146010303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36646170163975199430673535 54969255245962799146010303)
      ·
        refine ⟨82453882868944198719015455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54969255245962799146010303 82453882868944198719015455)
        ·
          refine ⟨123680824303416298078523183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82453882868944198719015455 123680824303416298078523183)
          ·
            refine ⟨185521236455124447117784775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123680824303416298078523183 185521236455124447117784775)
            ·
              refine ⟨278281854682686670676677163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185521236455124447117784775 278281854682686670676677163)
              ·
                refine ⟨417422782024030006015015745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278281854682686670676677163 417422782024030006015015745)
                ·
                  refine ⟨313067086518022504511261809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417422782024030006015015745 313067086518022504511261809)
                  ·
                    refine ⟨234800314888516878383446357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313067086518022504511261809 234800314888516878383446357)
                    ·
                      refine ⟨687891547524951792139003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 234800314888516878383446357 687891547524951792139003)
                      ·
                        rfl

theorem cell23_1339664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_1339664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339664 prefixEnd_1339664 := by exact prefixLift 1339664
  have htrace : WordTrace (prefixWord ++ tailWord_1339664) baseStart_1339664 baseEnd_1339664 := by
    simpa [prefixWord, tailWord_1339664, baseEnd_1339664] using wordTrace_append hprefix tailTrace_1339664
  have hstable : (prefixWord ++ tailWord_1339664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339664).length < 2 ^ (prefixWord ++ tailWord_1339664).sum := by decide
  have hdescent : baseEnd_1339664 < baseStart_1339664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339695 : List Nat := [1, 1, 2, 1, 2, 1, 7, 3, 1, 4]
def baseStart_1339695 : Nat := 118140960795 + 1339695 * 2 ^ 59
def prefixEnd_1339695 : Nat := 4983230072969 + 3 ^ 40 * 1339695 * 2
def baseEnd_1339695 : Nat := 229302488475080390283787

theorem tailTrace_1339695 : CollatzResearch.WordTrace tailWord_1339695 prefixEnd_1339695 229302488475080390283787 := by
  unfold tailWord_1339695
  simp only [CollatzResearch.WordTrace]
  refine ⟨48862690881521291535276539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32575127254347527690184359 48862690881521291535276539)
  ·
    refine ⟨73294036322281937302914809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48862690881521291535276539 73294036322281937302914809)
    ·
      refine ⟨54970527241711452977186107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73294036322281937302914809 54970527241711452977186107)
      ·
        refine ⟨82455790862567179465779161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54970527241711452977186107 82455790862567179465779161)
        ·
          refine ⟨61841843146925384599334371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82455790862567179465779161 61841843146925384599334371)
          ·
            refine ⟨92762764720388076899001557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61841843146925384599334371 92762764720388076899001557)
            ·
              refine ⟨2174127298134095552320349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 92762764720388076899001557 2174127298134095552320349)
              ·
                refine ⟨815297736800285832120131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174127298134095552320349 815297736800285832120131)
                ·
                  refine ⟨1222946605200428748180197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815297736800285832120131 1222946605200428748180197)
                  ·
                    refine ⟨229302488475080390283787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1222946605200428748180197 229302488475080390283787)
                    ·
                      rfl

theorem cell23_1339695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 4].length) (baseStart_1339695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339695 prefixEnd_1339695 := by exact prefixLift 1339695
  have htrace : WordTrace (prefixWord ++ tailWord_1339695) baseStart_1339695 baseEnd_1339695 := by
    simpa [prefixWord, tailWord_1339695, baseEnd_1339695] using wordTrace_append hprefix tailTrace_1339695
  have hstable : (prefixWord ++ tailWord_1339695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339695).length < 2 ^ (prefixWord ++ tailWord_1339695).sum := by decide
  have hdescent : baseEnd_1339695 < baseStart_1339695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339705 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1339705 : Nat := 118140960795 + 1339705 * 2 ^ 59
def prefixEnd_1339705 : Nat := 4983230072969 + 3 ^ 40 * 1339705 * 2
def baseEnd_1339705 : Nat := 687912600231786131726315

theorem tailTrace_1339705 : CollatzResearch.WordTrace tailWord_1339705 prefixEnd_1339705 687912600231786131726315 := by
  unfold tailWord_1339705
  simp only [CollatzResearch.WordTrace]
  refine ⟨48863055611485063243140569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32575370407656708828760379 48863055611485063243140569)
  ·
    refine ⟨36647291708613797432355427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48863055611485063243140569 36647291708613797432355427)
    ·
      refine ⟨54970937562920696148533141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36647291708613797432355427 54970937562920696148533141)
      ·
        refine ⟨2576762698261907631962491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54970937562920696148533141 2576762698261907631962491)
        ·
          refine ⟨3865144047392861447943737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2576762698261907631962491 3865144047392861447943737)
          ·
            refine ⟨2898858035544646085957803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3865144047392861447943737 2898858035544646085957803)
            ·
              refine ⟨4348287053316969128936705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898858035544646085957803 4348287053316969128936705)
              ·
                refine ⟨3261215289987726846702529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4348287053316969128936705 3261215289987726846702529)
                ·
                  refine ⟨2445911467490795135026897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3261215289987726846702529 2445911467490795135026897)
                  ·
                    refine ⟨1834433600618096351270173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2445911467490795135026897 1834433600618096351270173)
                    ·
                      refine ⟨687912600231786131726315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1834433600618096351270173 687912600231786131726315)
                      ·
                        rfl

theorem cell23_1339705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1339705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339705 prefixEnd_1339705 := by exact prefixLift 1339705
  have htrace : WordTrace (prefixWord ++ tailWord_1339705) baseStart_1339705 baseEnd_1339705 := by
    simpa [prefixWord, tailWord_1339705, baseEnd_1339705] using wordTrace_append hprefix tailTrace_1339705
  have hstable : (prefixWord ++ tailWord_1339705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339705).length < 2 ^ (prefixWord ++ tailWord_1339705).sum := by decide
  have hdescent : baseEnd_1339705 < baseStart_1339705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339721 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 3, 5]
def baseStart_1339721 : Nat := 118140960795 + 1339721 * 2 ^ 59
def prefixEnd_1339721 : Nat := 4983230072969 + 3 ^ 40 * 1339721 * 2
def baseEnd_1339721 : Nat := 229306938640752689708747

theorem tailTrace_1339721 : CollatzResearch.WordTrace tailWord_1339721 prefixEnd_1339721 229306938640752689708747 := by
  unfold tailWord_1339721
  simp only [CollatzResearch.WordTrace]
  refine ⟨48863639179427097975723017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32575759452951398650482011 48863639179427097975723017)
  ·
    refine ⟨36647729384570323481792263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48863639179427097975723017 36647729384570323481792263)
    ·
      refine ⟨54971594076855485222688395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36647729384570323481792263 54971594076855485222688395)
      ·
        refine ⟨82457391115283227834032593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54971594076855485222688395 82457391115283227834032593)
        ·
          refine ⟨61843043336462420875524445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82457391115283227834032593 61843043336462420875524445)
          ·
            refine ⟨23191141251173407828321667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61843043336462420875524445 23191141251173407828321667)
            ·
              refine ⟨34786711876760111742482501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23191141251173407828321667 34786711876760111742482501)
              ·
                refine ⟨6522508476892520951715469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34786711876760111742482501 6522508476892520951715469)
                ·
                  refine ⟨2445940678834695356893301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6522508476892520951715469 2445940678834695356893301)
                  ·
                    refine ⟨229306938640752689708747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2445940678834695356893301 229306938640752689708747)
                    ·
                      rfl

theorem cell23_1339721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_1339721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339721 prefixEnd_1339721 := by exact prefixLift 1339721
  have htrace : WordTrace (prefixWord ++ tailWord_1339721) baseStart_1339721 baseEnd_1339721 := by
    simpa [prefixWord, tailWord_1339721, baseEnd_1339721] using wordTrace_append hprefix tailTrace_1339721
  have hstable : (prefixWord ++ tailWord_1339721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339721).length < 2 ^ (prefixWord ++ tailWord_1339721).sum := by decide
  have hdescent : baseEnd_1339721 < baseStart_1339721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339785 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 2, 4]
def baseStart_1339785 : Nat := 118140960795 + 1339785 * 2 ^ 59
def prefixEnd_1339785 : Nat := 4983230072969 + 3 ^ 40 * 1339785 * 2
def baseEnd_1339785 : Nat := 229317892894715272908649

theorem tailTrace_1339785 : CollatzResearch.WordTrace tailWord_1339785 prefixEnd_1339785 229317892894715272908649 := by
  unfold tailWord_1339785
  simp only [CollatzResearch.WordTrace]
  refine ⟨48865973451195236906052809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32577315634130157937368539 48865973451195236906052809)
  ·
    refine ⟨36649480088396427679539607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48865973451195236906052809 36649480088396427679539607)
    ·
      refine ⟨54974220132594641519309411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36649480088396427679539607 54974220132594641519309411)
      ·
        refine ⟨82461330198891962278964117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54974220132594641519309411 82461330198891962278964117)
        ·
          refine ⟨3865374853073060731826443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82461330198891962278964117 3865374853073060731826443)
          ·
            refine ⟨5798062279609591097739665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3865374853073060731826443 5798062279609591097739665)
            ·
              refine ⟨4348546709707193323304749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5798062279609591097739665 4348546709707193323304749)
              ·
                refine ⟨1630705016140197496239281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4348546709707193323304749 1630705016140197496239281)
                ·
                  refine ⟨1223028762105148122179461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1630705016140197496239281 1223028762105148122179461)
                  ·
                    refine ⟨229317892894715272908649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1223028762105148122179461 229317892894715272908649)
                    ·
                      rfl

theorem cell23_1339785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_1339785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339785 prefixEnd_1339785 := by exact prefixLift 1339785
  have htrace : WordTrace (prefixWord ++ tailWord_1339785) baseStart_1339785 baseEnd_1339785 := by
    simpa [prefixWord, tailWord_1339785, baseEnd_1339785] using wordTrace_append hprefix tailTrace_1339785
  have hstable : (prefixWord ++ tailWord_1339785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339785).length < 2 ^ (prefixWord ++ tailWord_1339785).sum := by decide
  have hdescent : baseEnd_1339785 < baseStart_1339785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339788 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1339788 : Nat := 118140960795 + 1339788 * 2 ^ 59
def prefixEnd_1339788 : Nat := 4983230072969 + 3 ^ 40 * 1339788 * 2
def baseEnd_1339788 : Nat := 687955219126109306988433

theorem tailTrace_1339788 : CollatzResearch.WordTrace tailWord_1339788 prefixEnd_1339788 687955219126109306988433 := by
  unfold tailWord_1339788
  simp only [CollatzResearch.WordTrace]
  refine ⟨24433041435092184209206009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32577388580122912278941345 24433041435092184209206009)
  ·
    refine ⟨18324781076319138156904507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24433041435092184209206009 18324781076319138156904507)
    ·
      refine ⟨27487171614478707235356761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18324781076319138156904507 27487171614478707235356761)
      ·
        refine ⟨20615378710859030426517571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27487171614478707235356761 20615378710859030426517571)
        ·
          refine ⟨30923068066288545639776357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20615378710859030426517571 30923068066288545639776357)
          ·
            refine ⟨5798075262429102307458067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30923068066288545639776357 5798075262429102307458067)
            ·
              refine ⟨8697112893643653461187101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5798075262429102307458067 8697112893643653461187101)
              ·
                refine ⟨3261417335116370047945163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8697112893643653461187101 3261417335116370047945163)
                ·
                  refine ⟨4892126002674555071917745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261417335116370047945163 4892126002674555071917745)
                  ·
                    refine ⟨3669094502005916303938309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4892126002674555071917745 3669094502005916303938309)
                    ·
                      refine ⟨687955219126109306988433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3669094502005916303938309 687955219126109306988433)
                      ·
                        rfl

theorem cell23_1339788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1339788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339788 prefixEnd_1339788 := by exact prefixLift 1339788
  have htrace : WordTrace (prefixWord ++ tailWord_1339788) baseStart_1339788 baseEnd_1339788 := by
    simpa [prefixWord, tailWord_1339788, baseEnd_1339788] using wordTrace_append hprefix tailTrace_1339788
  have hstable : (prefixWord ++ tailWord_1339788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339788).length < 2 ^ (prefixWord ++ tailWord_1339788).sum := by decide
  have hdescent : baseEnd_1339788 < baseStart_1339788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339796 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1339796 : Nat := 118140960795 + 1339796 * 2 ^ 59
def prefixEnd_1339796 : Nat := 4983230072969 + 3 ^ 40 * 1339796 * 2
def baseEnd_1339796 : Nat := 687959326971345275688397

theorem tailTrace_1339796 : CollatzResearch.WordTrace tailWord_1339796 prefixEnd_1339796 687959326971345275688397 := by
  unfold tailWord_1339796
  simp only [CollatzResearch.WordTrace]
  refine ⟨24433187327077692892351621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32577583102770257189802161 24433187327077692892351621)
  ·
    refine ⟨4581222623827067417315929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24433187327077692892351621 4581222623827067417315929)
    ·
      refine ⟨3435916967870300562986947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4581222623827067417315929 3435916967870300562986947)
      ·
        refine ⟨5153875451805450844480421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435916967870300562986947 5153875451805450844480421)
        ·
          refine ⟨966351647213522033340079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5153875451805450844480421 966351647213522033340079)
          ·
            refine ⟨1449527470820283050010119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966351647213522033340079 1449527470820283050010119)
            ·
              refine ⟨2174291206230424575015179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449527470820283050010119 2174291206230424575015179)
              ·
                refine ⟨3261436809345636862522769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174291206230424575015179 3261436809345636862522769)
                ·
                  refine ⟨2446077607009227646892077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3261436809345636862522769 2446077607009227646892077)
                  ·
                    refine ⟨917279102628460367584529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446077607009227646892077 917279102628460367584529)
                    ·
                      refine ⟨687959326971345275688397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917279102628460367584529 687959326971345275688397)
                      ·
                        rfl

theorem cell23_1339796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1339796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339796 prefixEnd_1339796 := by exact prefixLift 1339796
  have htrace : WordTrace (prefixWord ++ tailWord_1339796) baseStart_1339796 baseEnd_1339796 := by
    simpa [prefixWord, tailWord_1339796, baseEnd_1339796] using wordTrace_append hprefix tailTrace_1339796
  have hstable : (prefixWord ++ tailWord_1339796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339796).length < 2 ^ (prefixWord ++ tailWord_1339796).sum := by decide
  have hdescent : baseEnd_1339796 < baseStart_1339796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339812 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_1339812 : Nat := 118140960795 + 1339812 * 2 ^ 59
def prefixEnd_1339812 : Nat := 4983230072969 + 3 ^ 40 * 1339812 * 2
def baseEnd_1339812 : Nat := 687967542661817213088323

theorem tailTrace_1339812 : CollatzResearch.WordTrace tailWord_1339812 prefixEnd_1339812 687967542661817213088323 := by
  unfold tailWord_1339812
  simp only [CollatzResearch.WordTrace]
  refine ⟨24433479111048710258642845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32577972148064947011523793 24433479111048710258642845)
  ·
    refine ⟨9162554666643266346991067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24433479111048710258642845 9162554666643266346991067)
    ·
      refine ⟨13743831999964899520486601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9162554666643266346991067 13743831999964899520486601)
      ·
        refine ⟨10307873999973674640364951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13743831999964899520486601 10307873999973674640364951)
        ·
          refine ⟨15461810999960511960547427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10307873999973674640364951 15461810999960511960547427)
          ·
            refine ⟨23192716499940767940821141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15461810999960511960547427 23192716499940767940821141)
            ·
              refine ⟨1087158585934723497225991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23192716499940767940821141 1087158585934723497225991)
              ·
                refine ⟨1630737878902085245838987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087158585934723497225991 1630737878902085245838987)
                ·
                  refine ⟨2446106818353127868758481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1630737878902085245838987 2446106818353127868758481)
                  ·
                    refine ⟨1834580113764845901568861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2446106818353127868758481 1834580113764845901568861)
                    ·
                      refine ⟨687967542661817213088323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1834580113764845901568861 687967542661817213088323)
                      ·
                        rfl

theorem cell23_1339812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_1339812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339812 prefixEnd_1339812 := by exact prefixLift 1339812
  have htrace : WordTrace (prefixWord ++ tailWord_1339812) baseStart_1339812 baseEnd_1339812 := by
    simpa [prefixWord, tailWord_1339812, baseEnd_1339812] using wordTrace_append hprefix tailTrace_1339812
  have hstable : (prefixWord ++ tailWord_1339812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339812).length < 2 ^ (prefixWord ++ tailWord_1339812).sum := by decide
  have hdescent : baseEnd_1339812 < baseStart_1339812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339865 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 3, 4, 2]
def baseStart_1339865 : Nat := 118140960795 + 1339865 * 2 ^ 59
def prefixEnd_1339865 : Nat := 4983230072969 + 3 ^ 40 * 1339865 * 2
def baseEnd_1339865 : Nat := 687994757136505505725579

theorem tailTrace_1339865 : CollatzResearch.WordTrace tailWord_1339865 prefixEnd_1339865 687994757136505505725579 := by
  unfold tailWord_1339865
  simp only [CollatzResearch.WordTrace]
  refine ⟨48868891290905410568965049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32579260860603607045976699 48868891290905410568965049)
  ·
    refine ⟨36651668468179057926723787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48868891290905410568965049 36651668468179057926723787)
    ·
      refine ⟨54977502702268586890085681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36651668468179057926723787 54977502702268586890085681)
      ·
        refine ⟨41233127026701440167564261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54977502702268586890085681 41233127026701440167564261)
        ·
          refine ⟨7731211317506520031418299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41233127026701440167564261 7731211317506520031418299)
          ·
            refine ⟨11596816976259780047127449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7731211317506520031418299 11596816976259780047127449)
            ·
              refine ⟨8697612732194835035345587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11596816976259780047127449 8697612732194835035345587)
              ·
                refine ⟨13046419098292252553018381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8697612732194835035345587 13046419098292252553018381)
                ·
                  refine ⟨4892407161859594707381893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13046419098292252553018381 4892407161859594707381893)
                  ·
                    refine ⟨917326342848674007634105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4892407161859594707381893 917326342848674007634105)
                    ·
                      refine ⟨687994757136505505725579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917326342848674007634105 687994757136505505725579)
                      ·
                        rfl

theorem cell23_1339865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_1339865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339865 prefixEnd_1339865 := by exact prefixLift 1339865
  have htrace : WordTrace (prefixWord ++ tailWord_1339865) baseStart_1339865 baseEnd_1339865 := by
    simpa [prefixWord, tailWord_1339865, baseEnd_1339865] using wordTrace_append hprefix tailTrace_1339865
  have hstable : (prefixWord ++ tailWord_1339865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339865).length < 2 ^ (prefixWord ++ tailWord_1339865).sum := by decide
  have hdescent : baseEnd_1339865 < baseStart_1339865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339893 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1339893 : Nat := 118140960795 + 1339893 * 2 ^ 59
def prefixEnd_1339893 : Nat := 4983230072969 + 3 ^ 40 * 1339893 * 2
def baseEnd_1339893 : Nat := 688009134594831396175451

theorem tailTrace_1339893 : CollatzResearch.WordTrace tailWord_1339893 prefixEnd_1339893 688009134594831396175451 := by
  unfold tailWord_1339893
  simp only [CollatzResearch.WordTrace]
  refine ⟨48869912534803971350984333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32579941689869314233989555 48869912534803971350984333)
  ·
    refine ⟨18326217200551489256619125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48869912534803971350984333 18326217200551489256619125)
    ·
      refine ⟨1718082862551702117808043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18326217200551489256619125 1718082862551702117808043)
      ·
        refine ⟨2577124293827553176712065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718082862551702117808043 2577124293827553176712065)
        ·
          refine ⟨1932843220370664882534049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2577124293827553176712065 1932843220370664882534049)
          ·
            refine ⟨1449632415277998661900537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1932843220370664882534049 1449632415277998661900537)
            ·
              refine ⟨1087224311458498996425403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449632415277998661900537 1087224311458498996425403)
              ·
                refine ⟨1630836467187748494638105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087224311458498996425403 1630836467187748494638105)
                ·
                  refine ⟨1223127350390811370978579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1630836467187748494638105 1223127350390811370978579)
                  ·
                    refine ⟨1834691025586217056467869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1223127350390811370978579 1834691025586217056467869)
                    ·
                      refine ⟨688009134594831396175451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1834691025586217056467869 688009134594831396175451)
                      ·
                        rfl

theorem cell23_1339893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1339893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339893 prefixEnd_1339893 := by exact prefixLift 1339893
  have htrace : WordTrace (prefixWord ++ tailWord_1339893) baseStart_1339893 baseEnd_1339893 := by
    simpa [prefixWord, tailWord_1339893, baseEnd_1339893] using wordTrace_append hprefix tailTrace_1339893
  have hstable : (prefixWord ++ tailWord_1339893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339893).length < 2 ^ (prefixWord ++ tailWord_1339893).sum := by decide
  have hdescent : baseEnd_1339893 < baseStart_1339893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339939 : List Nat := [1, 1, 1, 4, 4, 3, 2, 2, 5]
def baseStart_1339939 : Nat := 118140960795 + 1339939 * 2 ^ 59
def prefixEnd_1339939 : Nat := 4983230072969 + 3 ^ 40 * 1339939 * 2
def baseEnd_1339939 : Nat := 76448083856104246244471

theorem tailTrace_1339939 : CollatzResearch.WordTrace tailWord_1339939 prefixEnd_1339939 76448083856104246244471 := by
  unfold tailWord_1339939
  simp only [CollatzResearch.WordTrace]
  refine ⟨48871590292637321207158871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32581060195091547471439247 48871590292637321207158871)
  ·
    refine ⟨73307385438955981810738307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48871590292637321207158871 73307385438955981810738307)
    ·
      refine ⟨109961078158433972716107461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73307385438955981810738307 109961078158433972716107461)
      ·
        refine ⟨20617702154706369884270149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109961078158433972716107461 20617702154706369884270149)
        ·
          refine ⟨3865819154007444353300653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20617702154706369884270149 3865819154007444353300653)
          ·
            refine ⟨1449682182752791632487745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3865819154007444353300653 1449682182752791632487745)
            ·
              refine ⟨1087261637064593724365809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449682182752791632487745 1087261637064593724365809)
              ·
                refine ⟨815446227798445293274357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087261637064593724365809 815446227798445293274357)
                ·
                  refine ⟨76448083856104246244471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 815446227798445293274357 76448083856104246244471)
                  ·
                    rfl

theorem cell23_1339939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 5].length) (baseStart_1339939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1339939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1339939 prefixEnd_1339939 := by exact prefixLift 1339939
  have htrace : WordTrace (prefixWord ++ tailWord_1339939) baseStart_1339939 baseEnd_1339939 := by
    simpa [prefixWord, tailWord_1339939, baseEnd_1339939] using wordTrace_append hprefix tailTrace_1339939
  have hstable : (prefixWord ++ tailWord_1339939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339939).length < 2 ^ (prefixWord ++ tailWord_1339939).sum := by decide
  have hdescent : baseEnd_1339939 < baseStart_1339939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340032 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 1, 5, 2]
def baseStart_1340032 : Nat := 118140960795 + 1340032 * 2 ^ 59
def prefixEnd_1340032 : Nat := 4983230072969 + 3 ^ 40 * 1340032 * 2
def baseEnd_1340032 : Nat := 688080508405806352337311

theorem tailTrace_1340032 : CollatzResearch.WordTrace tailWord_1340032 prefixEnd_1340032 688080508405806352337311 := by
  unfold tailWord_1340032
  simp only [CollatzResearch.WordTrace]
  refine ⟨24437491140650199045147175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32583321520866932060196233 24437491140650199045147175)
  ·
    refine ⟨36656236710975298567720763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24437491140650199045147175 36656236710975298567720763)
    ·
      refine ⟨54984355066462947851581145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36656236710975298567720763 54984355066462947851581145)
      ·
        refine ⟨41238266299847210888685859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54984355066462947851581145 41238266299847210888685859)
        ·
          refine ⟨61857399449770816333028789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41238266299847210888685859 61857399449770816333028789)
          ·
            refine ⟨5799131198416014031221449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61857399449770816333028789 5799131198416014031221449)
            ·
              refine ⟨4349348398812010523416087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5799131198416014031221449 4349348398812010523416087)
              ·
                refine ⟨6524022598218015785124131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349348398812010523416087 6524022598218015785124131)
                ·
                  refine ⟨9786033897327023677686197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6524022598218015785124131 9786033897327023677686197)
                  ·
                    refine ⟨917440677874408469783081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9786033897327023677686197 917440677874408469783081)
                    ·
                      refine ⟨688080508405806352337311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917440677874408469783081 688080508405806352337311)
                      ·
                        rfl

theorem cell23_1340032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_1340032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340032 prefixEnd_1340032 := by exact prefixLift 1340032
  have htrace : WordTrace (prefixWord ++ tailWord_1340032) baseStart_1340032 baseEnd_1340032 := by
    simpa [prefixWord, tailWord_1340032, baseEnd_1340032] using wordTrace_append hprefix tailTrace_1340032
  have hstable : (prefixWord ++ tailWord_1340032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340032).length < 2 ^ (prefixWord ++ tailWord_1340032).sum := by decide
  have hdescent : baseEnd_1340032 < baseStart_1340032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340079 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 4]
def baseStart_1340079 : Nat := 118140960795 + 1340079 * 2 ^ 59
def prefixEnd_1340079 : Nat := 4983230072969 + 3 ^ 40 * 1340079 * 2
def baseEnd_1340079 : Nat := 688104641996567668449595

theorem tailTrace_1340079 : CollatzResearch.WordTrace tailWord_1340079 prefixEnd_1340079 688104641996567668449595 := by
  unfold tailWord_1340079
  simp only [CollatzResearch.WordTrace]
  refine ⟨48876696512130125117255291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32584464341420083411503527 48876696512130125117255291)
  ·
    refine ⟨73315044768195187675882937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48876696512130125117255291 73315044768195187675882937)
    ·
      refine ⟨54986283576146390756912203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73315044768195187675882937 54986283576146390756912203)
      ·
        refine ⟨82479425364219586135368305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54986283576146390756912203 82479425364219586135368305)
        ·
          refine ⟨61859569023164689601526229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82479425364219586135368305 61859569023164689601526229)
          ·
            refine ⟨1449833648980422412535771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61859569023164689601526229 1449833648980422412535771)
            ·
              refine ⟨2174750473470633618803657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449833648980422412535771 2174750473470633618803657)
              ·
                refine ⟨1631062855102975214102743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2174750473470633618803657 1631062855102975214102743)
                ·
                  refine ⟨2446594282654462821154115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631062855102975214102743 2446594282654462821154115)
                  ·
                    refine ⟨3669891423981694231731173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2446594282654462821154115 3669891423981694231731173)
                    ·
                      refine ⟨688104641996567668449595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3669891423981694231731173 688104641996567668449595)
                      ·
                        rfl

theorem cell23_1340079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_1340079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340079 prefixEnd_1340079 := by exact prefixLift 1340079
  have htrace : WordTrace (prefixWord ++ tailWord_1340079) baseStart_1340079 baseEnd_1340079 := by
    simpa [prefixWord, tailWord_1340079, baseEnd_1340079] using wordTrace_append hprefix tailTrace_1340079
  have hstable : (prefixWord ++ tailWord_1340079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340079).length < 2 ^ (prefixWord ++ tailWord_1340079).sum := by decide
  have hdescent : baseEnd_1340079 < baseStart_1340079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340092 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1340092 : Nat := 118140960795 + 1340092 * 2 ^ 59
def prefixEnd_1340092 : Nat := 4983230072969 + 3 ^ 40 * 1340092 * 2
def baseEnd_1340092 : Nat := 688111317245076117587035

theorem tailTrace_1340092 : CollatzResearch.WordTrace tailWord_1340092 prefixEnd_1340092 688111317245076117587035 := by
  unfold tailWord_1340092
  simp only [CollatzResearch.WordTrace]
  refine ⟨24438585330541514168739265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32584780440722018891652353 24438585330541514168739265)
  ·
    refine ⟨18328938997906135626554449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24438585330541514168739265 18328938997906135626554449)
    ·
      refine ⟨13746704248429601719915837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18328938997906135626554449 13746704248429601719915837)
      ·
        refine ⟨5155014093161100644968439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13746704248429601719915837 5155014093161100644968439)
        ·
          refine ⟨7732521139741650967452659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5155014093161100644968439 7732521139741650967452659)
          ·
            refine ⟨11598781709612476451178989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732521139741650967452659 11598781709612476451178989)
            ·
              refine ⟨4349543141104678669192121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11598781709612476451178989 4349543141104678669192121)
              ·
                refine ⟨3262157355828509001894091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4349543141104678669192121 3262157355828509001894091)
                ·
                  refine ⟨4893236033742763502841137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262157355828509001894091 4893236033742763502841137)
                  ·
                    refine ⟨3669927025307072627130853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4893236033742763502841137 3669927025307072627130853)
                    ·
                      refine ⟨688111317245076117587035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3669927025307072627130853 688111317245076117587035)
                      ·
                        rfl

theorem cell23_1340092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1340092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340092 prefixEnd_1340092 := by exact prefixLift 1340092
  have htrace : WordTrace (prefixWord ++ tailWord_1340092) baseStart_1340092 baseEnd_1340092 := by
    simpa [prefixWord, tailWord_1340092, baseEnd_1340092] using wordTrace_append hprefix tailTrace_1340092
  have hstable : (prefixWord ++ tailWord_1340092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340092).length < 2 ^ (prefixWord ++ tailWord_1340092).sum := by decide
  have hdescent : baseEnd_1340092 < baseStart_1340092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340112 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 8, 1, 3]
def baseStart_1340112 : Nat := 118140960795 + 1340112 * 2 ^ 59
def prefixEnd_1340112 : Nat := 4983230072969 + 3 ^ 40 * 1340112 * 2
def baseEnd_1340112 : Nat := 688121586858166039336943

theorem tailTrace_1340112 : CollatzResearch.WordTrace tailWord_1340112 prefixEnd_1340112 688121586858166039336943 := by
  unfold tailWord_1340112
  simp only [CollatzResearch.WordTrace]
  refine ⟨24438950060505285876603295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32585266747340381168804393 24438950060505285876603295)
  ·
    refine ⟨36658425090757928814904943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24438950060505285876603295 36658425090757928814904943)
    ·
      refine ⟨54987637636136893222357415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36658425090757928814904943 54987637636136893222357415)
      ·
        refine ⟨82481456454205339833536123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54987637636136893222357415 82481456454205339833536123)
        ·
          refine ⟨123722184681308009750304185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82481456454205339833536123 123722184681308009750304185)
          ·
            refine ⟨92791638510981007312728139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123722184681308009750304185 92791638510981007312728139)
            ·
              refine ⟨139187457766471510969092209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92791638510981007312728139 139187457766471510969092209)
              ·
                refine ⟨104390593324853633226819157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139187457766471510969092209 104390593324853633226819157)
                ·
                  refine ⟨1223327265525628514376787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 104390593324853633226819157 1223327265525628514376787)
                  ·
                    refine ⟨1834990898288442771565181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1223327265525628514376787 1834990898288442771565181)
                    ·
                      refine ⟨688121586858166039336943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1834990898288442771565181 688121586858166039336943)
                      ·
                        rfl

theorem cell23_1340112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 1, 3].length) (baseStart_1340112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340112 prefixEnd_1340112 := by exact prefixLift 1340112
  have htrace : WordTrace (prefixWord ++ tailWord_1340112) baseStart_1340112 baseEnd_1340112 := by
    simpa [prefixWord, tailWord_1340112, baseEnd_1340112] using wordTrace_append hprefix tailTrace_1340112
  have hstable : (prefixWord ++ tailWord_1340112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340112).length < 2 ^ (prefixWord ++ tailWord_1340112).sum := by decide
  have hdescent : baseEnd_1340112 < baseStart_1340112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340129 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_1340129 : Nat := 118140960795 + 1340129 * 2 ^ 59
def prefixEnd_1340129 : Nat := 4983230072969 + 3 ^ 40 * 1340129 * 2
def baseEnd_1340129 : Nat := 688130316029292472824365

theorem tailTrace_1340129 : CollatzResearch.WordTrace tailWord_1340129 prefixEnd_1340129 688130316029292472824365 := by
  unfold tailWord_1340129
  simp only [CollatzResearch.WordTrace]
  refine ⟨48878520161948983656575441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32585680107965989104383627 48878520161948983656575441)
  ·
    refine ⟨36658890121461737742431581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48878520161948983656575441 36658890121461737742431581)
    ·
      refine ⟨13747083795548151653411843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36658890121461737742431581 13747083795548151653411843)
      ·
        refine ⟨20620625693322227480117765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13747083795548151653411843 20620625693322227480117765)
        ·
          refine ⟨3866367317497917652522081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20620625693322227480117765 3866367317497917652522081)
          ·
            refine ⟨2899775488123438239391561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3866367317497917652522081 2899775488123438239391561)
            ·
              refine ⟨2174831616092578679543671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899775488123438239391561 2174831616092578679543671)
              ·
                refine ⟨3262247424138868019315507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174831616092578679543671 3262247424138868019315507)
                ·
                  refine ⟨4893371136208302028973261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262247424138868019315507 4893371136208302028973261)
                  ·
                    refine ⟨1835014176078113260864973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4893371136208302028973261 1835014176078113260864973)
                    ·
                      refine ⟨688130316029292472824365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1835014176078113260864973 688130316029292472824365)
                      ·
                        rfl

theorem cell23_1340129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_1340129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340129 prefixEnd_1340129 := by exact prefixLift 1340129
  have htrace : WordTrace (prefixWord ++ tailWord_1340129) baseStart_1340129 baseEnd_1340129 := by
    simpa [prefixWord, tailWord_1340129, baseEnd_1340129] using wordTrace_append hprefix tailTrace_1340129
  have hstable : (prefixWord ++ tailWord_1340129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340129).length < 2 ^ (prefixWord ++ tailWord_1340129).sum := by decide
  have hdescent : baseEnd_1340129 < baseStart_1340129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340139 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 1, 3, 2]
def baseStart_1340139 : Nat := 118140960795 + 1340139 * 2 ^ 59
def prefixEnd_1340139 : Nat := 4983230072969 + 3 ^ 40 * 1340139 * 2
def baseEnd_1340139 : Nat := 688135450835837433699319

theorem tailTrace_1340139 : CollatzResearch.WordTrace tailWord_1340139 prefixEnd_1340139 688135450835837433699319 := by
  unfold tailWord_1340139
  simp only [CollatzResearch.WordTrace]
  refine ⟨48878884891912755364439471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32585923261275170242959647 48878884891912755364439471)
  ·
    refine ⟨73318327337869133046659207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48878884891912755364439471 73318327337869133046659207)
    ·
      refine ⟨109977491006803699569988811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73318327337869133046659207 109977491006803699569988811)
      ·
        refine ⟨164966236510205549354983217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109977491006803699569988811 164966236510205549354983217)
        ·
          refine ⟨123724677382654162016237413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164966236510205549354983217 123724677382654162016237413)
          ·
            refine ⟨23198377009247655378044515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123724677382654162016237413 23198377009247655378044515)
            ·
              refine ⟨34797565513871483067066773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23198377009247655378044515 34797565513871483067066773)
              ·
                refine ⟨1631135883462725768768755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34797565513871483067066773 1631135883462725768768755)
                ·
                  refine ⟨2446703825194088653153133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631135883462725768768755 2446703825194088653153133)
                  ·
                    refine ⟨917513934447783244932425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446703825194088653153133 917513934447783244932425)
                    ·
                      refine ⟨688135450835837433699319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917513934447783244932425 688135450835837433699319)
                      ·
                        rfl

theorem cell23_1340139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 3, 2].length) (baseStart_1340139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340139 prefixEnd_1340139 := by exact prefixLift 1340139
  have htrace : WordTrace (prefixWord ++ tailWord_1340139) baseStart_1340139 baseEnd_1340139 := by
    simpa [prefixWord, tailWord_1340139, baseEnd_1340139] using wordTrace_append hprefix tailTrace_1340139
  have hstable : (prefixWord ++ tailWord_1340139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340139).length < 2 ^ (prefixWord ++ tailWord_1340139).sum := by decide
  have hdescent : baseEnd_1340139 < baseStart_1340139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340145 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 1, 8]
def baseStart_1340145 : Nat := 118140960795 + 1340145 * 2 ^ 59
def prefixEnd_1340145 : Nat := 4983230072969 + 3 ^ 40 * 1340145 * 2
def baseEnd_1340145 : Nat := 229379510573254803408097

theorem tailTrace_1340145 : CollatzResearch.WordTrace tailWord_1340145 prefixEnd_1340145 229379510573254803408097 := by
  unfold tailWord_1340145
  simp only [CollatzResearch.WordTrace]
  refine ⟨48879103729891018389157889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32586069153260678926105259 48879103729891018389157889)
  ·
    refine ⟨36659327797418263791868417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48879103729891018389157889 36659327797418263791868417)
    ·
      refine ⟨27494495848063697843901313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36659327797418263791868417 27494495848063697843901313)
      ·
        refine ⟨20620871886047773382925985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27494495848063697843901313 20620871886047773382925985)
        ·
          refine ⟨15465653914535830037194489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20620871886047773382925985 15465653914535830037194489)
          ·
            refine ⟨11599240435901872527895867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15465653914535830037194489 11599240435901872527895867)
            ·
              refine ⟨17398860653852808791843801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11599240435901872527895867 17398860653852808791843801)
              ·
                refine ⟨13049145490389606593882851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17398860653852808791843801 13049145490389606593882851)
                ·
                  refine ⟨19573718235584409890824277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13049145490389606593882851 19573718235584409890824277)
                  ·
                    refine ⟨229379510573254803408097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19573718235584409890824277 229379510573254803408097)
                    ·
                      rfl

theorem cell23_1340145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_1340145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340145 prefixEnd_1340145 := by exact prefixLift 1340145
  have htrace : WordTrace (prefixWord ++ tailWord_1340145) baseStart_1340145 baseEnd_1340145 := by
    simpa [prefixWord, tailWord_1340145, baseEnd_1340145] using wordTrace_append hprefix tailTrace_1340145
  have hstable : (prefixWord ++ tailWord_1340145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340145).length < 2 ^ (prefixWord ++ tailWord_1340145).sum := by decide
  have hdescent : baseEnd_1340145 < baseStart_1340145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340155 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5]
def baseStart_1340155 : Nat := 118140960795 + 1340155 * 2 ^ 59
def prefixEnd_1340155 : Nat := 4983230072969 + 3 ^ 40 * 1340155 * 2
def baseEnd_1340155 : Nat := 688143666526309371099245

theorem tailTrace_1340155 : CollatzResearch.WordTrace tailWord_1340155 prefixEnd_1340155 688143666526309371099245 := by
  unfold tailWord_1340155
  simp only [CollatzResearch.WordTrace]
  refine ⟨48879468459854790097021919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32586312306569860064681279 48879468459854790097021919)
  ·
    refine ⟨73319202689782185145532879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48879468459854790097021919 73319202689782185145532879)
    ·
      refine ⟨109978804034673277718299319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73319202689782185145532879 109978804034673277718299319)
      ·
        refine ⟨164968206052009916577448979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109978804034673277718299319 164968206052009916577448979)
        ·
          refine ⟨247452309078014874866173469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164968206052009916577448979 247452309078014874866173469)
          ·
            refine ⟨92794615904255578074815051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247452309078014874866173469 92794615904255578074815051)
            ·
              refine ⟨139191923856383367112222577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92794615904255578074815051 139191923856383367112222577)
              ·
                refine ⟨104393942892287525334166933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139191923856383367112222577 104393942892287525334166933)
                ·
                  refine ⟨4893466073075977750039075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104393942892287525334166933 4893466073075977750039075)
                  ·
                    refine ⟨7340199109613966625058613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893466073075977750039075 7340199109613966625058613)
                    ·
                      refine ⟨688143666526309371099245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7340199109613966625058613 688143666526309371099245)
                      ·
                        rfl

theorem cell23_1340155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_1340155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340155 prefixEnd_1340155 := by exact prefixLift 1340155
  have htrace : WordTrace (prefixWord ++ tailWord_1340155) baseStart_1340155 baseEnd_1340155 := by
    simpa [prefixWord, tailWord_1340155, baseEnd_1340155] using wordTrace_append hprefix tailTrace_1340155
  have hstable : (prefixWord ++ tailWord_1340155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340155).length < 2 ^ (prefixWord ++ tailWord_1340155).sum := by decide
  have hdescent : baseEnd_1340155 < baseStart_1340155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340156 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_1340156 : Nat := 118140960795 + 1340156 * 2 ^ 59
def prefixEnd_1340156 : Nat := 4983230072969 + 3 ^ 40 * 1340156 * 2
def baseEnd_1340156 : Nat := 688144180006963867186741

theorem tailTrace_1340156 : CollatzResearch.WordTrace tailWord_1340156 prefixEnd_1340156 688144180006963867186741 := by
  unfold tailWord_1340156
  simp only [CollatzResearch.WordTrace]
  refine ⟨24439752466425583633904161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32586336621900778178538881 24439752466425583633904161)
  ·
    refine ⟨18329814349819187725428121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24439752466425583633904161 18329814349819187725428121)
    ·
      refine ⟨13747360762364390794071091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18329814349819187725428121 13747360762364390794071091)
      ·
        refine ⟨20621041143546586191106637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13747360762364390794071091 20621041143546586191106637)
        ·
          refine ⟨7732890428829969821664989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20621041143546586191106637 7732890428829969821664989)
          ·
            refine ⟨2899833910811238683124371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7732890428829969821664989 2899833910811238683124371)
            ·
              refine ⟨4349750866216858024686557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899833910811238683124371 4349750866216858024686557)
              ·
                refine ⟨1631156574831321759257459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4349750866216858024686557 1631156574831321759257459)
                ·
                  refine ⟨2446734862246982638886189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631156574831321759257459 2446734862246982638886189)
                  ·
                    refine ⟨917525573342618489582321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2446734862246982638886189 917525573342618489582321)
                    ·
                      refine ⟨688144180006963867186741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917525573342618489582321 688144180006963867186741)
                      ·
                        rfl

theorem cell23_1340156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_1340156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340156 prefixEnd_1340156 := by exact prefixLift 1340156
  have htrace : WordTrace (prefixWord ++ tailWord_1340156) baseStart_1340156 baseEnd_1340156 := by
    simpa [prefixWord, tailWord_1340156, baseEnd_1340156] using wordTrace_append hprefix tailTrace_1340156
  have hstable : (prefixWord ++ tailWord_1340156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340156).length < 2 ^ (prefixWord ++ tailWord_1340156).sum := by decide
  have hdescent : baseEnd_1340156 < baseStart_1340156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340192 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 7]
def baseStart_1340192 : Nat := 118140960795 + 1340192 * 2 ^ 59
def prefixEnd_1340192 : Nat := 4983230072969 + 3 ^ 40 * 1340192 * 2
def baseEnd_1340192 : Nat := 76462518367836191815175

theorem tailTrace_1340192 : CollatzResearch.WordTrace tailWord_1340192 prefixEnd_1340192 76462518367836191815175 := by
  unfold tailWord_1340192
  simp only [CollatzResearch.WordTrace]
  refine ⟨24440408980360372708059415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32587211973813830277412553 24440408980360372708059415)
  ·
    refine ⟨36660613470540559062089123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24440408980360372708059415 36660613470540559062089123)
    ·
      refine ⟨54990920205810838593133685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36660613470540559062089123 54990920205810838593133685)
      ·
        refine ⟨5155398769294766118106283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54990920205810838593133685 5155398769294766118106283)
        ·
          refine ⟨7733098153942149177159425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5155398769294766118106283 7733098153942149177159425)
          ·
            refine ⟨5799823615456611882869569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7733098153942149177159425 5799823615456611882869569)
            ·
              refine ⟨4349867711592458912152177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5799823615456611882869569 4349867711592458912152177)
              ·
                refine ⟨3262400783694344184114133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4349867711592458912152177 3262400783694344184114133)
                ·
                  refine ⟨76462518367836191815175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3262400783694344184114133 76462518367836191815175)
                  ·
                    rfl

theorem cell23_1340192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_1340192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340192 prefixEnd_1340192 := by exact prefixLift 1340192
  have htrace : WordTrace (prefixWord ++ tailWord_1340192) baseStart_1340192 baseEnd_1340192 := by
    simpa [prefixWord, tailWord_1340192, baseEnd_1340192] using wordTrace_append hprefix tailTrace_1340192
  have hstable : (prefixWord ++ tailWord_1340192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340192).length < 2 ^ (prefixWord ++ tailWord_1340192).sum := by decide
  have hdescent : baseEnd_1340192 < baseStart_1340192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340232 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1340232 : Nat := 118140960795 + 1340232 * 2 ^ 59
def prefixEnd_1340232 : Nat := 4983230072969 + 3 ^ 40 * 1340232 * 2
def baseEnd_1340232 : Nat := 688183204536705569836391

theorem tailTrace_1340232 : CollatzResearch.WordTrace tailWord_1340232 prefixEnd_1340232 688183204536705569836391 := by
  unfold tailWord_1340232
  simp only [CollatzResearch.WordTrace]
  refine ⟨24441138440287916123787475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32588184587050554831716633 24441138440287916123787475)
  ·
    refine ⟨36661707660431874185681213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24441138440287916123787475 36661707660431874185681213)
    ·
      refine ⟨13748140372661952819630455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36661707660431874185681213 13748140372661952819630455)
      ·
        refine ⟨20622210558992929229445683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13748140372661952819630455 20622210558992929229445683)
        ·
          refine ⟨30933315838489393844168525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20622210558992929229445683 30933315838489393844168525)
          ·
            refine ⟨11599993439433522691563197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30933315838489393844168525 11599993439433522691563197)
            ·
              refine ⟨4349997539787571009336199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11599993439433522691563197 4349997539787571009336199)
              ·
                refine ⟨6524996309681356514004299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349997539787571009336199 6524996309681356514004299)
                ·
                  refine ⟨9787494464522034771006449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6524996309681356514004299 9787494464522034771006449)
                  ·
                    refine ⟨7340620848391526078254837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9787494464522034771006449 7340620848391526078254837)
                    ·
                      refine ⟨688183204536705569836391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7340620848391526078254837 688183204536705569836391)
                      ·
                        rfl

theorem cell23_1340232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1340232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340232 prefixEnd_1340232 := by exact prefixLift 1340232
  have htrace : WordTrace (prefixWord ++ tailWord_1340232) baseStart_1340232 baseEnd_1340232 := by
    simpa [prefixWord, tailWord_1340232, baseEnd_1340232] using wordTrace_append hprefix tailTrace_1340232
  have hstable : (prefixWord ++ tailWord_1340232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340232).length < 2 ^ (prefixWord ++ tailWord_1340232).sum := by decide
  have hdescent : baseEnd_1340232 < baseStart_1340232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340259 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1340259 : Nat := 118140960795 + 1340259 * 2 ^ 59
def prefixEnd_1340259 : Nat := 4983230072969 + 3 ^ 40 * 1340259 * 2
def baseEnd_1340259 : Nat := 688197068514376964198767

theorem tailTrace_1340259 : CollatzResearch.WordTrace tailWord_1340259 prefixEnd_1340259 688197068514376964198767 := by
  unfold tailWord_1340259
  simp only [CollatzResearch.WordTrace]
  refine ⟨48883261651478015858807831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32588841100985343905871887 48883261651478015858807831)
  ·
    refine ⟨73324892477217023788211747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48883261651478015858807831 73324892477217023788211747)
    ·
      refine ⟨109987338715825535682317621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73324892477217023788211747 109987338715825535682317621)
      ·
        refine ⟨10311313004608643970217277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109987338715825535682317621 10311313004608643970217277)
        ·
          refine ⟨3866742376728241488831479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10311313004608643970217277 3866742376728241488831479)
          ·
            refine ⟨5800113565092362233247219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866742376728241488831479 5800113565092362233247219)
            ·
              refine ⟨8700170347638543349870829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800113565092362233247219 8700170347638543349870829)
              ·
                refine ⟨3262563880364453756201561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8700170347638543349870829 3262563880364453756201561)
                ·
                  refine ⟨2446922910273340317151171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3262563880364453756201561 2446922910273340317151171)
                  ·
                    refine ⟨3670384365410010475726757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2446922910273340317151171 3670384365410010475726757)
                    ·
                      refine ⟨688197068514376964198767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3670384365410010475726757 688197068514376964198767)
                      ·
                        rfl

theorem cell23_1340259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1340259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340259 prefixEnd_1340259 := by exact prefixLift 1340259
  have htrace : WordTrace (prefixWord ++ tailWord_1340259) baseStart_1340259 baseEnd_1340259 := by
    simpa [prefixWord, tailWord_1340259, baseEnd_1340259] using wordTrace_append hprefix tailTrace_1340259
  have hstable : (prefixWord ++ tailWord_1340259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340259).length < 2 ^ (prefixWord ++ tailWord_1340259).sum := by decide
  have hdescent : baseEnd_1340259 < baseStart_1340259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340310 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1340310 : Nat := 118140960795 + 1340310 * 2 ^ 59
def prefixEnd_1340310 : Nat := 4983230072969 + 3 ^ 40 * 1340310 * 2
def baseEnd_1340310 : Nat := 688223256027756264661033

theorem tailTrace_1340310 : CollatzResearch.WordTrace tailWord_1340310 prefixEnd_1340310 688223256027756264661033 := by
  unfold tailWord_1340310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055320110893328223057149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32590081182862167712609589 3055320110893328223057149)
  ·
    refine ⟨1145745041584998083646431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3055320110893328223057149 1145745041584998083646431)
    ·
      refine ⟨1718617562377497125469647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145745041584998083646431 1718617562377497125469647)
      ·
        refine ⟨2577926343566245688204471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718617562377497125469647 2577926343566245688204471)
        ·
          refine ⟨3866889515349368532306707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577926343566245688204471 3866889515349368532306707)
          ·
            refine ⟨5800334273024052798460061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866889515349368532306707 5800334273024052798460061)
            ·
              refine ⟨2175125352384019799422523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5800334273024052798460061 2175125352384019799422523)
              ·
                refine ⟨3262688028576029699133785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175125352384019799422523 3262688028576029699133785)
                ·
                  refine ⟨2447016021432022274350339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3262688028576029699133785 2447016021432022274350339)
                  ·
                    refine ⟨3670524032148033411525509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447016021432022274350339 3670524032148033411525509)
                    ·
                      refine ⟨688223256027756264661033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3670524032148033411525509 688223256027756264661033)
                      ·
                        rfl

theorem cell23_1340310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1340310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340310 prefixEnd_1340310 := by exact prefixLift 1340310
  have htrace : WordTrace (prefixWord ++ tailWord_1340310) baseStart_1340310 baseEnd_1340310 := by
    simpa [prefixWord, tailWord_1340310, baseEnd_1340310] using wordTrace_append hprefix tailTrace_1340310
  have hstable : (prefixWord ++ tailWord_1340310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340310).length < 2 ^ (prefixWord ++ tailWord_1340310).sum := by decide
  have hdescent : baseEnd_1340310 < baseStart_1340310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340329 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 1, 5]
def baseStart_1340329 : Nat := 118140960795 + 1340329 * 2 ^ 59
def prefixEnd_1340329 : Nat := 4983230072969 + 3 ^ 40 * 1340329 * 2
def baseEnd_1340329 : Nat := 229411004053397230107815

theorem tailTrace_1340329 : CollatzResearch.WordTrace tailWord_1340329 prefixEnd_1340329 229411004053397230107815 := by
  unfold tailWord_1340329
  simp only [CollatzResearch.WordTrace]
  refine ⟨48885814761224417813856041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32590543174149611875904027 48885814761224417813856041)
  ·
    refine ⟨36664361070918313360392031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48885814761224417813856041 36664361070918313360392031)
    ·
      refine ⟨54996541606377470040588047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36664361070918313360392031 54996541606377470040588047)
      ·
        refine ⟨82494812409566205060882071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54996541606377470040588047 82494812409566205060882071)
        ·
          refine ⟨123742218614349307591323107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82494812409566205060882071 123742218614349307591323107)
          ·
            refine ⟨185613327921523961386984661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123742218614349307591323107 185613327921523961386984661)
            ·
              refine ⟨4350312373160717845007453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 185613327921523961386984661 4350312373160717845007453)
              ·
                refine ⟨1631367139935269191877795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4350312373160717845007453 1631367139935269191877795)
                ·
                  refine ⟨2447050709902903787816693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631367139935269191877795 2447050709902903787816693)
                  ·
                    refine ⟨229411004053397230107815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2447050709902903787816693 229411004053397230107815)
                    ·
                      rfl

theorem cell23_1340329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_1340329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340329 prefixEnd_1340329 := by exact prefixLift 1340329
  have htrace : WordTrace (prefixWord ++ tailWord_1340329) baseStart_1340329 baseEnd_1340329 := by
    simpa [prefixWord, tailWord_1340329, baseEnd_1340329] using wordTrace_append hprefix tailTrace_1340329
  have hstable : (prefixWord ++ tailWord_1340329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340329).length < 2 ^ (prefixWord ++ tailWord_1340329).sum := by decide
  have hdescent : baseEnd_1340329 < baseStart_1340329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340343 : List Nat := [1, 1, 3, 1, 3, 1, 4, 4, 1, 1, 3]
def baseStart_1340343 : Nat := 118140960795 + 1340343 * 2 ^ 59
def prefixEnd_1340343 : Nat := 4983230072969 + 3 ^ 40 * 1340343 * 2
def baseEnd_1340343 : Nat := 688240200889354635548381

theorem tailTrace_1340343 : CollatzResearch.WordTrace tailWord_1340343 prefixEnd_1340343 688240200889354635548381 := by
  unfold tailWord_1340343
  simp only [CollatzResearch.WordTrace]
  refine ⟨48886325383173698204865683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32590883588782465469910455 48886325383173698204865683)
  ·
    refine ⟨73329488074760547307298525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48886325383173698204865683 73329488074760547307298525)
    ·
      refine ⟨27498558028035205240236947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73329488074760547307298525 27498558028035205240236947)
      ·
        refine ⟨41247837042052807860355421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27498558028035205240236947 41247837042052807860355421)
        ·
          refine ⟨15467938890769802947633283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41247837042052807860355421 15467938890769802947633283)
          ·
            refine ⟨23201908336154704421449925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15467938890769802947633283 23201908336154704421449925)
            ·
              refine ⟨4350357813029007079021861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23201908336154704421449925 4350357813029007079021861)
              ·
                refine ⟨815692089942938827316599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4350357813029007079021861 815692089942938827316599)
                ·
                  refine ⟨1223538134914408240974899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815692089942938827316599 1223538134914408240974899)
                  ·
                    refine ⟨1835307202371612361462349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1223538134914408240974899 1835307202371612361462349)
                    ·
                      refine ⟨688240200889354635548381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1835307202371612361462349 688240200889354635548381)
                      ·
                        rfl

theorem cell23_1340343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_1340343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340343 prefixEnd_1340343 := by exact prefixLift 1340343
  have htrace : WordTrace (prefixWord ++ tailWord_1340343) baseStart_1340343 baseEnd_1340343 := by
    simpa [prefixWord, tailWord_1340343, baseEnd_1340343] using wordTrace_append hprefix tailTrace_1340343
  have hstable : (prefixWord ++ tailWord_1340343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340343).length < 2 ^ (prefixWord ++ tailWord_1340343).sum := by decide
  have hdescent : baseEnd_1340343 < baseStart_1340343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340359 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 1, 6]
def baseStart_1340359 : Nat := 118140960795 + 1340359 * 2 ^ 59
def prefixEnd_1340359 : Nat := 4983230072969 + 3 ^ 40 * 1340359 * 2
def baseEnd_1340359 : Nat := 229416138859942190982769

theorem tailTrace_1340359 : CollatzResearch.WordTrace tailWord_1340359 prefixEnd_1340359 229416138859942190982769 := by
  unfold tailWord_1340359
  simp only [CollatzResearch.WordTrace]
  refine ⟨48886908951115732937448131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32591272634077155291632087 48886908951115732937448131)
  ·
    refine ⟨73330363426673599406172197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48886908951115732937448131 73330363426673599406172197)
    ·
      refine ⟨13749443142501299888657287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73330363426673599406172197 13749443142501299888657287)
      ·
        refine ⟨20624164713751949832985931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13749443142501299888657287 20624164713751949832985931)
        ·
          refine ⟨30936247070627924749478897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20624164713751949832985931 30936247070627924749478897)
          ·
            refine ⟨23202185302970943562109173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30936247070627924749478897 23202185302970943562109173)
            ·
              refine ⟨2175204872153525958947735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23202185302970943562109173 2175204872153525958947735)
              ·
                refine ⟨3262807308230288938421603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175204872153525958947735 3262807308230288938421603)
                ·
                  refine ⟨4894210962345433407632405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262807308230288938421603 4894210962345433407632405)
                  ·
                    refine ⟨229416138859942190982769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4894210962345433407632405 229416138859942190982769)
                    ·
                      rfl

theorem cell23_1340359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_1340359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340359 prefixEnd_1340359 := by exact prefixLift 1340359
  have htrace : WordTrace (prefixWord ++ tailWord_1340359) baseStart_1340359 baseEnd_1340359 := by
    simpa [prefixWord, tailWord_1340359, baseEnd_1340359] using wordTrace_append hprefix tailTrace_1340359
  have hstable : (prefixWord ++ tailWord_1340359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340359).length < 2 ^ (prefixWord ++ tailWord_1340359).sum := by decide
  have hdescent : baseEnd_1340359 < baseStart_1340359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340366 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_1340366 : Nat := 118140960795 + 1340366 * 2 ^ 59
def prefixEnd_1340366 : Nat := 4983230072969 + 3 ^ 40 * 1340366 * 2
def baseEnd_1340366 : Nat := 688252010944408045560775

theorem tailTrace_1340366 : CollatzResearch.WordTrace tailWord_1340366 prefixEnd_1340366 688252010944408045560775 := by
  unfold tailWord_1340366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6110895532761296641619119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32591442841393582088635301 6110895532761296641619119)
  ·
    refine ⟨9166343299141944962428679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6110895532761296641619119 9166343299141944962428679)
    ·
      refine ⟨13749514948712917443643019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9166343299141944962428679 13749514948712917443643019)
      ·
        refine ⟨20624272423069376165464529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13749514948712917443643019 20624272423069376165464529)
        ·
          refine ⟨15468204317302032124098397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20624272423069376165464529 15468204317302032124098397)
          ·
            refine ⟨5800576618988262046536899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15468204317302032124098397 5800576618988262046536899)
            ·
              refine ⟨8700864928482393069805349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800576618988262046536899 8700864928482393069805349)
              ·
                refine ⟨1631412174090448700588503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8700864928482393069805349 1631412174090448700588503)
                ·
                  refine ⟨2447118261135673050882755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631412174090448700588503 2447118261135673050882755)
                  ·
                    refine ⟨3670677391703509576324133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447118261135673050882755 3670677391703509576324133)
                    ·
                      refine ⟨688252010944408045560775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3670677391703509576324133 688252010944408045560775)
                      ·
                        rfl

theorem cell23_1340366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_1340366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340366 prefixEnd_1340366 := by exact prefixLift 1340366
  have htrace : WordTrace (prefixWord ++ tailWord_1340366) baseStart_1340366 baseEnd_1340366 := by
    simpa [prefixWord, tailWord_1340366, baseEnd_1340366] using wordTrace_append hprefix tailTrace_1340366
  have hstable : (prefixWord ++ tailWord_1340366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340366).length < 2 ^ (prefixWord ++ tailWord_1340366).sum := by decide
  have hdescent : baseEnd_1340366 < baseStart_1340366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340406 : List Nat := [5, 1, 1, 1, 3, 2, 2, 8]
def baseStart_1340406 : Nat := 118140960795 + 1340406 * 2 ^ 59
def prefixEnd_1340406 : Nat := 4983230072969 + 3 ^ 40 * 1340406 * 2
def baseEnd_1340406 : Nat := 25491575932243995891133

theorem tailTrace_1340406 : CollatzResearch.WordTrace tailWord_1340406 prefixEnd_1340406 25491575932243995891133 := by
  unfold tailWord_1340406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055538948871591247775567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32592415454630306642939381 3055538948871591247775567)
  ·
    refine ⟨4583308423307386871663351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3055538948871591247775567 4583308423307386871663351)
    ·
      refine ⟨6874962634961080307495027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583308423307386871663351 6874962634961080307495027)
      ·
        refine ⟨10312443952441620461242541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6874962634961080307495027 10312443952441620461242541)
        ·
          refine ⟨3867166482165607672965953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10312443952441620461242541 3867166482165607672965953)
          ·
            refine ⟨2900374861624205754724465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3867166482165607672965953 2900374861624205754724465)
            ·
              refine ⟨2175281146218154316043349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900374861624205754724465 2175281146218154316043349)
              ·
                refine ⟨25491575932243995891133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2175281146218154316043349 25491575932243995891133)
                ·
                  rfl

theorem cell23_1340406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_1340406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340406 prefixEnd_1340406 := by exact prefixLift 1340406
  have htrace : WordTrace (prefixWord ++ tailWord_1340406) baseStart_1340406 baseEnd_1340406 := by
    simpa [prefixWord, tailWord_1340406, baseEnd_1340406] using wordTrace_append hprefix tailTrace_1340406
  have hstable : (prefixWord ++ tailWord_1340406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340406).length < 2 ^ (prefixWord ++ tailWord_1340406).sum := by decide
  have hdescent : baseEnd_1340406 < baseStart_1340406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340434 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1340434 : Nat := 118140960795 + 1340434 * 2 ^ 59
def prefixEnd_1340434 : Nat := 4983230072969 + 3 ^ 40 * 1340434 * 2
def baseEnd_1340434 : Nat := 688286927628913779510463

theorem tailTrace_1340434 : CollatzResearch.WordTrace tailWord_1340434 prefixEnd_1340434 688286927628913779510463 := by
  unfold tailWord_1340434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222411106461005186607089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32593096283896013830952237 12222411106461005186607089)
  ·
    refine ⟨9166808329845753889955317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12222411106461005186607089 9166808329845753889955317)
    ·
      refine ⟨859388280923039427183311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9166808329845753889955317 859388280923039427183311)
      ·
        refine ⟨1289082421384559140774967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859388280923039427183311 1289082421384559140774967)
        ·
          refine ⟨1933623632076838711162451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289082421384559140774967 1933623632076838711162451)
          ·
            refine ⟨2900435448115258066743677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933623632076838711162451 2900435448115258066743677)
            ·
              refine ⟨1087663293043221775028879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2900435448115258066743677 1087663293043221775028879)
              ·
                refine ⟨1631494939564832662543319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087663293043221775028879 1631494939564832662543319)
                ·
                  refine ⟨2447242409347248993814979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631494939564832662543319 2447242409347248993814979)
                  ·
                    refine ⟨3670863614020873490722469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447242409347248993814979 3670863614020873490722469)
                    ·
                      refine ⟨688286927628913779510463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3670863614020873490722469 688286927628913779510463)
                      ·
                        rfl

theorem cell23_1340434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1340434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340434 prefixEnd_1340434 := by exact prefixLift 1340434
  have htrace : WordTrace (prefixWord ++ tailWord_1340434) baseStart_1340434 baseEnd_1340434 := by
    simpa [prefixWord, tailWord_1340434, baseEnd_1340434] using wordTrace_append hprefix tailTrace_1340434
  have hstable : (prefixWord ++ tailWord_1340434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340434).length < 2 ^ (prefixWord ++ tailWord_1340434).sum := by decide
  have hdescent : baseEnd_1340434 < baseStart_1340434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340450 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1340450 : Nat := 118140960795 + 1340450 * 2 ^ 59
def prefixEnd_1340450 : Nat := 4983230072969 + 3 ^ 40 * 1340450 * 2
def baseEnd_1340450 : Nat := 688295143319385716910389

theorem tailTrace_1340450 : CollatzResearch.WordTrace tailWord_1340450 prefixEnd_1340450 688295143319385716910389 := by
  unfold tailWord_1340450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222556998446513869752701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32593485329190703652673869 12222556998446513869752701)
  ·
    refine ⟨4583458874417442701157263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12222556998446513869752701 4583458874417442701157263)
    ·
      refine ⟨6875188311626164051735895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583458874417442701157263 6875188311626164051735895)
      ·
        refine ⟨10312782467439246077603843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6875188311626164051735895 10312782467439246077603843)
        ·
          refine ⟨15469173701158869116405765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10312782467439246077603843 15469173701158869116405765)
          ·
            refine ⟨2900470068967287959326081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15469173701158869116405765 2900470068967287959326081)
            ·
              refine ⟨2175352551725465969494561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900470068967287959326081 2175352551725465969494561)
              ·
                refine ⟨1631514413794099477120921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2175352551725465969494561 1631514413794099477120921)
                ·
                  refine ⟨1223635810345574607840691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1631514413794099477120921 1223635810345574607840691)
                  ·
                    refine ⟨1835453715518361911761037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1223635810345574607840691 1835453715518361911761037)
                    ·
                      refine ⟨688295143319385716910389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1835453715518361911761037 688295143319385716910389)
                      ·
                        rfl

theorem cell23_1340450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1340450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340450 prefixEnd_1340450 := by exact prefixLift 1340450
  have htrace : WordTrace (prefixWord ++ tailWord_1340450) baseStart_1340450 baseEnd_1340450 := by
    simpa [prefixWord, tailWord_1340450, baseEnd_1340450] using wordTrace_append hprefix tailTrace_1340450
  have hstable : (prefixWord ++ tailWord_1340450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340450).length < 2 ^ (prefixWord ++ tailWord_1340450).sum := by decide
  have hdescent : baseEnd_1340450 < baseStart_1340450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340459 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 3]
def baseStart_1340459 : Nat := 118140960795 + 1340459 * 2 ^ 59
def prefixEnd_1340459 : Nat := 4983230072969 + 3 ^ 40 * 1340459 * 2
def baseEnd_1340459 : Nat := 688299764645276181697847

theorem tailTrace_1340459 : CollatzResearch.WordTrace tailWord_1340459 prefixEnd_1340459 688299764645276181697847 := by
  unfold tailWord_1340459
  simp only [CollatzResearch.WordTrace]
  refine ⟨48890556250753450016088431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32593704167168966677392287 48890556250753450016088431)
  ·
    refine ⟨73335834376130175024132647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48890556250753450016088431 73335834376130175024132647)
    ·
      refine ⟨110003751564195262536198971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73335834376130175024132647 110003751564195262536198971)
      ·
        refine ⟨165005627346292893804298457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110003751564195262536198971 165005627346292893804298457)
        ·
          refine ⟨123754220509719670353223843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165005627346292893804298457 123754220509719670353223843)
          ·
            refine ⟨185631330764579505529835765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123754220509719670353223843 185631330764579505529835765)
            ·
              refine ⟨17402937259179328643422103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185631330764579505529835765 17402937259179328643422103)
              ·
                refine ⟨26104405888768992965133155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17402937259179328643422103 26104405888768992965133155)
                ·
                  refine ⟨39156608833153489447699733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26104405888768992965133155 39156608833153489447699733)
                  ·
                    refine ⟨1835466039054069817860925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39156608833153489447699733 1835466039054069817860925)
                    ·
                      refine ⟨688299764645276181697847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1835466039054069817860925 688299764645276181697847)
                      ·
                        rfl

theorem cell23_1340459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 3].length) (baseStart_1340459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340459 prefixEnd_1340459 := by exact prefixLift 1340459
  have htrace : WordTrace (prefixWord ++ tailWord_1340459) baseStart_1340459 baseEnd_1340459 := by
    simpa [prefixWord, tailWord_1340459, baseEnd_1340459] using wordTrace_append hprefix tailTrace_1340459
  have hstable : (prefixWord ++ tailWord_1340459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340459).length < 2 ^ (prefixWord ++ tailWord_1340459).sum := by decide
  have hdescent : baseEnd_1340459 < baseStart_1340459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340473 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1340473 : Nat := 118140960795 + 1340473 * 2 ^ 59
def prefixEnd_1340473 : Nat := 4983230072969 + 3 ^ 40 * 1340473 * 2
def baseEnd_1340473 : Nat := 688306953374439126922783

theorem tailTrace_1340473 : CollatzResearch.WordTrace tailWord_1340473 prefixEnd_1340473 688306953374439126922783 := by
  unfold tailWord_1340473
  simp only [CollatzResearch.WordTrace]
  refine ⟨48891066872702730407098073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32594044581801820271398715 48891066872702730407098073)
  ·
    refine ⟨36668300154527047805323555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48891066872702730407098073 36668300154527047805323555)
    ·
      refine ⟨55002450231790571707985333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36668300154527047805323555 55002450231790571707985333)
      ·
        refine ⟨5156479709230366097623625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55002450231790571707985333 5156479709230366097623625)
        ·
          refine ⟨3867359781922774573217719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5156479709230366097623625 3867359781922774573217719)
          ·
            refine ⟨5801039672884161859826579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3867359781922774573217719 5801039672884161859826579)
            ·
              refine ⟨8701559509326242789739869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801039672884161859826579 8701559509326242789739869)
              ·
                refine ⟨3263084815997341046152451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8701559509326242789739869 3263084815997341046152451)
                ·
                  refine ⟨4894627223996011569228677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263084815997341046152451 4894627223996011569228677)
                  ·
                    refine ⟨917742604499252169230377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4894627223996011569228677 917742604499252169230377)
                    ·
                      refine ⟨688306953374439126922783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917742604499252169230377 688306953374439126922783)
                      ·
                        rfl

theorem cell23_1340473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1340473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340473 prefixEnd_1340473 := by exact prefixLift 1340473
  have htrace : WordTrace (prefixWord ++ tailWord_1340473) baseStart_1340473 baseEnd_1340473 := by
    simpa [prefixWord, tailWord_1340473, baseEnd_1340473] using wordTrace_append hprefix tailTrace_1340473
  have hstable : (prefixWord ++ tailWord_1340473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340473).length < 2 ^ (prefixWord ++ tailWord_1340473).sum := by decide
  have hdescent : baseEnd_1340473 < baseStart_1340473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340526 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1340526 : Nat := 118140960795 + 1340526 * 2 ^ 59
def prefixEnd_1340526 : Nat := 4983230072969 + 3 ^ 40 * 1340526 * 2
def baseEnd_1340526 : Nat := 229444722616375806520013

theorem tailTrace_1340526 : CollatzResearch.WordTrace tailWord_1340526 prefixEnd_1340526 229444722616375806520013 := by
  unfold tailWord_1340526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6111624992688840057347179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32595333294340480305851621 6111624992688840057347179)
  ·
    refine ⟨9167437489033260086020769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6111624992688840057347179 9167437489033260086020769)
    ·
      refine ⟨6875578116774945064515577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9167437489033260086020769 6875578116774945064515577)
      ·
        refine ⟨5156683587581208798386683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6875578116774945064515577 5156683587581208798386683)
        ·
          refine ⟨7735025381371813197580025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5156683587581208798386683 7735025381371813197580025)
          ·
            refine ⟨5801269036028859898185019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7735025381371813197580025 5801269036028859898185019)
            ·
              refine ⟨8701903554043289847277529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801269036028859898185019 8701903554043289847277529)
              ·
                refine ⟨6526427665532467385458147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8701903554043289847277529 6526427665532467385458147)
                ·
                  refine ⟨9789641498298701078187221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6526427665532467385458147 9789641498298701078187221)
                  ·
                    refine ⟨229444722616375806520013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9789641498298701078187221 229444722616375806520013)
                    ·
                      rfl

theorem cell23_1340526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1340526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340526 prefixEnd_1340526 := by exact prefixLift 1340526
  have htrace : WordTrace (prefixWord ++ tailWord_1340526) baseStart_1340526 baseEnd_1340526 := by
    simpa [prefixWord, tailWord_1340526, baseEnd_1340526] using wordTrace_append hprefix tailTrace_1340526
  have hstable : (prefixWord ++ tailWord_1340526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340526).length < 2 ^ (prefixWord ++ tailWord_1340526).sum := by decide
  have hdescent : baseEnd_1340526 < baseStart_1340526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340556 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_1340556 : Nat := 118140960795 + 1340556 * 2 ^ 59
def prefixEnd_1340556 : Nat := 4983230072969 + 3 ^ 40 * 1340556 * 2
def baseEnd_1340556 : Nat := 229449857422920767394967

theorem tailTrace_1340556 : CollatzResearch.WordTrace tailWord_1340556 prefixEnd_1340556 229449857422920767394967 := by
  unfold tailWord_1340556
  simp only [CollatzResearch.WordTrace]
  refine ⟨24447047065701017791184761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32596062754268023721579681 24447047065701017791184761)
  ·
    refine ⟨18335285299275763343388571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24447047065701017791184761 18335285299275763343388571)
    ·
      refine ⟨27502927948913645015082857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18335285299275763343388571 27502927948913645015082857)
      ·
        refine ⟨20627195961685233761312143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27502927948913645015082857 20627195961685233761312143)
        ·
          refine ⟨30940793942527850641968215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20627195961685233761312143 30940793942527850641968215)
          ·
            refine ⟨46411190913791775962952323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30940793942527850641968215 46411190913791775962952323)
            ·
              refine ⟨69616786370687663944428485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46411190913791775962952323 69616786370687663944428485)
              ·
                refine ⟨13053147444503936989580341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69616786370687663944428485 13053147444503936989580341)
                ·
                  refine ⟨1223732572922244092773157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13053147444503936989580341 1223732572922244092773157)
                  ·
                    refine ⟨229449857422920767394967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1223732572922244092773157 229449857422920767394967)
                    ·
                      rfl

theorem cell23_1340556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_1340556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340556 prefixEnd_1340556 := by exact prefixLift 1340556
  have htrace : WordTrace (prefixWord ++ tailWord_1340556) baseStart_1340556 baseEnd_1340556 := by
    simpa [prefixWord, tailWord_1340556, baseEnd_1340556] using wordTrace_append hprefix tailTrace_1340556
  have hstable : (prefixWord ++ tailWord_1340556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340556).length < 2 ^ (prefixWord ++ tailWord_1340556).sum := by decide
  have hdescent : baseEnd_1340556 < baseStart_1340556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340559 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_1340559 : Nat := 118140960795 + 1340559 * 2 ^ 59
def prefixEnd_1340559 : Nat := 4983230072969 + 3 ^ 40 * 1340559 * 2
def baseEnd_1340559 : Nat := 688351112710725790447387

theorem tailTrace_1340559 : CollatzResearch.WordTrace tailWord_1340559 prefixEnd_1340559 688351112710725790447387 := by
  unfold tailWord_1340559
  simp only [CollatzResearch.WordTrace]
  refine ⟨48894203550391167094728731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32596135700260778063152487 48894203550391167094728731)
  ·
    refine ⟨73341305325586750642093097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48894203550391167094728731 73341305325586750642093097)
    ·
      refine ⟨55005978994190062981569823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73341305325586750642093097 55005978994190062981569823)
      ·
        refine ⟨82508968491285094472354735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55005978994190062981569823 82508968491285094472354735)
        ·
          refine ⟨123763452736927641708532103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82508968491285094472354735 123763452736927641708532103)
          ·
            refine ⟨185645179105391462562798155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123763452736927641708532103 185645179105391462562798155)
            ·
              refine ⟨278467768658087193844197233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185645179105391462562798155 278467768658087193844197233)
              ·
                refine ⟨208850826493565395383147925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278467768658087193844197233 208850826493565395383147925)
                ·
                  refine ⟨9789882491885877908585059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208850826493565395383147925 9789882491885877908585059)
                  ·
                    refine ⟨14684823737828816862877589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9789882491885877908585059 14684823737828816862877589)
                    ·
                      refine ⟨688351112710725790447387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14684823737828816862877589 688351112710725790447387)
                      ·
                        rfl

theorem cell23_1340559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_1340559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340559 prefixEnd_1340559 := by exact prefixLift 1340559
  have htrace : WordTrace (prefixWord ++ tailWord_1340559) baseStart_1340559 baseEnd_1340559 := by
    simpa [prefixWord, tailWord_1340559, baseEnd_1340559] using wordTrace_append hprefix tailTrace_1340559
  have hstable : (prefixWord ++ tailWord_1340559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340559).length < 2 ^ (prefixWord ++ tailWord_1340559).sum := by decide
  have hdescent : baseEnd_1340559 < baseStart_1340559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340623 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 4, 3, 2]
def baseStart_1340623 : Nat := 118140960795 + 1340623 * 2 ^ 59
def prefixEnd_1340623 : Nat := 4983230072969 + 3 ^ 40 * 1340623 * 2
def baseEnd_1340623 : Nat := 688383975472613540047093

theorem tailTrace_1340623 : CollatzResearch.WordTrace tailWord_1340623 prefixEnd_1340623 688383975472613540047093 := by
  unfold tailWord_1340623
  simp only [CollatzResearch.WordTrace]
  refine ⟨48896537822159306025058523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32597691881439537350039015 48896537822159306025058523)
  ·
    refine ⟨73344806733238959037587785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48896537822159306025058523 73344806733238959037587785)
    ·
      refine ⟨55008605049929219278190839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73344806733238959037587785 55008605049929219278190839)
      ·
        refine ⟨82512907574893828917286259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55008605049929219278190839 82512907574893828917286259)
        ·
          refine ⟨123769361362340743375929389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82512907574893828917286259 123769361362340743375929389)
          ·
            refine ⟨46413510510877778765973521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123769361362340743375929389 46413510510877778765973521)
            ·
              refine ⟨34810132883158334074480141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46413510510877778765973521 34810132883158334074480141)
              ·
                refine ⟨13053799831184375277930053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34810132883158334074480141 13053799831184375277930053)
                ·
                  refine ⟨2447587468347070364611885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13053799831184375277930053 2447587468347070364611885)
                  ·
                    refine ⟨917845300630151386729457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2447587468347070364611885 917845300630151386729457)
                    ·
                      refine ⟨688383975472613540047093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917845300630151386729457 688383975472613540047093)
                      ·
                        rfl

theorem cell23_1340623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3, 2].length) (baseStart_1340623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340623 prefixEnd_1340623 := by exact prefixLift 1340623
  have htrace : WordTrace (prefixWord ++ tailWord_1340623) baseStart_1340623 baseEnd_1340623 := by
    simpa [prefixWord, tailWord_1340623, baseEnd_1340623] using wordTrace_append hprefix tailTrace_1340623
  have hstable : (prefixWord ++ tailWord_1340623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340623).length < 2 ^ (prefixWord ++ tailWord_1340623).sum := by decide
  have hdescent : baseEnd_1340623 < baseStart_1340623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340647 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1340647 : Nat := 118140960795 + 1340647 * 2 ^ 59
def prefixEnd_1340647 : Nat := 4983230072969 + 3 ^ 40 * 1340647 * 2
def baseEnd_1340647 : Nat := 688396299008321446146983

theorem tailTrace_1340647 : CollatzResearch.WordTrace tailWord_1340647 prefixEnd_1340647 688396299008321446146983 := by
  unfold tailWord_1340647
  simp only [CollatzResearch.WordTrace]
  refine ⟨48897413174072358123932195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32598275449381572082621463 48897413174072358123932195)
  ·
    refine ⟨73346119761108537185898293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48897413174072358123932195 73346119761108537185898293)
    ·
      refine ⟨6876198727603925361177965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73346119761108537185898293 6876198727603925361177965)
      ·
        refine ⟨2578574522851472010441737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6876198727603925361177965 2578574522851472010441737)
        ·
          refine ⟨1933930892138604007831303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2578574522851472010441737 1933930892138604007831303)
          ·
            refine ⟨2900896338207906011746955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933930892138604007831303 2900896338207906011746955)
            ·
              refine ⟨4351344507311859017620433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900896338207906011746955 4351344507311859017620433)
              ·
                refine ⟨3263508380483894263215325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351344507311859017620433 3263508380483894263215325)
                ·
                  refine ⟨1223815642681460348705747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3263508380483894263215325 1223815642681460348705747)
                  ·
                    refine ⟨1835723464022190523058621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1223815642681460348705747 1835723464022190523058621)
                    ·
                      refine ⟨688396299008321446146983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1835723464022190523058621 688396299008321446146983)
                      ·
                        rfl

theorem cell23_1340647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1340647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340647 prefixEnd_1340647 := by exact prefixLift 1340647
  have htrace : WordTrace (prefixWord ++ tailWord_1340647) baseStart_1340647 baseEnd_1340647 := by
    simpa [prefixWord, tailWord_1340647, baseEnd_1340647] using wordTrace_append hprefix tailTrace_1340647
  have hstable : (prefixWord ++ tailWord_1340647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340647).length < 2 ^ (prefixWord ++ tailWord_1340647).sum := by decide
  have hdescent : baseEnd_1340647 < baseStart_1340647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340680 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1340680 : Nat := 118140960795 + 1340680 * 2 ^ 59
def prefixEnd_1340680 : Nat := 4983230072969 + 3 ^ 40 * 1340680 * 2
def baseEnd_1340680 : Nat := 229471081289973272344777

theorem tailTrace_1340680 : CollatzResearch.WordTrace tailWord_1340680 prefixEnd_1340680 229471081289973272344777 := by
  unfold tailWord_1340680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24449308391476402379941747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32599077855301869839922329 24449308391476402379941747)
  ·
    refine ⟨36673962587214603569912621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24449308391476402379941747 36673962587214603569912621)
    ·
      refine ⟨13752735970205476338717233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36673962587214603569912621 13752735970205476338717233)
      ·
        refine ⟨10314551977654107254037925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13752735970205476338717233 10314551977654107254037925)
        ·
          refine ⟨1933978495810145110132111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10314551977654107254037925 1933978495810145110132111)
          ·
            refine ⟨2900967743715217665198167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933978495810145110132111 2900967743715217665198167)
            ·
              refine ⟨4351451615572826497797251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900967743715217665198167 4351451615572826497797251)
              ·
                refine ⟨6527177423359239746695877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351451615572826497797251 6527177423359239746695877)
                ·
                  refine ⟨1223845766879857452505477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6527177423359239746695877 1223845766879857452505477)
                  ·
                    refine ⟨229471081289973272344777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1223845766879857452505477 229471081289973272344777)
                    ·
                      rfl

theorem cell23_1340680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1340680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340680 prefixEnd_1340680 := by exact prefixLift 1340680
  have htrace : WordTrace (prefixWord ++ tailWord_1340680) baseStart_1340680 baseEnd_1340680 := by
    simpa [prefixWord, tailWord_1340680, baseEnd_1340680] using wordTrace_append hprefix tailTrace_1340680
  have hstable : (prefixWord ++ tailWord_1340680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340680).length < 2 ^ (prefixWord ++ tailWord_1340680).sum := by decide
  have hdescent : baseEnd_1340680 < baseStart_1340680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340721 : List Nat := [1, 2, 2, 3, 3, 3, 1, 3, 1, 2, 2]
def baseStart_1340721 : Nat := 118140960795 + 1340721 * 2 ^ 59
def prefixEnd_1340721 : Nat := 4983230072969 + 3 ^ 40 * 1340721 * 2
def baseEnd_1340721 : Nat := 688434296576754156621643

theorem tailTrace_1340721 : CollatzResearch.WordTrace tailWord_1340721 prefixEnd_1340721 688434296576754156621643 := by
  unfold tailWord_1340721
  simp only [CollatzResearch.WordTrace]
  refine ⟨48900112175804268762126017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32600074783869512508084011 48900112175804268762126017)
  ·
    refine ⟨36675084131853201571594513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48900112175804268762126017 36675084131853201571594513)
    ·
      refine ⟨27506313098889901178695885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36675084131853201571594513 27506313098889901178695885)
      ·
        refine ⟨10314867412083712942010957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27506313098889901178695885 10314867412083712942010957)
        ·
          refine ⟨3868075279531392353254109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10314867412083712942010957 3868075279531392353254109)
          ·
            refine ⟨1450528229824272132470291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3868075279531392353254109 1450528229824272132470291)
            ·
              refine ⟨2175792344736408198705437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450528229824272132470291 2175792344736408198705437)
              ·
                refine ⟨815922129276153074514539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2175792344736408198705437 815922129276153074514539)
                ·
                  refine ⟨1223883193914229611771809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815922129276153074514539 1223883193914229611771809)
                  ·
                    refine ⟨917912395435672208828857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1223883193914229611771809 917912395435672208828857)
                    ·
                      refine ⟨688434296576754156621643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917912395435672208828857 688434296576754156621643)
                      ·
                        rfl

theorem cell23_1340721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_1340721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340721 prefixEnd_1340721 := by exact prefixLift 1340721
  have htrace : WordTrace (prefixWord ++ tailWord_1340721) baseStart_1340721 baseEnd_1340721 := by
    simpa [prefixWord, tailWord_1340721, baseEnd_1340721] using wordTrace_append hprefix tailTrace_1340721
  have hstable : (prefixWord ++ tailWord_1340721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340721).length < 2 ^ (prefixWord ++ tailWord_1340721).sum := by decide
  have hdescent : baseEnd_1340721 < baseStart_1340721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340737 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1340737 : Nat := 118140960795 + 1340737 * 2 ^ 59
def prefixEnd_1340737 : Nat := 4983230072969 + 3 ^ 40 * 1340737 * 2
def baseEnd_1340737 : Nat := 688442512267226094021569

theorem tailTrace_1340737 : CollatzResearch.WordTrace tailWord_1340737 prefixEnd_1340737 688442512267226094021569 := by
  unfold tailWord_1340737
  simp only [CollatzResearch.WordTrace]
  refine ⟨48900695743746303494708465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32600463829164202329805643 48900695743746303494708465)
  ·
    refine ⟨36675521807809727621031349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48900695743746303494708465 36675521807809727621031349)
    ·
      refine ⟨3438330169482161964471689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36675521807809727621031349 3438330169482161964471689)
      ·
        refine ⟨2578747627111621473353767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3438330169482161964471689 2578747627111621473353767)
        ·
          refine ⟨3868121440667432210030651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578747627111621473353767 3868121440667432210030651)
          ·
            refine ⟨5802182161001148315045977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868121440667432210030651 5802182161001148315045977)
            ·
              refine ⟨4351636620750861236284483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5802182161001148315045977 4351636620750861236284483)
              ·
                refine ⟨6527454931126291854426725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351636620750861236284483 6527454931126291854426725)
                ·
                  refine ⟨1223897799586179722705011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6527454931126291854426725 1223897799586179722705011)
                  ·
                    refine ⟨1835846699379269584057517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1223897799586179722705011 1835846699379269584057517)
                    ·
                      refine ⟨688442512267226094021569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1835846699379269584057517 688442512267226094021569)
                      ·
                        rfl

theorem cell23_1340737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1340737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340737 prefixEnd_1340737 := by exact prefixLift 1340737
  have htrace : WordTrace (prefixWord ++ tailWord_1340737) baseStart_1340737 baseEnd_1340737 := by
    simpa [prefixWord, tailWord_1340737, baseEnd_1340737] using wordTrace_append hprefix tailTrace_1340737
  have hstable : (prefixWord ++ tailWord_1340737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340737).length < 2 ^ (prefixWord ++ tailWord_1340737).sum := by decide
  have hdescent : baseEnd_1340737 < baseStart_1340737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340760 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 1, 4, 2]
def baseStart_1340760 : Nat := 118140960795 + 1340760 * 2 ^ 59
def prefixEnd_1340760 : Nat := 4983230072969 + 3 ^ 40 * 1340760 * 2
def baseEnd_1340760 : Nat := 688454322322279504033963

theorem tailTrace_1340760 : CollatzResearch.WordTrace tailWord_1340760 prefixEnd_1340760 688454322322279504033963 := by
  unfold tailWord_1340760
  simp only [CollatzResearch.WordTrace]
  refine ⟨24450767311331489211397867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32601023081775318948530489 24450767311331489211397867)
  ·
    refine ⟨36676150966997233817096801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24450767311331489211397867 36676150966997233817096801)
    ·
      refine ⟨27507113225247925362822601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36676150966997233817096801 27507113225247925362822601)
      ·
        refine ⟨20630334918935944022116951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27507113225247925362822601 20630334918935944022116951)
        ·
          refine ⟨30945502378403916033175427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20630334918935944022116951 30945502378403916033175427)
          ·
            refine ⟨46418253567605874049763141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30945502378403916033175427 46418253567605874049763141)
            ·
              refine ⟨8703422543926101384330589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46418253567605874049763141 8703422543926101384330589)
              ·
                refine ⟨3263783453972288019123971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8703422543926101384330589 3263783453972288019123971)
                ·
                  refine ⟨4895675180958432028685957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263783453972288019123971 4895675180958432028685957)
                  ·
                    refine ⟨917939096429706005378617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4895675180958432028685957 917939096429706005378617)
                    ·
                      refine ⟨688454322322279504033963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 917939096429706005378617 688454322322279504033963)
                      ·
                        rfl

theorem cell23_1340760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_1340760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340760 prefixEnd_1340760 := by exact prefixLift 1340760
  have htrace : WordTrace (prefixWord ++ tailWord_1340760) baseStart_1340760 baseEnd_1340760 := by
    simpa [prefixWord, tailWord_1340760, baseEnd_1340760] using wordTrace_append hprefix tailTrace_1340760
  have hstable : (prefixWord ++ tailWord_1340760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340760).length < 2 ^ (prefixWord ++ tailWord_1340760).sum := by decide
  have hdescent : baseEnd_1340760 < baseStart_1340760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340958 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1340958 : Nat := 118140960795 + 1340958 * 2 ^ 59
def prefixEnd_1340958 : Nat := 4983230072969 + 3 ^ 40 * 1340958 * 2
def baseEnd_1340958 : Nat := 76506221276874414373117

theorem tailTrace_1340958 : CollatzResearch.WordTrace tailWord_1340958 prefixEnd_1340958 76506221276874414373117 := by
  unfold tailWord_1340958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113594534493207279812941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32605837517297105492335685 6113594534493207279812941)
  ·
    refine ⟨2292597950434952729929853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6113594534493207279812941 2292597950434952729929853)
    ·
      refine ⟨859724231413107273723695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2292597950434952729929853 859724231413107273723695)
      ·
        refine ⟨1289586347119660910585543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859724231413107273723695 1289586347119660910585543)
        ·
          refine ⟨1934379520679491365878315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289586347119660910585543 1934379520679491365878315)
          ·
            refine ⟨2901569281019237048817473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934379520679491365878315 2901569281019237048817473)
            ·
              refine ⟨2176176960764427786613105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2901569281019237048817473 2176176960764427786613105)
              ·
                refine ⟨1632132720573320839959829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176176960764427786613105 1632132720573320839959829)
                ·
                  refine ⟨76506221276874414373117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1632132720573320839959829 76506221276874414373117)
                  ·
                    rfl

theorem cell23_1340958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1340958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340958 prefixEnd_1340958 := by exact prefixLift 1340958
  have htrace : WordTrace (prefixWord ++ tailWord_1340958) baseStart_1340958 baseEnd_1340958 := by
    simpa [prefixWord, tailWord_1340958, baseEnd_1340958] using wordTrace_append hprefix tailTrace_1340958
  have hstable : (prefixWord ++ tailWord_1340958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340958).length < 2 ^ (prefixWord ++ tailWord_1340958).sum := by decide
  have hdescent : baseEnd_1340958 < baseStart_1340958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340963 : List Nat := [1, 1, 1, 4, 16]
def baseStart_1340963 : Nat := 118140960795 + 1340963 * 2 ^ 59
def prefixEnd_1340963 : Nat := 4983230072969 + 3 ^ 40 * 1340963 * 2
def baseEnd_1340963 : Nat := 944524772146971481201

theorem tailTrace_1340963 : CollatzResearch.WordTrace tailWord_1340963 prefixEnd_1340963 944524772146971481201 := by
  unfold tailWord_1340963
  simp only [CollatzResearch.WordTrace]
  refine ⟨48908938640927544092435543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32605959093951696061623695 48908938640927544092435543)
  ·
    refine ⟨73363407961391316138653315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48908938640927544092435543 73363407961391316138653315)
    ·
      refine ⟨110045111942086974207979973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73363407961391316138653315 110045111942086974207979973)
      ·
        refine ⟨20633458489141307663996245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110045111942086974207979973 20633458489141307663996245)
        ·
          refine ⟨944524772146971481201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 20633458489141307663996245 944524772146971481201)
          ·
            rfl

theorem cell23_1340963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 16].length) (baseStart_1340963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340963 prefixEnd_1340963 := by exact prefixLift 1340963
  have htrace : WordTrace (prefixWord ++ tailWord_1340963) baseStart_1340963 baseEnd_1340963 := by
    simpa [prefixWord, tailWord_1340963, baseEnd_1340963] using wordTrace_append hprefix tailTrace_1340963
  have hstable : (prefixWord ++ tailWord_1340963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340963).length < 2 ^ (prefixWord ++ tailWord_1340963).sum := by decide
  have hdescent : baseEnd_1340963 < baseStart_1340963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340968 : List Nat := [2, 1, 5, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1340968 : Nat := 118140960795 + 1340968 * 2 ^ 59
def prefixEnd_1340968 : Nat := 4983230072969 + 3 ^ 40 * 1340968 * 2
def baseEnd_1340968 : Nat := 688561126298414690233007

theorem tailTrace_1340968 : CollatzResearch.WordTrace tailWord_1340968 prefixEnd_1340968 688561126298414690233007 := by
  unfold tailWord_1340968
  simp only [CollatzResearch.WordTrace]
  refine ⟨24454560502954714973183779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32606080670606286630911705 24454560502954714973183779)
  ·
    refine ⟨36681840754432072459775669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24454560502954714973183779 36681840754432072459775669)
    ·
      refine ⟨3438922570728006793103969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36681840754432072459775669 3438922570728006793103969)
      ·
        refine ⟨2579191928046005094827977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3438922570728006793103969 2579191928046005094827977)
        ·
          refine ⟨1934393946034503821120983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2579191928046005094827977 1934393946034503821120983)
          ·
            refine ⟨2901590919051755731681475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934393946034503821120983 2901590919051755731681475)
            ·
              refine ⟨4352386378577633597522213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901590919051755731681475 4352386378577633597522213)
              ·
                refine ⟨816072445983306299535415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4352386378577633597522213 816072445983306299535415)
                ·
                  refine ⟨1224108668974959449303123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816072445983306299535415 1224108668974959449303123)
                  ·
                    refine ⟨1836163003462439173954685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1224108668974959449303123 1836163003462439173954685)
                    ·
                      refine ⟨688561126298414690233007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1836163003462439173954685 688561126298414690233007)
                      ·
                        rfl

theorem cell23_1340968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1340968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1340968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1340968 prefixEnd_1340968 := by exact prefixLift 1340968
  have htrace : WordTrace (prefixWord ++ tailWord_1340968) baseStart_1340968 baseEnd_1340968 := by
    simpa [prefixWord, tailWord_1340968, baseEnd_1340968] using wordTrace_append hprefix tailTrace_1340968
  have hstable : (prefixWord ++ tailWord_1340968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340968).length < 2 ^ (prefixWord ++ tailWord_1340968).sum := by decide
  have hdescent : baseEnd_1340968 < baseStart_1340968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341007 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 3]
def baseStart_1341007 : Nat := 118140960795 + 1341007 * 2 ^ 59
def prefixEnd_1341007 : Nat := 4983230072969 + 3 ^ 40 * 1341007 * 2
def baseEnd_1341007 : Nat := 688581152043940037645327

theorem tailTrace_1341007 : CollatzResearch.WordTrace tailWord_1341007 prefixEnd_1341007 688581152043940037645327 := by
  unfold tailWord_1341007
  simp only [CollatzResearch.WordTrace]
  refine ⟨48910543452768139607037275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32607028968512093071358183 48910543452768139607037275)
  ·
    refine ⟨73365815179152209410555913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48910543452768139607037275 73365815179152209410555913)
    ·
      refine ⟨55024361384364157057916935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73365815179152209410555913 55024361384364157057916935)
      ·
        refine ⟨82536542076546235586875403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55024361384364157057916935 82536542076546235586875403)
        ·
          refine ⟨123804813114819353380313105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82536542076546235586875403 123804813114819353380313105)
          ·
            refine ⟨92853609836114515035234829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123804813114819353380313105 92853609836114515035234829)
            ·
              refine ⟨34820103688542943138213061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92853609836114515035234829 34820103688542943138213061)
              ·
                refine ⟨6528769441601801838414949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34820103688542943138213061 6528769441601801838414949)
                ·
                  refine ⟨1224144270300337844702803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6528769441601801838414949 1224144270300337844702803)
                  ·
                    refine ⟨1836216405450506767054205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1224144270300337844702803 1836216405450506767054205)
                    ·
                      refine ⟨688581152043940037645327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1836216405450506767054205 688581152043940037645327)
                      ·
                        rfl

theorem cell23_1341007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 3].length) (baseStart_1341007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341007 prefixEnd_1341007 := by exact prefixLift 1341007
  have htrace : WordTrace (prefixWord ++ tailWord_1341007) baseStart_1341007 baseEnd_1341007 := by
    simpa [prefixWord, tailWord_1341007, baseEnd_1341007] using wordTrace_append hprefix tailTrace_1341007
  have hstable : (prefixWord ++ tailWord_1341007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341007).length < 2 ^ (prefixWord ++ tailWord_1341007).sum := by decide
  have hdescent : baseEnd_1341007 < baseStart_1341007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341102 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_1341102 : Nat := 118140960795 + 1341102 * 2 ^ 59
def prefixEnd_1341102 : Nat := 4983230072969 + 3 ^ 40 * 1341102 * 2
def baseEnd_1341102 : Nat := 688629932706117165957391

theorem tailTrace_1341102 : CollatzResearch.WordTrace tailWord_1341102 prefixEnd_1341102 688629932706117165957391 := by
  unfold tailWord_1341102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6114251048427996353968195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32609338924949313887830373 6114251048427996353968195)
  ·
    refine ⟨9171376572641994530952293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6114251048427996353968195 9171376572641994530952293)
    ·
      refine ⟨1719633107370373974553555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9171376572641994530952293 1719633107370373974553555)
      ·
        refine ⟨2579449661055560961830333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719633107370373974553555 2579449661055560961830333)
        ·
          refine ⟨967293622895835360686375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2579449661055560961830333 967293622895835360686375)
          ·
            refine ⟨1450940434343753041029563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967293622895835360686375 1450940434343753041029563)
            ·
              refine ⟨2176410651515629561544345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450940434343753041029563 2176410651515629561544345)
              ·
                refine ⟨1632307988636722171158259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176410651515629561544345 1632307988636722171158259)
                ·
                  refine ⟨2448461982955083256737389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632307988636722171158259 2448461982955083256737389)
                  ·
                    refine ⟨918173243608156221276521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448461982955083256737389 918173243608156221276521)
                    ·
                      refine ⟨688629932706117165957391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918173243608156221276521 688629932706117165957391)
                      ·
                        rfl

theorem cell23_1341102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_1341102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341102 prefixEnd_1341102 := by exact prefixLift 1341102
  have htrace : WordTrace (prefixWord ++ tailWord_1341102) baseStart_1341102 baseEnd_1341102 := by
    simpa [prefixWord, tailWord_1341102, baseEnd_1341102] using wordTrace_append hprefix tailTrace_1341102
  have hstable : (prefixWord ++ tailWord_1341102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341102).length < 2 ^ (prefixWord ++ tailWord_1341102).sum := by decide
  have hdescent : baseEnd_1341102 < baseStart_1341102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341138 : List Nat := [3, 2, 2, 2, 2, 3, 2, 2, 5]
def baseStart_1341138 : Nat := 118140960795 + 1341138 * 2 ^ 59
def prefixEnd_1341138 : Nat := 4983230072969 + 3 ^ 40 * 1341138 * 2
def baseEnd_1341138 : Nat := 76516490889964336123025

theorem tailTrace_1341138 : CollatzResearch.WordTrace tailWord_1341138 prefixEnd_1341138 76516490889964336123025 := by
  unfold tailWord_1341138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228830353823387245014017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32610214276862365986704045 12228830353823387245014017)
  ·
    refine ⟨9171622765367540433760513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12228830353823387245014017 9171622765367540433760513)
    ·
      refine ⟨6878717074025655325320385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9171622765367540433760513 6878717074025655325320385)
      ·
        refine ⟨5159037805519241493990289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6878717074025655325320385 5159037805519241493990289)
        ·
          refine ⟨3869278354139431120492717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5159037805519241493990289 3869278354139431120492717)
          ·
            refine ⟨1450979382802286670184769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3869278354139431120492717 1450979382802286670184769)
            ·
              refine ⟨1088234537101715002638577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450979382802286670184769 1088234537101715002638577)
              ·
                refine ⟨816175902826286251978933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088234537101715002638577 816175902826286251978933)
                ·
                  refine ⟨76516490889964336123025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 816175902826286251978933 76516490889964336123025)
                  ·
                    rfl

theorem cell23_1341138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_1341138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341138 prefixEnd_1341138 := by exact prefixLift 1341138
  have htrace : WordTrace (prefixWord ++ tailWord_1341138) baseStart_1341138 baseEnd_1341138 := by
    simpa [prefixWord, tailWord_1341138, baseEnd_1341138] using wordTrace_append hprefix tailTrace_1341138
  have hstable : (prefixWord ++ tailWord_1341138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341138).length < 2 ^ (prefixWord ++ tailWord_1341138).sum := by decide
  have hdescent : baseEnd_1341138 < baseStart_1341138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341194 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 6]
def baseStart_1341194 : Nat := 118140960795 + 1341194 * 2 ^ 59
def prefixEnd_1341194 : Nat := 4983230072969 + 3 ^ 40 * 1341194 * 2
def baseEnd_1341194 : Nat := 76519685880703422889663

theorem tailTrace_1341194 : CollatzResearch.WordTrace tailWord_1341194 prefixEnd_1341194 76519685880703422889663 := by
  unfold tailWord_1341194
  simp only [CollatzResearch.WordTrace]
  refine ⟨12229340975772667636023659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32611575935393780362729757 12229340975772667636023659)
  ·
    refine ⟨18344011463659001454035489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12229340975772667636023659 18344011463659001454035489)
    ·
      refine ⟨13758008597744251090526617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18344011463659001454035489 13758008597744251090526617)
      ·
        refine ⟨10318506448308188317894963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13758008597744251090526617 10318506448308188317894963)
        ·
          refine ⟨15477759672462282476842445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10318506448308188317894963 15477759672462282476842445)
          ·
            refine ⟨5804159877173355928815917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15477759672462282476842445 5804159877173355928815917)
            ·
              refine ⟨2176559953940008473305969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5804159877173355928815917 2176559953940008473305969)
              ·
                refine ⟨1632419965455006354979477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176559953940008473305969 1632419965455006354979477)
                ·
                  refine ⟨76519685880703422889663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1632419965455006354979477 76519685880703422889663)
                  ·
                    rfl

theorem cell23_1341194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_1341194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341194 prefixEnd_1341194 := by exact prefixLift 1341194
  have htrace : WordTrace (prefixWord ++ tailWord_1341194) baseStart_1341194 baseEnd_1341194 := by
    simpa [prefixWord, tailWord_1341194, baseEnd_1341194] using wordTrace_append hprefix tailTrace_1341194
  have hstable : (prefixWord ++ tailWord_1341194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341194).length < 2 ^ (prefixWord ++ tailWord_1341194).sum := by decide
  have hdescent : baseEnd_1341194 < baseStart_1341194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341221 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 3]
def baseStart_1341221 : Nat := 118140960795 + 1341221 * 2 ^ 59
def prefixEnd_1341221 : Nat := 4983230072969 + 3 ^ 40 * 1341221 * 2
def baseEnd_1341221 : Nat := 688691036904002200369343

theorem tailTrace_1341221 : CollatzResearch.WordTrace tailWord_1341221 prefixEnd_1341221 688691036904002200369343 := by
  unfold tailWord_1341221
  simp only [CollatzResearch.WordTrace]
  refine ⟨48918348673992854155327517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32612232449328569436885011 48918348673992854155327517)
  ·
    refine ⟨18344380752747320308247819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48918348673992854155327517 18344380752747320308247819)
    ·
      refine ⟨27516571129120980462371729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18344380752747320308247819 27516571129120980462371729)
      ·
        refine ⟨20637428346840735346778797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27516571129120980462371729 20637428346840735346778797)
        ·
          refine ⟨7739035630065275755042049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20637428346840735346778797 7739035630065275755042049)
          ·
            refine ⟨5804276722548956816281537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7739035630065275755042049 5804276722548956816281537)
            ·
              refine ⟨4353207541911717612211153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5804276722548956816281537 4353207541911717612211153)
              ·
                refine ⟨3264905656433788209158365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4353207541911717612211153 3264905656433788209158365)
                ·
                  refine ⟨1224339621162670578434387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3264905656433788209158365 1224339621162670578434387)
                  ·
                    refine ⟨1836509431744005867651581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1224339621162670578434387 1836509431744005867651581)
                    ·
                      refine ⟨688691036904002200369343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1836509431744005867651581 688691036904002200369343)
                      ·
                        rfl

theorem cell23_1341221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_1341221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341221 prefixEnd_1341221 := by exact prefixLift 1341221
  have htrace : WordTrace (prefixWord ++ tailWord_1341221) baseStart_1341221 baseEnd_1341221 := by
    simpa [prefixWord, tailWord_1341221, baseEnd_1341221] using wordTrace_append hprefix tailTrace_1341221
  have hstable : (prefixWord ++ tailWord_1341221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341221).length < 2 ^ (prefixWord ++ tailWord_1341221).sum := by decide
  have hdescent : baseEnd_1341221 < baseStart_1341221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341257 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_1341257 : Nat := 118140960795 + 1341257 * 2 ^ 59
def prefixEnd_1341257 : Nat := 4983230072969 + 3 ^ 40 * 1341257 * 2
def baseEnd_1341257 : Nat := 688709522207564059519177

theorem tailTrace_1341257 : CollatzResearch.WordTrace tailWord_1341257 prefixEnd_1341257 688709522207564059519177 := by
  unfold tailWord_1341257
  simp only [CollatzResearch.WordTrace]
  refine ⟨48919661701862432303638025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32613107801241621535758683 48919661701862432303638025)
  ·
    refine ⟨36689746276396824227728519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48919661701862432303638025 36689746276396824227728519)
    ·
      refine ⟨55034619414595236341592779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36689746276396824227728519 55034619414595236341592779)
      ·
        refine ⟨82551929121892854512389169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55034619414595236341592779 82551929121892854512389169)
        ·
          refine ⟨61913946841419640884291877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82551929121892854512389169 61913946841419640884291877)
          ·
            refine ⟨11608865032766182665804727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61913946841419640884291877 11608865032766182665804727)
            ·
              refine ⟨17413297549149273998707091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11608865032766182665804727 17413297549149273998707091)
              ·
                refine ⟨26119946323723910998060637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17413297549149273998707091 26119946323723910998060637)
                ·
                  refine ⟨9794979871396466624272739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26119946323723910998060637 9794979871396466624272739)
                  ·
                    refine ⟨14692469807094699936409109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9794979871396466624272739 14692469807094699936409109)
                    ·
                      refine ⟨688709522207564059519177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14692469807094699936409109 688709522207564059519177)
                      ·
                        rfl

theorem cell23_1341257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_1341257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341257 prefixEnd_1341257 := by exact prefixLift 1341257
  have htrace : WordTrace (prefixWord ++ tailWord_1341257) baseStart_1341257 baseEnd_1341257 := by
    simpa [prefixWord, tailWord_1341257, baseEnd_1341257] using wordTrace_append hprefix tailTrace_1341257
  have hstable : (prefixWord ++ tailWord_1341257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341257).length < 2 ^ (prefixWord ++ tailWord_1341257).sum := by decide
  have hdescent : baseEnd_1341257 < baseStart_1341257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341264 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3]
def baseStart_1341264 : Nat := 118140960795 + 1341264 * 2 ^ 59
def prefixEnd_1341264 : Nat := 4983230072969 + 3 ^ 40 * 1341264 * 2
def baseEnd_1341264 : Nat := 688713116572145532131645

theorem tailTrace_1341264 : CollatzResearch.WordTrace tailWord_1341264 prefixEnd_1341264 688713116572145532131645 := by
  unfold tailWord_1341264
  simp only [CollatzResearch.WordTrace]
  refine ⟨24459958506418536249571423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32613278008558048332761897 24459958506418536249571423)
  ·
    refine ⟨36689937759627804374357135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24459958506418536249571423 36689937759627804374357135)
    ·
      refine ⟨55034906639441706561535703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36689937759627804374357135 55034906639441706561535703)
      ·
        refine ⟨82552359959162559842303555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55034906639441706561535703 82552359959162559842303555)
        ·
          refine ⟨123828539938743839763455333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82552359959162559842303555 123828539938743839763455333)
          ·
            refine ⟨23217851238514469955647875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123828539938743839763455333 23217851238514469955647875)
            ·
              refine ⟨34826776857771704933471813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23217851238514469955647875 34826776857771704933471813)
              ·
                refine ⟨6530020660832194675025965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34826776857771704933471813 6530020660832194675025965)
                ·
                  refine ⟨2448757747812073003134737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6530020660832194675025965 2448757747812073003134737)
                  ·
                    refine ⟨1836568310859054752351053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2448757747812073003134737 1836568310859054752351053)
                    ·
                      refine ⟨688713116572145532131645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1836568310859054752351053 688713116572145532131645)
                      ·
                        rfl

theorem cell23_1341264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_1341264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341264 prefixEnd_1341264 := by exact prefixLift 1341264
  have htrace : WordTrace (prefixWord ++ tailWord_1341264) baseStart_1341264 baseEnd_1341264 := by
    simpa [prefixWord, tailWord_1341264, baseEnd_1341264] using wordTrace_append hprefix tailTrace_1341264
  have hstable : (prefixWord ++ tailWord_1341264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341264).length < 2 ^ (prefixWord ++ tailWord_1341264).sum := by decide
  have hdescent : baseEnd_1341264 < baseStart_1341264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341274 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1341274 : Nat := 118140960795 + 1341274 * 2 ^ 59
def prefixEnd_1341274 : Nat := 4983230072969 + 3 ^ 40 * 1341274 * 2
def baseEnd_1341274 : Nat := 688718251378690493006599

theorem tailTrace_1341274 : CollatzResearch.WordTrace tailWord_1341274 prefixEnd_1341274 688718251378690493006599 := by
  unfold tailWord_1341274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12230070435700211051751719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32613521161867229471337917 12230070435700211051751719)
  ·
    refine ⟨18345105653550316577627579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12230070435700211051751719 18345105653550316577627579)
    ·
      refine ⟨27517658480325474866441369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18345105653550316577627579 27517658480325474866441369)
      ·
        refine ⟨20638243860244106149831027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27517658480325474866441369 20638243860244106149831027)
        ·
          refine ⟨30957365790366159224746541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20638243860244106149831027 30957365790366159224746541)
          ·
            refine ⟨11609012171387309709279953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30957365790366159224746541 11609012171387309709279953)
            ·
              refine ⟨8706759128540482281959965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11609012171387309709279953 8706759128540482281959965)
              ·
                refine ⟨3265034673202680855734987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8706759128540482281959965 3265034673202680855734987)
                ·
                  refine ⟨4897552009804021283602481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265034673202680855734987 4897552009804021283602481)
                  ·
                    refine ⟨3673164007353015962701861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4897552009804021283602481 3673164007353015962701861)
                    ·
                      refine ⟨688718251378690493006599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3673164007353015962701861 688718251378690493006599)
                      ·
                        rfl

theorem cell23_1341274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1341274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341274 prefixEnd_1341274 := by exact prefixLift 1341274
  have htrace : WordTrace (prefixWord ++ tailWord_1341274) baseStart_1341274 baseEnd_1341274 := by
    simpa [prefixWord, tailWord_1341274, baseEnd_1341274] using wordTrace_append hprefix tailTrace_1341274
  have hstable : (prefixWord ++ tailWord_1341274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341274).length < 2 ^ (prefixWord ++ tailWord_1341274).sum := by decide
  have hdescent : baseEnd_1341274 < baseStart_1341274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341321 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 5, 3, 2]
def baseStart_1341321 : Nat := 118140960795 + 1341321 * 2 ^ 59
def prefixEnd_1341321 : Nat := 4983230072969 + 3 ^ 40 * 1341321 * 2
def baseEnd_1341321 : Nat := 688742384969451809118883

theorem tailTrace_1341321 : CollatzResearch.WordTrace tailWord_1341321 prefixEnd_1341321 688742384969451809118883 := by
  unfold tailWord_1341321
  simp only [CollatzResearch.WordTrace]
  refine ⟨48921995973630571233967817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32614663982420380822645211 48921995973630571233967817)
  ·
    refine ⟨36691496980222928425475863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48921995973630571233967817 36691496980222928425475863)
    ·
      refine ⟨55037245470334392638213795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36691496980222928425475863 55037245470334392638213795)
      ·
        refine ⟨82555868205501588957320693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55037245470334392638213795 82555868205501588957320693)
        ·
          refine ⟨7739612644265773964748815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82555868205501588957320693 7739612644265773964748815)
          ·
            refine ⟨11609418966398660947123223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7739612644265773964748815 11609418966398660947123223)
            ·
              refine ⟨17414128449597991420684835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11609418966398660947123223 17414128449597991420684835)
              ·
                refine ⟨26121192674396987131027253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17414128449597991420684835 26121192674396987131027253)
                ·
                  refine ⟨2448861813224717543533805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26121192674396987131027253 2448861813224717543533805)
                  ·
                    refine ⟨918323179959269078825177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448861813224717543533805 918323179959269078825177)
                    ·
                      refine ⟨688742384969451809118883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918323179959269078825177 688742384969451809118883)
                      ·
                        rfl

theorem cell23_1341321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 3, 2].length) (baseStart_1341321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341321 prefixEnd_1341321 := by exact prefixLift 1341321
  have htrace : WordTrace (prefixWord ++ tailWord_1341321) baseStart_1341321 baseEnd_1341321 := by
    simpa [prefixWord, tailWord_1341321, baseEnd_1341321] using wordTrace_append hprefix tailTrace_1341321
  have hstable : (prefixWord ++ tailWord_1341321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341321).length < 2 ^ (prefixWord ++ tailWord_1341321).sum := by decide
  have hdescent : baseEnd_1341321 < baseStart_1341321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341338 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2]
def baseStart_1341338 : Nat := 118140960795 + 1341338 * 2 ^ 59
def prefixEnd_1341338 : Nat := 4983230072969 + 3 ^ 40 * 1341338 * 2
def baseEnd_1341338 : Nat := 688751114140578242606305

theorem tailTrace_1341338 : CollatzResearch.WordTrace tailWord_1341338 prefixEnd_1341338 688751114140578242606305 := by
  unfold tailWord_1341338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12230654003642245784334167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32615077343045988758224445 12230654003642245784334167)
  ·
    refine ⟨18345981005463368676501251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12230654003642245784334167 18345981005463368676501251)
    ·
      refine ⟨27518971508195053014751877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18345981005463368676501251 27518971508195053014751877)
      ·
        refine ⟨5159807157786572440265977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27518971508195053014751877 5159807157786572440265977)
        ·
          refine ⟨3869855368339929330199483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5159807157786572440265977 3869855368339929330199483)
          ·
            refine ⟨5804783052509893995299225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3869855368339929330199483 5804783052509893995299225)
            ·
              refine ⟨4353587289382420496474419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5804783052509893995299225 4353587289382420496474419)
              ·
                refine ⟨6530380934073630744711629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353587289382420496474419 6530380934073630744711629)
                ·
                  refine ⟨2448892850277611529266861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6530380934073630744711629 2448892850277611529266861)
                  ·
                    refine ⟨918334818854104323475073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2448892850277611529266861 918334818854104323475073)
                    ·
                      refine ⟨688751114140578242606305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918334818854104323475073 688751114140578242606305)
                      ·
                        rfl

theorem cell23_1341338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_1341338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341338 prefixEnd_1341338 := by exact prefixLift 1341338
  have htrace : WordTrace (prefixWord ++ tailWord_1341338) baseStart_1341338 baseEnd_1341338 := by
    simpa [prefixWord, tailWord_1341338, baseEnd_1341338] using wordTrace_append hprefix tailTrace_1341338
  have hstable : (prefixWord ++ tailWord_1341338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341338).length < 2 ^ (prefixWord ++ tailWord_1341338).sum := by decide
  have hdescent : baseEnd_1341338 < baseStart_1341338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341368 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 4, 2, 2]
def baseStart_1341368 : Nat := 118140960795 + 1341368 * 2 ^ 59
def prefixEnd_1341368 : Nat := 4983230072969 + 3 ^ 40 * 1341368 * 2
def baseEnd_1341368 : Nat := 688766518560213125231167

theorem tailTrace_1341368 : CollatzResearch.WordTrace tailWord_1341368 prefixEnd_1341368 688766518560213125231167 := by
  unfold tailWord_1341368
  simp only [CollatzResearch.WordTrace]
  refine ⟨24461855102230149130464379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32615806802973532173952505 24461855102230149130464379)
  ·
    refine ⟨36692782653345223695696569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24461855102230149130464379 36692782653345223695696569)
    ·
      refine ⟨27519586990008917771772427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36692782653345223695696569 27519586990008917771772427)
      ·
        refine ⟨41279380485013376657658641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27519586990008917771772427 41279380485013376657658641)
        ·
          refine ⟨30959535363760032493243981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41279380485013376657658641 30959535363760032493243981)
          ·
            refine ⟨11609825761410012184966493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30959535363760032493243981 11609825761410012184966493)
            ·
              refine ⟨4353684660528754569362435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11609825761410012184966493 4353684660528754569362435)
              ·
                refine ⟨6530526990793131854043653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353684660528754569362435 6530526990793131854043653)
                ·
                  refine ⟨1224473810773712222633185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6530526990793131854043653 1224473810773712222633185)
                  ·
                    refine ⟨918355358080284166974889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1224473810773712222633185 918355358080284166974889)
                    ·
                      refine ⟨688766518560213125231167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918355358080284166974889 688766518560213125231167)
                      ·
                        rfl

theorem cell23_1341368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_1341368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341368 prefixEnd_1341368 := by exact prefixLift 1341368
  have htrace : WordTrace (prefixWord ++ tailWord_1341368) baseStart_1341368 baseEnd_1341368 := by
    simpa [prefixWord, tailWord_1341368, baseEnd_1341368] using wordTrace_append hprefix tailTrace_1341368
  have hstable : (prefixWord ++ tailWord_1341368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341368).length < 2 ^ (prefixWord ++ tailWord_1341368).sum := by decide
  have hdescent : baseEnd_1341368 < baseStart_1341368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341425 : List Nat := [1, 2, 2, 2, 5, 1, 3, 2, 5]
def baseStart_1341425 : Nat := 118140960795 + 1341425 * 2 ^ 59
def prefixEnd_1341425 : Nat := 4983230072969 + 3 ^ 40 * 1341425 * 2
def baseEnd_1341425 : Nat := 76532865217502155802045

theorem tailTrace_1341425 : CollatzResearch.WordTrace tailWord_1341425 prefixEnd_1341425 76532865217502155802045 := by
  unfold tailWord_1341425
  simp only [CollatzResearch.WordTrace]
  refine ⟨48925789165253796995753729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32617192776835864663835819 48925789165253796995753729)
  ·
    refine ⟨36694341873940347746815297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48925789165253796995753729 36694341873940347746815297)
    ·
      refine ⟨27520756405455260810111473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36694341873940347746815297 27520756405455260810111473)
      ·
        refine ⟨20640567304091445607583605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27520756405455260810111473 20640567304091445607583605)
        ·
          refine ⟨1935053184758573025710963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20640567304091445607583605 1935053184758573025710963)
          ·
            refine ⟨2902579777137859538566445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935053184758573025710963 2902579777137859538566445)
            ·
              refine ⟨1088467416426697326962417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2902579777137859538566445 1088467416426697326962417)
              ·
                refine ⟨816350562320022995221813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088467416426697326962417 816350562320022995221813)
                ·
                  refine ⟨76532865217502155802045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 816350562320022995221813 76532865217502155802045)
                  ·
                    rfl

theorem cell23_1341425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 5].length) (baseStart_1341425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341425 prefixEnd_1341425 := by exact prefixLift 1341425
  have htrace : WordTrace (prefixWord ++ tailWord_1341425) baseStart_1341425 baseEnd_1341425 := by
    simpa [prefixWord, tailWord_1341425, baseEnd_1341425] using wordTrace_append hprefix tailTrace_1341425
  have hstable : (prefixWord ++ tailWord_1341425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341425).length < 2 ^ (prefixWord ++ tailWord_1341425).sum := by decide
  have hdescent : baseEnd_1341425 < baseStart_1341425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341441 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1341441 : Nat := 118140960795 + 1341441 * 2 ^ 59
def prefixEnd_1341441 : Nat := 4983230072969 + 3 ^ 40 * 1341441 * 2
def baseEnd_1341441 : Nat := 688804002647991339618331

theorem tailTrace_1341441 : CollatzResearch.WordTrace tailWord_1341441 prefixEnd_1341441 688804002647991339618331 := by
  unfold tailWord_1341441
  simp only [CollatzResearch.WordTrace]
  refine ⟨48926372733195831728336177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32617581822130554485557451 48926372733195831728336177)
  ·
    refine ⟨36694779549896873796252133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48926372733195831728336177 36694779549896873796252133)
    ·
      refine ⟨6880271165605663836797275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36694779549896873796252133 6880271165605663836797275)
      ·
        refine ⟨10320406748408495755195913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880271165605663836797275 10320406748408495755195913)
        ·
          refine ⟨7740305061306371816396935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10320406748408495755195913 7740305061306371816396935)
          ·
            refine ⟨11610457591959557724595403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7740305061306371816396935 11610457591959557724595403)
            ·
              refine ⟨17415686387939336586893105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11610457591959557724595403 17415686387939336586893105)
              ·
                refine ⟨13061764790954502440169829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17415686387939336586893105 13061764790954502440169829)
                ·
                  refine ⟨2449080898303969207531843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13061764790954502440169829 2449080898303969207531843)
                  ·
                    refine ⟨3673621347455953811297765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2449080898303969207531843 3673621347455953811297765)
                    ·
                      refine ⟨688804002647991339618331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3673621347455953811297765 688804002647991339618331)
                      ·
                        rfl

theorem cell23_1341441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1341441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341441 prefixEnd_1341441 := by exact prefixLift 1341441
  have htrace : WordTrace (prefixWord ++ tailWord_1341441) baseStart_1341441 baseEnd_1341441 := by
    simpa [prefixWord, tailWord_1341441, baseEnd_1341441] using wordTrace_append hprefix tailTrace_1341441
  have hstable : (prefixWord ++ tailWord_1341441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341441).length < 2 ^ (prefixWord ++ tailWord_1341441).sum := by decide
  have hdescent : baseEnd_1341441 < baseStart_1341441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341451 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 5, 4]
def baseStart_1341451 : Nat := 118140960795 + 1341451 * 2 ^ 59
def prefixEnd_1341451 : Nat := 4983230072969 + 3 ^ 40 * 1341451 * 2
def baseEnd_1341451 : Nat := 229603045818178766831095

theorem tailTrace_1341451 : CollatzResearch.WordTrace tailWord_1341451 prefixEnd_1341451 229603045818178766831095 := by
  unfold tailWord_1341451
  simp only [CollatzResearch.WordTrace]
  refine ⟨48926737463159603436200207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32617824975439735624133471 48926737463159603436200207)
  ·
    refine ⟨73390106194739405154300311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48926737463159603436200207 73390106194739405154300311)
    ·
      refine ⟨110085159292109107731450467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73390106194739405154300311 110085159292109107731450467)
      ·
        refine ⟨165127738938163661597175701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110085159292109107731450467 165127738938163661597175701)
        ·
          refine ⟨7740362762726421637367611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 165127738938163661597175701 7740362762726421637367611)
          ·
            refine ⟨11610544144089632456051417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7740362762726421637367611 11610544144089632456051417)
            ·
              refine ⟨8707908108067224342038563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11610544144089632456051417 8707908108067224342038563)
              ·
                refine ⟨13061862162100836513057845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8707908108067224342038563 13061862162100836513057845)
                ·
                  refine ⟨1224549577696953423099173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13061862162100836513057845 1224549577696953423099173)
                  ·
                    refine ⟨229603045818178766831095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1224549577696953423099173 229603045818178766831095)
                    ·
                      rfl

theorem cell23_1341451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 4].length) (baseStart_1341451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341451 prefixEnd_1341451 := by exact prefixLift 1341451
  have htrace : WordTrace (prefixWord ++ tailWord_1341451) baseStart_1341451 baseEnd_1341451 := by
    simpa [prefixWord, tailWord_1341451, baseEnd_1341451] using wordTrace_append hprefix tailTrace_1341451
  have hstable : (prefixWord ++ tailWord_1341451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341451).length < 2 ^ (prefixWord ++ tailWord_1341451).sum := by decide
  have hdescent : baseEnd_1341451 < baseStart_1341451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341492 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_1341492 : Nat := 118140960795 + 1341492 * 2 ^ 59
def prefixEnd_1341492 : Nat := 4983230072969 + 3 ^ 40 * 1341492 * 2
def baseEnd_1341492 : Nat := 688830190161370640080597

theorem tailTrace_1341492 : CollatzResearch.WordTrace tailWord_1341492 prefixEnd_1341492 688830190161370640080597 := by
  unfold tailWord_1341492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24464116428005533719221365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32618821904007378292295153 24464116428005533719221365)
  ·
    refine ⟨2293510915125518786177003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24464116428005533719221365 2293510915125518786177003)
    ·
      refine ⟨3440266372688278179265505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2293510915125518786177003 3440266372688278179265505)
      ·
        refine ⟨2580199779516208634449129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3440266372688278179265505 2580199779516208634449129)
        ·
          refine ⟨1935149834637156475836847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580199779516208634449129 1935149834637156475836847)
          ·
            refine ⟨2902724751955734713755271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935149834637156475836847 2902724751955734713755271)
            ·
              refine ⟨4354087127933602070632907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902724751955734713755271 4354087127933602070632907)
              ·
                refine ⟨6531130691900403105949361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354087127933602070632907 6531130691900403105949361)
                ·
                  refine ⟨4898348018925302329462021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6531130691900403105949361 4898348018925302329462021)
                  ·
                    refine ⟨918440253548494186774129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898348018925302329462021 918440253548494186774129)
                    ·
                      refine ⟨688830190161370640080597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918440253548494186774129 688830190161370640080597)
                      ·
                        rfl

theorem cell23_1341492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_1341492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341492 prefixEnd_1341492 := by exact prefixLift 1341492
  have htrace : WordTrace (prefixWord ++ tailWord_1341492) baseStart_1341492 baseEnd_1341492 := by
    simpa [prefixWord, tailWord_1341492, baseEnd_1341492] using wordTrace_append hprefix tailTrace_1341492
  have hstable : (prefixWord ++ tailWord_1341492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341492).length < 2 ^ (prefixWord ++ tailWord_1341492).sum := by decide
  have hdescent : baseEnd_1341492 < baseStart_1341492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341511 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 3, 5]
def baseStart_1341511 : Nat := 118140960795 + 1341511 * 2 ^ 59
def prefixEnd_1341511 : Nat := 4983230072969 + 3 ^ 40 * 1341511 * 2
def baseEnd_1341511 : Nat := 229613315431268688581003

theorem tailTrace_1341511 : CollatzResearch.WordTrace tailWord_1341511 prefixEnd_1341511 229613315431268688581003 := by
  unfold tailWord_1341511
  simp only [CollatzResearch.WordTrace]
  refine ⟨48928925842942233683384387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32619283895294822455589591 48928925842942233683384387)
  ·
    refine ⟨73393388764413350525076581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48928925842942233683384387 73393388764413350525076581)
    ·
      refine ⟨13761260393327503223451859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73393388764413350525076581 13761260393327503223451859)
      ·
        refine ⟨20641890589991254835177789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13761260393327503223451859 20641890589991254835177789)
        ·
          refine ⟨7740708971246720563191671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20641890589991254835177789 7740708971246720563191671)
          ·
            refine ⟨11611063456870080844787507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7740708971246720563191671 11611063456870080844787507)
            ·
              refine ⟨17416595185305121267181261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11611063456870080844787507 17416595185305121267181261)
              ·
                refine ⟨6531223194489420475192973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17416595185305121267181261 6531223194489420475192973)
                ·
                  refine ⟨2449208697933532678197365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6531223194489420475192973 2449208697933532678197365)
                  ·
                    refine ⟨229613315431268688581003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2449208697933532678197365 229613315431268688581003)
                    ·
                      rfl

theorem cell23_1341511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_1341511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341511 prefixEnd_1341511 := by exact prefixLift 1341511
  have htrace : WordTrace (prefixWord ++ tailWord_1341511) baseStart_1341511 baseEnd_1341511 := by
    simpa [prefixWord, tailWord_1341511, baseEnd_1341511] using wordTrace_append hprefix tailTrace_1341511
  have hstable : (prefixWord ++ tailWord_1341511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341511).length < 2 ^ (prefixWord ++ tailWord_1341511).sum := by decide
  have hdescent : baseEnd_1341511 < baseStart_1341511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341528 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 1, 5]
def baseStart_1341528 : Nat := 118140960795 + 1341528 * 2 ^ 59
def prefixEnd_1341528 : Nat := 4983230072969 + 3 ^ 40 * 1341528 * 2
def baseEnd_1341528 : Nat := 229616225154977499743477

theorem tailTrace_1341528 : CollatzResearch.WordTrace tailWord_1341528 prefixEnd_1341528 229616225154977499743477 := by
  unfold tailWord_1341528
  simp only [CollatzResearch.WordTrace]
  refine ⟨24464772941940322793376619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32619697255920430391168825 24464772941940322793376619)
  ·
    refine ⟨36697159412910484190064929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24464772941940322793376619 36697159412910484190064929)
    ·
      refine ⟨27522869559682863142548697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36697159412910484190064929 27522869559682863142548697)
      ·
        refine ⟨20642152169762147356911523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27522869559682863142548697 20642152169762147356911523)
        ·
          refine ⟨30963228254643221035367285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20642152169762147356911523 30963228254643221035367285)
          ·
            refine ⟨2902802648872801972065683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30963228254643221035367285 2902802648872801972065683)
            ·
              refine ⟨4354203973309202958098525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902802648872801972065683 4354203973309202958098525)
              ·
                refine ⟨1632826489990951109286947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4354203973309202958098525 1632826489990951109286947)
                ·
                  refine ⟨2449239734986426663930421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632826489990951109286947 2449239734986426663930421)
                  ·
                    refine ⟨229616225154977499743477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2449239734986426663930421 229616225154977499743477)
                    ·
                      rfl

theorem cell23_1341528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_1341528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341528 prefixEnd_1341528 := by exact prefixLift 1341528
  have htrace : WordTrace (prefixWord ++ tailWord_1341528) baseStart_1341528 baseEnd_1341528 := by
    simpa [prefixWord, tailWord_1341528, baseEnd_1341528] using wordTrace_append hprefix tailTrace_1341528
  have hstable : (prefixWord ++ tailWord_1341528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341528).length < 2 ^ (prefixWord ++ tailWord_1341528).sum := by decide
  have hdescent : baseEnd_1341528 < baseStart_1341528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341551 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_1341551 : Nat := 118140960795 + 1341551 * 2 ^ 59
def prefixEnd_1341551 : Nat := 4983230072969 + 3 ^ 40 * 1341551 * 2
def baseEnd_1341551 : Nat := 688860485519985909242825

theorem tailTrace_1341551 : CollatzResearch.WordTrace tailWord_1341551 prefixEnd_1341551 688860485519985909242825 := by
  unfold tailWord_1341551
  simp only [CollatzResearch.WordTrace]
  refine ⟨48930384762797320514840507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32620256508531547009893671 48930384762797320514840507)
  ·
    refine ⟨73395577144195980772260761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48930384762797320514840507 73395577144195980772260761)
    ·
      refine ⟨55046682858146985579195571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73395577144195980772260761 55046682858146985579195571)
      ·
        refine ⟨82570024287220478368793357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55046682858146985579195571 82570024287220478368793357)
        ·
          refine ⟨30963759107707679388297509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82570024287220478368793357 30963759107707679388297509)
          ·
            refine ⟨5805704832695189885305783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30963759107707679388297509 5805704832695189885305783)
            ·
              refine ⟨8708557249042784827958675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805704832695189885305783 8708557249042784827958675)
              ·
                refine ⟨13062835873564177241938013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8708557249042784827958675 13062835873564177241938013)
                ·
                  refine ⟨4898563452586566465726755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13062835873564177241938013 4898563452586566465726755)
                  ·
                    refine ⟨7347845178879849698590133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898563452586566465726755 7347845178879849698590133)
                    ·
                      refine ⟨688860485519985909242825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7347845178879849698590133 688860485519985909242825)
                      ·
                        rfl

theorem cell23_1341551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_1341551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341551 prefixEnd_1341551 := by exact prefixLift 1341551
  have htrace : WordTrace (prefixWord ++ tailWord_1341551) baseStart_1341551 baseEnd_1341551 := by
    simpa [prefixWord, tailWord_1341551, baseEnd_1341551] using wordTrace_append hprefix tailTrace_1341551
  have hstable : (prefixWord ++ tailWord_1341551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341551).length < 2 ^ (prefixWord ++ tailWord_1341551).sum := by decide
  have hdescent : baseEnd_1341551 < baseStart_1341551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341565 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_1341565 : Nat := 118140960795 + 1341565 * 2 ^ 59
def prefixEnd_1341565 : Nat := 4983230072969 + 3 ^ 40 * 1341565 * 2
def baseEnd_1341565 : Nat := 688867674249148854467761

theorem tailTrace_1341565 : CollatzResearch.WordTrace tailWord_1341565 prefixEnd_1341565 688867674249148854467761 := by
  unfold tailWord_1341565
  simp only [CollatzResearch.WordTrace]
  refine ⟨48930895384746600905850149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32620596923164400603900099 48930895384746600905850149)
  ·
    refine ⟨9174542884639987669846903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48930895384746600905850149 9174542884639987669846903)
    ·
      refine ⟨13761814326959981504770355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9174542884639987669846903 13761814326959981504770355)
      ·
        refine ⟨20642721490439972257155533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13761814326959981504770355 20642721490439972257155533)
        ·
          refine ⟨7741020558914989596433325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20642721490439972257155533 7741020558914989596433325)
          ·
            refine ⟨2902882709593121098662497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7741020558914989596433325 2902882709593121098662497)
            ·
              refine ⟨2177162032194840823996873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2902882709593121098662497 2177162032194840823996873)
              ·
                refine ⟨1632871524146130617997655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177162032194840823996873 1632871524146130617997655)
                ·
                  refine ⟨2449307286219195926996483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632871524146130617997655 2449307286219195926996483)
                  ·
                    refine ⟨3673960929328793890494725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2449307286219195926996483 3673960929328793890494725)
                    ·
                      refine ⟨688867674249148854467761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3673960929328793890494725 688867674249148854467761)
                      ·
                        rfl

theorem cell23_1341565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_1341565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341565 prefixEnd_1341565 := by exact prefixLift 1341565
  have htrace : WordTrace (prefixWord ++ tailWord_1341565) baseStart_1341565 baseEnd_1341565 := by
    simpa [prefixWord, tailWord_1341565, baseEnd_1341565] using wordTrace_append hprefix tailTrace_1341565
  have hstable : (prefixWord ++ tailWord_1341565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341565).length < 2 ^ (prefixWord ++ tailWord_1341565).sum := by decide
  have hdescent : baseEnd_1341565 < baseStart_1341565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341571 : List Nat := [1, 1, 1, 3, 3, 4, 1, 9]
def baseStart_1341571 : Nat := 118140960795 + 1341571 * 2 ^ 59
def prefixEnd_1341571 : Nat := 4983230072969 + 3 ^ 40 * 1341571 * 2
def baseEnd_1341571 : Nat := 25513731671595401147879

theorem tailTrace_1341571 : CollatzResearch.WordTrace tailWord_1341571 prefixEnd_1341571 25513731671595401147879 := by
  unfold tailWord_1341571
  simp only [CollatzResearch.WordTrace]
  refine ⟨48931114222724863930568567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32620742815149909287045711 48931114222724863930568567)
  ·
    refine ⟨73396671334087295895852851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48931114222724863930568567 73396671334087295895852851)
    ·
      refine ⟨110095007001130943843779277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73396671334087295895852851 110095007001130943843779277)
      ·
        refine ⟨41285627625424103941417229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110095007001130943843779277 41285627625424103941417229)
        ·
          refine ⟨15482110359534038978031461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41285627625424103941417229 15482110359534038978031461)
          ·
            refine ⟨2902895692412632308380899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15482110359534038978031461 2902895692412632308380899)
            ·
              refine ⟨4354343538618948462571349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902895692412632308380899 4354343538618948462571349)
              ·
                refine ⟨25513731671595401147879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4354343538618948462571349 25513731671595401147879)
                ·
                  rfl

theorem cell23_1341571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 9].length) (baseStart_1341571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341571 prefixEnd_1341571 := by exact prefixLift 1341571
  have htrace : WordTrace (prefixWord ++ tailWord_1341571) baseStart_1341571 baseEnd_1341571 := by
    simpa [prefixWord, tailWord_1341571, baseEnd_1341571] using wordTrace_append hprefix tailTrace_1341571
  have hstable : (prefixWord ++ tailWord_1341571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341571).length < 2 ^ (prefixWord ++ tailWord_1341571).sum := by decide
  have hdescent : baseEnd_1341571 < baseStart_1341571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341599 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1341599 : Nat := 118140960795 + 1341599 * 2 ^ 59
def prefixEnd_1341599 : Nat := 4983230072969 + 3 ^ 40 * 1341599 * 2
def baseEnd_1341599 : Nat := 688885132591401721442605

theorem tailTrace_1341599 : CollatzResearch.WordTrace tailWord_1341599 prefixEnd_1341599 688885132591401721442605 := by
  unfold tailWord_1341599
  simp only [CollatzResearch.WordTrace]
  refine ⟨48932135466623424712587851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32621423644415616475058567 48932135466623424712587851)
  ·
    refine ⟨73398203199935137068881777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48932135466623424712587851 73398203199935137068881777)
    ·
      refine ⟨55048652399951352801661333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73398203199935137068881777 55048652399951352801661333)
      ·
        refine ⟨2580405581247719662577875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55048652399951352801661333 2580405581247719662577875)
        ·
          refine ⟨3870608371871579493866813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580405581247719662577875 3870608371871579493866813)
          ·
            refine ⟨1451478139451842310200055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3870608371871579493866813 1451478139451842310200055)
            ·
              refine ⟨2177217209177763465300083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451478139451842310200055 2177217209177763465300083)
              ·
                refine ⟨3265825813766645197950125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177217209177763465300083 3265825813766645197950125)
                ·
                  refine ⟨1224684680162491949231297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3265825813766645197950125 1224684680162491949231297)
                  ·
                    refine ⟨918513510121868961923473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1224684680162491949231297 918513510121868961923473)
                    ·
                      refine ⟨688885132591401721442605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918513510121868961923473 688885132591401721442605)
                      ·
                        rfl

theorem cell23_1341599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1341599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341599 prefixEnd_1341599 := by exact prefixLift 1341599
  have htrace : WordTrace (prefixWord ++ tailWord_1341599) baseStart_1341599 baseEnd_1341599 := by
    simpa [prefixWord, tailWord_1341599, baseEnd_1341599] using wordTrace_append hprefix tailTrace_1341599
  have hstable : (prefixWord ++ tailWord_1341599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341599).length < 2 ^ (prefixWord ++ tailWord_1341599).sum := by decide
  have hdescent : baseEnd_1341599 < baseStart_1341599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341625 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 3, 3, 2]
def baseStart_1341625 : Nat := 118140960795 + 1341625 * 2 ^ 59
def prefixEnd_1341625 : Nat := 4983230072969 + 3 ^ 40 * 1341625 * 2
def baseEnd_1341625 : Nat := 688898483088418619717485

theorem tailTrace_1341625 : CollatzResearch.WordTrace tailWord_1341625 prefixEnd_1341625 688898483088418619717485 := by
  unfold tailWord_1341625
  simp only [CollatzResearch.WordTrace]
  refine ⟨48933083764529231153034329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32622055843019487435356219 48933083764529231153034329)
  ·
    refine ⟨36699812823396923364775747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48933083764529231153034329 36699812823396923364775747)
    ·
      refine ⟨55049719235095385047163621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36699812823396923364775747 55049719235095385047163621)
      ·
        refine ⟨10321822356580384696343179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55049719235095385047163621 10321822356580384696343179)
        ·
          refine ⟨15482733534870577044514769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10321822356580384696343179 15482733534870577044514769)
          ·
            refine ⟨11612050151152932783386077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15482733534870577044514769 11612050151152932783386077)
            ·
              refine ⟨4354518806682349793769779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11612050151152932783386077 4354518806682349793769779)
              ·
                refine ⟨6531778210023524690654669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354518806682349793769779 6531778210023524690654669)
                ·
                  refine ⟨2449416828758821758995501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6531778210023524690654669 2449416828758821758995501)
                  ·
                    refine ⟨918531310784558159623313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2449416828758821758995501 918531310784558159623313)
                    ·
                      refine ⟨688898483088418619717485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918531310784558159623313 688898483088418619717485)
                      ·
                        rfl

theorem cell23_1341625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_1341625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341625 prefixEnd_1341625 := by exact prefixLift 1341625
  have htrace : WordTrace (prefixWord ++ tailWord_1341625) baseStart_1341625 baseEnd_1341625 := by
    simpa [prefixWord, tailWord_1341625, baseEnd_1341625] using wordTrace_append hprefix tailTrace_1341625
  have hstable : (prefixWord ++ tailWord_1341625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341625).length < 2 ^ (prefixWord ++ tailWord_1341625).sum := by decide
  have hdescent : baseEnd_1341625 < baseStart_1341625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341631 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 4, 6]
def baseStart_1341631 : Nat := 118140960795 + 1341631 * 2 ^ 59
def prefixEnd_1341631 : Nat := 4983230072969 + 3 ^ 40 * 1341631 * 2
def baseEnd_1341631 : Nat := 229633854657448532080819

theorem tailTrace_1341631 : CollatzResearch.WordTrace tailWord_1341631 prefixEnd_1341631 229633854657448532080819 := by
  unfold tailWord_1341631
  simp only [CollatzResearch.WordTrace]
  refine ⟨48933302602507494177752747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32622201735004996118501831 48933302602507494177752747)
  ·
    refine ⟨73399953903761241266629121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48933302602507494177752747 73399953903761241266629121)
    ·
      refine ⟨55049965427820930949971841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73399953903761241266629121 55049965427820930949971841)
      ·
        refine ⟨41287474070865698212478881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55049965427820930949971841 41287474070865698212478881)
        ·
          refine ⟨30965605553149273659359161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41287474070865698212478881 30965605553149273659359161)
          ·
            refine ⟨23224204164861955244519371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30965605553149273659359161 23224204164861955244519371)
            ·
              refine ⟨34836306247292932866779057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23224204164861955244519371 34836306247292932866779057)
              ·
                refine ⟨26127229685469699650084293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34836306247292932866779057 26127229685469699650084293)
                ·
                  refine ⟨4898855566025568684390805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26127229685469699650084293 4898855566025568684390805)
                  ·
                    refine ⟨229633854657448532080819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4898855566025568684390805 229633854657448532080819)
                    ·
                      rfl

theorem cell23_1341631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_1341631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341631 prefixEnd_1341631 := by exact prefixLift 1341631
  have htrace : WordTrace (prefixWord ++ tailWord_1341631) baseStart_1341631 baseEnd_1341631 := by
    simpa [prefixWord, tailWord_1341631, baseEnd_1341631] using wordTrace_append hprefix tailTrace_1341631
  have hstable : (prefixWord ++ tailWord_1341631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341631).length < 2 ^ (prefixWord ++ tailWord_1341631).sum := by decide
  have hdescent : baseEnd_1341631 < baseStart_1341631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341641 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_1341641 : Nat := 118140960795 + 1341641 * 2 ^ 59
def prefixEnd_1341641 : Nat := 4983230072969 + 3 ^ 40 * 1341641 * 2
def baseEnd_1341641 : Nat := 688906698778890557117411

theorem tailTrace_1341641 : CollatzResearch.WordTrace tailWord_1341641 prefixEnd_1341641 688906698778890557117411 := by
  unfold tailWord_1341641
  simp only [CollatzResearch.WordTrace]
  refine ⟨48933667332471265885616777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32622444888314177257077851 48933667332471265885616777)
  ·
    refine ⟨36700250499353449414212583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48933667332471265885616777 36700250499353449414212583)
    ·
      refine ⟨55050375749030174121318875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36700250499353449414212583 55050375749030174121318875)
      ·
        refine ⟨82575563623545261181978313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55050375749030174121318875 82575563623545261181978313)
        ·
          refine ⟨61931672717658945886483735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82575563623545261181978313 61931672717658945886483735)
          ·
            refine ⟨92897509076488418829725603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61931672717658945886483735 92897509076488418829725603)
            ·
              refine ⟨139346263614732628244588405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92897509076488418829725603 139346263614732628244588405)
              ·
                refine ⟨13063712213881183897930163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139346263614732628244588405 13063712213881183897930163)
                ·
                  refine ⟨19595568320821775846895245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13063712213881183897930163 19595568320821775846895245)
                  ·
                    refine ⟨7348338120308165942585717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19595568320821775846895245 7348338120308165942585717)
                    ·
                      refine ⟨688906698778890557117411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7348338120308165942585717 688906698778890557117411)
                      ·
                        rfl

theorem cell23_1341641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_1341641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341641 prefixEnd_1341641 := by exact prefixLift 1341641
  have htrace : WordTrace (prefixWord ++ tailWord_1341641) baseStart_1341641 baseEnd_1341641 := by
    simpa [prefixWord, tailWord_1341641, baseEnd_1341641] using wordTrace_append hprefix tailTrace_1341641
  have hstable : (prefixWord ++ tailWord_1341641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341641).length < 2 ^ (prefixWord ++ tailWord_1341641).sum := by decide
  have hdescent : baseEnd_1341641 < baseStart_1341641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341658 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3]
def baseStart_1341658 : Nat := 118140960795 + 1341658 * 2 ^ 59
def prefixEnd_1341658 : Nat := 4983230072969 + 3 ^ 40 * 1341658 * 2
def baseEnd_1341658 : Nat := 688915427950016990604833

theorem tailTrace_1341658 : CollatzResearch.WordTrace tailWord_1341658 prefixEnd_1341658 688915427950016990604833 := by
  unfold tailWord_1341658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12233571843352419447246407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32622858248939785192657085 12233571843352419447246407)
  ·
    refine ⟨18350357765028629170869611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12233571843352419447246407 18350357765028629170869611)
    ·
      refine ⟨27525536647542943756304417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18350357765028629170869611 27525536647542943756304417)
      ·
        refine ⟨20644152485657207817228313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27525536647542943756304417 20644152485657207817228313)
        ·
          refine ⟨15483114364242905862921235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20644152485657207817228313 15483114364242905862921235)
          ·
            refine ⟨23224671546364358794381853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15483114364242905862921235 23224671546364358794381853)
            ·
              refine ⟨8709251829886634547893195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23224671546364358794381853 8709251829886634547893195)
              ·
                refine ⟨13063877744829951821839793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709251829886634547893195 13063877744829951821839793)
                ·
                  refine ⟨9797908308622463866379845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13063877744829951821839793 9797908308622463866379845)
                  ·
                    refine ⟨1837107807866711974946221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9797908308622463866379845 1837107807866711974946221)
                    ·
                      refine ⟨688915427950016990604833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1837107807866711974946221 688915427950016990604833)
                      ·
                        rfl

theorem cell23_1341658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_1341658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341658 prefixEnd_1341658 := by exact prefixLift 1341658
  have htrace : WordTrace (prefixWord ++ tailWord_1341658) baseStart_1341658 baseEnd_1341658 := by
    simpa [prefixWord, tailWord_1341658, baseEnd_1341658] using wordTrace_append hprefix tailTrace_1341658
  have hstable : (prefixWord ++ tailWord_1341658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341658).length < 2 ^ (prefixWord ++ tailWord_1341658).sum := by decide
  have hdescent : baseEnd_1341658 < baseStart_1341658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341666 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1341666 : Nat := 118140960795 + 1341666 * 2 ^ 59
def prefixEnd_1341666 : Nat := 4983230072969 + 3 ^ 40 * 1341666 * 2
def baseEnd_1341666 : Nat := 688919535795252959304797

theorem tailTrace_1341666 : CollatzResearch.WordTrace tailWord_1341666 prefixEnd_1341666 688919535795252959304797 := by
  unfold tailWord_1341666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12233644789345173788819213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32623052771587130103517901 12233644789345173788819213)
  ·
    refine ⟨4587616796004440170807205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12233644789345173788819213 4587616796004440170807205)
    ·
      refine ⟨860178149250832532026351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4587616796004440170807205 860178149250832532026351)
      ·
        refine ⟨1290267223876248798039527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860178149250832532026351 1290267223876248798039527)
        ·
          refine ⟨1935400835814373197059291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290267223876248798039527 1935400835814373197059291)
          ·
            refine ⟨2903101253721559795588937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935400835814373197059291 2903101253721559795588937)
            ·
              refine ⟨2177325940291169846691703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2903101253721559795588937 2177325940291169846691703)
              ·
                refine ⟨3265988910436754770037555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177325940291169846691703 3265988910436754770037555)
                ·
                  refine ⟨4898983365655132155056333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265988910436754770037555 4898983365655132155056333)
                  ·
                    refine ⟨1837118762120674558146125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4898983365655132155056333 1837118762120674558146125)
                    ·
                      refine ⟨688919535795252959304797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1837118762120674558146125 688919535795252959304797)
                      ·
                        rfl

theorem cell23_1341666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1341666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341666 prefixEnd_1341666 := by exact prefixLift 1341666
  have htrace : WordTrace (prefixWord ++ tailWord_1341666) baseStart_1341666 baseEnd_1341666 := by
    simpa [prefixWord, tailWord_1341666, baseEnd_1341666] using wordTrace_append hprefix tailTrace_1341666
  have hstable : (prefixWord ++ tailWord_1341666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341666).length < 2 ^ (prefixWord ++ tailWord_1341666).sum := by decide
  have hdescent : baseEnd_1341666 < baseStart_1341666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341672 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_1341672 : Nat := 118140960795 + 1341672 * 2 ^ 59
def prefixEnd_1341672 : Nat := 4983230072969 + 3 ^ 40 * 1341672 * 2
def baseEnd_1341672 : Nat := 688922616679179935829769

theorem tailTrace_1341672 : CollatzResearch.WordTrace tailWord_1341672 prefixEnd_1341672 688922616679179935829769 := by
  unfold tailWord_1341672
  simp only [CollatzResearch.WordTrace]
  refine ⟨24467398997679479089997635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32623198663572638786663513 24467398997679479089997635)
  ·
    refine ⟨36701098496519218634996453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24467398997679479089997635 36701098496519218634996453)
    ·
      refine ⟨6881455968097353494061835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36701098496519218634996453 6881455968097353494061835)
      ·
        refine ⟨10322183952146030241092753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6881455968097353494061835 10322183952146030241092753)
        ·
          refine ⟨7741637964109522680819565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10322183952146030241092753 7741637964109522680819565)
          ·
            refine ⟨2903114236541071005307337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7741637964109522680819565 2903114236541071005307337)
            ·
              refine ⟨2177335677405803253980503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2903114236541071005307337 2177335677405803253980503)
              ·
                refine ⟨3266003516108704880970755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177335677405803253980503 3266003516108704880970755)
                ·
                  refine ⟨4899005274163057321456133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266003516108704880970755 4899005274163057321456133)
                  ·
                    refine ⟨918563488905573247773025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4899005274163057321456133 918563488905573247773025)
                    ·
                      refine ⟨688922616679179935829769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918563488905573247773025 688922616679179935829769)
                      ·
                        rfl

theorem cell23_1341672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_1341672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341672 prefixEnd_1341672 := by exact prefixLift 1341672
  have htrace : WordTrace (prefixWord ++ tailWord_1341672) baseStart_1341672 baseEnd_1341672 := by
    simpa [prefixWord, tailWord_1341672, baseEnd_1341672] using wordTrace_append hprefix tailTrace_1341672
  have hstable : (prefixWord ++ tailWord_1341672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341672).length < 2 ^ (prefixWord ++ tailWord_1341672).sum := by decide
  have hdescent : baseEnd_1341672 < baseStart_1341672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341695 : List Nat := [1, 1, 2, 2, 1, 4, 4, 3, 5]
def baseStart_1341695 : Nat := 118140960795 + 1341695 * 2 ^ 59
def prefixEnd_1341695 : Nat := 4983230072969 + 3 ^ 40 * 1341695 * 2
def baseEnd_1341695 : Nat := 76548269637137038426907

theorem tailTrace_1341695 : CollatzResearch.WordTrace tailWord_1341695 prefixEnd_1341695 76548269637137038426907 := by
  unfold tailWord_1341695
  simp only [CollatzResearch.WordTrace]
  refine ⟨48935636874275633108082539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32623757916183755405388359 48935636874275633108082539)
  ·
    refine ⟨73403455311413449662123809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48935636874275633108082539 73403455311413449662123809)
    ·
      refine ⟨55052591483560087246592857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73403455311413449662123809 55052591483560087246592857)
      ·
        refine ⟨41289443612670065434944643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55052591483560087246592857 41289443612670065434944643)
        ·
          refine ⟨61934165419005098152416965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41289443612670065434944643 61934165419005098152416965)
          ·
            refine ⟨11612656016063455903578181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61934165419005098152416965 11612656016063455903578181)
            ·
              refine ⟨2177373003011897981920909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11612656016063455903578181 2177373003011897981920909)
              ·
                refine ⟨816514876129461743220341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2177373003011897981920909 816514876129461743220341)
                ·
                  refine ⟨76548269637137038426907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 816514876129461743220341 76548269637137038426907)
                  ·
                    rfl

theorem cell23_1341695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 5].length) (baseStart_1341695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341695 prefixEnd_1341695 := by exact prefixLift 1341695
  have htrace : WordTrace (prefixWord ++ tailWord_1341695) baseStart_1341695 baseEnd_1341695 := by
    simpa [prefixWord, tailWord_1341695, baseEnd_1341695] using wordTrace_append hprefix tailTrace_1341695
  have hstable : (prefixWord ++ tailWord_1341695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341695).length < 2 ^ (prefixWord ++ tailWord_1341695).sum := by decide
  have hdescent : baseEnd_1341695 < baseStart_1341695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341708 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_1341708 : Nat := 118140960795 + 1341708 * 2 ^ 59
def prefixEnd_1341708 : Nat := 4983230072969 + 3 ^ 40 * 1341708 * 2
def baseEnd_1341708 : Nat := 229647033994247264993201

theorem tailTrace_1341708 : CollatzResearch.WordTrace tailWord_1341708 prefixEnd_1341708 229647033994247264993201 := by
  unfold tailWord_1341708
  simp only [CollatzResearch.WordTrace]
  refine ⟨24468055511614268164152889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32624074015485690885537185 24468055511614268164152889)
  ·
    refine ⟨18351041633710701123114667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24468055511614268164152889 18351041633710701123114667)
    ·
      refine ⟨27526562450566051684672001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18351041633710701123114667 27526562450566051684672001)
      ·
        refine ⟨20644921837924538763504001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27526562450566051684672001 20644921837924538763504001)
        ·
          refine ⟨15483691378443404072628001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20644921837924538763504001 15483691378443404072628001)
          ·
            refine ⟨11612768533832553054471001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15483691378443404072628001 11612768533832553054471001)
            ·
              refine ⟨8709576400374414790853251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11612768533832553054471001 8709576400374414790853251)
              ·
                refine ⟨13064364600561622186279877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709576400374414790853251 13064364600561622186279877)
                ·
                  refine ⟨2449568362605304159927477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13064364600561622186279877 2449568362605304159927477)
                  ·
                    refine ⟨229647033994247264993201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2449568362605304159927477 229647033994247264993201)
                    ·
                      rfl

theorem cell23_1341708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_1341708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341708 prefixEnd_1341708 := by exact prefixLift 1341708
  have htrace : WordTrace (prefixWord ++ tailWord_1341708) baseStart_1341708 baseEnd_1341708 := by
    simpa [prefixWord, tailWord_1341708, baseEnd_1341708] using wordTrace_append hprefix tailTrace_1341708
  have hstable : (prefixWord ++ tailWord_1341708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341708).length < 2 ^ (prefixWord ++ tailWord_1341708).sum := by decide
  have hdescent : baseEnd_1341708 < baseStart_1341708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341768 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 8]
def baseStart_1341768 : Nat := 118140960795 + 1341768 * 2 ^ 59
def prefixEnd_1341768 : Nat := 4983230072969 + 3 ^ 40 * 1341768 * 2
def baseEnd_1341768 : Nat := 76552434535779062247703

theorem tailTrace_1341768 : CollatzResearch.WordTrace tailWord_1341768 prefixEnd_1341768 76552434535779062247703 := by
  unfold tailWord_1341768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24469149701505583287744979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32625532935340777716993305 24469149701505583287744979)
  ·
    refine ⟨36703724552258374931617469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24469149701505583287744979 36703724552258374931617469)
    ·
      refine ⟨13763896707096890599356551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36703724552258374931617469 13763896707096890599356551)
      ·
        refine ⟨20645845060645335899034827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13763896707096890599356551 20645845060645335899034827)
        ·
          refine ⟨30968767590968003848552241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20645845060645335899034827 30968767590968003848552241)
          ·
            refine ⟨23226575693226002886414181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30968767590968003848552241 23226575693226002886414181)
            ·
              refine ⟨4354982942479875541202659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23226575693226002886414181 4354982942479875541202659)
              ·
                refine ⟨6532474413719813311803989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354982942479875541202659 6532474413719813311803989)
                ·
                  refine ⟨76552434535779062247703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6532474413719813311803989 76552434535779062247703)
                  ·
                    rfl

theorem cell23_1341768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 8].length) (baseStart_1341768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341768 prefixEnd_1341768 := by exact prefixLift 1341768
  have htrace : WordTrace (prefixWord ++ tailWord_1341768) baseStart_1341768 baseEnd_1341768 := by
    simpa [prefixWord, tailWord_1341768, baseEnd_1341768] using wordTrace_append hprefix tailTrace_1341768
  have hstable : (prefixWord ++ tailWord_1341768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341768).length < 2 ^ (prefixWord ++ tailWord_1341768).sum := by decide
  have hdescent : baseEnd_1341768 < baseStart_1341768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341835 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 4]
def baseStart_1341835 : Nat := 118140960795 + 1341835 * 2 ^ 59
def prefixEnd_1341835 : Nat := 4983230072969 + 3 ^ 40 * 1341835 * 2
def baseEnd_1341835 : Nat := 689006314025862798091519

theorem tailTrace_1341835 : CollatzResearch.WordTrace tailWord_1341835 prefixEnd_1341835 689006314025862798091519 := by
  unfold tailWord_1341835
  simp only [CollatzResearch.WordTrace]
  refine ⟨48940743093768437018178959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32627162062512291345452639 48940743093768437018178959)
  ·
    refine ⟨73411114640652655527268439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48940743093768437018178959 73411114640652655527268439)
    ·
      refine ⟨110116671960978983290902659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73411114640652655527268439 110116671960978983290902659)
      ·
        refine ⟨165175007941468474936353989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110116671960978983290902659 165175007941468474936353989)
        ·
          refine ⟨30970313989025339050566373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165175007941468474936353989 30970313989025339050566373)
          ·
            refine ⟨5806933872942251071981195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30970313989025339050566373 5806933872942251071981195)
            ·
              refine ⟨8710400809413376607971793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5806933872942251071981195 8710400809413376607971793)
              ·
                refine ⟨6532800607060032455978845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8710400809413376607971793 6532800607060032455978845)
                ·
                  refine ⟨2449800227647512170992067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6532800607060032455978845 2449800227647512170992067)
                  ·
                    refine ⟨3674700341471268256488101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2449800227647512170992067 3674700341471268256488101)
                    ·
                      refine ⟨689006314025862798091519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3674700341471268256488101 689006314025862798091519)
                      ·
                        rfl

theorem cell23_1341835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 4].length) (baseStart_1341835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341835 prefixEnd_1341835 := by exact prefixLift 1341835
  have htrace : WordTrace (prefixWord ++ tailWord_1341835) baseStart_1341835 baseEnd_1341835 := by
    simpa [prefixWord, tailWord_1341835, baseEnd_1341835] using wordTrace_append hprefix tailTrace_1341835
  have hstable : (prefixWord ++ tailWord_1341835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341835).length < 2 ^ (prefixWord ++ tailWord_1341835).sum := by decide
  have hdescent : baseEnd_1341835 < baseStart_1341835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341845 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1341845 : Nat := 118140960795 + 1341845 * 2 ^ 59
def prefixEnd_1341845 : Nat := 4983230072969 + 3 ^ 40 * 1341845 * 2
def baseEnd_1341845 : Nat := 229670482944135919655491

theorem tailTrace_1341845 : CollatzResearch.WordTrace tailWord_1341845 prefixEnd_1341845 229670482944135919655491 := by
  unfold tailWord_1341845
  simp only [CollatzResearch.WordTrace]
  refine ⟨48941107823732208726042989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32627405215821472484028659 48941107823732208726042989)
  ·
    refine ⟨18352915433899578272266121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48941107823732208726042989 18352915433899578272266121)
    ·
      refine ⟨13764686575424683704199591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18352915433899578272266121 13764686575424683704199591)
      ·
        refine ⟨20647029863137025556299387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13764686575424683704199591 20647029863137025556299387)
        ·
          refine ⟨30970544794705538334449081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20647029863137025556299387 30970544794705538334449081)
          ·
            refine ⟨23227908596029153750836811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30970544794705538334449081 23227908596029153750836811)
            ·
              refine ⟨34841862894043730626255217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23227908596029153750836811 34841862894043730626255217)
              ·
                refine ⟨26131397170532797969691413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34841862894043730626255217 26131397170532797969691413)
                ·
                  refine ⟨1224909242368724904829285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26131397170532797969691413 1224909242368724904829285)
                  ·
                    refine ⟨229670482944135919655491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1224909242368724904829285 229670482944135919655491)
                    ·
                      rfl

theorem cell23_1341845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1341845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341845 prefixEnd_1341845 := by exact prefixLift 1341845
  have htrace : WordTrace (prefixWord ++ tailWord_1341845) baseStart_1341845 baseEnd_1341845 := by
    simpa [prefixWord, tailWord_1341845, baseEnd_1341845] using wordTrace_append hprefix tailTrace_1341845
  have hstable : (prefixWord ++ tailWord_1341845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341845).length < 2 ^ (prefixWord ++ tailWord_1341845).sum := by decide
  have hdescent : baseEnd_1341845 < baseStart_1341845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341879 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 2, 4]
def baseStart_1341879 : Nat := 118140960795 + 1341879 * 2 ^ 59
def prefixEnd_1341879 : Nat := 4983230072969 + 3 ^ 40 * 1341879 * 2
def baseEnd_1341879 : Nat := 229676302391553541980439

theorem tailTrace_1341879 : CollatzResearch.WordTrace tailWord_1341879 prefixEnd_1341879 229676302391553541980439 := by
  unfold tailWord_1341879
  simp only [CollatzResearch.WordTrace]
  refine ⟨48942347905609032532780691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32628231937072688355187127 48942347905609032532780691)
  ·
    refine ⟨73413521858413548799171037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48942347905609032532780691 73413521858413548799171037)
    ·
      refine ⟨27530070696905080799689139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73413521858413548799171037 27530070696905080799689139)
      ·
        refine ⟨41295106045357621199533709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27530070696905080799689139 41295106045357621199533709)
        ·
          refine ⟨15485664767009107949825141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41295106045357621199533709 15485664767009107949825141)
          ·
            refine ⟨1451781071907103870296107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15485664767009107949825141 1451781071907103870296107)
            ·
              refine ⟨2177671607860655805444161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451781071907103870296107 2177671607860655805444161)
              ·
                refine ⟨1633253705895491854083121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177671607860655805444161 1633253705895491854083121)
                ·
                  refine ⟨1224940279421618890562341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1633253705895491854083121 1224940279421618890562341)
                  ·
                    refine ⟨229676302391553541980439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1224940279421618890562341 229676302391553541980439)
                    ·
                      rfl

theorem cell23_1341879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_1341879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341879 prefixEnd_1341879 := by exact prefixLift 1341879
  have htrace : WordTrace (prefixWord ++ tailWord_1341879) baseStart_1341879 baseEnd_1341879 := by
    simpa [prefixWord, tailWord_1341879, baseEnd_1341879] using wordTrace_append hprefix tailTrace_1341879
  have hstable : (prefixWord ++ tailWord_1341879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341879).length < 2 ^ (prefixWord ++ tailWord_1341879).sum := by decide
  have hdescent : baseEnd_1341879 < baseStart_1341879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341942 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1341942 : Nat := 118140960795 + 1341942 * 2 ^ 59
def prefixEnd_1341942 : Nat := 4983230072969 + 3 ^ 40 * 1341942 * 2
def baseEnd_1341942 : Nat := 689061256455893879453527

theorem tailTrace_1341942 : CollatzResearch.WordTrace tailWord_1341942 prefixEnd_1341942 689061256455893879453527 := by
  unfold tailWord_1341942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059040356523799643270255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32629763802920529528216053 3059040356523799643270255)
  ·
    refine ⟨4588560534785699464905383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3059040356523799643270255 4588560534785699464905383)
    ·
      refine ⟨6882840802178549197358075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4588560534785699464905383 6882840802178549197358075)
      ·
        refine ⟨10324261203267823796037113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882840802178549197358075 10324261203267823796037113)
        ·
          refine ⟨7743195902450867847027835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10324261203267823796037113 7743195902450867847027835)
          ·
            refine ⟨11614793853676301770541753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743195902450867847027835 11614793853676301770541753)
            ·
              refine ⟨8711095390257226327906315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11614793853676301770541753 8711095390257226327906315)
              ·
                refine ⟨13066643085385839491859473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8711095390257226327906315 13066643085385839491859473)
                ·
                  refine ⟨9799982314039379618894605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13066643085385839491859473 9799982314039379618894605)
                  ·
                    refine ⟨3674993367764767357085477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9799982314039379618894605 3674993367764767357085477)
                    ·
                      refine ⟨689061256455893879453527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3674993367764767357085477 689061256455893879453527)
                      ·
                        rfl

theorem cell23_1341942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1341942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341942 prefixEnd_1341942 := by exact prefixLift 1341942
  have htrace : WordTrace (prefixWord ++ tailWord_1341942) baseStart_1341942 baseEnd_1341942 := by
    simpa [prefixWord, tailWord_1341942, baseEnd_1341942] using wordTrace_append hprefix tailTrace_1341942
  have hstable : (prefixWord ++ tailWord_1341942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341942).length < 2 ^ (prefixWord ++ tailWord_1341942).sum := by decide
  have hdescent : baseEnd_1341942 < baseStart_1341942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341953 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 2, 1, 3]
def baseStart_1341953 : Nat := 118140960795 + 1341953 * 2 ^ 59
def prefixEnd_1341953 : Nat := 4983230072969 + 3 ^ 40 * 1341953 * 2
def baseEnd_1341953 : Nat := 689066904743093336415977

theorem tailTrace_1341953 : CollatzResearch.WordTrace tailWord_1341953 prefixEnd_1341953 689066904743093336415977 := by
  unfold tailWord_1341953
  simp only [CollatzResearch.WordTrace]
  refine ⟨48945046907340943170974513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32630031271560628780649675 48945046907340943170974513)
  ·
    refine ⟨36708785180505707378230885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48945046907340943170974513 36708785180505707378230885)
    ·
      refine ⟨6882897221344820133418291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36708785180505707378230885 6882897221344820133418291)
      ·
        refine ⟨10324345832017230200127437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882897221344820133418291 10324345832017230200127437)
        ·
          refine ⟨3871629687006461325047789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10324345832017230200127437 3871629687006461325047789)
          ·
            refine ⟨1451861132627422996892921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3871629687006461325047789 1451861132627422996892921)
            ·
              refine ⟨1088895849470567247669691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451861132627422996892921 1088895849470567247669691)
              ·
                refine ⟨1633343774205850871504537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088895849470567247669691 1633343774205850871504537)
                ·
                  refine ⟨1225007830654388153628403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1633343774205850871504537 1225007830654388153628403)
                  ·
                    refine ⟨1837511745981582230442605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1225007830654388153628403 1837511745981582230442605)
                    ·
                      refine ⟨689066904743093336415977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1837511745981582230442605 689066904743093336415977)
                      ·
                        rfl

theorem cell23_1341953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_1341953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341953 prefixEnd_1341953 := by exact prefixLift 1341953
  have htrace : WordTrace (prefixWord ++ tailWord_1341953) baseStart_1341953 baseEnd_1341953 := by
    simpa [prefixWord, tailWord_1341953, baseEnd_1341953] using wordTrace_append hprefix tailTrace_1341953
  have hstable : (prefixWord ++ tailWord_1341953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341953).length < 2 ^ (prefixWord ++ tailWord_1341953).sum := by decide
  have hdescent : baseEnd_1341953 < baseStart_1341953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341955 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4]
def baseStart_1341955 : Nat := 118140960795 + 1341955 * 2 ^ 59
def prefixEnd_1341955 : Nat := 4983230072969 + 3 ^ 40 * 1341955 * 2
def baseEnd_1341955 : Nat := 689067931704402328590967

theorem tailTrace_1341955 : CollatzResearch.WordTrace tailWord_1341955 prefixEnd_1341955 689067931704402328590967 := by
  unfold tailWord_1341955
  simp only [CollatzResearch.WordTrace]
  refine ⟨48945119853333697512547319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32630079902222465008364879 48945119853333697512547319)
  ·
    refine ⟨73417679780000546268820979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48945119853333697512547319 73417679780000546268820979)
    ·
      refine ⟨110126519670000819403231469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73417679780000546268820979 110126519670000819403231469)
      ·
        refine ⟨41297444876250307276211801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110126519670000819403231469 41297444876250307276211801)
        ·
          refine ⟨30973083657187730457158851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41297444876250307276211801 30973083657187730457158851)
          ·
            refine ⟨46459625485781595685738277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30973083657187730457158851 46459625485781595685738277)
            ·
              refine ⟨8711179778584049191075927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46459625485781595685738277 8711179778584049191075927)
              ·
                refine ⟨13066769667876073786613891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8711179778584049191075927 13066769667876073786613891)
                ·
                  refine ⟨19600154501814110679920837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13066769667876073786613891 19600154501814110679920837)
                  ·
                    refine ⟨3675028969090145752485157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19600154501814110679920837 3675028969090145752485157)
                    ·
                      refine ⟨689067931704402328590967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3675028969090145752485157 689067931704402328590967)
                      ·
                        rfl

theorem cell23_1341955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_1341955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1341955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1341955 prefixEnd_1341955 := by exact prefixLift 1341955
  have htrace : WordTrace (prefixWord ++ tailWord_1341955) baseStart_1341955 baseEnd_1341955 := by
    simpa [prefixWord, tailWord_1341955, baseEnd_1341955] using wordTrace_append hprefix tailTrace_1341955
  have hstable : (prefixWord ++ tailWord_1341955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341955).length < 2 ^ (prefixWord ++ tailWord_1341955).sum := by decide
  have hdescent : baseEnd_1341955 < baseStart_1341955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342029 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1342029 : Nat := 118140960795 + 1342029 * 2 ^ 59
def prefixEnd_1342029 : Nat := 4983230072969 + 3 ^ 40 * 1342029 * 2
def baseEnd_1342029 : Nat := 229701976424278346355209

theorem tailTrace_1342029 : CollatzResearch.WordTrace tailWord_1342029 prefixEnd_1342029 229701976424278346355209 := by
  unfold tailWord_1342029
  simp only [CollatzResearch.WordTrace]
  refine ⟨48947818855065608150741141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32631879236710405433827427 48947818855065608150741141)
  ·
    refine ⟨2294429008831200382065991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48947818855065608150741141 2294429008831200382065991)
    ·
      refine ⟨3441643513246800573098987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294429008831200382065991 3441643513246800573098987)
      ·
        refine ⟨5162465269870200859648481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441643513246800573098987 5162465269870200859648481)
        ·
          refine ⟨3871848952402650644736361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5162465269870200859648481 3871848952402650644736361)
          ·
            refine ⟨2903886714301987983552271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3871848952402650644736361 2903886714301987983552271)
            ·
              refine ⟨4355830071452981975328407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903886714301987983552271 4355830071452981975328407)
              ·
                refine ⟨6533745107179472962992611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4355830071452981975328407 6533745107179472962992611)
                ·
                  refine ⟨9800617660769209444488917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6533745107179472962992611 9800617660769209444488917)
                  ·
                    refine ⟨229701976424278346355209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9800617660769209444488917 229701976424278346355209)
                    ·
                      rfl

theorem cell23_1342029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1342029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342029 prefixEnd_1342029 := by exact prefixLift 1342029
  have htrace : WordTrace (prefixWord ++ tailWord_1342029) baseStart_1342029 baseEnd_1342029 := by
    simpa [prefixWord, tailWord_1342029, baseEnd_1342029] using wordTrace_append hprefix tailTrace_1342029
  have hstable : (prefixWord ++ tailWord_1342029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342029).length < 2 ^ (prefixWord ++ tailWord_1342029).sum := by decide
  have hdescent : baseEnd_1342029 < baseStart_1342029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342032 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_1342032 : Nat := 118140960795 + 1342032 * 2 ^ 59
def prefixEnd_1342032 : Nat := 4983230072969 + 3 ^ 40 * 1342032 * 2
def baseEnd_1342032 : Nat := 689107469714798527328113

theorem tailTrace_1342032 : CollatzResearch.WordTrace tailWord_1342032 prefixEnd_1342032 689107469714798527328113 := by
  unfold tailWord_1342032
  simp only [CollatzResearch.WordTrace]
  refine ⟨24473964137027369831550175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32631952182703159775400233 24473964137027369831550175)
  ·
    refine ⟨36710946205541054747325263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24473964137027369831550175 36710946205541054747325263)
    ·
      refine ⟨55066419308311582120987895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36710946205541054747325263 55066419308311582120987895)
      ·
        refine ⟨82599628962467373181481843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55066419308311582120987895 82599628962467373181481843)
        ·
          refine ⟨123899443443701059772222765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82599628962467373181481843 123899443443701059772222765)
          ·
            refine ⟨46462291291387897414583537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123899443443701059772222765 46462291291387897414583537)
            ·
              refine ⟨34846718468540923060937653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46462291291387897414583537 34846718468540923060937653)
              ·
                refine ⟨3266879856425711536962905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34846718468540923060937653 3266879856425711536962905)
                ·
                  refine ⟨2450159892319283652722179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3266879856425711536962905 2450159892319283652722179)
                  ·
                    refine ⟨3675239838478925479083269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2450159892319283652722179 3675239838478925479083269)
                    ·
                      refine ⟨689107469714798527328113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3675239838478925479083269 689107469714798527328113)
                      ·
                        rfl

theorem cell23_1342032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_1342032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342032 prefixEnd_1342032 := by exact prefixLift 1342032
  have htrace : WordTrace (prefixWord ++ tailWord_1342032) baseStart_1342032 baseEnd_1342032 := by
    simpa [prefixWord, tailWord_1342032, baseEnd_1342032] using wordTrace_append hprefix tailTrace_1342032
  have hstable : (prefixWord ++ tailWord_1342032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342032).length < 2 ^ (prefixWord ++ tailWord_1342032).sum := by decide
  have hdescent : baseEnd_1342032 < baseStart_1342032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342049 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 2, 4, 2]
def baseStart_1342049 : Nat := 118140960795 + 1342049 * 2 ^ 59
def prefixEnd_1342049 : Nat := 4983230072969 + 3 ^ 40 * 1342049 * 2
def baseEnd_1342049 : Nat := 689116198885924960815535

theorem tailTrace_1342049 : CollatzResearch.WordTrace tailWord_1342049 prefixEnd_1342049 689116198885924960815535 := by
  unfold tailWord_1342049
  simp only [CollatzResearch.WordTrace]
  refine ⟨48948548314993151566469201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32632365543328767710979467 48948548314993151566469201)
  ·
    refine ⟨36711411236244863674851901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48948548314993151566469201 36711411236244863674851901)
    ·
      refine ⟨13766779213591823878069463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36711411236244863674851901 13766779213591823878069463)
      ·
        refine ⟨20650168820387735817104195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13766779213591823878069463 20650168820387735817104195)
        ·
          refine ⟨30975253230581603725656293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20650168820387735817104195 30975253230581603725656293)
          ·
            refine ⟨5807859980734050698560555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30975253230581603725656293 5807859980734050698560555)
            ·
              refine ⟨8711789971101076047840833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807859980734050698560555 8711789971101076047840833)
              ·
                refine ⟨6533842478325807035880625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8711789971101076047840833 6533842478325807035880625)
                ·
                  refine ⟨4900381858744355276910469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6533842478325807035880625 4900381858744355276910469)
                  ·
                    refine ⟨918821598514566614420713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4900381858744355276910469 918821598514566614420713)
                    ·
                      refine ⟨689116198885924960815535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918821598514566614420713 689116198885924960815535)
                      ·
                        rfl

theorem cell23_1342049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_1342049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342049 prefixEnd_1342049 := by exact prefixLift 1342049
  have htrace : WordTrace (prefixWord ++ tailWord_1342049) baseStart_1342049 baseEnd_1342049 := by
    simpa [prefixWord, tailWord_1342049, baseEnd_1342049] using wordTrace_append hprefix tailTrace_1342049
  have hstable : (prefixWord ++ tailWord_1342049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342049).length < 2 ^ (prefixWord ++ tailWord_1342049).sum := by decide
  have hdescent : baseEnd_1342049 < baseStart_1342049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342110 : List Nat := [4, 3, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1342110 : Nat := 118140960795 + 1342110 * 2 ^ 59
def prefixEnd_1342110 : Nat := 4983230072969 + 3 ^ 40 * 1342110 * 2
def baseEnd_1342110 : Nat := 229715840401949740717585

theorem tailTrace_1342110 : CollatzResearch.WordTrace tailWord_1342110 prefixEnd_1342110 229715840401949740717585 := by
  unfold tailWord_1342110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118846645971519873054973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32633848778514772656293189 6118846645971519873054973)
  ·
    refine ⟨2294567492239319952395615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6118846645971519873054973 2294567492239319952395615)
    ·
      refine ⟨3441851238358979928593423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294567492239319952395615 3441851238358979928593423)
      ·
        refine ⟨5162776857538469892890135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441851238358979928593423 5162776857538469892890135)
        ·
          refine ⟨7744165286307704839335203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162776857538469892890135 7744165286307704839335203)
          ·
            refine ⟨11616247929461557259002805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7744165286307704839335203 11616247929461557259002805)
            ·
              refine ⟨1089023243387020993031513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11616247929461557259002805 1089023243387020993031513)
              ·
                refine ⟨816767432540265744773635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089023243387020993031513 816767432540265744773635)
                ·
                  refine ⟨1225151148810398617160453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816767432540265744773635 1225151148810398617160453)
                  ·
                    refine ⟨229715840401949740717585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1225151148810398617160453 229715840401949740717585)
                    ·
                      rfl

theorem cell23_1342110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1342110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342110 prefixEnd_1342110 := by exact prefixLift 1342110
  have htrace : WordTrace (prefixWord ++ tailWord_1342110) baseStart_1342110 baseEnd_1342110 := by
    simpa [prefixWord, tailWord_1342110, baseEnd_1342110] using wordTrace_append hprefix tailTrace_1342110
  have hstable : (prefixWord ++ tailWord_1342110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342110).length < 2 ^ (prefixWord ++ tailWord_1342110).sum := by decide
  have hdescent : baseEnd_1342110 < baseStart_1342110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342162 : List Nat := [3, 2, 2, 2, 14]
def baseStart_1342162 : Nat := 118140960795 + 1342162 * 2 ^ 59
def prefixEnd_1342162 : Nat := 4983230072969 + 3 ^ 40 * 1342162 * 2
def baseEnd_1342162 : Nat := 945369303429194813035

theorem tailTrace_1342162 : CollatzResearch.WordTrace tailWord_1342162 prefixEnd_1342162 945369303429194813035 := by
  unfold tailWord_1342162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12238167440895942966333185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32635113175722514576888493 12238167440895942966333185)
  ·
    refine ⟨9178625580671957224749889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12238167440895942966333185 9178625580671957224749889)
    ·
      refine ⟨6883969185503967918562417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9178625580671957224749889 6883969185503967918562417)
      ·
        refine ⟨5162976889127975938921813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6883969185503967918562417 5162976889127975938921813)
        ·
          refine ⟨945369303429194813035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 5162976889127975938921813 945369303429194813035)
          ·
            rfl

theorem cell23_1342162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 14].length) (baseStart_1342162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342162 prefixEnd_1342162 := by exact prefixLift 1342162
  have htrace : WordTrace (prefixWord ++ tailWord_1342162) baseStart_1342162 baseEnd_1342162 := by
    simpa [prefixWord, tailWord_1342162, baseEnd_1342162] using wordTrace_append hprefix tailTrace_1342162
  have hstable : (prefixWord ++ tailWord_1342162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342162).length < 2 ^ (prefixWord ++ tailWord_1342162).sum := by decide
  have hdescent : baseEnd_1342162 < baseStart_1342162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342179 : List Nat := [1, 1, 1, 7, 1, 1, 3, 8]
def baseStart_1342179 : Nat := 118140960795 + 1342179 * 2 ^ 59
def prefixEnd_1342179 : Nat := 4983230072969 + 3 ^ 40 * 1342179 * 2
def baseEnd_1342179 : Nat := 25525294495222572303331

theorem tailTrace_1342179 : CollatzResearch.WordTrace tailWord_1342179 prefixEnd_1342179 25525294495222572303331 := by
  unfold tailWord_1342179
  simp only [CollatzResearch.WordTrace]
  refine ⟨48953289804522183768701591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32635526536348122512467727 48953289804522183768701591)
  ·
    refine ⟨73429934706783275653052387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48953289804522183768701591 73429934706783275653052387)
    ·
      refine ⟨110144902060174913479578581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73429934706783275653052387 110144902060174913479578581)
      ·
        refine ⟨2581521142035349534677623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 110144902060174913479578581 2581521142035349534677623)
        ·
          refine ⟨3872281713053024302016435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581521142035349534677623 3872281713053024302016435)
          ·
            refine ⟨5808422569579536453024653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872281713053024302016435 5808422569579536453024653)
            ·
              refine ⟨2178158463592326169884245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5808422569579536453024653 2178158463592326169884245)
              ·
                refine ⟨25525294495222572303331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2178158463592326169884245 25525294495222572303331)
                ·
                  rfl

theorem cell23_1342179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 8].length) (baseStart_1342179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342179 prefixEnd_1342179 := by exact prefixLift 1342179
  have htrace : WordTrace (prefixWord ++ tailWord_1342179) baseStart_1342179 baseEnd_1342179 := by
    simpa [prefixWord, tailWord_1342179, baseEnd_1342179] using wordTrace_append hprefix tailTrace_1342179
  have hstable : (prefixWord ++ tailWord_1342179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342179).length < 2 ^ (prefixWord ++ tailWord_1342179).sum := by decide
  have hdescent : baseEnd_1342179 < baseStart_1342179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342192 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 2, 7]
def baseStart_1342192 : Nat := 118140960795 + 1342192 * 2 ^ 59
def prefixEnd_1342192 : Nat := 4983230072969 + 3 ^ 40 * 1342192 * 2
def baseEnd_1342192 : Nat := 229729875539839300442459

theorem tailTrace_1342192 : CollatzResearch.WordTrace tailWord_1342192 prefixEnd_1342192 229729875539839300442459 := by
  unfold tailWord_1342192
  simp only [CollatzResearch.WordTrace]
  refine ⟨24476881976737543494462415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32635842635650057992616553 24476881976737543494462415)
  ·
    refine ⟨36715322965106315241693623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24476881976737543494462415 36715322965106315241693623)
    ·
      refine ⟨55072984447659472862540435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36715322965106315241693623 55072984447659472862540435)
      ·
        refine ⟨82609476671489209293810653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55072984447659472862540435 82609476671489209293810653)
        ·
          refine ⟨30978553751808453485178995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82609476671489209293810653 30978553751808453485178995)
          ·
            refine ⟨46467830627712680227768493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30978553751808453485178995 46467830627712680227768493)
            ·
              refine ⟨17425436485392255085413185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46467830627712680227768493 17425436485392255085413185)
              ·
                refine ⟨13069077364044191314059889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17425436485392255085413185 13069077364044191314059889)
                ·
                  refine ⟨9801808023033143485544917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13069077364044191314059889 9801808023033143485544917)
                  ·
                    refine ⟨229729875539839300442459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9801808023033143485544917 229729875539839300442459)
                    ·
                      rfl

theorem cell23_1342192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_1342192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342192 prefixEnd_1342192 := by exact prefixLift 1342192
  have htrace : WordTrace (prefixWord ++ tailWord_1342192) baseStart_1342192 baseEnd_1342192 := by
    simpa [prefixWord, tailWord_1342192, baseEnd_1342192] using wordTrace_append hprefix tailTrace_1342192
  have hstable : (prefixWord ++ tailWord_1342192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342192).length < 2 ^ (prefixWord ++ tailWord_1342192).sum := by decide
  have hdescent : baseEnd_1342192 < baseStart_1342192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342210 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_1342210 : Nat := 118140960795 + 1342210 * 2 ^ 59
def prefixEnd_1342210 : Nat := 4983230072969 + 3 ^ 40 * 1342210 * 2
def baseEnd_1342210 : Nat := 689198869271298830902295

theorem tailTrace_1342210 : CollatzResearch.WordTrace tailWord_1342210 prefixEnd_1342210 689198869271298830902295 := by
  unfold tailWord_1342210
  simp only [CollatzResearch.WordTrace]
  refine ⟨12238605116852469015770021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32636280311606584042053389 12238605116852469015770021)
  ·
    refine ⟨2294738459409837940456879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12238605116852469015770021 2294738459409837940456879)
    ·
      refine ⟨3442107689114756910685319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2294738459409837940456879 3442107689114756910685319)
      ·
        refine ⟨5163161533672135366027979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442107689114756910685319 5163161533672135366027979)
        ·
          refine ⟨7744742300508203049041969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163161533672135366027979 7744742300508203049041969)
          ·
            refine ⟨5808556725381152286781477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7744742300508203049041969 5808556725381152286781477)
            ·
              refine ⟨1089104386008966053771527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5808556725381152286781477 1089104386008966053771527)
              ·
                refine ⟨1633656579013449080657291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089104386008966053771527 1633656579013449080657291)
                ·
                  refine ⟨2450484868520173620985937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633656579013449080657291 2450484868520173620985937)
                  ·
                    refine ⟨1837863651390130215739453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2450484868520173620985937 1837863651390130215739453)
                    ·
                      refine ⟨689198869271298830902295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1837863651390130215739453 689198869271298830902295)
                      ·
                        rfl

theorem cell23_1342210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_1342210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342210 prefixEnd_1342210 := by exact prefixLift 1342210
  have htrace : WordTrace (prefixWord ++ tailWord_1342210) baseStart_1342210 baseEnd_1342210 := by
    simpa [prefixWord, tailWord_1342210, baseEnd_1342210] using wordTrace_append hprefix tailTrace_1342210
  have hstable : (prefixWord ++ tailWord_1342210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342210).length < 2 ^ (prefixWord ++ tailWord_1342210).sum := by decide
  have hdescent : baseEnd_1342210 < baseStart_1342210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342239 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 2, 6]
def baseStart_1342239 : Nat := 118140960795 + 1342239 * 2 ^ 59
def prefixEnd_1342239 : Nat := 4983230072969 + 3 ^ 40 * 1342239 * 2
def baseEnd_1342239 : Nat := 229737920070093072479887

theorem tailTrace_1342239 : CollatzResearch.WordTrace tailWord_1342239 prefixEnd_1342239 229737920070093072479887 := by
  unfold tailWord_1342239
  simp only [CollatzResearch.WordTrace]
  refine ⟨48955478184304814015885771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32636985456203209343923847 48955478184304814015885771)
  ·
    refine ⟨73433217276457221023828657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48955478184304814015885771 73433217276457221023828657)
    ·
      refine ⟨55074912957342915767871493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73433217276457221023828657 55074912957342915767871493)
      ·
        refine ⟨10326546179501796706475905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55074912957342915767871493 10326546179501796706475905)
        ·
          refine ⟨7744909634626347529856929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10326546179501796706475905 7744909634626347529856929)
          ·
            refine ⟨5808682225969760647392697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7744909634626347529856929 5808682225969760647392697)
            ·
              refine ⟨4356511669477320485544523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5808682225969760647392697 4356511669477320485544523)
              ·
                refine ⟨6534767504215980728316785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356511669477320485544523 6534767504215980728316785)
                ·
                  refine ⟨4901075628161985546237589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6534767504215980728316785 4901075628161985546237589)
                  ·
                    refine ⟨229737920070093072479887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4901075628161985546237589 229737920070093072479887)
                    ·
                      rfl

theorem cell23_1342239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_1342239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342239 prefixEnd_1342239 := by exact prefixLift 1342239
  have htrace : WordTrace (prefixWord ++ tailWord_1342239) baseStart_1342239 baseEnd_1342239 := by
    simpa [prefixWord, tailWord_1342239, baseEnd_1342239] using wordTrace_append hprefix tailTrace_1342239
  have hstable : (prefixWord ++ tailWord_1342239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342239).length < 2 ^ (prefixWord ++ tailWord_1342239).sum := by decide
  have hdescent : baseEnd_1342239 < baseStart_1342239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342240 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1342240 : Nat := 118140960795 + 1342240 * 2 ^ 59
def prefixEnd_1342240 : Nat := 4983230072969 + 3 ^ 40 * 1342240 * 2
def baseEnd_1342240 : Nat := 689214273690933713527157

theorem tailTrace_1342240 : CollatzResearch.WordTrace tailWord_1342240 prefixEnd_1342240 689214273690933713527157 := by
  unfold tailWord_1342240
  simp only [CollatzResearch.WordTrace]
  refine ⟨24477757328650595593336087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32637009771534127457781449 24477757328650595593336087)
  ·
    refine ⟨36716635992975893390004131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24477757328650595593336087 36716635992975893390004131)
    ·
      refine ⟨55074953989463840085006197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36716635992975893390004131 55074953989463840085006197)
      ·
        refine ⟨5163276936512235007969331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55074953989463840085006197 5163276936512235007969331)
        ·
          refine ⟨7744915404768352511953997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163276936512235007969331 7744915404768352511953997)
          ·
            refine ⟨2904343276788132191982749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7744915404768352511953997 2904343276788132191982749)
            ·
              refine ⟨1089128728795549571993531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2904343276788132191982749 1089128728795549571993531)
              ·
                refine ⟨1633693093193324357990297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089128728795549571993531 1633693093193324357990297)
                ·
                  refine ⟨1225269819894993268492723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1633693093193324357990297 1225269819894993268492723)
                  ·
                    refine ⟨1837904729842489902739085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1225269819894993268492723 1837904729842489902739085)
                    ·
                      refine ⟨689214273690933713527157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1837904729842489902739085 689214273690933713527157)
                      ·
                        rfl

theorem cell23_1342240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1342240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342240 prefixEnd_1342240 := by exact prefixLift 1342240
  have htrace : WordTrace (prefixWord ++ tailWord_1342240) baseStart_1342240 baseEnd_1342240 := by
    simpa [prefixWord, tailWord_1342240, baseEnd_1342240] using wordTrace_append hprefix tailTrace_1342240
  have hstable : (prefixWord ++ tailWord_1342240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342240).length < 2 ^ (prefixWord ++ tailWord_1342240).sum := by decide
  have hdescent : baseEnd_1342240 < baseStart_1342240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342266 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5]
def baseStart_1342266 : Nat := 118140960795 + 1342266 * 2 ^ 59
def prefixEnd_1342266 : Nat := 4983230072969 + 3 ^ 40 * 1342266 * 2
def baseEnd_1342266 : Nat := 689227624187950611802037

theorem tailTrace_1342266 : CollatzResearch.WordTrace tailWord_1342266 prefixEnd_1342266 689227624187950611802037 := by
  unfold tailWord_1342266
  simp only [CollatzResearch.WordTrace]
  refine ⟨12239115738801749406779663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32637641970137998418079101 12239115738801749406779663)
  ·
    refine ⟨18358673608202624110169495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12239115738801749406779663 18358673608202624110169495)
    ·
      refine ⟨27538010412303936165254243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18358673608202624110169495 27538010412303936165254243)
      ·
        refine ⟨41307015618455904247881365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27538010412303936165254243 41307015618455904247881365)
        ·
          refine ⟨1936266357115120511619439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41307015618455904247881365 1936266357115120511619439)
          ·
            refine ⟨2904399535672680767429159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936266357115120511619439 2904399535672680767429159)
            ·
              refine ⟨4356599303509021151143739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904399535672680767429159 4356599303509021151143739)
              ·
                refine ⟨6534898955263531726715609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356599303509021151143739 6534898955263531726715609)
                ·
                  refine ⟨4901174216447648795036707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6534898955263531726715609 4901174216447648795036707)
                  ·
                    refine ⟨7351761324671473192555061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4901174216447648795036707 7351761324671473192555061)
                    ·
                      refine ⟨689227624187950611802037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7351761324671473192555061 689227624187950611802037)
                      ·
                        rfl

theorem cell23_1342266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_1342266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342266 prefixEnd_1342266 := by exact prefixLift 1342266
  have htrace : WordTrace (prefixWord ++ tailWord_1342266) baseStart_1342266 baseEnd_1342266 := by
    simpa [prefixWord, tailWord_1342266, baseEnd_1342266] using wordTrace_append hprefix tailTrace_1342266
  have hstable : (prefixWord ++ tailWord_1342266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342266).length < 2 ^ (prefixWord ++ tailWord_1342266).sum := by decide
  have hdescent : baseEnd_1342266 < baseStart_1342266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342286 : List Nat := [4, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_1342286 : Nat := 118140960795 + 1342286 * 2 ^ 59
def prefixEnd_1342286 : Nat := 4983230072969 + 3 ^ 40 * 1342286 * 2
def baseEnd_1342286 : Nat := 76581988200115614839105

theorem tailTrace_1342286 : CollatzResearch.WordTrace tailWord_1342286 prefixEnd_1342286 76581988200115614839105 := by
  unfold tailWord_1342286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119649051891817630355839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32638128276756360695231141 6119649051891817630355839)
  ·
    refine ⟨9179473577837726445533759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6119649051891817630355839 9179473577837726445533759)
    ·
      refine ⟨13769210366756589668300639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9179473577837726445533759 13769210366756589668300639)
      ·
        refine ⟨20653815550134884502450959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13769210366756589668300639 20653815550134884502450959)
        ·
          refine ⟨30980723325202326753676439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20653815550134884502450959 30980723325202326753676439)
          ·
            refine ⟨46471084987803490130514659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30980723325202326753676439 46471084987803490130514659)
            ·
              refine ⟨69706627481705235195771989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46471084987803490130514659 69706627481705235195771989)
              ·
                refine ⟨816874540801233224950453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 69706627481705235195771989 816874540801233224950453)
                ·
                  refine ⟨76581988200115614839105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 816874540801233224950453 76581988200115614839105)
                  ·
                    rfl

theorem cell23_1342286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_1342286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342286 prefixEnd_1342286 := by exact prefixLift 1342286
  have htrace : WordTrace (prefixWord ++ tailWord_1342286) baseStart_1342286 baseEnd_1342286 := by
    simpa [prefixWord, tailWord_1342286, baseEnd_1342286] using wordTrace_append hprefix tailTrace_1342286
  have hstable : (prefixWord ++ tailWord_1342286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342286).length < 2 ^ (prefixWord ++ tailWord_1342286).sum := by decide
  have hdescent : baseEnd_1342286 < baseStart_1342286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342297 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 2, 2, 2]
def baseStart_1342297 : Nat := 118140960795 + 1342297 * 2 ^ 59
def prefixEnd_1342297 : Nat := 4983230072969 + 3 ^ 40 * 1342297 * 2
def baseEnd_1342297 : Nat := 689243542088239990514395

theorem tailTrace_1342297 : CollatzResearch.WordTrace tailWord_1342297 prefixEnd_1342297 689243542088239990514395 := by
  unfold tailWord_1342297
  simp only [CollatzResearch.WordTrace]
  refine ⟨48957593618094689921497145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32638395745396459947664763 48957593618094689921497145)
  ·
    refine ⟨36718195213571017441122859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48957593618094689921497145 36718195213571017441122859)
    ·
      refine ⟨55077292820356526161684289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36718195213571017441122859 55077292820356526161684289)
      ·
        refine ⟨41307969615267394621263217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55077292820356526161684289 41307969615267394621263217)
        ·
          refine ⟨30980977211450545965947413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41307969615267394621263217 30980977211450545965947413)
          ·
            refine ⟨1452233306786744342153785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30980977211450545965947413 1452233306786744342153785)
            ·
              refine ⟨1089174980090058256615339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452233306786744342153785 1089174980090058256615339)
              ·
                refine ⟨1633762470135087384923009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089174980090058256615339 1633762470135087384923009)
                ·
                  refine ⟨1225321852601315538692257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1633762470135087384923009 1225321852601315538692257)
                  ·
                    refine ⟨918991389450986654019193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1225321852601315538692257 918991389450986654019193)
                    ·
                      refine ⟨689243542088239990514395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 918991389450986654019193 689243542088239990514395)
                      ·
                        rfl

theorem cell23_1342297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_1342297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342297 prefixEnd_1342297 := by exact prefixLift 1342297
  have htrace : WordTrace (prefixWord ++ tailWord_1342297) baseStart_1342297 baseEnd_1342297 := by
    simpa [prefixWord, tailWord_1342297, baseEnd_1342297] using wordTrace_append hprefix tailTrace_1342297
  have hstable : (prefixWord ++ tailWord_1342297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342297).length < 2 ^ (prefixWord ++ tailWord_1342297).sum := by decide
  have hdescent : baseEnd_1342297 < baseStart_1342297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342316 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_1342316 : Nat := 118140960795 + 1342316 * 2 ^ 59
def prefixEnd_1342316 : Nat := 4983230072969 + 3 ^ 40 * 1342316 * 2
def baseEnd_1342316 : Nat := 229751099406891805392269

theorem tailTrace_1342316 : CollatzResearch.WordTrace tailWord_1342316 prefixEnd_1342316 229751099406891805392269 := by
  unfold tailWord_1342316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24479143302512928083219401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32638857736683904110959201 24479143302512928083219401)
  ·
    refine ⟨18359357476884696062414551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24479143302512928083219401 18359357476884696062414551)
    ·
      refine ⟨27539036215327044093621827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18359357476884696062414551 27539036215327044093621827)
      ·
        refine ⟨41308554322990566140432741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27539036215327044093621827 41308554322990566140432741)
        ·
          refine ⟨7745353935560731151331139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41308554322990566140432741 7745353935560731151331139)
          ·
            refine ⟨11618030903341096726996709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7745353935560731151331139 11618030903341096726996709)
            ·
              refine ⟨2178380794376455636311883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11618030903341096726996709 2178380794376455636311883)
              ·
                refine ⟨3267571191564683454467825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178380794376455636311883 3267571191564683454467825)
                ·
                  refine ⟨2450678393673512590850869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3267571191564683454467825 2450678393673512590850869)
                  ·
                    refine ⟨229751099406891805392269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2450678393673512590850869 229751099406891805392269)
                    ·
                      rfl

theorem cell23_1342316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_1342316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342316 prefixEnd_1342316 := by exact prefixLift 1342316
  have htrace : WordTrace (prefixWord ++ tailWord_1342316) baseStart_1342316 baseEnd_1342316 := by
    simpa [prefixWord, tailWord_1342316, baseEnd_1342316] using wordTrace_append hprefix tailTrace_1342316
  have hstable : (prefixWord ++ tailWord_1342316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342316).length < 2 ^ (prefixWord ++ tailWord_1342316).sum := by decide
  have hdescent : baseEnd_1342316 < baseStart_1342316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342319 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 4]
def baseStart_1342319 : Nat := 118140960795 + 1342319 * 2 ^ 59
def prefixEnd_1342319 : Nat := 4983230072969 + 3 ^ 40 * 1342319 * 2
def baseEnd_1342319 : Nat := 689254838662638904439293

theorem tailTrace_1342319 : CollatzResearch.WordTrace tailWord_1342319 prefixEnd_1342319 689254838662638904439293 := by
  unfold tailWord_1342319
  simp only [CollatzResearch.WordTrace]
  refine ⟨48958396024014987678798011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32638930682676658452532007 48958396024014987678798011)
  ·
    refine ⟨73437594036022481518197017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48958396024014987678798011 73437594036022481518197017)
    ·
      refine ⟨55078195527016861138647763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73437594036022481518197017 55078195527016861138647763)
      ·
        refine ⟨82617293290525291707971645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55078195527016861138647763 82617293290525291707971645)
        ·
          refine ⟨30981484983946984390489367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82617293290525291707971645 30981484983946984390489367)
          ·
            refine ⟨46472227475920476585734051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30981484983946984390489367 46472227475920476585734051)
            ·
              refine ⟨69708341213880714878601077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46472227475920476585734051 69708341213880714878601077)
              ·
                refine ⟨6535156988801317019868851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69708341213880714878601077 6535156988801317019868851)
                ·
                  refine ⟨9802735483201975529803277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535156988801317019868851 9802735483201975529803277)
                  ·
                    refine ⟨3676025806200740823676229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9802735483201975529803277 3676025806200740823676229)
                    ·
                      refine ⟨689254838662638904439293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3676025806200740823676229 689254838662638904439293)
                      ·
                        rfl

theorem cell23_1342319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 4].length) (baseStart_1342319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342319 prefixEnd_1342319 := by exact prefixLift 1342319
  have htrace : WordTrace (prefixWord ++ tailWord_1342319) baseStart_1342319 baseEnd_1342319 := by
    simpa [prefixWord, tailWord_1342319, baseEnd_1342319] using wordTrace_append hprefix tailTrace_1342319
  have hstable : (prefixWord ++ tailWord_1342319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342319).length < 2 ^ (prefixWord ++ tailWord_1342319).sum := by decide
  have hdescent : baseEnd_1342319 < baseStart_1342319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342339 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1342339 : Nat := 118140960795 + 1342339 * 2 ^ 59
def prefixEnd_1342339 : Nat := 4983230072969 + 3 ^ 40 * 1342339 * 2
def baseEnd_1342339 : Nat := 689265108275728826189201

theorem tailTrace_1342339 : CollatzResearch.WordTrace tailWord_1342339 prefixEnd_1342339 689265108275728826189201 := by
  unfold tailWord_1342339
  simp only [CollatzResearch.WordTrace]
  refine ⟨48959125483942531094526071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32639416989295020729684047 48959125483942531094526071)
  ·
    refine ⟨73438688225913796641789107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48959125483942531094526071 73438688225913796641789107)
    ·
      refine ⟨110158032338870694962683661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73438688225913796641789107 110158032338870694962683661)
      ·
        refine ⟨41309262127076510611006373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110158032338870694962683661 41309262127076510611006373)
        ·
          refine ⟨7745486648826845739563695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41309262127076510611006373 7745486648826845739563695)
          ·
            refine ⟨11618229973240268609345543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7745486648826845739563695 11618229973240268609345543)
            ·
              refine ⟨17427344959860402914018315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11618229973240268609345543 17427344959860402914018315)
              ·
                refine ⟨26141017439790604371027473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17427344959860402914018315 26141017439790604371027473)
                ·
                  refine ⟨19605763079842953278270605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26141017439790604371027473 19605763079842953278270605)
                  ·
                    refine ⟨7352161154941107479351477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19605763079842953278270605 7352161154941107479351477)
                    ·
                      refine ⟨689265108275728826189201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7352161154941107479351477 689265108275728826189201)
                      ·
                        rfl

theorem cell23_1342339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1342339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342339 prefixEnd_1342339 := by exact prefixLift 1342339
  have htrace : WordTrace (prefixWord ++ tailWord_1342339) baseStart_1342339 baseEnd_1342339 := by
    simpa [prefixWord, tailWord_1342339, baseEnd_1342339] using wordTrace_append hprefix tailTrace_1342339
  have hstable : (prefixWord ++ tailWord_1342339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342339).length < 2 ^ (prefixWord ++ tailWord_1342339).sum := by decide
  have hdescent : baseEnd_1342339 < baseStart_1342339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342370 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1342370 : Nat := 118140960795 + 1342370 * 2 ^ 59
def prefixEnd_1342370 : Nat := 4983230072969 + 3 ^ 40 * 1342370 * 2
def baseEnd_1342370 : Nat := 689281026176018204901559

theorem tailTrace_1342370 : CollatzResearch.WordTrace tailWord_1342370 prefixEnd_1342370 689281026176018204901559 := by
  unfold tailWord_1342370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240064036707555847226141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32640170764553482259269709 12240064036707555847226141)
  ·
    refine ⟨4590024013765333442709803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12240064036707555847226141 4590024013765333442709803)
    ·
      refine ⟨6885036020648000164064705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590024013765333442709803 6885036020648000164064705)
      ·
        refine ⟨5163777015486000123048529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6885036020648000164064705 5163777015486000123048529)
        ·
          refine ⟨3872832761614500092286397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5163777015486000123048529 3872832761614500092286397)
          ·
            refine ⟨1452312285605437534607399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3872832761614500092286397 1452312285605437534607399)
            ·
              refine ⟨2178468428408156301911099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452312285605437534607399 2178468428408156301911099)
              ·
                refine ⟨3267702642612234452866649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178468428408156301911099 3267702642612234452866649)
                ·
                  refine ⟨2450776981959175839649987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3267702642612234452866649 2450776981959175839649987)
                  ·
                    refine ⟨3676165472938763759474981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2450776981959175839649987 3676165472938763759474981)
                    ·
                      refine ⟨689281026176018204901559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3676165472938763759474981 689281026176018204901559)
                      ·
                        rfl

theorem cell23_1342370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1342370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342370 prefixEnd_1342370 := by exact prefixLift 1342370
  have htrace : WordTrace (prefixWord ++ tailWord_1342370) baseStart_1342370 baseEnd_1342370 := by
    simpa [prefixWord, tailWord_1342370, baseEnd_1342370] using wordTrace_append hprefix tailTrace_1342370
  have hstable : (prefixWord ++ tailWord_1342370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342370).length < 2 ^ (prefixWord ++ tailWord_1342370).sum := by decide
  have hdescent : baseEnd_1342370 < baseStart_1342370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342393 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 6]
def baseStart_1342393 : Nat := 118140960795 + 1342393 * 2 ^ 59
def prefixEnd_1342393 : Nat := 4983230072969 + 3 ^ 40 * 1342393 * 2
def baseEnd_1342393 : Nat := 76588092914563512768217

theorem tailTrace_1342393 : CollatzResearch.WordTrace tailWord_1342393 prefixEnd_1342393 76588092914563512768217 := by
  unfold tailWord_1342393
  simp only [CollatzResearch.WordTrace]
  refine ⟨48961095025746898316991833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32640730017164598877994555 48961095025746898316991833)
  ·
    refine ⟨36720821269310173737743875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48961095025746898316991833 36720821269310173737743875)
    ·
      refine ⟨55081231903965260606615813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36720821269310173737743875 55081231903965260606615813)
      ·
        refine ⟨10327730981993486363740465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55081231903965260606615813 10327730981993486363740465)
        ·
          refine ⟨7745798236495114772805349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10327730981993486363740465 7745798236495114772805349)
          ·
            refine ⟨1452337169342834019901003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7745798236495114772805349 1452337169342834019901003)
            ·
              refine ⟨2178505754014251029851505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452337169342834019901003 2178505754014251029851505)
              ·
                refine ⟨1633879315510688272388629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178505754014251029851505 1633879315510688272388629)
                ·
                  refine ⟨76588092914563512768217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1633879315510688272388629 76588092914563512768217)
                  ·
                    rfl

theorem cell23_1342393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 6].length) (baseStart_1342393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342393 prefixEnd_1342393 := by exact prefixLift 1342393
  have htrace : WordTrace (prefixWord ++ tailWord_1342393) baseStart_1342393 baseEnd_1342393 := by
    simpa [prefixWord, tailWord_1342393, baseEnd_1342393] using wordTrace_append hprefix tailTrace_1342393
  have hstable : (prefixWord ++ tailWord_1342393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342393).length < 2 ^ (prefixWord ++ tailWord_1342393).sum := by decide
  have hdescent : baseEnd_1342393 < baseStart_1342393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342399 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1342399 : Nat := 118140960795 + 1342399 * 2 ^ 59
def prefixEnd_1342399 : Nat := 4983230072969 + 3 ^ 40 * 1342399 * 2
def baseEnd_1342399 : Nat := 689295917114998591438925

theorem tailTrace_1342399 : CollatzResearch.WordTrace tailWord_1342399 prefixEnd_1342399 689295917114998591438925 := by
  unfold tailWord_1342399
  simp only [CollatzResearch.WordTrace]
  refine ⟨48961313863725161341710251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32640875909150107561140167 48961313863725161341710251)
  ·
    refine ⟨73441970795587742012565377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48961313863725161341710251 73441970795587742012565377)
    ·
      refine ⟨55081478096690806509424033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73441970795587742012565377 55081478096690806509424033)
      ·
        refine ⟨41311108572518104882068025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55081478096690806509424033 41311108572518104882068025)
        ·
          refine ⟨30983331429388578661551019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41311108572518104882068025 30983331429388578661551019)
          ·
            refine ⟨46474997144082867992326529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30983331429388578661551019 46474997144082867992326529)
            ·
              refine ⟨34856247858062150994244897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46474997144082867992326529 34856247858062150994244897)
              ·
                refine ⟨26142185893546613245683673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34856247858062150994244897 26142185893546613245683673)
                ·
                  refine ⟨19606639420159959934262755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26142185893546613245683673 19606639420159959934262755)
                  ·
                    refine ⟨29409959130239939901394133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19606639420159959934262755 29409959130239939901394133)
                    ·
                      refine ⟨689295917114998591438925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29409959130239939901394133 689295917114998591438925)
                      ·
                        rfl

theorem cell23_1342399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1342399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342399 prefixEnd_1342399 := by exact prefixLift 1342399
  have htrace : WordTrace (prefixWord ++ tailWord_1342399) baseStart_1342399 baseEnd_1342399 := by
    simpa [prefixWord, tailWord_1342399, baseEnd_1342399] using wordTrace_append hprefix tailTrace_1342399
  have hstable : (prefixWord ++ tailWord_1342399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342399).length < 2 ^ (prefixWord ++ tailWord_1342399).sum := by decide
  have hdescent : baseEnd_1342399 < baseStart_1342399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342420 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1342420 : Nat := 118140960795 + 1342420 * 2 ^ 59
def prefixEnd_1342420 : Nat := 4983230072969 + 3 ^ 40 * 1342420 * 2
def baseEnd_1342420 : Nat := 689306700208743009276329

theorem tailTrace_1342420 : CollatzResearch.WordTrace tailWord_1342420 prefixEnd_1342420 689306700208743009276329 := by
  unfold tailWord_1342420
  simp only [CollatzResearch.WordTrace]
  refine ⟨24481039898324540964112357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32641386531099387952149809 24481039898324540964112357)
  ·
    refine ⟨4590194980935851430771067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24481039898324540964112357 4590194980935851430771067)
    ·
      refine ⟨6885292471403777146156601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590194980935851430771067 6885292471403777146156601)
      ·
        refine ⟨5163969353552832859617451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6885292471403777146156601 5163969353552832859617451)
        ·
          refine ⟨7745954030329249289426177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163969353552832859617451 7745954030329249289426177)
          ·
            refine ⟨5809465522746936967069633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7745954030329249289426177 5809465522746936967069633)
            ·
              refine ⟨4357099142060202725302225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5809465522746936967069633 4357099142060202725302225)
              ·
                refine ⟨3267824356545152043976669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357099142060202725302225 3267824356545152043976669)
                ·
                  refine ⟨1225434133704432016491251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3267824356545152043976669 1225434133704432016491251)
                  ·
                    refine ⟨1838151200556648024736877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1225434133704432016491251 1838151200556648024736877)
                    ·
                      refine ⟨689306700208743009276329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1838151200556648024736877 689306700208743009276329)
                      ·
                        rfl

theorem cell23_1342420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1342420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342420 prefixEnd_1342420 := by exact prefixLift 1342420
  have htrace : WordTrace (prefixWord ++ tailWord_1342420) baseStart_1342420 baseEnd_1342420 := by
    simpa [prefixWord, tailWord_1342420, baseEnd_1342420] using wordTrace_append hprefix tailTrace_1342420
  have hstable : (prefixWord ++ tailWord_1342420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342420).length < 2 ^ (prefixWord ++ tailWord_1342420).sum := by decide
  have hdescent : baseEnd_1342420 < baseStart_1342420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342497 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_1342497 : Nat := 118140960795 + 1342497 * 2 ^ 59
def prefixEnd_1342497 : Nat := 4983230072969 + 3 ^ 40 * 1342497 * 2
def baseEnd_1342497 : Nat := 689346238219139208013475

theorem tailTrace_1342497 : CollatzResearch.WordTrace tailWord_1342497 prefixEnd_1342497 689346238219139208013475 := by
  unfold tailWord_1342497
  simp only [CollatzResearch.WordTrace]
  refine ⟨48964888217370124078777745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32643258811580082719185163 48964888217370124078777745)
  ·
    refine ⟨36723666163027593059083309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48964888217370124078777745 36723666163027593059083309)
    ·
      refine ⟨13771374811135347397156241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36723666163027593059083309 13771374811135347397156241)
      ·
        refine ⟨10328531108351510547867181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13771374811135347397156241 10328531108351510547867181)
        ·
          refine ⟨3873199165631816455450193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10328531108351510547867181 3873199165631816455450193)
          ·
            refine ⟨2904899374223862341587645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3873199165631816455450193 2904899374223862341587645)
            ·
              refine ⟨1089337265333948378095367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2904899374223862341587645 1089337265333948378095367)
              ·
                refine ⟨1634005898000922567143051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089337265333948378095367 1634005898000922567143051)
                ·
                  refine ⟨2451008847001383850714577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634005898000922567143051 2451008847001383850714577)
                  ·
                    refine ⟨1838256635251037888035933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2451008847001383850714577 1838256635251037888035933)
                    ·
                      refine ⟨689346238219139208013475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1838256635251037888035933 689346238219139208013475)
                      ·
                        rfl

theorem cell23_1342497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_1342497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342497 prefixEnd_1342497 := by exact prefixLift 1342497
  have htrace : WordTrace (prefixWord ++ tailWord_1342497) baseStart_1342497 baseEnd_1342497 := by
    simpa [prefixWord, tailWord_1342497, baseEnd_1342497] using wordTrace_append hprefix tailTrace_1342497
  have hstable : (prefixWord ++ tailWord_1342497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342497).length < 2 ^ (prefixWord ++ tailWord_1342497).sum := by decide
  have hdescent : baseEnd_1342497 < baseStart_1342497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342520 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 3, 3, 2]
def baseStart_1342520 : Nat := 118140960795 + 1342520 * 2 ^ 59
def prefixEnd_1342520 : Nat := 4983230072969 + 3 ^ 40 * 1342520 * 2
def baseEnd_1342520 : Nat := 689358048274192618025869

theorem tailTrace_1342520 : CollatzResearch.WordTrace tailWord_1342520 prefixEnd_1342520 689358048274192618025869 := by
  unfold tailWord_1342520
  simp only [CollatzResearch.WordTrace]
  refine ⟨24482863548143399503432507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32643818064191199337910009 24482863548143399503432507)
  ·
    refine ⟨36724295322215099255148761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24482863548143399503432507 36724295322215099255148761)
    ·
      refine ⟨27543221491661324441361571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36724295322215099255148761 27543221491661324441361571)
      ·
        refine ⟨41314832237491986662042357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27543221491661324441361571 41314832237491986662042357)
        ·
          refine ⟨3873265522264873749566471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41314832237491986662042357 3873265522264873749566471)
          ·
            refine ⟨5809898283397310624349707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873265522264873749566471 5809898283397310624349707)
            ·
              refine ⟨8714847425095965936524561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5809898283397310624349707 8714847425095965936524561)
              ·
                refine ⟨6536135568821974452393421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8714847425095965936524561 6536135568821974452393421)
                ·
                  refine ⟨2451050838308240419647533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6536135568821974452393421 2451050838308240419647533)
                  ·
                    refine ⟨919144064365590157367825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2451050838308240419647533 919144064365590157367825)
                    ·
                      refine ⟨689358048274192618025869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919144064365590157367825 689358048274192618025869)
                      ·
                        rfl

theorem cell23_1342520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_1342520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342520 prefixEnd_1342520 := by exact prefixLift 1342520
  have htrace : WordTrace (prefixWord ++ tailWord_1342520) baseStart_1342520 baseEnd_1342520 := by
    simpa [prefixWord, tailWord_1342520, baseEnd_1342520] using wordTrace_append hprefix tailTrace_1342520
  have hstable : (prefixWord ++ tailWord_1342520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342520).length < 2 ^ (prefixWord ++ tailWord_1342520).sum := by decide
  have hdescent : baseEnd_1342520 < baseStart_1342520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342567 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_1342567 : Nat := 118140960795 + 1342567 * 2 ^ 59
def prefixEnd_1342567 : Nat := 4983230072969 + 3 ^ 40 * 1342567 * 2
def baseEnd_1342567 : Nat := 689382181864953934138153

theorem tailTrace_1342567 : CollatzResearch.WordTrace tailWord_1342567 prefixEnd_1342567 689382181864953934138153 := by
  unfold tailWord_1342567
  simp only [CollatzResearch.WordTrace]
  refine ⟨48967441327116526033825955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32644960884744350689217303 48967441327116526033825955)
  ·
    refine ⟨73451161990674789050738933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48967441327116526033825955 73451161990674789050738933)
    ·
      refine ⟨6886046436625761473506775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73451161990674789050738933 6886046436625761473506775)
      ·
        refine ⟨10329069654938642210260163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886046436625761473506775 10329069654938642210260163)
        ·
          refine ⟨15493604482407963315390245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10329069654938642210260163 15493604482407963315390245)
          ·
            refine ⟨2905050840451493121635671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15493604482407963315390245 2905050840451493121635671)
            ·
              refine ⟨4357576260677239682453507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905050840451493121635671 4357576260677239682453507)
              ·
                refine ⟨6536364391015859523680261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4357576260677239682453507 6536364391015859523680261)
                ·
                  refine ⟨1225568323315473660690049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6536364391015859523680261 1225568323315473660690049)
                  ·
                    refine ⟨919176242486605245517537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1225568323315473660690049 919176242486605245517537)
                    ·
                      refine ⟨689382181864953934138153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 919176242486605245517537 689382181864953934138153)
                      ·
                        rfl

theorem cell23_1342567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_1342567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342567 prefixEnd_1342567 := by exact prefixLift 1342567
  have htrace : WordTrace (prefixWord ++ tailWord_1342567) baseStart_1342567 baseEnd_1342567 := by
    simpa [prefixWord, tailWord_1342567, baseEnd_1342567] using wordTrace_append hprefix tailTrace_1342567
  have hstable : (prefixWord ++ tailWord_1342567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342567).length < 2 ^ (prefixWord ++ tailWord_1342567).sum := by decide
  have hdescent : baseEnd_1342567 < baseStart_1342567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342573 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 7]
def baseStart_1342573 : Nat := 118140960795 + 1342573 * 2 ^ 59
def prefixEnd_1342573 : Nat := 4983230072969 + 3 ^ 40 * 1342573 * 2
def baseEnd_1342573 : Nat := 76598362527653434518125

theorem tailTrace_1342573 : CollatzResearch.WordTrace tailWord_1342573 prefixEnd_1342573 76598362527653434518125 := by
  unfold tailWord_1342573
  simp only [CollatzResearch.WordTrace]
  refine ⟨48967660165094789058544373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32645106776729859372362915 48967660165094789058544373)
  ·
    refine ⟨4590718140477636474238535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48967660165094789058544373 4590718140477636474238535)
    ·
      refine ⟨6886077210716454711357803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590718140477636474238535 6886077210716454711357803)
      ·
        refine ⟨10329115816074682067036705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886077210716454711357803 10329115816074682067036705)
        ·
          refine ⟨7746836862056011550277529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10329115816074682067036705 7746836862056011550277529)
          ·
            refine ⟨5810127646542008662708147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7746836862056011550277529 5810127646542008662708147)
            ·
              refine ⟨8715191469813012994062221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5810127646542008662708147 8715191469813012994062221)
              ·
                refine ⟨3268196801179879872773333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8715191469813012994062221 3268196801179879872773333)
                ·
                  refine ⟨76598362527653434518125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3268196801179879872773333 76598362527653434518125)
                  ·
                    rfl

theorem cell23_1342573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_1342573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342573 prefixEnd_1342573 := by exact prefixLift 1342573
  have htrace : WordTrace (prefixWord ++ tailWord_1342573) baseStart_1342573 baseEnd_1342573 := by
    simpa [prefixWord, tailWord_1342573, baseEnd_1342573] using wordTrace_append hprefix tailTrace_1342573
  have hstable : (prefixWord ++ tailWord_1342573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342573).length < 2 ^ (prefixWord ++ tailWord_1342573).sum := by decide
  have hdescent : baseEnd_1342573 < baseStart_1342573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342583 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_1342583 : Nat := 118140960795 + 1342583 * 2 ^ 59
def prefixEnd_1342583 : Nat := 4983230072969 + 3 ^ 40 * 1342583 * 2
def baseEnd_1342583 : Nat := 689390397555425871538079

theorem tailTrace_1342583 : CollatzResearch.WordTrace tailWord_1342583 prefixEnd_1342583 689390397555425871538079 := by
  unfold tailWord_1342583
  simp only [CollatzResearch.WordTrace]
  refine ⟨48968024895058560766408403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32645349930039040510938935 48968024895058560766408403)
  ·
    refine ⟨73452037342587841149612605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48968024895058560766408403 73452037342587841149612605)
    ·
      refine ⟨27544514003470440431104727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73452037342587841149612605 27544514003470440431104727)
      ·
        refine ⟨41316771005205660646657091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27544514003470440431104727 41316771005205660646657091)
        ·
          refine ⟨61975156507808490969985637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41316771005205660646657091 61975156507808490969985637)
          ·
            refine ⟨11620341845214092056872307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61975156507808490969985637 11620341845214092056872307)
            ·
              refine ⟨17430512767821138085308461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11620341845214092056872307 17430512767821138085308461)
              ·
                refine ⟨6536442287932926781990673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17430512767821138085308461 6536442287932926781990673)
                ·
                  refine ⟨4902331715949695086493005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6536442287932926781990673 4902331715949695086493005)
                  ·
                    refine ⟨1838374393481135657434877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4902331715949695086493005 1838374393481135657434877)
                    ·
                      refine ⟨689390397555425871538079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1838374393481135657434877 689390397555425871538079)
                      ·
                        rfl

theorem cell23_1342583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_1342583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342583 prefixEnd_1342583 := by exact prefixLift 1342583
  have htrace : WordTrace (prefixWord ++ tailWord_1342583) baseStart_1342583 baseEnd_1342583 := by
    simpa [prefixWord, tailWord_1342583, baseEnd_1342583] using wordTrace_append hprefix tailTrace_1342583
  have hstable : (prefixWord ++ tailWord_1342583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342583).length < 2 ^ (prefixWord ++ tailWord_1342583).sum := by decide
  have hdescent : baseEnd_1342583 < baseStart_1342583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342620 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1342620 : Nat := 118140960795 + 1342620 * 2 ^ 59
def prefixEnd_1342620 : Nat := 4983230072969 + 3 ^ 40 * 1342620 * 2
def baseEnd_1342620 : Nat := 229803132113214075591803

theorem tailTrace_1342620 : CollatzResearch.WordTrace tailWord_1342620 prefixEnd_1342620 229803132113214075591803 := by
  unfold tailWord_1342620
  simp only [CollatzResearch.WordTrace]
  refine ⟨24484687197962258042752657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32646249597283010723670209 24484687197962258042752657)
  ·
    refine ⟨18363515398471693532064493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24484687197962258042752657 18363515398471693532064493)
    ·
      refine ⟨6886318274426885074524185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18363515398471693532064493 6886318274426885074524185)
      ·
        refine ⟨5164738705820163805893139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6886318274426885074524185 5164738705820163805893139)
        ·
          refine ⟨7747108058730245708839709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164738705820163805893139 7747108058730245708839709)
          ·
            refine ⟨2905165522023842140814891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7747108058730245708839709 2905165522023842140814891)
            ·
              refine ⟨4357748283035763211222337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905165522023842140814891 4357748283035763211222337)
              ·
                refine ⟨3268311212276822408416753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357748283035763211222337 3268311212276822408416753)
                ·
                  refine ⟨2451233409207616806312565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268311212276822408416753 2451233409207616806312565)
                  ·
                    refine ⟨229803132113214075591803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2451233409207616806312565 229803132113214075591803)
                    ·
                      rfl

theorem cell23_1342620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1342620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342620 prefixEnd_1342620 := by exact prefixLift 1342620
  have htrace : WordTrace (prefixWord ++ tailWord_1342620) baseStart_1342620 baseEnd_1342620 := by
    simpa [prefixWord, tailWord_1342620, baseEnd_1342620] using wordTrace_append hprefix tailTrace_1342620
  have hstable : (prefixWord ++ tailWord_1342620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342620).length < 2 ^ (prefixWord ++ tailWord_1342620).sum := by decide
  have hdescent : baseEnd_1342620 < baseStart_1342620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342633 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 9, 4]
def baseStart_1342633 : Nat := 118140960795 + 1342633 * 2 ^ 59
def prefixEnd_1342633 : Nat := 4983230072969 + 3 ^ 40 * 1342633 * 2
def baseEnd_1342633 : Nat := 229805357196050225304283

theorem tailTrace_1342633 : CollatzResearch.WordTrace tailWord_1342633 prefixEnd_1342633 229805357196050225304283 := by
  unfold tailWord_1342633
  simp only [CollatzResearch.WordTrace]
  refine ⟨48969848544877419305728553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32646565696584946203819035 48969848544877419305728553)
  ·
    refine ⟨36727386408658064479296415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48969848544877419305728553 36727386408658064479296415)
    ·
      refine ⟨55091079612987096718944623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36727386408658064479296415 55091079612987096718944623)
      ·
        refine ⟨82636619419480645078416935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55091079612987096718944623 82636619419480645078416935)
        ·
          refine ⟨123954929129220967617625403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82636619419480645078416935 123954929129220967617625403)
          ·
            refine ⟨185932393693831451426438105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123954929129220967617625403 185932393693831451426438105)
            ·
              refine ⟨139449295270373588569828579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185932393693831451426438105 139449295270373588569828579)
              ·
                refine ⟨209173942905560382854742869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139449295270373588569828579 209173942905560382854742869)
                ·
                  refine ⟨1225628571712267868289509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 209173942905560382854742869 1225628571712267868289509)
                  ·
                    refine ⟨229805357196050225304283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1225628571712267868289509 229805357196050225304283)
                    ·
                      rfl

theorem cell23_1342633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_1342633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342633 prefixEnd_1342633 := by exact prefixLift 1342633
  have htrace : WordTrace (prefixWord ++ tailWord_1342633) baseStart_1342633 baseEnd_1342633 := by
    simpa [prefixWord, tailWord_1342633, baseEnd_1342633] using wordTrace_append hprefix tailTrace_1342633
  have hstable : (prefixWord ++ tailWord_1342633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342633).length < 2 ^ (prefixWord ++ tailWord_1342633).sum := by decide
  have hdescent : baseEnd_1342633 < baseStart_1342633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342643 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 3]
def baseStart_1342643 : Nat := 118140960795 + 1342643 * 2 ^ 59
def prefixEnd_1342643 : Nat := 4983230072969 + 3 ^ 40 * 1342643 * 2
def baseEnd_1342643 : Nat := 689421206394695636787803

theorem tailTrace_1342643 : CollatzResearch.WordTrace tailWord_1342643 prefixEnd_1342643 689421206394695636787803 := by
  unfold tailWord_1342643
  simp only [CollatzResearch.WordTrace]
  refine ⟨48970213274841191013592583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32646808849894127342395055 48970213274841191013592583)
  ·
    refine ⟨73455319912261786520388875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48970213274841191013592583 73455319912261786520388875)
    ·
      refine ⟨110182979868392679780583313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73455319912261786520388875 110182979868392679780583313)
      ·
        refine ⟨82637234901294509835437485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110182979868392679780583313 82637234901294509835437485)
        ·
          refine ⟨30988963087985441188289057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82637234901294509835437485 30988963087985441188289057)
          ·
            refine ⟨23241722315989080891216793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30988963087985441188289057 23241722315989080891216793)
            ·
              refine ⟨17431291736991810668412595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23241722315989080891216793 17431291736991810668412595)
              ·
                refine ⟨26146937605487716002618893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17431291736991810668412595 26146937605487716002618893)
                ·
                  refine ⟨9805101602057893500982085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26146937605487716002618893 9805101602057893500982085)
                  ·
                    refine ⟨1838456550385855031434141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9805101602057893500982085 1838456550385855031434141)
                    ·
                      refine ⟨689421206394695636787803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1838456550385855031434141 689421206394695636787803)
                      ·
                        rfl

theorem cell23_1342643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_1342643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1342643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1342643 prefixEnd_1342643 := by exact prefixLift 1342643
  have htrace : WordTrace (prefixWord ++ tailWord_1342643) baseStart_1342643 baseEnd_1342643 := by
    simpa [prefixWord, tailWord_1342643, baseEnd_1342643] using wordTrace_append hprefix tailTrace_1342643
  have hstable : (prefixWord ++ tailWord_1342643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342643).length < 2 ^ (prefixWord ++ tailWord_1342643).sum := by decide
  have hdescent : baseEnd_1342643 < baseStart_1342643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
