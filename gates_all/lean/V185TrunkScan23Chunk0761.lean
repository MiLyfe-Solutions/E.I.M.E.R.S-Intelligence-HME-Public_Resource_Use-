import V185TrunkScan23Chunk0760

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4500580 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_4500580 : Nat := 118140960795 + 4500580 * 2 ^ 59
def prefixEnd_4500580 : Nat := 4983230072969 + 3 ^ 40 * 4500580 * 2
def baseEnd_4500580 : Nat := 2310960764012106693752215

theorem tailTrace_4500580 : CollatzResearch.WordTrace tailWord_4500580 prefixEnd_4500580 2310960764012106693752215 := by
  unfold tailWord_4500580
  simp only [CollatzResearch.WordTrace]
  refine ⟨82074819017587386357361597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109433092023449848476482129 82074819017587386357361597)
  ·
    refine ⟨30778057131595269884010599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82074819017587386357361597 30778057131595269884010599)
    ·
      refine ⟨46167085697392904826015899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30778057131595269884010599 46167085697392904826015899)
      ·
        refine ⟨69250628546089357239023849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46167085697392904826015899 69250628546089357239023849)
        ·
          refine ⟨51937971409567017929267887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69250628546089357239023849 51937971409567017929267887)
          ·
            refine ⟨77906957114350526893901831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51937971409567017929267887 77906957114350526893901831)
            ·
              refine ⟨116860435671525790340852747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77906957114350526893901831 116860435671525790340852747)
              ·
                refine ⟨175290653507288685511279121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116860435671525790340852747 175290653507288685511279121)
                ·
                  refine ⟨131467990130466514133459341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175290653507288685511279121 131467990130466514133459341)
                  ·
                    refine ⟨49300496298924942800047253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 131467990130466514133459341 49300496298924942800047253)
                    ·
                      refine ⟨2310960764012106693752215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49300496298924942800047253 2310960764012106693752215)
                      ·
                        rfl

theorem cell23_4500580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_4500580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500580 prefixEnd_4500580 := by exact prefixLift 4500580
  have htrace : WordTrace (prefixWord ++ tailWord_4500580) baseStart_4500580 baseEnd_4500580 := by
    simpa [prefixWord, tailWord_4500580, baseEnd_4500580] using wordTrace_append hprefix tailTrace_4500580
  have hstable : (prefixWord ++ tailWord_4500580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500580).length < 2 ^ (prefixWord ++ tailWord_4500580).sum := by decide
  have hdescent : baseEnd_4500580 < baseStart_4500580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500601 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 1, 4, 2]
def baseStart_4500601 : Nat := 118140960795 + 4500601 * 2 ^ 59
def prefixEnd_4500601 : Nat := 4983230072969 + 3 ^ 40 * 4500601 * 2
def baseEnd_4500601 : Nat := 2310971547105851111589619

theorem tailTrace_4500601 : CollatzResearch.WordTrace tailWord_4500601 prefixEnd_4500601 2310971547105851111589619 := by
  unfold tailWord_4500601
  simp only [CollatzResearch.WordTrace]
  refine ⟨164150403968098693301237657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109433602645399128867491771 164150403968098693301237657)
  ·
    refine ⟨123112802976074019975928243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164150403968098693301237657 123112802976074019975928243)
    ·
      refine ⟨184669204464111029963892365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123112802976074019975928243 184669204464111029963892365)
      ·
        refine ⟨69250951674041636236459637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184669204464111029963892365 69250951674041636236459637)
        ·
          refine ⟨6492276719441403397168091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69250951674041636236459637 6492276719441403397168091)
          ·
            refine ⟨9738415079162105095752137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6492276719441403397168091 9738415079162105095752137)
            ·
              refine ⟨7303811309371578821814103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9738415079162105095752137 7303811309371578821814103)
              ·
                refine ⟨10955716964057368232721155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7303811309371578821814103 10955716964057368232721155)
                ·
                  refine ⟨16433575446086052349081733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10955716964057368232721155 16433575446086052349081733)
                  ·
                    refine ⟨3081295396141134815452825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16433575446086052349081733 3081295396141134815452825)
                    ·
                      refine ⟨2310971547105851111589619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081295396141134815452825 2310971547105851111589619)
                      ·
                        rfl

theorem cell23_4500601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_4500601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500601 prefixEnd_4500601 := by exact prefixLift 4500601
  have htrace : WordTrace (prefixWord ++ tailWord_4500601) baseStart_4500601 baseEnd_4500601 := by
    simpa [prefixWord, tailWord_4500601, baseEnd_4500601] using wordTrace_append hprefix tailTrace_4500601
  have hstable : (prefixWord ++ tailWord_4500601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500601).length < 2 ^ (prefixWord ++ tailWord_4500601).sum := by decide
  have hdescent : baseEnd_4500601 < baseStart_4500601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500634 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4500634 : Nat := 118140960795 + 4500634 * 2 ^ 59
def prefixEnd_4500634 : Nat := 4983230072969 + 3 ^ 40 * 4500634 * 2
def baseEnd_4500634 : Nat := 2310988491967449482476967

theorem tailTrace_4500634 : CollatzResearch.WordTrace tailWord_4500634 prefixEnd_4500634 2310988491967449482476967 := by
  unfold tailWord_4500634
  simp only [CollatzResearch.WordTrace]
  refine ⟨41037901894244784984297239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109434405051319426624792637 41037901894244784984297239)
  ·
    refine ⟨61556852841367177476445859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41037901894244784984297239 61556852841367177476445859)
    ·
      refine ⟨92335279262050766214668789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61556852841367177476445859 92335279262050766214668789)
      ·
        refine ⟨8656432430817259332625199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92335279262050766214668789 8656432430817259332625199)
        ·
          refine ⟨12984648646225888998937799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8656432430817259332625199 12984648646225888998937799)
          ·
            refine ⟨19476972969338833498406699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12984648646225888998937799 19476972969338833498406699)
            ·
              refine ⟨29215459454008250247610049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19476972969338833498406699 29215459454008250247610049)
              ·
                refine ⟨21911594590506187685707537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29215459454008250247610049 21911594590506187685707537)
                ·
                  refine ⟨16433695942879640764280653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21911594590506187685707537 16433695942879640764280653)
                  ·
                    refine ⟨6162635978579865286605245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16433695942879640764280653 6162635978579865286605245)
                    ·
                      refine ⟨2310988491967449482476967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162635978579865286605245 2310988491967449482476967)
                      ·
                        rfl

theorem cell23_4500634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4500634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500634 prefixEnd_4500634 := by exact prefixLift 4500634
  have htrace : WordTrace (prefixWord ++ tailWord_4500634) baseStart_4500634 baseEnd_4500634 := by
    simpa [prefixWord, tailWord_4500634, baseEnd_4500634] using wordTrace_append hprefix tailTrace_4500634
  have hstable : (prefixWord ++ tailWord_4500634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500634).length < 2 ^ (prefixWord ++ tailWord_4500634).sum := by decide
  have hdescent : baseEnd_4500634 < baseStart_4500634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500637 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4500637 : Nat := 118140960795 + 4500637 * 2 ^ 59
def prefixEnd_4500637 : Nat := 4983230072969 + 3 ^ 40 * 4500637 * 2
def baseEnd_4500637 : Nat := 770330010803137656913151

theorem tailTrace_4500637 : CollatzResearch.WordTrace tailWord_4500637 prefixEnd_4500637 770330010803137656913151 := by
  unfold tailWord_4500637
  simp only [CollatzResearch.WordTrace]
  refine ⟨164151716995968271449548165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109434477997312180966365443 164151716995968271449548165)
  ·
    refine ⟨30778446936744050896790281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164151716995968271449548165 30778446936744050896790281)
    ·
      refine ⟨23083835202558038172592711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30778446936744050896790281 23083835202558038172592711)
      ·
        refine ⟨34625752803837057258889067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23083835202558038172592711 34625752803837057258889067)
        ·
          refine ⟨51938629205755585888333601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34625752803837057258889067 51938629205755585888333601)
          ·
            refine ⟨38953971904316689416250201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51938629205755585888333601 38953971904316689416250201)
            ·
              refine ⟨29215478928237517062187651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38953971904316689416250201 29215478928237517062187651)
              ·
                refine ⟨43823218392356275593281477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29215478928237517062187651 43823218392356275593281477)
                ·
                  refine ⟨8216853448566801673740277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43823218392356275593281477 8216853448566801673740277)
                  ·
                    refine ⟨770330010803137656913151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8216853448566801673740277 770330010803137656913151)
                    ·
                      rfl

theorem cell23_4500637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4500637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500637 prefixEnd_4500637 := by exact prefixLift 4500637
  have htrace : WordTrace (prefixWord ++ tailWord_4500637) baseStart_4500637 baseEnd_4500637 := by
    simpa [prefixWord, tailWord_4500637, baseEnd_4500637] using wordTrace_append hprefix tailTrace_4500637
  have hstable : (prefixWord ++ tailWord_4500637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500637).length < 2 ^ (prefixWord ++ tailWord_4500637).sum := by decide
  have hdescent : baseEnd_4500637 < baseStart_4500637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500667 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 5, 4]
def baseStart_4500667 : Nat := 118140960795 + 4500667 * 2 ^ 59
def prefixEnd_4500667 : Nat := 4983230072969 + 3 ^ 40 * 4500667 * 2
def baseEnd_4500667 : Nat := 770335145609682617788105

theorem tailTrace_4500667 : CollatzResearch.WordTrace tailWord_4500667 prefixEnd_4500667 770335145609682617788105 := by
  unfold tailWord_4500667
  simp only [CollatzResearch.WordTrace]
  refine ⟨164152811185859586573140255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109435207457239724382093503 164152811185859586573140255)
  ·
    refine ⟨246229216778789379859710383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164152811185859586573140255 246229216778789379859710383)
    ·
      refine ⟨369343825168184069789565575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246229216778789379859710383 369343825168184069789565575)
      ·
        refine ⟨554015737752276104684348363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369343825168184069789565575 554015737752276104684348363)
        ·
          refine ⟨831023606628414157026522545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554015737752276104684348363 831023606628414157026522545)
          ·
            refine ⟨623267704971310617769891909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831023606628414157026522545 623267704971310617769891909)
            ·
              refine ⟨116862694682120740831854733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 623267704971310617769891909 116862694682120740831854733)
              ·
                refine ⟨43823510505795277811945525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116862694682120740831854733 43823510505795277811945525)
                ·
                  refine ⟨4108454109918307294869893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43823510505795277811945525 4108454109918307294869893)
                  ·
                    refine ⟨770335145609682617788105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4108454109918307294869893 770335145609682617788105)
                    ·
                      rfl

theorem cell23_4500667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 4].length) (baseStart_4500667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500667 prefixEnd_4500667 := by exact prefixLift 4500667
  have htrace : WordTrace (prefixWord ++ tailWord_4500667) baseStart_4500667 baseEnd_4500667 := by
    simpa [prefixWord, tailWord_4500667, baseEnd_4500667] using wordTrace_append hprefix tailTrace_4500667
  have hstable : (prefixWord ++ tailWord_4500667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500667).length < 2 ^ (prefixWord ++ tailWord_4500667).sum := by decide
  have hdescent : baseEnd_4500667 < baseStart_4500667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500697 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 6]
def baseStart_4500697 : Nat := 118140960795 + 4500697 * 2 ^ 59
def prefixEnd_4500697 : Nat := 4983230072969 + 3 ^ 40 * 4500697 * 2
def baseEnd_4500697 : Nat := 256780093472075859554353

theorem tailTrace_4500697 : CollatzResearch.WordTrace tailWord_4500697 prefixEnd_4500697 256780093472075859554353 := by
  unfold tailWord_4500697
  simp only [CollatzResearch.WordTrace]
  refine ⟨164153905375750901696732345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109435936917167267797821563 164153905375750901696732345)
  ·
    refine ⟨123115429031813176272549259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164153905375750901696732345 123115429031813176272549259)
    ·
      refine ⟨184673143547719764408823889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123115429031813176272549259 184673143547719764408823889)
      ·
        refine ⟨138504857660789823306617917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184673143547719764408823889 138504857660789823306617917)
        ·
          refine ⟨51939321622796183739981719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138504857660789823306617917 51939321622796183739981719)
          ·
            refine ⟨77908982434194275609972579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51939321622796183739981719 77908982434194275609972579)
            ·
              refine ⟨116863473651291413414958869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77908982434194275609972579 116863473651291413414958869)
              ·
                refine ⟨5477975327404285003826197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116863473651291413414958869 5477975327404285003826197)
                ·
                  refine ⟨256780093472075859554353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5477975327404285003826197 256780093472075859554353)
                  ·
                    rfl

theorem cell23_4500697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 6].length) (baseStart_4500697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500697 prefixEnd_4500697 := by exact prefixLift 4500697
  have htrace : WordTrace (prefixWord ++ tailWord_4500697) baseStart_4500697 baseEnd_4500697 := by
    simpa [prefixWord, tailWord_4500697, baseEnd_4500697] using wordTrace_append hprefix tailTrace_4500697
  have hstable : (prefixWord ++ tailWord_4500697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500697).length < 2 ^ (prefixWord ++ tailWord_4500697).sum := by decide
  have hdescent : baseEnd_4500697 < baseStart_4500697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500714 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 6]
def baseStart_4500714 : Nat := 118140960795 + 4500714 * 2 ^ 59
def prefixEnd_4500714 : Nat := 4983230072969 + 3 ^ 40 * 4500714 * 2
def baseEnd_4500714 : Nat := 256781063379978796608511

theorem tailTrace_4500714 : CollatzResearch.WordTrace tailWord_4500714 prefixEnd_4500714 256781063379978796608511 := by
  unfold tailWord_4500714
  simp only [CollatzResearch.WordTrace]
  refine ⟨41038631354172328400025299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109436350277792875733400797 41038631354172328400025299)
  ·
    refine ⟨61557947031258492600037949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41038631354172328400025299 61557947031258492600037949)
    ·
      refine ⟨23084230136721934725014231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61557947031258492600037949 23084230136721934725014231)
      ·
        refine ⟨34626345205082902087521347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23084230136721934725014231 34626345205082902087521347)
        ·
          refine ⟨51939517807624353131282021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34626345205082902087521347 51939517807624353131282021)
          ·
            refine ⟨9738659588929566212115379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51939517807624353131282021 9738659588929566212115379)
            ·
              refine ⟨14607989383394349318173069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9738659588929566212115379 14607989383394349318173069)
              ·
                refine ⟨5477996018772880994314901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14607989383394349318173069 5477996018772880994314901)
                ·
                  refine ⟨256781063379978796608511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5477996018772880994314901 256781063379978796608511)
                  ·
                    rfl

theorem cell23_4500714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_4500714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500714 prefixEnd_4500714 := by exact prefixLift 4500714
  have htrace : WordTrace (prefixWord ++ tailWord_4500714) baseStart_4500714 baseEnd_4500714 := by
    simpa [prefixWord, tailWord_4500714, baseEnd_4500714] using wordTrace_append hprefix tailTrace_4500714
  have hstable : (prefixWord ++ tailWord_4500714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500714).length < 2 ^ (prefixWord ++ tailWord_4500714).sum := by decide
  have hdescent : baseEnd_4500714 < baseStart_4500714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500727 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 3, 5]
def baseStart_4500727 : Nat := 118140960795 + 4500727 * 2 ^ 59
def prefixEnd_4500727 : Nat := 4983230072969 + 3 ^ 40 * 4500727 * 2
def baseEnd_4500727 : Nat := 770345415222772539538013

theorem tailTrace_4500727 : CollatzResearch.WordTrace tailWord_4500727 prefixEnd_4500727 770345415222772539538013 := by
  unfold tailWord_4500727
  simp only [CollatzResearch.WordTrace]
  refine ⟨164154999565642216820324435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109436666377094811213549623 164154999565642216820324435)
  ·
    refine ⟨246232499348463325230486653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164154999565642216820324435 246232499348463325230486653)
    ·
      refine ⟨92337187255673746961432495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246232499348463325230486653 92337187255673746961432495)
      ·
        refine ⟨138505780883510620442148743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92337187255673746961432495 138505780883510620442148743)
        ·
          refine ⟨207758671325265930663223115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138505780883510620442148743 207758671325265930663223115)
          ·
            refine ⟨311638006987898895994834673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207758671325265930663223115 311638006987898895994834673)
            ·
              refine ⟨233728505240924171996126005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311638006987898895994834673 233728505240924171996126005)
              ·
                refine ⟨21912047366336641124636813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233728505240924171996126005 21912047366336641124636813)
                ·
                  refine ⟨8217017762376240421738805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21912047366336641124636813 8217017762376240421738805)
                  ·
                    refine ⟨770345415222772539538013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8217017762376240421738805 770345415222772539538013)
                    ·
                      rfl

theorem cell23_4500727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_4500727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500727 prefixEnd_4500727 := by exact prefixLift 4500727
  have htrace : WordTrace (prefixWord ++ tailWord_4500727) baseStart_4500727 baseEnd_4500727 := by
    simpa [prefixWord, tailWord_4500727, baseEnd_4500727] using wordTrace_append hprefix tailTrace_4500727
  have hstable : (prefixWord ++ tailWord_4500727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500727).length < 2 ^ (prefixWord ++ tailWord_4500727).sum := by decide
  have hdescent : baseEnd_4500727 < baseStart_4500727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500757 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_4500757 : Nat := 118140960795 + 4500757 * 2 ^ 59
def prefixEnd_4500757 : Nat := 4983230072969 + 3 ^ 40 * 4500757 * 2
def baseEnd_4500757 : Nat := 770350550029317500412967

theorem tailTrace_4500757 : CollatzResearch.WordTrace tailWord_4500757 prefixEnd_4500757 770350550029317500412967 := by
  unfold tailWord_4500757
  simp only [CollatzResearch.WordTrace]
  refine ⟨164156093755533531943916525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109437395837022354629277683 164156093755533531943916525)
  ·
    refine ⟨61558535158325074478968697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164156093755533531943916525 61558535158325074478968697)
    ·
      refine ⟨46168901368743805859226523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61558535158325074478968697 46168901368743805859226523)
      ·
        refine ⟨69253352053115708788839785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46168901368743805859226523 69253352053115708788839785)
        ·
          refine ⟨51940014039836781591629839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69253352053115708788839785 51940014039836781591629839)
          ·
            refine ⟨77910021059755172387444759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51940014039836781591629839 77910021059755172387444759)
            ·
              refine ⟨116865031589632758581167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77910021059755172387444759 116865031589632758581167139)
              ·
                refine ⟨175297547384449137871750709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116865031589632758581167139 175297547384449137871750709)
                ·
                  refine ⟨16434145067292106675476629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175297547384449137871750709 16434145067292106675476629)
                  ·
                    refine ⟨770350550029317500412967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16434145067292106675476629 770350550029317500412967)
                    ·
                      rfl

theorem cell23_4500757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_4500757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500757 prefixEnd_4500757 := by exact prefixLift 4500757
  have htrace : WordTrace (prefixWord ++ tailWord_4500757) baseStart_4500757 baseEnd_4500757 := by
    simpa [prefixWord, tailWord_4500757, baseEnd_4500757] using wordTrace_append hprefix tailTrace_4500757
  have hstable : (prefixWord ++ tailWord_4500757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500757).length < 2 ^ (prefixWord ++ tailWord_4500757).sum := by decide
  have hdescent : baseEnd_4500757 < baseStart_4500757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500764 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4500764 : Nat := 118140960795 + 4500764 * 2 ^ 59
def prefixEnd_4500764 : Nat := 4983230072969 + 3 ^ 40 * 4500764 * 2
def baseEnd_4500764 : Nat := 2311055244452533973851369

theorem tailTrace_4500764 : CollatzResearch.WordTrace tailWord_4500764 prefixEnd_4500764 2311055244452533973851369 := by
  unfold tailWord_4500764
  simp only [CollatzResearch.WordTrace]
  refine ⟨82078174533254086069710673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109437566044338781426280897 82078174533254086069710673)
  ·
    refine ⟨61558630899940564552283005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82078174533254086069710673 61558630899940564552283005)
    ·
      refine ⟨23084486587477711707106127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61558630899940564552283005 23084486587477711707106127)
      ·
        refine ⟨34626729881216567560659191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23084486587477711707106127 34626729881216567560659191)
        ·
          refine ⟨51940094821824851340988787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34626729881216567560659191 51940094821824851340988787)
          ·
            refine ⟨77910142232737277011483181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51940094821824851340988787 77910142232737277011483181)
            ·
              refine ⟨29216303337276478879306193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77910142232737277011483181 29216303337276478879306193)
              ·
                refine ⟨21912227502957359159479645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29216303337276478879306193 21912227502957359159479645)
                ·
                  refine ⟨8217085313609009684804867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21912227502957359159479645 8217085313609009684804867)
                  ·
                    refine ⟨12325627970413514527207301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8217085313609009684804867 12325627970413514527207301)
                    ·
                      refine ⟨2311055244452533973851369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12325627970413514527207301 2311055244452533973851369)
                      ·
                        rfl

theorem cell23_4500764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4500764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500764 prefixEnd_4500764 := by exact prefixLift 4500764
  have htrace : WordTrace (prefixWord ++ tailWord_4500764) baseStart_4500764 baseEnd_4500764 := by
    simpa [prefixWord, tailWord_4500764, baseEnd_4500764] using wordTrace_append hprefix tailTrace_4500764
  have hstable : (prefixWord ++ tailWord_4500764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500764).length < 2 ^ (prefixWord ++ tailWord_4500764).sum := by decide
  have hdescent : baseEnd_4500764 < baseStart_4500764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500784 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3]
def baseStart_4500784 : Nat := 118140960795 + 4500784 * 2 ^ 59
def prefixEnd_4500784 : Nat := 4983230072969 + 3 ^ 40 * 4500784 * 2
def baseEnd_4500784 : Nat := 2311065514065623895601277

theorem tailTrace_4500784 : CollatzResearch.WordTrace tailWord_4500784 prefixEnd_4500784 2311065514065623895601277 := by
  unfold tailWord_4500784
  simp only [CollatzResearch.WordTrace]
  refine ⟨82078539263217857777574703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109438052350957143703432937 82078539263217857777574703)
  ·
    refine ⟨123117808894826786666362055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82078539263217857777574703 123117808894826786666362055)
    ·
      refine ⟨184676713342240179999543083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123117808894826786666362055 184676713342240179999543083)
      ·
        refine ⟨277015070013360269999314625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184676713342240179999543083 277015070013360269999314625)
        ·
          refine ⟨207761302510020202499485969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277015070013360269999314625 207761302510020202499485969)
          ·
            refine ⟨155820976882515151874614477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207761302510020202499485969 155820976882515151874614477)
            ·
              refine ⟨58432866330943181952980429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155820976882515151874614477 58432866330943181952980429)
              ·
                refine ⟨21912324874103693232367661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58432866330943181952980429 21912324874103693232367661)
                ·
                  refine ⟨8217121827788884962137873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21912324874103693232367661 8217121827788884962137873)
                  ·
                    refine ⟨6162841370841663721603405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8217121827788884962137873 6162841370841663721603405)
                    ·
                      refine ⟨2311065514065623895601277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162841370841663721603405 2311065514065623895601277)
                      ·
                        rfl

theorem cell23_4500784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_4500784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500784 prefixEnd_4500784 := by exact prefixLift 4500784
  have htrace : WordTrace (prefixWord ++ tailWord_4500784) baseStart_4500784 baseEnd_4500784 := by
    simpa [prefixWord, tailWord_4500784, baseEnd_4500784] using wordTrace_append hprefix tailTrace_4500784
  have hstable : (prefixWord ++ tailWord_4500784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500784).length < 2 ^ (prefixWord ++ tailWord_4500784).sum := by decide
  have hdescent : baseEnd_4500784 < baseStart_4500784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500794 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_4500794 : Nat := 118140960795 + 4500794 * 2 ^ 59
def prefixEnd_4500794 : Nat := 4983230072969 + 3 ^ 40 * 4500794 * 2
def baseEnd_4500794 : Nat := 2311070648872168856476231

theorem tailTrace_4500794 : CollatzResearch.WordTrace tailWord_4500794 prefixEnd_4500794 2311070648872168856476231 := by
  unfold tailWord_4500794
  simp only [CollatzResearch.WordTrace]
  refine ⟨41039360814099871815753359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109438295504266324842008957 41039360814099871815753359)
  ·
    refine ⟨61559041221149807723630039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41039360814099871815753359 61559041221149807723630039)
    ·
      refine ⟨92338561831724711585445059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61559041221149807723630039 92338561831724711585445059)
      ·
        refine ⟨138507842747587067378167589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92338561831724711585445059 138507842747587067378167589)
        ·
          refine ⟨25970220515172575133406423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138507842747587067378167589 25970220515172575133406423)
          ·
            refine ⟨38955330772758862700109635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25970220515172575133406423 38955330772758862700109635)
            ·
              refine ⟨58432996159138294050164453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38955330772758862700109635 58432996159138294050164453)
              ·
                refine ⟨10956186779838430134405835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58432996159138294050164453 10956186779838430134405835)
                ·
                  refine ⟨16434280169757645201608753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10956186779838430134405835 16434280169757645201608753)
                  ·
                    refine ⟨12325710127318233901206565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16434280169757645201608753 12325710127318233901206565)
                    ·
                      refine ⟨2311070648872168856476231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12325710127318233901206565 2311070648872168856476231)
                      ·
                        rfl

theorem cell23_4500794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_4500794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500794 prefixEnd_4500794 := by exact prefixLift 4500794
  have htrace : WordTrace (prefixWord ++ tailWord_4500794) baseStart_4500794 baseEnd_4500794 := by
    simpa [prefixWord, tailWord_4500794, baseEnd_4500794] using wordTrace_append hprefix tailTrace_4500794
  have hstable : (prefixWord ++ tailWord_4500794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500794).length < 2 ^ (prefixWord ++ tailWord_4500794).sum := by decide
  have hdescent : baseEnd_4500794 < baseStart_4500794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500798 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_4500798 : Nat := 118140960795 + 4500798 * 2 ^ 59
def prefixEnd_4500798 : Nat := 4983230072969 + 3 ^ 40 * 4500798 * 2
def baseEnd_4500798 : Nat := 2311072702794786840826213

theorem tailTrace_4500798 : CollatzResearch.WordTrace tailWord_4500798 prefixEnd_4500798 2311072702794786840826213 := by
  unfold tailWord_4500798
  simp only [CollatzResearch.WordTrace]
  refine ⟨20519698643548124493269881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109438392765589997297439365 20519698643548124493269881)
  ·
    refine ⟨15389773982661093369952411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20519698643548124493269881 15389773982661093369952411)
    ·
      refine ⟨23084660973991640054928617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15389773982661093369952411 23084660973991640054928617)
      ·
        refine ⟨17313495730493730041196463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23084660973991640054928617 17313495730493730041196463)
        ·
          refine ⟨25970243595740595061794695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17313495730493730041196463 25970243595740595061794695)
          ·
            refine ⟨38955365393610892592692043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25970243595740595061794695 38955365393610892592692043)
            ·
              refine ⟨58433048090416338889038065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38955365393610892592692043 58433048090416338889038065)
              ·
                refine ⟨43824786067812254166778549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58433048090416338889038065 43824786067812254166778549)
                ·
                  refine ⟨4108573693857398828135489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43824786067812254166778549 4108573693857398828135489)
                  ·
                    refine ⟨3081430270393049121101617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4108573693857398828135489 3081430270393049121101617)
                    ·
                      refine ⟨2311072702794786840826213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081430270393049121101617 2311072702794786840826213)
                      ·
                        rfl

theorem cell23_4500798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_4500798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500798 prefixEnd_4500798 := by exact prefixLift 4500798
  have htrace : WordTrace (prefixWord ++ tailWord_4500798) baseStart_4500798 baseEnd_4500798 := by
    simpa [prefixWord, tailWord_4500798, baseEnd_4500798] using wordTrace_append hprefix tailTrace_4500798
  have hstable : (prefixWord ++ tailWord_4500798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500798).length < 2 ^ (prefixWord ++ tailWord_4500798).sum := by decide
  have hdescent : baseEnd_4500798 < baseStart_4500798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500844 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_4500844 : Nat := 118140960795 + 4500844 * 2 ^ 59
def prefixEnd_4500844 : Nat := 4983230072969 + 3 ^ 40 * 4500844 * 2
def baseEnd_4500844 : Nat := 2311096322904893660851001

theorem tailTrace_4500844 : CollatzResearch.WordTrace tailWord_4500844 prefixEnd_4500844 2311096322904893660851001 := by
  unfold tailWord_4500844
  simp only [CollatzResearch.WordTrace]
  refine ⟨82079633453109172901166793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109439511270812230534889057 82079633453109172901166793)
  ·
    refine ⟨61559725089831879675875095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82079633453109172901166793 61559725089831879675875095)
    ·
      refine ⟨92339587634747819513812643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61559725089831879675875095 92339587634747819513812643)
      ·
        refine ⟨138509381452121729270718965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92339587634747819513812643 138509381452121729270718965)
        ·
          refine ⟨12985254511136412119129903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138509381452121729270718965 12985254511136412119129903)
          ·
            refine ⟨19477881766704618178694855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12985254511136412119129903 19477881766704618178694855)
            ·
              refine ⟨29216822650056927268042283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19477881766704618178694855 29216822650056927268042283)
              ·
                refine ⟨43825233975085390902063425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29216822650056927268042283 43825233975085390902063425)
                ·
                  refine ⟨32868925481314043176547569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43825233975085390902063425 32868925481314043176547569)
                  ·
                    refine ⟨24651694110985532382410677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32868925481314043176547569 24651694110985532382410677)
                    ·
                      refine ⟨2311096322904893660851001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24651694110985532382410677 2311096322904893660851001)
                      ·
                        rfl

theorem cell23_4500844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_4500844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500844 prefixEnd_4500844 := by exact prefixLift 4500844
  have htrace : WordTrace (prefixWord ++ tailWord_4500844) baseStart_4500844 baseEnd_4500844 := by
    simpa [prefixWord, tailWord_4500844, baseEnd_4500844] using wordTrace_append hprefix tailTrace_4500844
  have hstable : (prefixWord ++ tailWord_4500844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500844).length < 2 ^ (prefixWord ++ tailWord_4500844).sum := by decide
  have hdescent : baseEnd_4500844 < baseStart_4500844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500866 : List Nat := [3, 4, 2, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_4500866 : Nat := 118140960795 + 4500866 * 2 ^ 59
def prefixEnd_4500866 : Nat := 4983230072969 + 3 ^ 40 * 4500866 * 2
def baseEnd_4500866 : Nat := 2311107619479292574775901

theorem tailTrace_4500866 : CollatzResearch.WordTrace tailWord_4500866 prefixEnd_4500866 2311107619479292574775901 := by
  unfold tailWord_4500866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41040017328034660889908613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109440046208092429039756301 41040017328034660889908613)
  ·
    refine ⟨7695003249006498916857865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41040017328034660889908613 7695003249006498916857865)
    ·
      refine ⟨5771252436754874187643399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7695003249006498916857865 5771252436754874187643399)
      ·
        refine ⟨8656878655132311281465099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771252436754874187643399 8656878655132311281465099)
        ·
          refine ⟨12985317982698466922197649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8656878655132311281465099 12985317982698466922197649)
          ·
            refine ⟨9738988487023850191648237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12985317982698466922197649 9738988487023850191648237)
            ·
              refine ⟨3652120682633943821868089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9738988487023850191648237 3652120682633943821868089)
              ·
                refine ⟨2739090511975457866401067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652120682633943821868089 2739090511975457866401067)
                ·
                  refine ⟨4108635767963186799601601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739090511975457866401067 4108635767963186799601601)
                  ·
                    refine ⟨3081476825972390099701201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4108635767963186799601601 3081476825972390099701201)
                    ·
                      refine ⟨2311107619479292574775901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081476825972390099701201 2311107619479292574775901)
                      ·
                        rfl

theorem cell23_4500866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_4500866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500866 prefixEnd_4500866 := by exact prefixLift 4500866
  have htrace : WordTrace (prefixWord ++ tailWord_4500866) baseStart_4500866 baseEnd_4500866 := by
    simpa [prefixWord, tailWord_4500866, baseEnd_4500866] using wordTrace_append hprefix tailTrace_4500866
  have hstable : (prefixWord ++ tailWord_4500866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500866).length < 2 ^ (prefixWord ++ tailWord_4500866).sum := by decide
  have hdescent : baseEnd_4500866 < baseStart_4500866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500882 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4500882 : Nat := 118140960795 + 4500882 * 2 ^ 59
def prefixEnd_4500882 : Nat := 4983230072969 + 3 ^ 40 * 4500882 * 2
def baseEnd_4500882 : Nat := 2311115835169764512175827

theorem tailTrace_4500882 : CollatzResearch.WordTrace tailWord_4500882 prefixEnd_4500882 2311115835169764512175827 := by
  unfold tailWord_4500882
  simp only [CollatzResearch.WordTrace]
  refine ⟨41040163220020169573054225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109440435253387118861477933 41040163220020169573054225)
  ·
    refine ⟨30780122415015127179790669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41040163220020169573054225 30780122415015127179790669)
    ·
      refine ⟨11542545905630672692421501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30780122415015127179790669 11542545905630672692421501)
      ·
        refine ⟨4328454714611502259658063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11542545905630672692421501 4328454714611502259658063)
        ·
          refine ⟨6492682071917253389487095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328454714611502259658063 6492682071917253389487095)
          ·
            refine ⟨9739023107875880084230643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6492682071917253389487095 9739023107875880084230643)
            ·
              refine ⟨14608534661813820126345965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9739023107875880084230643 14608534661813820126345965)
              ·
                refine ⟨5478200498180182547379737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14608534661813820126345965 5478200498180182547379737)
                ·
                  refine ⟨4108650373635136910534803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5478200498180182547379737 4108650373635136910534803)
                  ·
                    refine ⟨6162975560452705365802205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4108650373635136910534803 6162975560452705365802205)
                    ·
                      refine ⟨2311115835169764512175827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6162975560452705365802205 2311115835169764512175827)
                      ·
                        rfl

theorem cell23_4500882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4500882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500882 prefixEnd_4500882 := by exact prefixLift 4500882
  have htrace : WordTrace (prefixWord ++ tailWord_4500882) baseStart_4500882 baseEnd_4500882 := by
    simpa [prefixWord, tailWord_4500882, baseEnd_4500882] using wordTrace_append hprefix tailTrace_4500882
  have hstable : (prefixWord ++ tailWord_4500882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500882).length < 2 ^ (prefixWord ++ tailWord_4500882).sum := by decide
  have hdescent : baseEnd_4500882 < baseStart_4500882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500928 : List Nat := [2, 1, 1, 2, 3, 1, 6, 2, 5]
def baseStart_4500928 : Nat := 118140960795 + 4500928 * 2 ^ 59
def prefixEnd_4500928 : Nat := 4983230072969 + 3 ^ 40 * 4500928 * 2
def baseEnd_4500928 : Nat := 256793272808874592466735

theorem tailTrace_4500928 : CollatzResearch.WordTrace tailWord_4500928 prefixEnd_4500928 256793272808874592466735 := by
  unfold tailWord_4500928
  simp only [CollatzResearch.WordTrace]
  refine ⟨82081165318957014074195719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109441553758609352098927625 82081165318957014074195719)
  ·
    refine ⟨123121747978435521111293579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82081165318957014074195719 123121747978435521111293579)
    ·
      refine ⟨184682621967653281666940369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123121747978435521111293579 184682621967653281666940369)
      ·
        refine ⟨138511966475739961250205277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184682621967653281666940369 138511966475739961250205277)
        ·
          refine ⟨51941987428402485468826979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138511966475739961250205277 51941987428402485468826979)
          ·
            refine ⟨77912981142603728203240469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51941987428402485468826979 77912981142603728203240469)
            ·
              refine ⟨3652170991059549759526897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77912981142603728203240469 3652170991059549759526897)
              ·
                refine ⟨2739128243294662319645173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652170991059549759526897 2739128243294662319645173)
                ·
                  refine ⟨256793272808874592466735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2739128243294662319645173 256793272808874592466735)
                  ·
                    rfl

theorem cell23_4500928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 5].length) (baseStart_4500928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500928 prefixEnd_4500928 := by exact prefixLift 4500928
  have htrace : WordTrace (prefixWord ++ tailWord_4500928) baseStart_4500928 baseEnd_4500928 := by
    simpa [prefixWord, tailWord_4500928, baseEnd_4500928] using wordTrace_append hprefix tailTrace_4500928
  have hstable : (prefixWord ++ tailWord_4500928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500928).length < 2 ^ (prefixWord ++ tailWord_4500928).sum := by decide
  have hdescent : baseEnd_4500928 < baseStart_4500928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500931 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 2, 5, 2]
def baseStart_4500931 : Nat := 118140960795 + 4500931 * 2 ^ 59
def prefixEnd_4500931 : Nat := 4983230072969 + 3 ^ 40 * 4500931 * 2
def baseEnd_4500931 : Nat := 2311140995721834820463101

theorem tailTrace_4500931 : CollatzResearch.WordTrace tailWord_4500931 prefixEnd_4500931 2311140995721834820463101 := by
  unfold tailWord_4500931
  simp only [CollatzResearch.WordTrace]
  refine ⟨164162440056903159660750647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109441626704602106440500431 164162440056903159660750647)
  ·
    refine ⟨246243660085354739491125971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164162440056903159660750647 246243660085354739491125971)
    ·
      refine ⟨369365490128032109236688957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246243660085354739491125971 369365490128032109236688957)
      ·
        refine ⟨138512058798012040963758359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369365490128032109236688957 138512058798012040963758359)
        ·
          refine ⟨207768088197018061445637539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138512058798012040963758359 207768088197018061445637539)
          ·
            refine ⟨311652132295527092168456309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207768088197018061445637539 311652132295527092168456309)
            ·
              refine ⟨29217387402705664890792779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 311652132295527092168456309 29217387402705664890792779)
              ·
                refine ⟨43826081104058497336189169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29217387402705664890792779 43826081104058497336189169)
                ·
                  refine ⟨32869560828043873002141877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43826081104058497336189169 32869560828043873002141877)
                  ·
                    refine ⟨3081521327629113093950801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32869560828043873002141877 3081521327629113093950801)
                    ·
                      refine ⟨2311140995721834820463101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081521327629113093950801 2311140995721834820463101)
                      ·
                        rfl

theorem cell23_4500931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_4500931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500931 prefixEnd_4500931 := by exact prefixLift 4500931
  have htrace : WordTrace (prefixWord ++ tailWord_4500931) baseStart_4500931 baseEnd_4500931 := by
    simpa [prefixWord, tailWord_4500931, baseEnd_4500931] using wordTrace_append hprefix tailTrace_4500931
  have hstable : (prefixWord ++ tailWord_4500931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500931).length < 2 ^ (prefixWord ++ tailWord_4500931).sum := by decide
  have hdescent : baseEnd_4500931 < baseStart_4500931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500944 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_4500944 : Nat := 118140960795 + 4500944 * 2 ^ 59
def prefixEnd_4500944 : Nat := 4983230072969 + 3 ^ 40 * 4500944 * 2
def baseEnd_4500944 : Nat := 2311147670970343269600541

theorem tailTrace_4500944 : CollatzResearch.WordTrace tailWord_4500944 prefixEnd_4500944 2311147670970343269600541 := by
  unfold tailWord_4500944
  simp only [CollatzResearch.WordTrace]
  refine ⟨82081457102928031440486943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109441942803904041920649257 82081457102928031440486943)
  ·
    refine ⟨123122185654392047160730415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82081457102928031440486943 123122185654392047160730415)
    ·
      refine ⟨184683278481588070741095623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123122185654392047160730415 184683278481588070741095623)
      ·
        refine ⟨277024917722382106111643435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184683278481588070741095623 277024917722382106111643435)
        ·
          refine ⟨415537376583573159167465153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277024917722382106111643435 415537376583573159167465153)
          ·
            refine ⟨311653032437679869375598865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415537376583573159167465153 311653032437679869375598865)
            ·
              refine ⟨233739774328259902031699149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311653032437679869375598865 233739774328259902031699149)
              ·
                refine ⟨87652415373097463261887181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233739774328259902031699149 87652415373097463261887181)
                ·
                  refine ⟨32869655764911548723207693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87652415373097463261887181 32869655764911548723207693)
                  ·
                    refine ⟨12326120911841830771202885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32869655764911548723207693 12326120911841830771202885)
                    ·
                      refine ⟨2311147670970343269600541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12326120911841830771202885 2311147670970343269600541)
                      ·
                        rfl

theorem cell23_4500944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_4500944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500944 prefixEnd_4500944 := by exact prefixLift 4500944
  have htrace : WordTrace (prefixWord ++ tailWord_4500944) baseStart_4500944 baseEnd_4500944 := by
    simpa [prefixWord, tailWord_4500944, baseEnd_4500944] using wordTrace_append hprefix tailTrace_4500944
  have hstable : (prefixWord ++ tailWord_4500944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500944).length < 2 ^ (prefixWord ++ tailWord_4500944).sum := by decide
  have hdescent : baseEnd_4500944 < baseStart_4500944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4500961 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_4500961 : Nat := 118140960795 + 4500961 * 2 ^ 59
def prefixEnd_4500961 : Nat := 4983230072969 + 3 ^ 40 * 4500961 * 2
def baseEnd_4500961 : Nat := 2311156400141469703087963

theorem tailTrace_4500961 : CollatzResearch.WordTrace tailWord_4500961 prefixEnd_4500961 2311156400141469703087963 := by
  unfold tailWord_4500961
  simp only [CollatzResearch.WordTrace]
  refine ⟨164163534246794474784342737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109442356164529649856228491 164163534246794474784342737)
  ·
    refine ⟨123122650685095856088257053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164163534246794474784342737 123122650685095856088257053)
    ·
      refine ⟨46170994006910946033096395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123122650685095856088257053 46170994006910946033096395)
      ·
        refine ⟨69256491010366419049644593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46170994006910946033096395 69256491010366419049644593)
        ·
          refine ⟨51942368257774814287233445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69256491010366419049644593 51942368257774814287233445)
          ·
            refine ⟨9739194048332777678856271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51942368257774814287233445 9739194048332777678856271)
            ·
              refine ⟨14608791072499166518284407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9739194048332777678856271 14608791072499166518284407)
              ·
                refine ⟨21913186608748749777426611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14608791072499166518284407 21913186608748749777426611)
                ·
                  refine ⟨32869779913123124666139917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21913186608748749777426611 32869779913123124666139917)
                  ·
                    refine ⟨12326167467421171749802469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32869779913123124666139917 12326167467421171749802469)
                    ·
                      refine ⟨2311156400141469703087963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12326167467421171749802469 2311156400141469703087963)
                      ·
                        rfl

theorem cell23_4500961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_4500961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4500961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4500961 prefixEnd_4500961 := by exact prefixLift 4500961
  have htrace : WordTrace (prefixWord ++ tailWord_4500961) baseStart_4500961 baseEnd_4500961 := by
    simpa [prefixWord, tailWord_4500961, baseEnd_4500961] using wordTrace_append hprefix tailTrace_4500961
  have hstable : (prefixWord ++ tailWord_4500961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4500961).length < 2 ^ (prefixWord ++ tailWord_4500961).sum := by decide
  have hdescent : baseEnd_4500961 < baseStart_4500961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4500961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501045 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_4501045 : Nat := 118140960795 + 4501045 * 2 ^ 59
def prefixEnd_4501045 : Nat := 4983230072969 + 3 ^ 40 * 4501045 * 2
def baseEnd_4501045 : Nat := 2311199532516447374437577

theorem tailTrace_4501045 : CollatzResearch.WordTrace tailWord_4501045 prefixEnd_4501045 2311199532516447374437577 := by
  unfold tailWord_4501045
  simp only [CollatzResearch.WordTrace]
  refine ⟨164166597978490157130400589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109444398652326771420267059 164166597978490157130400589)
  ·
    refine ⟨61562474241933808923900221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164166597978490157130400589 61562474241933808923900221)
    ·
      refine ⟨23085927840725178346462583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61562474241933808923900221 23085927840725178346462583)
      ·
        refine ⟨34628891761087767519693875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23085927840725178346462583 34628891761087767519693875)
        ·
          refine ⟨51943337641631651279540813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34628891761087767519693875 51943337641631651279540813)
          ·
            refine ⟨19478751615611869229827805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51943337641631651279540813 19478751615611869229827805)
            ·
              refine ⟨7304531855854450961185427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19478751615611869229827805 7304531855854450961185427)
              ·
                refine ⟨10956797783781676441778141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7304531855854450961185427 10956797783781676441778141)
                ·
                  refine ⟨4108799168918128665666803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10956797783781676441778141 4108799168918128665666803)
                  ·
                    refine ⟨6163198753377192998500205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4108799168918128665666803 6163198753377192998500205)
                    ·
                      refine ⟨2311199532516447374437577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163198753377192998500205 2311199532516447374437577)
                      ·
                        rfl

theorem cell23_4501045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_4501045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501045 prefixEnd_4501045 := by exact prefixLift 4501045
  have htrace : WordTrace (prefixWord ++ tailWord_4501045) baseStart_4501045 baseEnd_4501045 := by
    simpa [prefixWord, tailWord_4501045, baseEnd_4501045] using wordTrace_append hprefix tailTrace_4501045
  have hstable : (prefixWord ++ tailWord_4501045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501045).length < 2 ^ (prefixWord ++ tailWord_4501045).sum := by decide
  have hdescent : baseEnd_4501045 < baseStart_4501045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501052 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 6]
def baseStart_4501052 : Nat := 118140960795 + 4501052 * 2 ^ 59
def prefixEnd_4501052 : Nat := 4983230072969 + 3 ^ 40 * 4501052 * 2
def baseEnd_4501052 : Nat := 256800347431225427450005

theorem tailTrace_4501052 : CollatzResearch.WordTrace tailWord_4501052 prefixEnd_4501052 256800347431225427450005 := by
  unfold tailWord_4501052
  simp only [CollatzResearch.WordTrace]
  refine ⟨82083426644732398662952705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109444568859643198217270273 82083426644732398662952705)
  ·
    refine ⟨61562569983549298997214529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82083426644732398662952705 61562569983549298997214529)
    ·
      refine ⟨46171927487661974247910897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61562569983549298997214529 46171927487661974247910897)
      ·
        refine ⟨34628945615746480685933173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46171927487661974247910897 34628945615746480685933173)
        ·
          refine ⟨3246463651476232564306235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34628945615746480685933173 3246463651476232564306235)
          ·
            refine ⟨4869695477214348846459353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246463651476232564306235 4869695477214348846459353)
            ·
              refine ⟨3652271607910761634844515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869695477214348846459353 3652271607910761634844515)
              ·
                refine ⟨5478407411866142452266773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3652271607910761634844515 5478407411866142452266773)
                ·
                  refine ⟨256800347431225427450005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5478407411866142452266773 256800347431225427450005)
                  ·
                    rfl

theorem cell23_4501052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_4501052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501052 prefixEnd_4501052 := by exact prefixLift 4501052
  have htrace : WordTrace (prefixWord ++ tailWord_4501052) baseStart_4501052 baseEnd_4501052 := by
    simpa [prefixWord, tailWord_4501052, baseEnd_4501052] using wordTrace_append hprefix tailTrace_4501052
  have hstable : (prefixWord ++ tailWord_4501052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501052).length < 2 ^ (prefixWord ++ tailWord_4501052).sum := by decide
  have hdescent : baseEnd_4501052 < baseStart_4501052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501061 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_4501061 : Nat := 118140960795 + 4501061 * 2 ^ 59
def prefixEnd_4501061 : Nat := 4983230072969 + 3 ^ 40 * 4501061 * 2
def baseEnd_4501061 : Nat := 770402582735639770612501

theorem tailTrace_4501061 : CollatzResearch.WordTrace tailWord_4501061 prefixEnd_4501061 770402582735639770612501 := by
  unfold tailWord_4501061
  simp only [CollatzResearch.WordTrace]
  refine ⟨164167181546432191862983037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109444787697621461241988691 164167181546432191862983037)
  ·
    refine ⟨61562693079912071948618639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164167181546432191862983037 61562693079912071948618639)
    ·
      refine ⟨92344039619868107922927959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61562693079912071948618639 92344039619868107922927959)
      ·
        refine ⟨138516059429802161884391939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92344039619868107922927959 138516059429802161884391939)
        ·
          refine ⟨207774089144703242826587909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138516059429802161884391939 207774089144703242826587909)
          ·
            refine ⟨38957641714631858029985233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207774089144703242826587909 38957641714631858029985233)
            ·
              refine ⟨29218231285973893522488925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38957641714631858029985233 29218231285973893522488925)
              ·
                refine ⟨10956836732240210070933347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29218231285973893522488925 10956836732240210070933347)
                ·
                  refine ⟨16435255098360315106400021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10956836732240210070933347 16435255098360315106400021)
                  ·
                    refine ⟨770402582735639770612501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16435255098360315106400021 770402582735639770612501)
                    ·
                      rfl

theorem cell23_4501061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_4501061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501061 prefixEnd_4501061 := by exact prefixLift 4501061
  have htrace : WordTrace (prefixWord ++ tailWord_4501061) baseStart_4501061 baseEnd_4501061 := by
    simpa [prefixWord, tailWord_4501061, baseEnd_4501061] using wordTrace_append hprefix tailTrace_4501061
  have hstable : (prefixWord ++ tailWord_4501061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501061).length < 2 ^ (prefixWord ++ tailWord_4501061).sum := by decide
  have hdescent : baseEnd_4501061 < baseStart_4501061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501068 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_4501068 : Nat := 118140960795 + 4501068 * 2 ^ 59
def prefixEnd_4501068 : Nat := 4983230072969 + 3 ^ 40 * 4501068 * 2
def baseEnd_4501068 : Nat := 2311211342571500784449971

theorem tailTrace_4501068 : CollatzResearch.WordTrace tailWord_4501068 prefixEnd_4501068 2311211342571500784449971 := by
  unfold tailWord_4501068
  simp only [CollatzResearch.WordTrace]
  refine ⟨82083718428703416029243929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109444957904937888038991905 82083718428703416029243929)
  ·
    refine ⟨61562788821527562021932947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82083718428703416029243929 61562788821527562021932947)
    ·
      refine ⟨92344183232291343032899421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61562788821527562021932947 92344183232291343032899421)
      ·
        refine ⟨34629068712109253637337283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92344183232291343032899421 34629068712109253637337283)
        ·
          refine ⟨51943603068163880456005925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34629068712109253637337283 51943603068163880456005925)
          ·
            refine ⟨9739425575280727585501111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51943603068163880456005925 9739425575280727585501111)
            ·
              refine ⟨14609138362921091378251667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9739425575280727585501111 14609138362921091378251667)
              ·
                refine ⟨21913707544381637067377501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14609138362921091378251667 21913707544381637067377501)
                ·
                  refine ⟨8217640329143113900266563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21913707544381637067377501 8217640329143113900266563)
                  ·
                    refine ⟨12326460493714670850399845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8217640329143113900266563 12326460493714670850399845)
                    ·
                      refine ⟨2311211342571500784449971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12326460493714670850399845 2311211342571500784449971)
                      ·
                        rfl

theorem cell23_4501068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_4501068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501068 prefixEnd_4501068 := by exact prefixLift 4501068
  have htrace : WordTrace (prefixWord ++ tailWord_4501068) baseStart_4501068 baseEnd_4501068 := by
    simpa [prefixWord, tailWord_4501068, baseEnd_4501068] using wordTrace_append hprefix tailTrace_4501068
  have hstable : (prefixWord ++ tailWord_4501068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501068).length < 2 ^ (prefixWord ++ tailWord_4501068).sum := by decide
  have hdescent : baseEnd_4501068 < baseStart_4501068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501096 : List Nat := [2, 1, 4, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4501096 : Nat := 118140960795 + 4501096 * 2 ^ 59
def prefixEnd_4501096 : Nat := 4983230072969 + 3 ^ 40 * 4501096 * 2
def baseEnd_4501096 : Nat := 2311225720029826674899843

theorem tailTrace_4501096 : CollatzResearch.WordTrace tailWord_4501096 prefixEnd_4501096 2311225720029826674899843 := by
  unfold tailWord_4501096
  simp only [CollatzResearch.WordTrace]
  refine ⟨82084229050652696420253571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109445638734203595227004761 82084229050652696420253571)
  ·
    refine ⟨123126343575979044630380357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82084229050652696420253571 123126343575979044630380357)
    ·
      refine ⟨23086189420496070868196317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123126343575979044630380357 23086189420496070868196317)
      ·
        refine ⟨8657321032686026575573619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23086189420496070868196317 8657321032686026575573619)
        ·
          refine ⟨12985981549029039863360429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8657321032686026575573619 12985981549029039863360429)
          ·
            refine ⟨4869743080885889948760161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12985981549029039863360429 4869743080885889948760161)
            ·
              refine ⟨3652307310664417461570121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869743080885889948760161 3652307310664417461570121)
              ·
                refine ⟨2739230482998313096177591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652307310664417461570121 2739230482998313096177591)
                ·
                  refine ⟨4108845724497469644266387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739230482998313096177591 4108845724497469644266387)
                  ·
                    refine ⟨6163268586746204466399581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4108845724497469644266387 6163268586746204466399581)
                    ·
                      refine ⟨2311225720029826674899843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163268586746204466399581 2311225720029826674899843)
                      ·
                        rfl

theorem cell23_4501096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4501096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501096 prefixEnd_4501096 := by exact prefixLift 4501096
  have htrace : WordTrace (prefixWord ++ tailWord_4501096) baseStart_4501096 baseEnd_4501096 := by
    simpa [prefixWord, tailWord_4501096, baseEnd_4501096] using wordTrace_append hprefix tailTrace_4501096
  have hstable : (prefixWord ++ tailWord_4501096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501096).length < 2 ^ (prefixWord ++ tailWord_4501096).sum := by decide
  have hdescent : baseEnd_4501096 < baseStart_4501096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501131 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5]
def baseStart_4501131 : Nat := 118140960795 + 4501131 * 2 ^ 59
def prefixEnd_4501131 : Nat := 4983230072969 + 3 ^ 40 * 4501131 * 2
def baseEnd_4501131 : Nat := 2311243691852734037962181

theorem tailTrace_4501131 : CollatzResearch.WordTrace tailWord_4501131 prefixEnd_4501131 2311243691852734037962181 := by
  unfold tailWord_4501131
  simp only [CollatzResearch.WordTrace]
  refine ⟨164169734656178593818031247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109446489770785729212020831 164169734656178593818031247)
  ·
    refine ⟨246254601984267890727046871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164169734656178593818031247 246254601984267890727046871)
    ·
      refine ⟨369381902976401836090570307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246254601984267890727046871 369381902976401836090570307)
      ·
        refine ⟨554072854464602754135855461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369381902976401836090570307 554072854464602754135855461)
        ·
          refine ⟨103888660212113016400472899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 554072854464602754135855461 103888660212113016400472899)
          ·
            refine ⟨155832990318169524600709349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103888660212113016400472899 155832990318169524600709349)
            ·
              refine ⟨29218685684656785862633003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155832990318169524600709349 29218685684656785862633003)
              ·
                refine ⟨43828028526985178793949505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29218685684656785862633003 43828028526985178793949505)
                ·
                  refine ⟨32871021395238884095462129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43828028526985178793949505 32871021395238884095462129)
                  ·
                    refine ⟨24653266046429163071596597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32871021395238884095462129 24653266046429163071596597)
                    ·
                      refine ⟨2311243691852734037962181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24653266046429163071596597 2311243691852734037962181)
                      ·
                        rfl

theorem cell23_4501131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_4501131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501131 prefixEnd_4501131 := by exact prefixLift 4501131
  have htrace : WordTrace (prefixWord ++ tailWord_4501131) baseStart_4501131 baseEnd_4501131 := by
    simpa [prefixWord, tailWord_4501131, baseEnd_4501131] using wordTrace_append hprefix tailTrace_4501131
  have hstable : (prefixWord ++ tailWord_4501131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501131).length < 2 ^ (prefixWord ++ tailWord_4501131).sum := by decide
  have hdescent : baseEnd_4501131 < baseStart_4501131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501152 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 2, 1, 3]
def baseStart_4501152 : Nat := 118140960795 + 4501152 * 2 ^ 59
def prefixEnd_4501152 : Nat := 4983230072969 + 3 ^ 40 * 4501152 * 2
def baseEnd_4501152 : Nat := 2311254474946478455799585

theorem tailTrace_4501152 : CollatzResearch.WordTrace tailWord_4501152 prefixEnd_4501152 2311254474946478455799585 := by
  unfold tailWord_4501152
  simp only [CollatzResearch.WordTrace]
  refine ⟨82085250294551257202272855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109447000392735009603030473 82085250294551257202272855)
  ·
    refine ⟨123127875441826885803409283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82085250294551257202272855 123127875441826885803409283)
    ·
      refine ⟨184691813162740328705113925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123127875441826885803409283 184691813162740328705113925)
      ·
        refine ⟨34629714968013811632208861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184691813162740328705113925 34629714968013811632208861)
        ·
          refine ⟨12986143113005179362078323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34629714968013811632208861 12986143113005179362078323)
          ·
            refine ⟨19479214669507769043117485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12986143113005179362078323 19479214669507769043117485)
            ·
              refine ⟨7304705501065413391169057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19479214669507769043117485 7304705501065413391169057)
              ·
                refine ⟨5478529125799060043376793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7304705501065413391169057 5478529125799060043376793)
                ·
                  refine ⟨4108896844349295032532595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5478529125799060043376793 4108896844349295032532595)
                  ·
                    refine ⟨6163345266523942548798893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4108896844349295032532595 6163345266523942548798893)
                    ·
                      refine ⟨2311254474946478455799585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163345266523942548798893 2311254474946478455799585)
                      ·
                        rfl

theorem cell23_4501152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_4501152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501152 prefixEnd_4501152 := by exact prefixLift 4501152
  have htrace : WordTrace (prefixWord ++ tailWord_4501152) baseStart_4501152 baseEnd_4501152 := by
    simpa [prefixWord, tailWord_4501152, baseEnd_4501152] using wordTrace_append hprefix tailTrace_4501152
  have hstable : (prefixWord ++ tailWord_4501152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501152).length < 2 ^ (prefixWord ++ tailWord_4501152).sum := by decide
  have hdescent : baseEnd_4501152 < baseStart_4501152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501248 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_4501248 : Nat := 118140960795 + 4501248 * 2 ^ 59
def prefixEnd_4501248 : Nat := 4983230072969 + 3 ^ 40 * 4501248 * 2
def baseEnd_4501248 : Nat := 2311303769089310080199143

theorem tailTrace_4501248 : CollatzResearch.WordTrace tailWord_4501248 prefixEnd_4501248 2311303769089310080199143 := by
  unfold tailWord_4501248
  simp only [CollatzResearch.WordTrace]
  refine ⟨82087000998377361400020199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109449334664503148533360265 82087000998377361400020199)
  ·
    refine ⟨123130501497566042100030299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82087000998377361400020199 123130501497566042100030299)
    ·
      refine ⟨184695752246349063150045449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123130501497566042100030299 184695752246349063150045449)
      ·
        refine ⟨138521814184761797362534087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184695752246349063150045449 138521814184761797362534087)
        ·
          refine ⟨207782721277142696043801131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138521814184761797362534087 207782721277142696043801131)
          ·
            refine ⟨311674081915714044065701697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207782721277142696043801131 311674081915714044065701697)
            ·
              refine ⟨233755561436785533049276273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311674081915714044065701697 233755561436785533049276273)
              ·
                refine ⟨175316671077589149786957205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 233755561436785533049276273 175316671077589149786957205)
                ·
                  refine ⟨8217968956761991396263619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175316671077589149786957205 8217968956761991396263619)
                  ·
                    refine ⟨12326953435142987094395429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8217968956761991396263619 12326953435142987094395429)
                    ·
                      refine ⟨2311303769089310080199143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12326953435142987094395429 2311303769089310080199143)
                      ·
                        rfl

theorem cell23_4501248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_4501248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501248 prefixEnd_4501248 := by exact prefixLift 4501248
  have htrace : WordTrace (prefixWord ++ tailWord_4501248) baseStart_4501248 baseEnd_4501248 := by
    simpa [prefixWord, tailWord_4501248, baseEnd_4501248] using wordTrace_append hprefix tailTrace_4501248
  have hstable : (prefixWord ++ tailWord_4501248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501248).length < 2 ^ (prefixWord ++ tailWord_4501248).sum := by decide
  have hdescent : baseEnd_4501248 < baseStart_4501248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501265 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 2, 4, 2]
def baseStart_4501265 : Nat := 118140960795 + 4501265 * 2 ^ 59
def prefixEnd_4501265 : Nat := 4983230072969 + 3 ^ 40 * 4501265 * 2
def baseEnd_4501265 : Nat := 2311312498260436513686565

theorem tailTrace_4501265 : CollatzResearch.WordTrace tailWord_4501265 prefixEnd_4501265 2311312498260436513686565 := by
  unfold tailWord_4501265
  simp only [CollatzResearch.WordTrace]
  refine ⟨164174622037693134703409249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109449748025128756468939499 164174622037693134703409249)
  ·
    refine ⟨123130966528269851027556937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164174622037693134703409249 123130966528269851027556937)
    ·
      refine ⟨92348224896202388270667703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123130966528269851027556937 92348224896202388270667703)
      ·
        refine ⟨138522337344303582406001555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92348224896202388270667703 138522337344303582406001555)
        ·
          refine ⟨207783506016455373609002333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138522337344303582406001555 207783506016455373609002333)
          ·
            refine ⟨77918814756170765103375875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207783506016455373609002333 77918814756170765103375875)
            ·
              refine ⟨116878222134256147655063813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77918814756170765103375875 116878222134256147655063813)
              ·
                refine ⟨21914666650173027685324465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116878222134256147655063813 21914666650173027685324465)
                ·
                  refine ⟨16435999987629770763993349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21914666650173027685324465 16435999987629770763993349)
                  ·
                    refine ⟨3081749997680582018248753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16435999987629770763993349 3081749997680582018248753)
                    ·
                      refine ⟨2311312498260436513686565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081749997680582018248753 2311312498260436513686565)
                      ·
                        rfl

theorem cell23_4501265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_4501265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501265 prefixEnd_4501265 := by exact prefixLift 4501265
  have htrace : WordTrace (prefixWord ++ tailWord_4501265) baseStart_4501265 baseEnd_4501265 := by
    simpa [prefixWord, tailWord_4501265, baseEnd_4501265] using wordTrace_append hprefix tailTrace_4501265
  have hstable : (prefixWord ++ tailWord_4501265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501265).length < 2 ^ (prefixWord ++ tailWord_4501265).sum := by decide
  have hdescent : baseEnd_4501265 < baseStart_4501265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501266 : List Nat := [3, 2, 4, 1, 1, 3, 2, 2, 5]
def baseStart_4501266 : Nat := 118140960795 + 4501266 * 2 ^ 59
def prefixEnd_4501266 : Nat := 4983230072969 + 3 ^ 40 * 4501266 * 2
def baseEnd_4501266 : Nat := 256812556860121223308229

theorem tailTrace_4501266 : CollatzResearch.WordTrace tailWord_4501266 prefixEnd_4501266 256812556860121223308229 := by
  unfold tailWord_4501266
  simp only [CollatzResearch.WordTrace]
  refine ⟨41043664627672377968548913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109449772340459674582797101 41043664627672377968548913)
  ·
    refine ⟨30782748470754283476411685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41043664627672377968548913 30782748470754283476411685)
    ·
      refine ⟨5771765338266428151827191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30782748470754283476411685 5771765338266428151827191)
      ·
        refine ⟨8657648007399642227740787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771765338266428151827191 8657648007399642227740787)
        ·
          refine ⟨12986472011099463341611181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8657648007399642227740787 12986472011099463341611181)
          ·
            refine ⟨4869927004162298753104193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12986472011099463341611181 4869927004162298753104193)
            ·
              refine ⟨3652445253121724064828145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869927004162298753104193 3652445253121724064828145)
              ·
                refine ⟨2739333939841293048621109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652445253121724064828145 2739333939841293048621109)
                ·
                  refine ⟨256812556860121223308229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2739333939841293048621109 256812556860121223308229)
                  ·
                    rfl

theorem cell23_4501266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_4501266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501266 prefixEnd_4501266 := by exact prefixLift 4501266
  have htrace : WordTrace (prefixWord ++ tailWord_4501266) baseStart_4501266 baseEnd_4501266 := by
    simpa [prefixWord, tailWord_4501266, baseEnd_4501266] using wordTrace_append hprefix tailTrace_4501266
  have hstable : (prefixWord ++ tailWord_4501266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501266).length < 2 ^ (prefixWord ++ tailWord_4501266).sum := by decide
  have hdescent : baseEnd_4501266 < baseStart_4501266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501282 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_4501282 : Nat := 118140960795 + 4501282 * 2 ^ 59
def prefixEnd_4501282 : Nat := 4983230072969 + 3 ^ 40 * 4501282 * 2
def baseEnd_4501282 : Nat := 2311321227431562947173987

theorem tailTrace_4501282 : CollatzResearch.WordTrace tailWord_4501282 prefixEnd_4501282 2311321227431562947173987 := by
  unfold tailWord_4501282
  simp only [CollatzResearch.WordTrace]
  refine ⟨41043810519657886651694525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109450161385754364404518733 41043810519657886651694525)
  ·
    refine ⟨15391428944871707494385447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41043810519657886651694525 15391428944871707494385447)
    ·
      refine ⟨23087143417307561241578171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15391428944871707494385447 23087143417307561241578171)
      ·
        refine ⟨34630715125961341862367257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23087143417307561241578171 34630715125961341862367257)
        ·
          refine ⟨25973036344471006396775443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34630715125961341862367257 25973036344471006396775443)
          ·
            refine ⟨38959554516706509595163165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25973036344471006396775443 38959554516706509595163165)
            ·
              refine ⟨14609832943764941098186187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38959554516706509595163165 14609832943764941098186187)
              ·
                refine ⟨21914749415647411647279281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14609832943764941098186187 21914749415647411647279281)
                ·
                  refine ⟨16436062061735558735459461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21914749415647411647279281 16436062061735558735459461)
                  ·
                    refine ⟨3081761636575417262898649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16436062061735558735459461 3081761636575417262898649)
                    ·
                      refine ⟨2311321227431562947173987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081761636575417262898649 2311321227431562947173987)
                      ·
                        rfl

theorem cell23_4501282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_4501282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501282 prefixEnd_4501282 := by exact prefixLift 4501282
  have htrace : WordTrace (prefixWord ++ tailWord_4501282) baseStart_4501282 baseEnd_4501282 := by
    simpa [prefixWord, tailWord_4501282, baseEnd_4501282] using wordTrace_append hprefix tailTrace_4501282
  have hstable : (prefixWord ++ tailWord_4501282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501282).length < 2 ^ (prefixWord ++ tailWord_4501282).sum := by decide
  have hdescent : baseEnd_4501282 < baseStart_4501282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501299 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 2, 1, 4]
def baseStart_4501299 : Nat := 118140960795 + 4501299 * 2 ^ 59
def prefixEnd_4501299 : Nat := 4983230072969 + 3 ^ 40 * 4501299 * 2
def baseEnd_4501299 : Nat := 2311329956602689380661409

theorem tailTrace_4501299 : CollatzResearch.WordTrace tailWord_4501299 prefixEnd_4501299 2311329956602689380661409 := by
  unfold tailWord_4501299
  simp only [CollatzResearch.WordTrace]
  refine ⟨164175862119569958510146951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109450574746379972340097967 164175862119569958510146951)
  ·
    refine ⟨246263793179354937765220427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164175862119569958510146951 246263793179354937765220427)
    ·
      refine ⟨369395689769032406647830641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246263793179354937765220427 369395689769032406647830641)
      ·
        refine ⟨277046767326774304985872981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369395689769032406647830641 277046767326774304985872981)
        ·
          refine ⟨3246641804610636386553199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 277046767326774304985872981 3246641804610636386553199)
          ·
            refine ⟨4869962706915954579829799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246641804610636386553199 4869962706915954579829799)
            ·
              refine ⟨7304944060373931869744699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4869962706915954579829799 7304944060373931869744699)
              ·
                refine ⟨10957416090560897804617049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7304944060373931869744699 10957416090560897804617049)
                ·
                  refine ⟨8218062067920673353462787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10957416090560897804617049 8218062067920673353462787)
                  ·
                    refine ⟨12327093101881010030194181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8218062067920673353462787 12327093101881010030194181)
                    ·
                      refine ⟨2311329956602689380661409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12327093101881010030194181 2311329956602689380661409)
                      ·
                        rfl

theorem cell23_4501299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 2, 1, 4].length) (baseStart_4501299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501299 prefixEnd_4501299 := by exact prefixLift 4501299
  have htrace : WordTrace (prefixWord ++ tailWord_4501299) baseStart_4501299 baseEnd_4501299 := by
    simpa [prefixWord, tailWord_4501299, baseEnd_4501299] using wordTrace_append hprefix tailTrace_4501299
  have hstable : (prefixWord ++ tailWord_4501299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501299).length < 2 ^ (prefixWord ++ tailWord_4501299).sum := by decide
  have hdescent : baseEnd_4501299 < baseStart_4501299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501309 : List Nat := [1, 4, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_4501309 : Nat := 118140960795 + 4501309 * 2 ^ 59
def prefixEnd_4501309 : Nat := 4983230072969 + 3 ^ 40 * 4501309 * 2
def baseEnd_4501309 : Nat := 770445030469744780512121

theorem tailTrace_4501309 : CollatzResearch.WordTrace tailWord_4501309 prefixEnd_4501309 770445030469744780512121 := by
  unfold tailWord_4501309
  simp only [CollatzResearch.WordTrace]
  refine ⟨164176226849533730218010981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109450817899689153478673987 164176226849533730218010981)
  ·
    refine ⟨30783042534287574415877059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164176226849533730218010981 30783042534287574415877059)
    ·
      refine ⟨46174563801431361623815589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30783042534287574415877059 46174563801431361623815589)
      ·
        refine ⟨8657730712768380304465423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46174563801431361623815589 8657730712768380304465423)
        ·
          refine ⟨12986596069152570456698135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8657730712768380304465423 12986596069152570456698135)
          ·
            refine ⟨19479894103728855685047203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12986596069152570456698135 19479894103728855685047203)
            ·
              refine ⟨29219841155593283527570805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19479894103728855685047203 29219841155593283527570805)
              ·
                refine ⟨2739360108336870330709763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29219841155593283527570805 2739360108336870330709763)
                ·
                  refine ⟨4109040162505305496064645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739360108336870330709763 4109040162505305496064645)
                  ·
                    refine ⟨770445030469744780512121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4109040162505305496064645 770445030469744780512121)
                    ·
                      rfl

theorem cell23_4501309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_4501309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501309 prefixEnd_4501309 := by exact prefixLift 4501309
  have htrace : WordTrace (prefixWord ++ tailWord_4501309) baseStart_4501309 baseEnd_4501309 := by
    simpa [prefixWord, tailWord_4501309, baseEnd_4501309] using wordTrace_append hprefix tailTrace_4501309
  have hstable : (prefixWord ++ tailWord_4501309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501309).length < 2 ^ (prefixWord ++ tailWord_4501309).sum := by decide
  have hdescent : baseEnd_4501309 < baseStart_4501309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501352 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 1, 5]
def baseStart_4501352 : Nat := 118140960795 + 4501352 * 2 ^ 59
def prefixEnd_4501352 : Nat := 4983230072969 + 3 ^ 40 * 4501352 * 2
def baseEnd_4501352 : Nat := 770452390359125891099555

theorem tailTrace_4501352 : CollatzResearch.WordTrace tailWord_4501352 prefixEnd_4501352 770452390359125891099555 := by
  unfold tailWord_4501352
  simp only [CollatzResearch.WordTrace]
  refine ⟨82088897594188974280913155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109451863458918632374550873 82088897594188974280913155)
  ·
    refine ⟨123133346391283461421369733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82088897594188974280913155 123133346391283461421369733)
    ·
      refine ⟨23087502448365649016506825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123133346391283461421369733 23087502448365649016506825)
      ·
        refine ⟨17315626836274236762380119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23087502448365649016506825 17315626836274236762380119)
        ·
          refine ⟨25973440254411355143570179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17315626836274236762380119 25973440254411355143570179)
          ·
            refine ⟨38960160381617032715355269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25973440254411355143570179 38960160381617032715355269)
            ·
              refine ⟨7305030071553193634129113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38960160381617032715355269 7305030071553193634129113)
              ·
                refine ⟨5478772553664895225596835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7305030071553193634129113 5478772553664895225596835)
                ·
                  refine ⟨8218158830497342838395253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5478772553664895225596835 8218158830497342838395253)
                  ·
                    refine ⟨770452390359125891099555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8218158830497342838395253 770452390359125891099555)
                    ·
                      rfl

theorem cell23_4501352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_4501352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501352 prefixEnd_4501352 := by exact prefixLift 4501352
  have htrace : WordTrace (prefixWord ++ tailWord_4501352) baseStart_4501352 baseEnd_4501352 := by
    simpa [prefixWord, tailWord_4501352, baseEnd_4501352] using wordTrace_append hprefix tailTrace_4501352
  have hstable : (prefixWord ++ tailWord_4501352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501352).length < 2 ^ (prefixWord ++ tailWord_4501352).sum := by decide
  have hdescent : baseEnd_4501352 < baseStart_4501352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501355 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 8, 2]
def baseStart_4501355 : Nat := 118140960795 + 4501355 * 2 ^ 59
def prefixEnd_4501355 : Nat := 4983230072969 + 3 ^ 40 * 4501355 * 2
def baseEnd_4501355 : Nat := 2311358711519341161561151

theorem tailTrace_4501355 : CollatzResearch.WordTrace tailWord_4501355 prefixEnd_4501355 2311358711519341161561151 := by
  unfold tailWord_4501355
  simp only [CollatzResearch.WordTrace]
  refine ⟨164177904607367080074185519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109451936404911386716123679 164177904607367080074185519)
  ·
    refine ⟨246266856911050620111278279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164177904607367080074185519 246266856911050620111278279)
    ·
      refine ⟨369400285366575930166917419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246266856911050620111278279 369400285366575930166917419)
      ·
        refine ⟨554100428049863895250376129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369400285366575930166917419 554100428049863895250376129)
        ·
          refine ⟨415575321037397921437782097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 554100428049863895250376129 415575321037397921437782097)
          ·
            refine ⟨311681490778048441078336573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415575321037397921437782097 311681490778048441078336573)
            ·
              refine ⟨116880559041768165404376215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 311681490778048441078336573 116880559041768165404376215)
              ·
                refine ⟨175320838562652248106564323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116880559041768165404376215 175320838562652248106564323)
                ·
                  refine ⟨262981257843978372159846485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175320838562652248106564323 262981257843978372159846485)
                  ·
                    refine ⟨3081811615359121548748201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 262981257843978372159846485 3081811615359121548748201)
                    ·
                      refine ⟨2311358711519341161561151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081811615359121548748201 2311358711519341161561151)
                      ·
                        rfl

theorem cell23_4501355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 8, 2].length) (baseStart_4501355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501355 prefixEnd_4501355 := by exact prefixLift 4501355
  have htrace : WordTrace (prefixWord ++ tailWord_4501355) baseStart_4501355 baseEnd_4501355 := by
    simpa [prefixWord, tailWord_4501355, baseEnd_4501355] using wordTrace_append hprefix tailTrace_4501355
  have hstable : (prefixWord ++ tailWord_4501355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501355).length < 2 ^ (prefixWord ++ tailWord_4501355).sum := by decide
  have hdescent : baseEnd_4501355 < baseStart_4501355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501365 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4501365 : Nat := 118140960795 + 4501365 * 2 ^ 59
def prefixEnd_4501365 : Nat := 4983230072969 + 3 ^ 40 * 4501365 * 2
def baseEnd_4501365 : Nat := 770454615441962040812035

theorem tailTrace_4501365 : CollatzResearch.WordTrace tailWord_4501365 prefixEnd_4501365 770454615441962040812035 := by
  unfold tailWord_4501365
  simp only [CollatzResearch.WordTrace]
  refine ⟨164178269337330851782049549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109452179558220567854699699 164178269337330851782049549)
  ·
    refine ⟨61566851001499069418268581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164178269337330851782049549 61566851001499069418268581)
    ·
      refine ⟨11543784562781075515925359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61566851001499069418268581 11543784562781075515925359)
      ·
        refine ⟨17315676844171613273888039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11543784562781075515925359 17315676844171613273888039)
        ·
          refine ⟨25973515266257419910832059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17315676844171613273888039 25973515266257419910832059)
          ·
            refine ⟨38960272899386129866248089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25973515266257419910832059 38960272899386129866248089)
            ·
              refine ⟨29220204674539597399686067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38960272899386129866248089 29220204674539597399686067)
              ·
                refine ⟨43830307011809396099529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29220204674539597399686067 43830307011809396099529101)
                ·
                  refine ⟨16436365129428523537323413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43830307011809396099529101 16436365129428523537323413)
                  ·
                    refine ⟨770454615441962040812035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16436365129428523537323413 770454615441962040812035)
                    ·
                      rfl

theorem cell23_4501365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4501365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501365 prefixEnd_4501365 := by exact prefixLift 4501365
  have htrace : WordTrace (prefixWord ++ tailWord_4501365) baseStart_4501365 baseEnd_4501365 := by
    simpa [prefixWord, tailWord_4501365, baseEnd_4501365] using wordTrace_append hprefix tailTrace_4501365
  have hstable : (prefixWord ++ tailWord_4501365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501365).length < 2 ^ (prefixWord ++ tailWord_4501365).sum := by decide
  have hdescent : baseEnd_4501365 < baseStart_4501365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501375 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 3]
def baseStart_4501375 : Nat := 118140960795 + 4501375 * 2 ^ 59
def prefixEnd_4501375 : Nat := 4983230072969 + 3 ^ 40 * 4501375 * 2
def baseEnd_4501375 : Nat := 2311368981132431083311059

theorem tailTrace_4501375 : CollatzResearch.WordTrace tailWord_4501375 prefixEnd_4501375 2311368981132431083311059 := by
  unfold tailWord_4501375
  simp only [CollatzResearch.WordTrace]
  refine ⟨164178634067294623489913579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109452422711529748993275719 164178634067294623489913579)
  ·
    refine ⟨246267951100941935234870369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164178634067294623489913579 246267951100941935234870369)
    ·
      refine ⟨184700963325706451426152777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246267951100941935234870369 184700963325706451426152777)
      ·
        refine ⟨138525722494279838569614583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184700963325706451426152777 138525722494279838569614583)
        ·
          refine ⟨207788583741419757854421875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138525722494279838569614583 207788583741419757854421875)
          ·
            refine ⟨311682875612129636781632813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207788583741419757854421875 311682875612129636781632813)
            ·
              refine ⟨116881078354548613793112305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 311682875612129636781632813 116881078354548613793112305)
              ·
                refine ⟨87660808765911460344834229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116881078354548613793112305 87660808765911460344834229)
                ·
                  refine ⟨8218200821804199407328209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87660808765911460344834229 8218200821804199407328209)
                  ·
                    refine ⟨6163650616353149555496157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8218200821804199407328209 6163650616353149555496157)
                    ·
                      refine ⟨2311368981132431083311059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163650616353149555496157 2311368981132431083311059)
                      ·
                        rfl

theorem cell23_4501375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_4501375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501375 prefixEnd_4501375 := by exact prefixLift 4501375
  have htrace : WordTrace (prefixWord ++ tailWord_4501375) baseStart_4501375 baseEnd_4501375 := by
    simpa [prefixWord, tailWord_4501375, baseEnd_4501375] using wordTrace_append hprefix tailTrace_4501375
  have hstable : (prefixWord ++ tailWord_4501375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501375).length < 2 ^ (prefixWord ++ tailWord_4501375).sum := by decide
  have hdescent : baseEnd_4501375 < baseStart_4501375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501383 : List Nat := [1, 1, 4, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_4501383 : Nat := 118140960795 + 4501383 * 2 ^ 59
def prefixEnd_4501383 : Nat := 4983230072969 + 3 ^ 40 * 4501383 * 2
def baseEnd_4501383 : Nat := 2311373088977667052011023

theorem tailTrace_4501383 : CollatzResearch.WordTrace tailWord_4501383 prefixEnd_4501383 2311373088977667052011023 := by
  unfold tailWord_4501383
  simp only [CollatzResearch.WordTrace]
  refine ⟨164178925851265640856204803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109452617234177093904136535 164178925851265640856204803)
  ·
    refine ⟨246268388776898461284307205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164178925851265640856204803 246268388776898461284307205)
    ·
      refine ⟨46175322895668461490807601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246268388776898461284307205 46175322895668461490807601)
      ·
        refine ⟨34631492171751346118105701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46175322895668461490807601 34631492171751346118105701)
        ·
          refine ⟨6493404782203377397144819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34631492171751346118105701 6493404782203377397144819)
          ·
            refine ⟨9740107173305066095717229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493404782203377397144819 9740107173305066095717229)
            ·
              refine ⟨3652540189989399785893961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9740107173305066095717229 3652540189989399785893961)
              ·
                refine ⟨2739405142492049839420471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652540189989399785893961 2739405142492049839420471)
                ·
                  refine ⟨4109107713738074759130707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739405142492049839420471 4109107713738074759130707)
                  ·
                    refine ⟨6163661570607112138696061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109107713738074759130707 6163661570607112138696061)
                    ·
                      refine ⟨2311373088977667052011023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163661570607112138696061 2311373088977667052011023)
                      ·
                        rfl

theorem cell23_4501383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_4501383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501383 prefixEnd_4501383 := by exact prefixLift 4501383
  have htrace : WordTrace (prefixWord ++ tailWord_4501383) baseStart_4501383 baseEnd_4501383 := by
    simpa [prefixWord, tailWord_4501383, baseEnd_4501383] using wordTrace_append hprefix tailTrace_4501383
  have hstable : (prefixWord ++ tailWord_4501383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501383).length < 2 ^ (prefixWord ++ tailWord_4501383).sum := by decide
  have hdescent : baseEnd_4501383 < baseStart_4501383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501399 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 2, 4]
def baseStart_4501399 : Nat := 118140960795 + 4501399 * 2 ^ 59
def prefixEnd_4501399 : Nat := 4983230072969 + 3 ^ 40 * 4501399 * 2
def baseEnd_4501399 : Nat := 770460434889379663136983

theorem tailTrace_4501399 : CollatzResearch.WordTrace tailWord_4501399 prefixEnd_4501399 770460434889379663136983 := by
  unfold tailWord_4501399
  simp only [CollatzResearch.WordTrace]
  refine ⟨164179509419207675588787251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109453006279471783725858167 164179509419207675588787251)
  ·
    refine ⟨246269264128811513383180877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164179509419207675588787251 246269264128811513383180877)
    ·
      refine ⟨92350974048304317518692829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246269264128811513383180877 92350974048304317518692829)
      ·
        refine ⟨34631615268114119069509811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92350974048304317518692829 34631615268114119069509811)
        ·
          refine ⟨51947422902171178604264717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34631615268114119069509811 51947422902171178604264717)
          ·
            refine ⟨19480283588314191976599269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51947422902171178604264717 19480283588314191976599269)
            ·
              refine ⟨3652553172808910995612363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19480283588314191976599269 3652553172808910995612363)
              ·
                refine ⟨5478829759213366493418545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3652553172808910995612363 5478829759213366493418545)
                ·
                  refine ⟨4109122319410024870063909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5478829759213366493418545 4109122319410024870063909)
                  ·
                    refine ⟨770460434889379663136983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4109122319410024870063909 770460434889379663136983)
                    ·
                      rfl

theorem cell23_4501399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_4501399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501399 prefixEnd_4501399 := by exact prefixLift 4501399
  have htrace : WordTrace (prefixWord ++ tailWord_4501399) baseStart_4501399 baseEnd_4501399 := by
    simpa [prefixWord, tailWord_4501399, baseEnd_4501399] using wordTrace_append hprefix tailTrace_4501399
  have hstable : (prefixWord ++ tailWord_4501399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501399).length < 2 ^ (prefixWord ++ tailWord_4501399).sum := by decide
  have hdescent : baseEnd_4501399 < baseStart_4501399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501406 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4501406 : Nat := 118140960795 + 4501406 * 2 ^ 59
def prefixEnd_4501406 : Nat := 4983230072969 + 3 ^ 40 * 4501406 * 2
def baseEnd_4501406 : Nat := 2311384899032720462023417

theorem tailTrace_4501406 : CollatzResearch.WordTrace tailWord_4501406 prefixEnd_4501406 2311384899032720462023417 := by
  unfold tailWord_4501406
  simp only [CollatzResearch.WordTrace]
  refine ⟨20522470591272789473036509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109453176486788210522861381 20522470591272789473036509)
  ·
    refine ⟨7695926471727296052388691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20522470591272789473036509 7695926471727296052388691)
    ·
      refine ⟨11543889707590944078583037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7695926471727296052388691 11543889707590944078583037)
      ·
        refine ⟨4328958640346604029468639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11543889707590944078583037 4328958640346604029468639)
        ·
          refine ⟨6493437960519906044202959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328958640346604029468639 6493437960519906044202959)
          ·
            refine ⟨9740156940779859066304439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493437960519906044202959 9740156940779859066304439)
            ·
              refine ⟨14610235411169788599456659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9740156940779859066304439 14610235411169788599456659)
              ·
                refine ⟨21915353116754682899184989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14610235411169788599456659 21915353116754682899184989)
                ·
                  refine ⟨8218257418783006087194371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21915353116754682899184989 8218257418783006087194371)
                  ·
                    refine ⟨12327386128174509130791557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8218257418783006087194371 12327386128174509130791557)
                    ·
                      refine ⟨2311384899032720462023417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12327386128174509130791557 2311384899032720462023417)
                      ·
                        rfl

theorem cell23_4501406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4501406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501406 prefixEnd_4501406 := by exact prefixLift 4501406
  have htrace : WordTrace (prefixWord ++ tailWord_4501406) baseStart_4501406 baseEnd_4501406 := by
    simpa [prefixWord, tailWord_4501406, baseEnd_4501406] using wordTrace_append hprefix tailTrace_4501406
  have hstable : (prefixWord ++ tailWord_4501406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501406).length < 2 ^ (prefixWord ++ tailWord_4501406).sum := by decide
  have hdescent : baseEnd_4501406 < baseStart_4501406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501409 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4501409 : Nat := 118140960795 + 4501409 * 2 ^ 59
def prefixEnd_4501409 : Nat := 4983230072969 + 3 ^ 40 * 4501409 * 2
def baseEnd_4501409 : Nat := 2311386439474683950285903

theorem tailTrace_4501409 : CollatzResearch.WordTrace tailWord_4501409 prefixEnd_4501409 2311386439474683950285903 := by
  unfold tailWord_4501409
  simp only [CollatzResearch.WordTrace]
  refine ⟨164179874149171447296651281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109453249432780964864434187 164179874149171447296651281)
  ·
    refine ⟨123134905611878585472488461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164179874149171447296651281 123134905611878585472488461)
    ·
      refine ⟨46175589604454469552183173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123134905611878585472488461 46175589604454469552183173)
      ·
        refine ⟨8657923050835213041034345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46175589604454469552183173 8657923050835213041034345)
        ·
          refine ⟨6493442288126409780775759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8657923050835213041034345 6493442288126409780775759)
          ·
            refine ⟨9740163432189614671163639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493442288126409780775759 9740163432189614671163639)
            ·
              refine ⟨14610245148284422006745459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9740163432189614671163639 14610245148284422006745459)
              ·
                refine ⟨21915367722426633010118189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14610245148284422006745459 21915367722426633010118189)
                ·
                  refine ⟨8218262895909987378794321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21915367722426633010118189 8218262895909987378794321)
                  ·
                    refine ⟨6163697171932490534095741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8218262895909987378794321 6163697171932490534095741)
                    ·
                      refine ⟨2311386439474683950285903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163697171932490534095741 2311386439474683950285903)
                      ·
                        rfl

theorem cell23_4501409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4501409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501409 prefixEnd_4501409 := by exact prefixLift 4501409
  have htrace : WordTrace (prefixWord ++ tailWord_4501409) baseStart_4501409 baseEnd_4501409 := by
    simpa [prefixWord, tailWord_4501409, baseEnd_4501409] using wordTrace_append hprefix tailTrace_4501409
  have hstable : (prefixWord ++ tailWord_4501409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501409).length < 2 ^ (prefixWord ++ tailWord_4501409).sum := by decide
  have hdescent : baseEnd_4501409 < baseStart_4501409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501439 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 3]
def baseStart_4501439 : Nat := 118140960795 + 4501439 * 2 ^ 59
def prefixEnd_4501439 : Nat := 4983230072969 + 3 ^ 40 * 4501439 * 2
def baseEnd_4501439 : Nat := 2311401843894318832910765

theorem tailTrace_4501439 : CollatzResearch.WordTrace tailWord_4501439 prefixEnd_4501439 2311401843894318832910765 := by
  unfold tailWord_4501439
  simp only [CollatzResearch.WordTrace]
  refine ⟨164180968339062762420243371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109453978892708508280162247 164180968339062762420243371)
  ·
    refine ⟨246271452508594143630365057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164180968339062762420243371 246271452508594143630365057)
    ·
      refine ⟨184703589381445607722773793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246271452508594143630365057 184703589381445607722773793)
      ·
        refine ⟨138527692036084205792080345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184703589381445607722773793 138527692036084205792080345)
        ·
          refine ⟨103895769027063154344060259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138527692036084205792080345 103895769027063154344060259)
          ·
            refine ⟨155843653540594731516090389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103895769027063154344060259 155843653540594731516090389)
            ·
              refine ⟨7305171259715378039816737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155843653540594731516090389 7305171259715378039816737)
              ·
                refine ⟨5478878444786533529862553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7305171259715378039816737 5478878444786533529862553)
                ·
                  refine ⟨4109158833589900147396915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5478878444786533529862553 4109158833589900147396915)
                  ·
                    refine ⟨6163738250384850221095373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109158833589900147396915 6163738250384850221095373)
                    ·
                      refine ⟨2311401843894318832910765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163738250384850221095373 2311401843894318832910765)
                      ·
                        rfl

theorem cell23_4501439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_4501439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501439 prefixEnd_4501439 := by exact prefixLift 4501439
  have htrace : WordTrace (prefixWord ++ tailWord_4501439) baseStart_4501439 baseEnd_4501439 := by
    simpa [prefixWord, tailWord_4501439, baseEnd_4501439] using wordTrace_append hprefix tailTrace_4501439
  have hstable : (prefixWord ++ tailWord_4501439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501439).length < 2 ^ (prefixWord ++ tailWord_4501439).sum := by decide
  have hdescent : baseEnd_4501439 < baseStart_4501439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501455 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 2, 6]
def baseStart_4501455 : Nat := 118140960795 + 4501455 * 2 ^ 59
def prefixEnd_4501455 : Nat := 4983230072969 + 3 ^ 40 * 4501455 * 2
def baseEnd_4501455 : Nat := 770470019861596923436897

theorem tailTrace_4501455 : CollatzResearch.WordTrace tailWord_4501455 prefixEnd_4501455 770470019861596923436897 := by
  unfold tailWord_4501455
  simp only [CollatzResearch.WordTrace]
  refine ⟨164181551907004797152825819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109454367938003198101883879 164181551907004797152825819)
  ·
    refine ⟨246272327860507195729238729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164181551907004797152825819 246272327860507195729238729)
    ·
      refine ⟨184704245895380396796929047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246272327860507195729238729 184704245895380396796929047)
      ·
        refine ⟨277056368843070595195393571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184704245895380396796929047 277056368843070595195393571)
        ·
          refine ⟨415584553264605892793090357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277056368843070595195393571 415584553264605892793090357)
          ·
            refine ⟨38961051868556802449352221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 415584553264605892793090357 38961051868556802449352221)
            ·
              refine ⟨14610394450708800918507083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38961051868556802449352221 14610394450708800918507083)
              ·
                refine ⟨21915591676063201377760625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14610394450708800918507083 21915591676063201377760625)
                ·
                  refine ⟨16436693757047401033320469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21915591676063201377760625 16436693757047401033320469)
                  ·
                    refine ⟨770470019861596923436897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16436693757047401033320469 770470019861596923436897)
                    ·
                      rfl

theorem cell23_4501455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_4501455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501455 prefixEnd_4501455 := by exact prefixLift 4501455
  have htrace : WordTrace (prefixWord ++ tailWord_4501455) baseStart_4501455 baseEnd_4501455 := by
    simpa [prefixWord, tailWord_4501455, baseEnd_4501455] using wordTrace_append hprefix tailTrace_4501455
  have hstable : (prefixWord ++ tailWord_4501455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501455).length < 2 ^ (prefixWord ++ tailWord_4501455).sum := by decide
  have hdescent : baseEnd_4501455 < baseStart_4501455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501496 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 2, 2, 2]
def baseStart_4501496 : Nat := 118140960795 + 4501496 * 2 ^ 59
def prefixEnd_4501496 : Nat := 4983230072969 + 3 ^ 40 * 4501496 * 2
def baseEnd_4501496 : Nat := 2311431112291625109898003

theorem tailTrace_4501496 : CollatzResearch.WordTrace tailWord_4501496 prefixEnd_4501496 2311431112291625109898003 := by
  unfold tailWord_4501496
  simp only [CollatzResearch.WordTrace]
  refine ⟨82091523649928130577534171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109455364866570840770045561 82091523649928130577534171)
  ·
    refine ⟨123137285474892195866301257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82091523649928130577534171 123137285474892195866301257)
    ·
      refine ⟨92352964106169146899725943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123137285474892195866301257 92352964106169146899725943)
      ·
        refine ⟨138529446159253720349588915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92352964106169146899725943 138529446159253720349588915)
        ·
          refine ⟨207794169238880580524383373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138529446159253720349588915 207794169238880580524383373)
          ·
            refine ⟨77922813464580217696643765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207794169238880580524383373 77922813464580217696643765)
            ·
              refine ⟨7305263762304395409060353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77922813464580217696643765 7305263762304395409060353)
              ·
                refine ⟨5478947821728296556795265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7305263762304395409060353 5478947821728296556795265)
                ·
                  refine ⟨4109210866296222417596449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5478947821728296556795265 4109210866296222417596449)
                  ·
                    refine ⟨3081908149722166813197337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4109210866296222417596449 3081908149722166813197337)
                    ·
                      refine ⟨2311431112291625109898003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081908149722166813197337 2311431112291625109898003)
                      ·
                        rfl

theorem cell23_4501496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_4501496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501496 prefixEnd_4501496 := by exact prefixLift 4501496
  have htrace : WordTrace (prefixWord ++ tailWord_4501496) baseStart_4501496 baseEnd_4501496 := by
    simpa [prefixWord, tailWord_4501496, baseEnd_4501496] using wordTrace_append hprefix tailTrace_4501496
  have hstable : (prefixWord ++ tailWord_4501496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501496).length < 2 ^ (prefixWord ++ tailWord_4501496).sum := by decide
  have hdescent : baseEnd_4501496 < baseStart_4501496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501512 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_4501512 : Nat := 118140960795 + 4501512 * 2 ^ 59
def prefixEnd_4501512 : Nat := 4983230072969 + 3 ^ 40 * 4501512 * 2
def baseEnd_4501512 : Nat := 2311439327982097047297929

theorem tailTrace_4501512 : CollatzResearch.WordTrace tailWord_4501512 prefixEnd_4501512 2311439327982097047297929 := by
  unfold tailWord_4501512
  simp only [CollatzResearch.WordTrace]
  refine ⟨82091815433899147943825395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109455753911865530591767193 82091815433899147943825395)
  ·
    refine ⟨123137723150848721915738093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82091815433899147943825395 123137723150848721915738093)
    ·
      refine ⟨46176646181568270718401785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123137723150848721915738093 46176646181568270718401785)
      ·
        refine ⟨34632484636176203038801339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46176646181568270718401785 34632484636176203038801339)
        ·
          refine ⟨51948726954264304558202009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34632484636176203038801339 51948726954264304558202009)
          ·
            refine ⟨38961545215698228418651507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51948726954264304558202009 38961545215698228418651507)
            ·
              refine ⟨58442317823547342627977261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38961545215698228418651507 58442317823547342627977261)
              ·
                refine ⟨21915869183830253485491473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58442317823547342627977261 21915869183830253485491473)
                ·
                  refine ⟨16436901887872690114118605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21915869183830253485491473 16436901887872690114118605)
                  ·
                    refine ⟨6163838207952258792794477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16436901887872690114118605 6163838207952258792794477)
                    ·
                      refine ⟨2311439327982097047297929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163838207952258792794477 2311439327982097047297929)
                      ·
                        rfl

theorem cell23_4501512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_4501512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501512 prefixEnd_4501512 := by exact prefixLift 4501512
  have htrace : WordTrace (prefixWord ++ tailWord_4501512) baseStart_4501512 baseEnd_4501512 := by
    simpa [prefixWord, tailWord_4501512, baseEnd_4501512] using wordTrace_append hprefix tailTrace_4501512
  have hstable : (prefixWord ++ tailWord_4501512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501512).length < 2 ^ (prefixWord ++ tailWord_4501512).sum := by decide
  have hdescent : baseEnd_4501512 < baseStart_4501512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501515 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 3, 7]
def baseStart_4501515 : Nat := 118140960795 + 4501515 * 2 ^ 59
def prefixEnd_4501515 : Nat := 4983230072969 + 3 ^ 40 * 4501515 * 2
def baseEnd_4501515 : Nat := 770480289474686845186805

theorem tailTrace_4501515 : CollatzResearch.WordTrace tailWord_4501515 prefixEnd_4501515 770480289474686845186805 := by
  unfold tailWord_4501515
  simp only [CollatzResearch.WordTrace]
  refine ⟨164183740286787427400009999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109455826857858284933339999 164183740286787427400009999)
  ·
    refine ⟨246275610430181141100014999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164183740286787427400009999 246275610430181141100014999)
    ·
      refine ⟨369413415645271711650022499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246275610430181141100014999 369413415645271711650022499)
      ·
        refine ⟨554120123467907567475033749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369413415645271711650022499 554120123467907567475033749)
        ·
          refine ⟨25974380787558167225392207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 554120123467907567475033749 25974380787558167225392207)
          ·
            refine ⟨38961571181337250838088311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25974380787558167225392207 38961571181337250838088311)
            ·
              refine ⟨58442356772005876257132467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38961571181337250838088311 58442356772005876257132467)
              ·
                refine ⟨87663535158008814385698701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58442356772005876257132467 87663535158008814385698701)
                ·
                  refine ⟨32873825684253305394637013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87663535158008814385698701 32873825684253305394637013)
                  ·
                    refine ⟨770480289474686845186805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32873825684253305394637013 770480289474686845186805)
                    ·
                      rfl

theorem cell23_4501515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_4501515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501515 prefixEnd_4501515 := by exact prefixLift 4501515
  have htrace : WordTrace (prefixWord ++ tailWord_4501515) baseStart_4501515 baseEnd_4501515 := by
    simpa [prefixWord, tailWord_4501515, baseEnd_4501515] using wordTrace_append hprefix tailTrace_4501515
  have hstable : (prefixWord ++ tailWord_4501515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501515).length < 2 ^ (prefixWord ++ tailWord_4501515).sum := by decide
  have hdescent : baseEnd_4501515 < baseStart_4501515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501517 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4501517 : Nat := 118140960795 + 4501517 * 2 ^ 59
def prefixEnd_4501517 : Nat := 4983230072969 + 3 ^ 40 * 4501517 * 2
def baseEnd_4501517 : Nat := 2311441895385369527735407

theorem tailTrace_4501517 : CollatzResearch.WordTrace tailWord_4501517 prefixEnd_4501517 2311441895385369527735407 := by
  unfold tailWord_4501517
  simp only [CollatzResearch.WordTrace]
  refine ⟨164183813232780181741582805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109455875488520121161055203 164183813232780181741582805)
  ·
    refine ⟨3848058122643285509568347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 164183813232780181741582805 3848058122643285509568347)
    ·
      refine ⟨5772087183964928264352521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3848058122643285509568347 5772087183964928264352521)
      ·
        refine ⟨4329065387973696198264391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5772087183964928264352521 4329065387973696198264391)
        ·
          refine ⟨6493598081960544297396587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4329065387973696198264391 6493598081960544297396587)
          ·
            refine ⟨9740397122940816446094881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493598081960544297396587 9740397122940816446094881)
            ·
              refine ⟨7305297842205612334571161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9740397122940816446094881 7305297842205612334571161)
              ·
                refine ⟨5478973381654209250928371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7305297842205612334571161 5478973381654209250928371)
                ·
                  refine ⟨8218460072481313876392557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5478973381654209250928371 8218460072481313876392557)
                  ·
                    refine ⟨3081922527180492703647209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8218460072481313876392557 3081922527180492703647209)
                    ·
                      refine ⟨2311441895385369527735407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3081922527180492703647209 2311441895385369527735407)
                      ·
                        rfl

theorem cell23_4501517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4501517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501517 prefixEnd_4501517 := by exact prefixLift 4501517
  have htrace : WordTrace (prefixWord ++ tailWord_4501517) baseStart_4501517 baseEnd_4501517 := by
    simpa [prefixWord, tailWord_4501517, baseEnd_4501517] using wordTrace_append hprefix tailTrace_4501517
  have hstable : (prefixWord ++ tailWord_4501517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501517).length < 2 ^ (prefixWord ++ tailWord_4501517).sum := by decide
  have hdescent : baseEnd_4501517 < baseStart_4501517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501532 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_4501532 : Nat := 118140960795 + 4501532 * 2 ^ 59
def prefixEnd_4501532 : Nat := 4983230072969 + 3 ^ 40 * 4501532 * 2
def baseEnd_4501532 : Nat := 770483199198395656349279

theorem tailTrace_4501532 : CollatzResearch.WordTrace tailWord_4501532 prefixEnd_4501532 770483199198395656349279 := by
  unfold tailWord_4501532
  simp only [CollatzResearch.WordTrace]
  refine ⟨82092180163862919651689425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109456240218483892868919233 82092180163862919651689425)
  ·
    refine ⟨61569135122897189738767069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82092180163862919651689425 61569135122897189738767069)
    ·
      refine ⟨23088425671086446152037651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61569135122897189738767069 23088425671086446152037651)
      ·
        refine ⟨34632638506629669228056477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23088425671086446152037651 34632638506629669228056477)
        ·
          refine ⟨12987239439986125960521179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34632638506629669228056477 12987239439986125960521179)
          ·
            refine ⟨19480859159979188940781769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12987239439986125960521179 19480859159979188940781769)
            ·
              refine ⟨14610644369984391705586327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19480859159979188940781769 14610644369984391705586327)
              ·
                refine ⟨21915966554976587558379491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14610644369984391705586327 21915966554976587558379491)
                ·
                  refine ⟨32873949832464881337569237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21915966554976587558379491 32873949832464881337569237)
                  ·
                    refine ⟨770483199198395656349279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32873949832464881337569237 770483199198395656349279)
                    ·
                      rfl

theorem cell23_4501532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_4501532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501532 prefixEnd_4501532 := by exact prefixLift 4501532
  have htrace : WordTrace (prefixWord ++ tailWord_4501532) baseStart_4501532 baseEnd_4501532 := by
    simpa [prefixWord, tailWord_4501532, baseEnd_4501532] using wordTrace_append hprefix tailTrace_4501532
  have hstable : (prefixWord ++ tailWord_4501532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501532).length < 2 ^ (prefixWord ++ tailWord_4501532).sum := by decide
  have hdescent : baseEnd_4501532 < baseStart_4501532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501552 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_4501552 : Nat := 118140960795 + 4501552 * 2 ^ 59
def prefixEnd_4501552 : Nat := 4983230072969 + 3 ^ 40 * 4501552 * 2
def baseEnd_4501552 : Nat := 2311459867208276890797745

theorem tailTrace_4501552 : CollatzResearch.WordTrace tailWord_4501552 prefixEnd_4501552 2311459867208276890797745 := by
  unfold tailWord_4501552
  simp only [CollatzResearch.WordTrace]
  refine ⟨82092544893826691359553455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109456726525102255146071273 82092544893826691359553455)
  ·
    refine ⟨123138817340740037039330183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82092544893826691359553455 123138817340740037039330183)
    ·
      refine ⟨184708226011110055558995275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123138817340740037039330183 184708226011110055558995275)
      ·
        refine ⟨277062339016665083338492913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184708226011110055558995275 277062339016665083338492913)
        ·
          refine ⟨207796754262498812503869685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277062339016665083338492913 207796754262498812503869685)
          ·
            refine ⟨19480945712109263672237783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 207796754262498812503869685 19480945712109263672237783)
            ·
              refine ⟨29221418568163895508356675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19480945712109263672237783 29221418568163895508356675)
              ·
                refine ⟨43832127852245843262535013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29221418568163895508356675 43832127852245843262535013)
                ·
                  refine ⟨8218523972296095611725315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43832127852245843262535013 8218523972296095611725315)
                  ·
                    refine ⟨12327785958444143417587973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8218523972296095611725315 12327785958444143417587973)
                    ·
                      refine ⟨2311459867208276890797745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12327785958444143417587973 2311459867208276890797745)
                      ·
                        rfl

theorem cell23_4501552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_4501552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501552 prefixEnd_4501552 := by exact prefixLift 4501552
  have htrace : WordTrace (prefixWord ++ tailWord_4501552) baseStart_4501552 baseEnd_4501552 := by
    simpa [prefixWord, tailWord_4501552, baseEnd_4501552] using wordTrace_append hprefix tailTrace_4501552
  have hstable : (prefixWord ++ tailWord_4501552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501552).length < 2 ^ (prefixWord ++ tailWord_4501552).sum := by decide
  have hdescent : baseEnd_4501552 < baseStart_4501552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501586 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_4501586 : Nat := 118140960795 + 4501586 * 2 ^ 59
def prefixEnd_4501586 : Nat := 4983230072969 + 3 ^ 40 * 4501586 * 2
def baseEnd_4501586 : Nat := 2311477325550529757772589

theorem tailTrace_4501586 : CollatzResearch.WordTrace tailWord_4501586 prefixEnd_4501586 2311477325550529757772589 := by
  unfold tailWord_4501586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41046582467382551631461153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109457553246353471017229741 41046582467382551631461153)
  ·
    refine ⟨30784936850536913723595865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41046582467382551631461153 30784936850536913723595865)
    ·
      refine ⟨23088702637902685292696899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30784936850536913723595865 23088702637902685292696899)
      ·
        refine ⟨34633053956854027939045349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23088702637902685292696899 34633053956854027939045349)
        ·
          refine ⟨6493697616910130238571003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34633053956854027939045349 6493697616910130238571003)
          ·
            refine ⟨9740546425365195357856505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493697616910130238571003 9740546425365195357856505)
            ·
              refine ⟨7305409819023896518392379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9740546425365195357856505 7305409819023896518392379)
              ·
                refine ⟨10958114728535844777588569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7305409819023896518392379 10958114728535844777588569)
                ·
                  refine ⟨8218586046401883583191427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10958114728535844777588569 8218586046401883583191427)
                  ·
                    refine ⟨12327879069602825374787141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8218586046401883583191427 12327879069602825374787141)
                    ·
                      refine ⟨2311477325550529757772589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12327879069602825374787141 2311477325550529757772589)
                      ·
                        rfl

theorem cell23_4501586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_4501586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501586 prefixEnd_4501586 := by exact prefixLift 4501586
  have htrace : WordTrace (prefixWord ++ tailWord_4501586) baseStart_4501586 baseEnd_4501586 := by
    simpa [prefixWord, tailWord_4501586, baseEnd_4501586] using wordTrace_append hprefix tailTrace_4501586
  have hstable : (prefixWord ++ tailWord_4501586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501586).length < 2 ^ (prefixWord ++ tailWord_4501586).sum := by decide
  have hdescent : baseEnd_4501586 < baseStart_4501586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501589 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4501589 : Nat := 118140960795 + 4501589 * 2 ^ 59
def prefixEnd_4501589 : Nat := 4983230072969 + 3 ^ 40 * 4501589 * 2
def baseEnd_4501589 : Nat := 2311478865992493246035075

theorem tailTrace_4501589 : CollatzResearch.WordTrace tailWord_4501589 prefixEnd_4501589 2311478865992493246035075 := by
  unfold tailWord_4501589
  simp only [CollatzResearch.WordTrace]
  refine ⟨164186439288519338038203821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109457626192346225358802547 164186439288519338038203821)
  ·
    refine ⟨61569914733194751764326433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164186439288519338038203821 61569914733194751764326433)
    ·
      refine ⟨46177436049896063823244825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61569914733194751764326433 46177436049896063823244825)
      ·
        refine ⟨34633077037422047867433619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46177436049896063823244825 34633077037422047867433619)
        ·
          refine ⟨51949615556133071801150429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34633077037422047867433619 51949615556133071801150429)
          ·
            refine ⟨19481105833549901925431411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51949615556133071801150429 19481105833549901925431411)
            ·
              refine ⟨29221658750324852888147117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19481105833549901925431411 29221658750324852888147117)
              ·
                refine ⟨10958122031371819833055169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29221658750324852888147117 10958122031371819833055169)
                ·
                  refine ⟨8218591523528864874791377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10958122031371819833055169 8218591523528864874791377)
                  ·
                    refine ⟨6163943642646648656093533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8218591523528864874791377 6163943642646648656093533)
                    ·
                      refine ⟨2311478865992493246035075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6163943642646648656093533 2311478865992493246035075)
                      ·
                        rfl

theorem cell23_4501589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4501589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501589 prefixEnd_4501589 := by exact prefixLift 4501589
  have htrace : WordTrace (prefixWord ++ tailWord_4501589) baseStart_4501589 baseEnd_4501589 := by
    simpa [prefixWord, tailWord_4501589, baseEnd_4501589] using wordTrace_append hprefix tailTrace_4501589
  have hstable : (prefixWord ++ tailWord_4501589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501589).length < 2 ^ (prefixWord ++ tailWord_4501589).sum := by decide
  have hdescent : baseEnd_4501589 < baseStart_4501589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501636 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_4501636 : Nat := 118140960795 + 4501636 * 2 ^ 59
def prefixEnd_4501636 : Nat := 4983230072969 + 3 ^ 40 * 4501636 * 2
def baseEnd_4501636 : Nat := 2311502999583254562147359

theorem tailTrace_4501636 : CollatzResearch.WordTrace tailWord_4501636 prefixEnd_4501636 2311502999583254562147359 := by
  unfold tailWord_4501636
  simp only [CollatzResearch.WordTrace]
  refine ⟨82094076759674532532582381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109458769012899376710109841 82094076759674532532582381)
  ·
    refine ⟨30785278784877949699718393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82094076759674532532582381 30785278784877949699718393)
    ·
      refine ⟨23088959088658462274788795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30785278784877949699718393 23088959088658462274788795)
      ·
        refine ⟨34633438632987693412183193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23088959088658462274788795 34633438632987693412183193)
        ·
          refine ⟨25975078974740770059137395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34633438632987693412183193 25975078974740770059137395)
          ·
            refine ⟨38962618462111155088706093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25975078974740770059137395 38962618462111155088706093)
            ·
              refine ⟨14610981923291683158264785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38962618462111155088706093 14610981923291683158264785)
              ·
                refine ⟨10958236442468762368698589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14610981923291683158264785 10958236442468762368698589)
                ·
                  refine ⟨4109338665925785888261971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10958236442468762368698589 4109338665925785888261971)
                  ·
                    refine ⟨6164007998888678832392957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109338665925785888261971 6164007998888678832392957)
                    ·
                      refine ⟨2311502999583254562147359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164007998888678832392957 2311502999583254562147359)
                      ·
                        rfl

theorem cell23_4501636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_4501636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501636 prefixEnd_4501636 := by exact prefixLift 4501636
  have htrace : WordTrace (prefixWord ++ tailWord_4501636) baseStart_4501636 baseEnd_4501636 := by
    simpa [prefixWord, tailWord_4501636, baseEnd_4501636] using wordTrace_append hprefix tailTrace_4501636
  have hstable : (prefixWord ++ tailWord_4501636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501636).length < 2 ^ (prefixWord ++ tailWord_4501636).sum := by decide
  have hdescent : baseEnd_4501636 < baseStart_4501636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501653 : List Nat := [1, 3, 2, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_4501653 : Nat := 118140960795 + 4501653 * 2 ^ 59
def prefixEnd_4501653 : Nat := 4983230072969 + 3 ^ 40 * 4501653 * 2
def baseEnd_4501653 : Nat := 2311511728754380995634781

theorem tailTrace_4501653 : CollatzResearch.WordTrace tailWord_4501653 prefixEnd_4501653 2311511728754380995634781 := by
  unfold tailWord_4501653
  simp only [CollatzResearch.WordTrace]
  refine ⟨164188773560287476968533613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109459182373524984645689075 164188773560287476968533613)
  ·
    refine ⟨61570790085107803863200105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164188773560287476968533613 61570790085107803863200105)
    ·
      refine ⟨46178092563830852897400079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61570790085107803863200105 46178092563830852897400079)
      ·
        refine ⟨69267138845746279346100119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46178092563830852897400079 69267138845746279346100119)
        ·
          refine ⟨103900708268619419019150179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69267138845746279346100119 103900708268619419019150179)
          ·
            refine ⟨155851062402929128528725269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103900708268619419019150179 155851062402929128528725269)
            ·
              refine ⟨7305518550137302899783997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155851062402929128528725269 7305518550137302899783997)
              ·
                refine ⟨2739569456301488587418999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7305518550137302899783997 2739569456301488587418999)
                ·
                  refine ⟨4109354184452232881128499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739569456301488587418999 4109354184452232881128499)
                  ·
                    refine ⟨6164031276678349321692749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109354184452232881128499 6164031276678349321692749)
                    ·
                      refine ⟨2311511728754380995634781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164031276678349321692749 2311511728754380995634781)
                      ·
                        rfl

theorem cell23_4501653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_4501653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501653 prefixEnd_4501653 := by exact prefixLift 4501653
  have htrace : WordTrace (prefixWord ++ tailWord_4501653) baseStart_4501653 baseEnd_4501653 := by
    simpa [prefixWord, tailWord_4501653, baseEnd_4501653] using wordTrace_append hprefix tailTrace_4501653
  have hstable : (prefixWord ++ tailWord_4501653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501653).length < 2 ^ (prefixWord ++ tailWord_4501653).sum := by decide
  have hdescent : baseEnd_4501653 < baseStart_4501653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501656 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 1, 5]
def baseStart_4501656 : Nat := 118140960795 + 4501656 * 2 ^ 59
def prefixEnd_4501656 : Nat := 4983230072969 + 3 ^ 40 * 4501656 * 2
def baseEnd_4501656 : Nat := 770504423065448161299089

theorem tailTrace_4501656 : CollatzResearch.WordTrace tailWord_4501656 prefixEnd_4501656 770504423065448161299089 := by
  unfold tailWord_4501656
  simp only [CollatzResearch.WordTrace]
  refine ⟨82094441489638304240446411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109459255319517738987261881 82094441489638304240446411)
  ·
    refine ⟨123141662234457456360669617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82094441489638304240446411 123141662234457456360669617)
    ·
      refine ⟨92356246675843092270502213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123141662234457456360669617 92356246675843092270502213)
      ·
        refine ⟨17316796251720579800719165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92356246675843092270502213 17316796251720579800719165)
        ·
          refine ⟨6493798594395217425269687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17316796251720579800719165 6493798594395217425269687)
          ·
            refine ⟨9740697891592826137904531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493798594395217425269687 9740697891592826137904531)
            ·
              refine ⟨14611046837389239206856797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9740697891592826137904531 14611046837389239206856797)
              ·
                refine ⟨5479142564020964702571299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14611046837389239206856797 5479142564020964702571299)
                ·
                  refine ⟨8218713846031447053856949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5479142564020964702571299 8218713846031447053856949)
                  ·
                    refine ⟨770504423065448161299089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8218713846031447053856949 770504423065448161299089)
                    ·
                      rfl

theorem cell23_4501656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_4501656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501656 prefixEnd_4501656 := by exact prefixLift 4501656
  have htrace : WordTrace (prefixWord ++ tailWord_4501656) baseStart_4501656 baseEnd_4501656 := by
    simpa [prefixWord, tailWord_4501656, baseEnd_4501656] using wordTrace_append hprefix tailTrace_4501656
  have hstable : (prefixWord ++ tailWord_4501656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501656).length < 2 ^ (prefixWord ++ tailWord_4501656).sum := by decide
  have hdescent : baseEnd_4501656 < baseStart_4501656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501669 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_4501669 : Nat := 118140960795 + 4501669 * 2 ^ 59
def prefixEnd_4501669 : Nat := 4983230072969 + 3 ^ 40 * 4501669 * 2
def baseEnd_4501669 : Nat := 770506648148284311011569

theorem tailTrace_4501669 : CollatzResearch.WordTrace tailWord_4501669 prefixEnd_4501669 770506648148284311011569 := by
  unfold tailWord_4501669
  simp only [CollatzResearch.WordTrace]
  refine ⟨164189357128229511701116061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109459571418819674467410707 164189357128229511701116061)
  ·
    refine ⟨61571008923086066887918523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164189357128229511701116061 61571008923086066887918523)
    ·
      refine ⟨92356513384629100331877785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61571008923086066887918523 92356513384629100331877785)
      ·
        refine ⟨69267385038471825248908339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92356513384629100331877785 69267385038471825248908339)
        ·
          refine ⟨103901077557707737873362509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69267385038471825248908339 103901077557707737873362509)
          ·
            refine ⟨38962904084140401702510941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103901077557707737873362509 38962904084140401702510941)
            ·
              refine ⟨14611089031552650638441603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38962904084140401702510941 14611089031552650638441603)
              ·
                refine ⟨21916633547328975957662405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14611089031552650638441603 21916633547328975957662405)
                ·
                  refine ⟨4109368790124182992061701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21916633547328975957662405 4109368790124182992061701)
                  ·
                    refine ⟨770506648148284311011569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4109368790124182992061701 770506648148284311011569)
                    ·
                      rfl

theorem cell23_4501669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_4501669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501669 prefixEnd_4501669 := by exact prefixLift 4501669
  have htrace : WordTrace (prefixWord ++ tailWord_4501669) baseStart_4501669 baseEnd_4501669 := by
    simpa [prefixWord, tailWord_4501669, baseEnd_4501669] using wordTrace_append hprefix tailTrace_4501669
  have hstable : (prefixWord ++ tailWord_4501669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501669).length < 2 ^ (prefixWord ++ tailWord_4501669).sum := by decide
  have hdescent : baseEnd_4501669 < baseStart_4501669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501682 : List Nat := [3, 2, 1, 1, 1, 3, 2, 10]
def baseStart_4501682 : Nat := 118140960795 + 4501682 * 2 ^ 59
def prefixEnd_4501682 : Nat := 4983230072969 + 3 ^ 40 * 4501682 * 2
def baseEnd_4501682 : Nat := 85612097025680051191561

theorem tailTrace_4501682 : CollatzResearch.WordTrace tailWord_4501682 prefixEnd_4501682 85612097025680051191561 := by
  unfold tailWord_4501682
  simp only [CollatzResearch.WordTrace]
  refine ⟨41047457819295603730334825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109459887518121609947559533 41047457819295603730334825)
  ·
    refine ⟨30785593364471702797751119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41047457819295603730334825 30785593364471702797751119)
    ·
      refine ⟨46178390046707554196626679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30785593364471702797751119 46178390046707554196626679)
      ·
        refine ⟨69267585070061331294940019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46178390046707554196626679 69267585070061331294940019)
        ·
          refine ⟨103901377605091996942410029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69267585070061331294940019 103901377605091996942410029)
          ·
            refine ⟨38963016601909498853403761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103901377605091996942410029 38963016601909498853403761)
            ·
              refine ⟨29222262451432124140052821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38963016601909498853403761 29222262451432124140052821)
              ·
                refine ⟨85612097025680051191561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29222262451432124140052821 85612097025680051191561)
                ·
                  rfl

theorem cell23_4501682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 10].length) (baseStart_4501682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501682 prefixEnd_4501682 := by exact prefixLift 4501682
  have htrace : WordTrace (prefixWord ++ tailWord_4501682) baseStart_4501682 baseEnd_4501682 := by
    simpa [prefixWord, tailWord_4501682, baseEnd_4501682] using wordTrace_append hprefix tailTrace_4501682
  have hstable : (prefixWord ++ tailWord_4501682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501682).length < 2 ^ (prefixWord ++ tailWord_4501682).sum := by decide
  have hdescent : baseEnd_4501682 < baseStart_4501682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501696 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3]
def baseStart_4501696 : Nat := 118140960795 + 4501696 * 2 ^ 59
def prefixEnd_4501696 : Nat := 4983230072969 + 3 ^ 40 * 4501696 * 2
def baseEnd_4501696 : Nat := 2311533808422524327397083

theorem tailTrace_4501696 : CollatzResearch.WordTrace tailWord_4501696 prefixEnd_4501696 2311533808422524327397083 := by
  unfold tailWord_4501696
  simp only [CollatzResearch.WordTrace]
  refine ⟨82095170949565847656174471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109460227932754463541565961 82095170949565847656174471)
  ·
    refine ⟨123142756424348771484261707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82095170949565847656174471 123142756424348771484261707)
    ·
      refine ⟨184714134636523157226392561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123142756424348771484261707 184714134636523157226392561)
      ·
        refine ⟨138535600977392367919794421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184714134636523157226392561 138535600977392367919794421)
        ·
          refine ⟨12987712591630534492480727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138535600977392367919794421 12987712591630534492480727)
          ·
            refine ⟨19481568887445801738721091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12987712591630534492480727 19481568887445801738721091)
            ·
              refine ⟨29222353331168702608081637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19481568887445801738721091 29222353331168702608081637)
              ·
                refine ⟨5479191249594131739015307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29222353331168702608081637 5479191249594131739015307)
                ·
                  refine ⟨8218786874391197608522961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5479191249594131739015307 8218786874391197608522961)
                  ·
                    refine ⟨6164090155793398206392221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8218786874391197608522961 6164090155793398206392221)
                    ·
                      refine ⟨2311533808422524327397083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164090155793398206392221 2311533808422524327397083)
                      ·
                        rfl

theorem cell23_4501696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_4501696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501696 prefixEnd_4501696 := by exact prefixLift 4501696
  have htrace : WordTrace (prefixWord ++ tailWord_4501696) baseStart_4501696 baseEnd_4501696 := by
    simpa [prefixWord, tailWord_4501696, baseEnd_4501696] using wordTrace_append hprefix tailTrace_4501696
  have hstable : (prefixWord ++ tailWord_4501696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501696).length < 2 ^ (prefixWord ++ tailWord_4501696).sum := by decide
  have hdescent : baseEnd_4501696 < baseStart_4501696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501743 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 3]
def baseStart_4501743 : Nat := 118140960795 + 4501743 * 2 ^ 59
def prefixEnd_4501743 : Nat := 4983230072969 + 3 ^ 40 * 4501743 * 2
def baseEnd_4501743 : Nat := 2311557942013285643509367

theorem tailTrace_4501743 : CollatzResearch.WordTrace tailWord_4501743 prefixEnd_4501743 2311557942013285643509367 := by
  unfold tailWord_4501743
  simp only [CollatzResearch.WordTrace]
  refine ⟨164192056129961422339309883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109461370753307614892873255 164192056129961422339309883)
  ·
    refine ⟨246288084194942133508964825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164192056129961422339309883 246288084194942133508964825)
    ·
      refine ⟨184716063146206600131723619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246288084194942133508964825 184716063146206600131723619)
      ·
        refine ⟨277074094719309900197585429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184716063146206600131723619 277074094719309900197585429)
        ·
          refine ⟨12987848189967651571761817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 277074094719309900197585429 12987848189967651571761817)
          ·
            refine ⟨9740886142475738678821363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12987848189967651571761817 9740886142475738678821363)
            ·
              refine ⟨14611329213713608018232045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9740886142475738678821363 14611329213713608018232045)
              ·
                refine ⟨5479248455142603006837017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14611329213713608018232045 5479248455142603006837017)
                ·
                  refine ⟨4109436341356952255127763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5479248455142603006837017 4109436341356952255127763)
                  ·
                    refine ⟨6164154512035428382691645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109436341356952255127763 6164154512035428382691645)
                    ·
                      refine ⟨2311557942013285643509367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164154512035428382691645 2311557942013285643509367)
                      ·
                        rfl

theorem cell23_4501743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 3].length) (baseStart_4501743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501743 prefixEnd_4501743 := by exact prefixLift 4501743
  have htrace : WordTrace (prefixWord ++ tailWord_4501743) baseStart_4501743 baseEnd_4501743 := by
    simpa [prefixWord, tailWord_4501743, baseEnd_4501743] using wordTrace_append hprefix tailTrace_4501743
  have hstable : (prefixWord ++ tailWord_4501743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501743).length < 2 ^ (prefixWord ++ tailWord_4501743).sum := by decide
  have hdescent : baseEnd_4501743 < baseStart_4501743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501769 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_4501769 : Nat := 118140960795 + 4501769 * 2 ^ 59
def prefixEnd_4501769 : Nat := 4983230072969 + 3 ^ 40 * 4501769 * 2
def baseEnd_4501769 : Nat := 2311571292510302541784247

theorem tailTrace_4501769 : CollatzResearch.WordTrace tailWord_4501769 prefixEnd_4501769 2311571292510302541784247 := by
  unfold tailWord_4501769
  simp only [CollatzResearch.WordTrace]
  refine ⟨164193004427867228779756361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109462002951911485853170907 164193004427867228779756361)
  ·
    refine ⟨123144753320900421584817271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164193004427867228779756361 123144753320900421584817271)
    ·
      refine ⟨184717129981350632377225907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123144753320900421584817271 184717129981350632377225907)
      ·
        refine ⟨277075694972025948565838861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184717129981350632377225907 277075694972025948565838861)
        ·
          refine ⟨103903385614509730712189573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277075694972025948565838861 103903385614509730712189573)
          ·
            refine ⟨19481884802720574508535545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103903385614509730712189573 19481884802720574508535545)
            ·
              refine ⟨14611413602040430881401659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19481884802720574508535545 14611413602040430881401659)
              ·
                refine ⟨21917120403060646322102489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14611413602040430881401659 21917120403060646322102489)
                ·
                  refine ⟨16437840302295484741576867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21917120403060646322102489 16437840302295484741576867)
                  ·
                    refine ⟨24656760453443227112365301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16437840302295484741576867 24656760453443227112365301)
                    ·
                      refine ⟨2311571292510302541784247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24656760453443227112365301 2311571292510302541784247)
                      ·
                        rfl

theorem cell23_4501769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_4501769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501769 prefixEnd_4501769 := by exact prefixLift 4501769
  have htrace : WordTrace (prefixWord ++ tailWord_4501769) baseStart_4501769 baseEnd_4501769 := by
    simpa [prefixWord, tailWord_4501769, baseEnd_4501769] using wordTrace_append hprefix tailTrace_4501769
  have hstable : (prefixWord ++ tailWord_4501769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501769).length < 2 ^ (prefixWord ++ tailWord_4501769).sum := by decide
  have hdescent : baseEnd_4501769 < baseStart_4501769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501796 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4501796 : Nat := 118140960795 + 4501796 * 2 ^ 59
def prefixEnd_4501796 : Nat := 4983230072969 + 3 ^ 40 * 4501796 * 2
def baseEnd_4501796 : Nat := 2311585156487973936146623

theorem tailTrace_4501796 : CollatzResearch.WordTrace tailWord_4501796 prefixEnd_4501796 2311585156487973936146623 := by
  unfold tailWord_4501796
  simp only [CollatzResearch.WordTrace]
  refine ⟨82096994599384706195494621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109462659465846274927326161 82096994599384706195494621)
  ·
    refine ⟨30786372974769264823310483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82096994599384706195494621 30786372974769264823310483)
    ·
      refine ⟨46179559462153897234965725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30786372974769264823310483 46179559462153897234965725)
      ·
        refine ⟨17317334798307711463112147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46179559462153897234965725 17317334798307711463112147)
        ·
          refine ⟨25976002197461567194668221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17317334798307711463112147 25976002197461567194668221)
          ·
            refine ⟨9741000824048087698000583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25976002197461567194668221 9741000824048087698000583)
            ·
              refine ⟨14611501236072131547000875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9741000824048087698000583 14611501236072131547000875)
              ·
                refine ⟨21917251854108197320501313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14611501236072131547000875 21917251854108197320501313)
                ·
                  refine ⟨16437938890581147990375985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21917251854108197320501313 16437938890581147990375985)
                  ·
                    refine ⟨12328454167935860992781989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16437938890581147990375985 12328454167935860992781989)
                    ·
                      refine ⟨2311585156487973936146623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12328454167935860992781989 2311585156487973936146623)
                      ·
                        rfl

theorem cell23_4501796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4501796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501796 prefixEnd_4501796 := by exact prefixLift 4501796
  have htrace : WordTrace (prefixWord ++ tailWord_4501796) baseStart_4501796 baseEnd_4501796 := by
    simpa [prefixWord, tailWord_4501796, baseEnd_4501796] using wordTrace_append hprefix tailTrace_4501796
  have hstable : (prefixWord ++ tailWord_4501796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501796).length < 2 ^ (prefixWord ++ tailWord_4501796).sum := by decide
  have hdescent : baseEnd_4501796 < baseStart_4501796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501800 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_4501800 : Nat := 118140960795 + 4501800 * 2 ^ 59
def prefixEnd_4501800 : Nat := 4983230072969 + 3 ^ 40 * 4501800 * 2
def baseEnd_4501800 : Nat := 2311587210410591920496605

theorem tailTrace_4501800 : CollatzResearch.WordTrace tailWord_4501800 prefixEnd_4501800 2311587210410591920496605 := by
  unfold tailWord_4501800
  simp only [CollatzResearch.WordTrace]
  refine ⟨82097067545377460537067427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109462756727169947382756569 82097067545377460537067427)
  ·
    refine ⟨123145601318066190805601141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82097067545377460537067427 123145601318066190805601141)
    ·
      refine ⟨11544900123568705388025107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123145601318066190805601141 11544900123568705388025107)
      ·
        refine ⟨17317350185353058082037661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11544900123568705388025107 17317350185353058082037661)
        ·
          refine ⟨6494006319507396780764123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17317350185353058082037661 6494006319507396780764123)
          ·
            refine ⟨9741009479261095171146185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6494006319507396780764123 9741009479261095171146185)
            ·
              refine ⟨7305757109445821378359639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9741009479261095171146185 7305757109445821378359639)
              ·
                refine ⟨10958635664168732067539459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7305757109445821378359639 10958635664168732067539459)
                ·
                  refine ⟨16437953496253098101309189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10958635664168732067539459 16437953496253098101309189)
                  ·
                    refine ⟨3082116280547455893995473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16437953496253098101309189 3082116280547455893995473)
                    ·
                      refine ⟨2311587210410591920496605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082116280547455893995473 2311587210410591920496605)
                      ·
                        rfl

theorem cell23_4501800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_4501800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501800 prefixEnd_4501800 := by exact prefixLift 4501800
  have htrace : WordTrace (prefixWord ++ tailWord_4501800) baseStart_4501800 baseEnd_4501800 := by
    simpa [prefixWord, tailWord_4501800, baseEnd_4501800] using wordTrace_append hprefix tailTrace_4501800
  have hstable : (prefixWord ++ tailWord_4501800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501800).length < 2 ^ (prefixWord ++ tailWord_4501800).sum := by decide
  have hdescent : baseEnd_4501800 < baseStart_4501800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501896 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 6]
def baseStart_4501896 : Nat := 118140960795 + 4501896 * 2 ^ 59
def prefixEnd_4501896 : Nat := 4983230072969 + 3 ^ 40 * 4501896 * 2
def baseEnd_4501896 : Nat := 256848500505935949432907

theorem tailTrace_4501896 : CollatzResearch.WordTrace tailWord_4501896 prefixEnd_4501896 256848500505935949432907 := by
  unfold tailWord_4501896
  simp only [CollatzResearch.WordTrace]
  refine ⟨82098818249203564734814771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109465090998938086313086361 82098818249203564734814771)
  ·
    refine ⟨123148227373805347102222157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82098818249203564734814771 123148227373805347102222157)
    ·
      refine ⟨46180585265177005163333309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123148227373805347102222157 46180585265177005163333309)
      ·
        refine ⟨17317719474441376936249991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46180585265177005163333309 17317719474441376936249991)
        ·
          refine ⟨25976579211662065404374987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17317719474441376936249991 25976579211662065404374987)
          ·
            refine ⟨38964868817493098106562481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25976579211662065404374987 38964868817493098106562481)
            ·
              refine ⟨29223651613119823579921861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38964868817493098106562481 29223651613119823579921861)
              ·
                refine ⟨5479434677459966921235349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29223651613119823579921861 5479434677459966921235349)
                ·
                  refine ⟨256848500505935949432907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5479434677459966921235349 256848500505935949432907)
                  ·
                    rfl

theorem cell23_4501896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 6].length) (baseStart_4501896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501896 prefixEnd_4501896 := by exact prefixLift 4501896
  have htrace : WordTrace (prefixWord ++ tailWord_4501896) baseStart_4501896 baseEnd_4501896 := by
    simpa [prefixWord, tailWord_4501896, baseEnd_4501896] using wordTrace_append hprefix tailTrace_4501896
  have hstable : (prefixWord ++ tailWord_4501896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501896).length < 2 ^ (prefixWord ++ tailWord_4501896).sum := by decide
  have hdescent : baseEnd_4501896 < baseStart_4501896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501909 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_4501909 : Nat := 118140960795 + 4501909 * 2 ^ 59
def prefixEnd_4501909 : Nat := 4983230072969 + 3 ^ 40 * 4501909 * 2
def baseEnd_4501909 : Nat := 770547726600643998011201

theorem tailTrace_4501909 : CollatzResearch.WordTrace tailWord_4501909 prefixEnd_4501909 770547726600643998011201 := by
  unfold tailWord_4501909
  simp only [CollatzResearch.WordTrace]
  refine ⟨164198110647360032689852781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109465407098240021793235187 164198110647360032689852781)
  ·
    refine ⟨61574291492760012258694793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164198110647360032689852781 61574291492760012258694793)
    ·
      refine ⟨46180718619570009194021095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61574291492760012258694793 46180718619570009194021095)
      ·
        refine ⟨69271077929355013791031643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46180718619570009194021095 69271077929355013791031643)
        ·
          refine ⟨103906616894032520686547465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69271077929355013791031643 103906616894032520686547465)
          ·
            refine ⟨77929962670524390514910599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103906616894032520686547465 77929962670524390514910599)
            ·
              refine ⟨116894944005786585772365899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77929962670524390514910599 116894944005786585772365899)
              ·
                refine ⟨175342416008679878658548849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116894944005786585772365899 175342416008679878658548849)
                ·
                  refine ⟨131506812006509908993911637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 175342416008679878658548849 131506812006509908993911637)
                  ·
                    refine ⟨770547726600643998011201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 131506812006509908993911637 770547726600643998011201)
                    ·
                      rfl

theorem cell23_4501909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_4501909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501909 prefixEnd_4501909 := by exact prefixLift 4501909
  have htrace : WordTrace (prefixWord ++ tailWord_4501909) baseStart_4501909 baseEnd_4501909 := by
    simpa [prefixWord, tailWord_4501909, baseEnd_4501909] using wordTrace_append hprefix tailTrace_4501909
  have hstable : (prefixWord ++ tailWord_4501909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501909).length < 2 ^ (prefixWord ++ tailWord_4501909).sum := by decide
  have hdescent : baseEnd_4501909 < baseStart_4501909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501950 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_4501950 : Nat := 118140960795 + 4501950 * 2 ^ 59
def prefixEnd_4501950 : Nat := 4983230072969 + 3 ^ 40 * 4501950 * 2
def baseEnd_4501950 : Nat := 2311664232508766333620915

theorem tailTrace_4501950 : CollatzResearch.WordTrace tailWord_4501950 prefixEnd_4501950 2311664232508766333620915 := by
  unfold tailWord_4501950
  simp only [CollatzResearch.WordTrace]
  refine ⟨20524950755026437086511913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109466404026807664461396869 20524950755026437086511913)
  ·
    refine ⟨15393713066269827814883935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20524950755026437086511913 15393713066269827814883935)
    ·
      refine ⟨23090569599404741722325903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15393713066269827814883935 23090569599404741722325903)
      ·
        refine ⟨34635854399107112583488855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23090569599404741722325903 34635854399107112583488855)
        ·
          refine ⟨51953781598660668875233283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34635854399107112583488855 51953781598660668875233283)
          ·
            refine ⟨77930672397991003312849925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51953781598660668875233283 77930672397991003312849925)
            ·
              refine ⟨14612001074623313121159361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77930672397991003312849925 14612001074623313121159361)
              ·
                refine ⟨10959000805967484840869521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14612001074623313121159361 10959000805967484840869521)
                ·
                  refine ⟨8219250604475613630652141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10959000805967484840869521 8219250604475613630652141)
                  ·
                    refine ⟨3082218976678355111494553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8219250604475613630652141 3082218976678355111494553)
                    ·
                      refine ⟨2311664232508766333620915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082218976678355111494553 2311664232508766333620915)
                      ·
                        rfl

theorem cell23_4501950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_4501950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501950 prefixEnd_4501950 := by exact prefixLift 4501950
  have htrace : WordTrace (prefixWord ++ tailWord_4501950) baseStart_4501950 baseEnd_4501950 := by
    simpa [prefixWord, tailWord_4501950, baseEnd_4501950] using wordTrace_append hprefix tailTrace_4501950
  have hstable : (prefixWord ++ tailWord_4501950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501950).length < 2 ^ (prefixWord ++ tailWord_4501950).sum := by decide
  have hdescent : baseEnd_4501950 < baseStart_4501950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501966 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_4501966 : Nat := 118140960795 + 4501966 * 2 ^ 59
def prefixEnd_4501966 : Nat := 4983230072969 + 3 ^ 40 * 4501966 * 2
def baseEnd_4501966 : Nat := 2311672448199238271020841

theorem tailTrace_4501966 : CollatzResearch.WordTrace tailWord_4501966 prefixEnd_4501966 2311672448199238271020841 := by
  unfold tailWord_4501966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20525023701019191428084719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109466793072102354283118501 20525023701019191428084719)
  ·
    refine ⟨30787535551528787142127079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20525023701019191428084719 30787535551528787142127079)
    ·
      refine ⟨46181303327293180713190619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30787535551528787142127079 46181303327293180713190619)
      ·
        refine ⟨69271954990939771069785929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46181303327293180713190619 69271954990939771069785929)
        ·
          refine ⟨51953966243204828302339447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69271954990939771069785929 51953966243204828302339447)
          ·
            refine ⟨77930949364807242453509171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51953966243204828302339447 77930949364807242453509171)
            ·
              refine ⟨116896424047210863680263757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77930949364807242453509171 116896424047210863680263757)
              ·
                refine ⟨43836159017704073880098909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116896424047210863680263757 43836159017704073880098909)
                ·
                  refine ⟨16438559631639027705037091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43836159017704073880098909 16438559631639027705037091)
                  ·
                    refine ⟨24657839447458541557555637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16438559631639027705037091 24657839447458541557555637)
                    ·
                      refine ⟨2311672448199238271020841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24657839447458541557555637 2311672448199238271020841)
                      ·
                        rfl

theorem cell23_4501966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_4501966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501966 prefixEnd_4501966 := by exact prefixLift 4501966
  have htrace : WordTrace (prefixWord ++ tailWord_4501966) baseStart_4501966 baseEnd_4501966 := by
    simpa [prefixWord, tailWord_4501966, baseEnd_4501966] using wordTrace_append hprefix tailTrace_4501966
  have hstable : (prefixWord ++ tailWord_4501966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501966).length < 2 ^ (prefixWord ++ tailWord_4501966).sum := by decide
  have hdescent : baseEnd_4501966 < baseStart_4501966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501973 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_4501973 : Nat := 118140960795 + 4501973 * 2 ^ 59
def prefixEnd_4501973 : Nat := 4983230072969 + 3 ^ 40 * 4501973 * 2
def baseEnd_4501973 : Nat := 770558680854606581211103

theorem tailTrace_4501973 : CollatzResearch.WordTrace tailWord_4501973 prefixEnd_4501973 770558680854606581211103 := by
  unfold tailWord_4501973
  simp only [CollatzResearch.WordTrace]
  refine ⟨164200444919128171620182573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109466963279418781080121715 164200444919128171620182573)
  ·
    refine ⟨61575166844673064357568465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164200444919128171620182573 61575166844673064357568465)
    ·
      refine ⟨46181375133504798268176349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61575166844673064357568465 46181375133504798268176349)
      ·
        refine ⟨17318015675064299350566131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46181375133504798268176349 17318015675064299350566131)
        ·
          refine ⟨25977023512596449025849197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17318015675064299350566131 25977023512596449025849197)
          ·
            refine ⟨9741383817223668384693449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25977023512596449025849197 9741383817223668384693449)
            ·
              refine ⟨7306037862917751288520087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9741383817223668384693449 7306037862917751288520087)
              ·
                refine ⟨10959056794376626932780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7306037862917751288520087 10959056794376626932780131)
                ·
                  refine ⟨16438585191564940399170197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10959056794376626932780131 16438585191564940399170197)
                  ·
                    refine ⟨770558680854606581211103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16438585191564940399170197 770558680854606581211103)
                    ·
                      rfl

theorem cell23_4501973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_4501973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501973 prefixEnd_4501973 := by exact prefixLift 4501973
  have htrace : WordTrace (prefixWord ++ tailWord_4501973) baseStart_4501973 baseEnd_4501973 := by
    simpa [prefixWord, tailWord_4501973, baseEnd_4501973] using wordTrace_append hprefix tailTrace_4501973
  have hstable : (prefixWord ++ tailWord_4501973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501973).length < 2 ^ (prefixWord ++ tailWord_4501973).sum := by decide
  have hdescent : baseEnd_4501973 < baseStart_4501973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501983 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 3]
def baseStart_4501983 : Nat := 118140960795 + 4501983 * 2 ^ 59
def prefixEnd_4501983 : Nat := 4983230072969 + 3 ^ 40 * 4501983 * 2
def baseEnd_4501983 : Nat := 2311681177370364704508263

theorem tailTrace_4501983 : CollatzResearch.WordTrace tailWord_4501983 prefixEnd_4501983 2311681177370364704508263 := by
  unfold tailWord_4501983
  simp only [CollatzResearch.WordTrace]
  refine ⟨164200809649091943328046603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109467206432727962218697735 164200809649091943328046603)
  ·
    refine ⟨246301214473637914992069905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164200809649091943328046603 246301214473637914992069905)
    ·
      refine ⟨184725910855228436244052429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246301214473637914992069905 184725910855228436244052429)
      ·
        refine ⟨69272216570710663591519661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184725910855228436244052429 69272216570710663591519661)
        ·
          refine ⟨25977081214016498846819873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69272216570710663591519661 25977081214016498846819873)
          ·
            refine ⟨19482810910512374135114905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25977081214016498846819873 19482810910512374135114905)
            ·
              refine ⟨14612108182884280601336179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19482810910512374135114905 14612108182884280601336179)
              ·
                refine ⟨21918162274326420902004269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14612108182884280601336179 21918162274326420902004269)
                ·
                  refine ⟨8219310852872407838251601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21918162274326420902004269 8219310852872407838251601)
                  ·
                    refine ⟨6164483139654305878688701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8219310852872407838251601 6164483139654305878688701)
                    ·
                      refine ⟨2311681177370364704508263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164483139654305878688701 2311681177370364704508263)
                      ·
                        rfl

theorem cell23_4501983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_4501983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501983 prefixEnd_4501983 := by exact prefixLift 4501983
  have htrace : WordTrace (prefixWord ++ tailWord_4501983) baseStart_4501983 baseEnd_4501983 := by
    simpa [prefixWord, tailWord_4501983, baseEnd_4501983] using wordTrace_append hprefix tailTrace_4501983
  have hstable : (prefixWord ++ tailWord_4501983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501983).length < 2 ^ (prefixWord ++ tailWord_4501983).sum := by decide
  have hdescent : baseEnd_4501983 < baseStart_4501983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4501997 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4501997 : Nat := 118140960795 + 4501997 * 2 ^ 59
def prefixEnd_4501997 : Nat := 4983230072969 + 3 ^ 40 * 4501997 * 2
def baseEnd_4501997 : Nat := 2311688366099527649733199

theorem tailTrace_4501997 : CollatzResearch.WordTrace tailWord_4501997 prefixEnd_4501997 2311688366099527649733199 := by
  unfold tailWord_4501997
  simp only [CollatzResearch.WordTrace]
  refine ⟨164201320271041223719056245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109467546847360815812704163 164201320271041223719056245)
  ·
    refine ⟨15393873775410114723661523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164201320271041223719056245 15393873775410114723661523)
    ·
      refine ⟨23090810663115172085492285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15393873775410114723661523 23090810663115172085492285)
      ·
        refine ⟨8659053998668189532059607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23090810663115172085492285 8659053998668189532059607)
        ·
          refine ⟨12988580998002284298089411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8659053998668189532059607 12988580998002284298089411)
          ·
            refine ⟨19482871497003426447134117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12988580998002284298089411 19482871497003426447134117)
            ·
              refine ⟨3653038405688142458837647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19482871497003426447134117 3653038405688142458837647)
              ·
                refine ⟨5479557608532213688256471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653038405688142458837647 5479557608532213688256471)
                ·
                  refine ⟨8219336412798320532384707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5479557608532213688256471 8219336412798320532384707)
                  ·
                    refine ⟨12329004619197480798577061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8219336412798320532384707 12329004619197480798577061)
                    ·
                      refine ⟨2311688366099527649733199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12329004619197480798577061 2311688366099527649733199)
                      ·
                        rfl

theorem cell23_4501997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4501997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4501997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4501997 prefixEnd_4501997 := by exact prefixLift 4501997
  have htrace : WordTrace (prefixWord ++ tailWord_4501997) baseStart_4501997 baseEnd_4501997 := by
    simpa [prefixWord, tailWord_4501997, baseEnd_4501997] using wordTrace_append hprefix tailTrace_4501997
  have hstable : (prefixWord ++ tailWord_4501997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4501997).length < 2 ^ (prefixWord ++ tailWord_4501997).sum := by decide
  have hdescent : baseEnd_4501997 < baseStart_4501997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4501997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502030 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_4502030 : Nat := 118140960795 + 4502030 * 2 ^ 59
def prefixEnd_4502030 : Nat := 4983230072969 + 3 ^ 40 * 4502030 * 2
def baseEnd_4502030 : Nat := 2311705310961126020620547

theorem tailTrace_4502030 : CollatzResearch.WordTrace tailWord_4502030 prefixEnd_4502030 2311705310961126020620547 := by
  unfold tailWord_4502030
  simp only [CollatzResearch.WordTrace]
  refine ⟨20525315484990208794375943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109468349253281113570005029 20525315484990208794375943)
  ·
    refine ⟨30787973227485313191563915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20525315484990208794375943 30787973227485313191563915)
    ·
      refine ⟨46181959841227969787345873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30787973227485313191563915 46181959841227969787345873)
      ·
        refine ⟨34636469880920977340509405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46181959841227969787345873 34636469880920977340509405)
        ·
          refine ⟨12988676205345366502691027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34636469880920977340509405 12988676205345366502691027)
          ·
            refine ⟨19483014308018049754036541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12988676205345366502691027 19483014308018049754036541)
            ·
              refine ⟨7306130365506768657763703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19483014308018049754036541 7306130365506768657763703)
              ·
                refine ⟨10959195548260152986645555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7306130365506768657763703 10959195548260152986645555)
                ·
                  refine ⟨16438793322390229479968333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10959195548260152986645555 16438793322390229479968333)
                  ·
                    refine ⟨6164547495896336054988125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16438793322390229479968333 6164547495896336054988125)
                    ·
                      refine ⟨2311705310961126020620547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164547495896336054988125 2311705310961126020620547)
                      ·
                        rfl

theorem cell23_4502030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_4502030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502030 prefixEnd_4502030 := by exact prefixLift 4502030
  have htrace : WordTrace (prefixWord ++ tailWord_4502030) baseStart_4502030 baseEnd_4502030 := by
    simpa [prefixWord, tailWord_4502030, baseEnd_4502030] using wordTrace_append hprefix tailTrace_4502030
  have hstable : (prefixWord ++ tailWord_4502030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502030).length < 2 ^ (prefixWord ++ tailWord_4502030).sum := by decide
  have hdescent : baseEnd_4502030 < baseStart_4502030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502048 : List Nat := [2, 1, 1, 6, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4502048 : Nat := 118140960795 + 4502048 * 2 ^ 59
def prefixEnd_4502048 : Nat := 4983230072969 + 3 ^ 40 * 4502048 * 2
def baseEnd_4502048 : Nat := 2311714553612906950195465

theorem tailTrace_4502048 : CollatzResearch.WordTrace tailWord_4502048 prefixEnd_4502048 2311714553612906950195465 := by
  unfold tailWord_4502048
  simp only [CollatzResearch.WordTrace]
  refine ⟨82101590196928229714581399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109468786929237639619441865 82101590196928229714581399)
  ·
    refine ⟨123152385295392344571872099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82101590196928229714581399 123152385295392344571872099)
    ·
      refine ⟨184728577943088516857808149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123152385295392344571872099 184728577943088516857808149)
      ·
        refine ⟨8659152091082274227709757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 184728577943088516857808149 8659152091082274227709757)
        ·
          refine ⟨3247182034155852835391159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8659152091082274227709757 3247182034155852835391159)
          ·
            refine ⟨4870773051233779253086739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247182034155852835391159 4870773051233779253086739)
            ·
              refine ⟨7306159576850668879630109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870773051233779253086739 7306159576850668879630109)
              ·
                refine ⟨2739809841319000829861291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7306159576850668879630109 2739809841319000829861291)
                ·
                  refine ⟨4109714761978501244791937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739809841319000829861291 4109714761978501244791937)
                  ·
                    refine ⟨3082286071483875933593953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4109714761978501244791937 3082286071483875933593953)
                    ·
                      refine ⟨2311714553612906950195465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082286071483875933593953 2311714553612906950195465)
                      ·
                        rfl

theorem cell23_4502048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4502048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502048 prefixEnd_4502048 := by exact prefixLift 4502048
  have htrace : WordTrace (prefixWord ++ tailWord_4502048) baseStart_4502048 baseEnd_4502048 := by
    simpa [prefixWord, tailWord_4502048, baseEnd_4502048] using wordTrace_append hprefix tailTrace_4502048
  have hstable : (prefixWord ++ tailWord_4502048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502048).length < 2 ^ (prefixWord ++ tailWord_4502048).sum := by decide
  have hdescent : baseEnd_4502048 < baseStart_4502048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502073 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4502073 : Nat := 118140960795 + 4502073 * 2 ^ 59
def prefixEnd_4502073 : Nat := 4983230072969 + 3 ^ 40 * 4502073 * 2
def baseEnd_4502073 : Nat := 2311727390629269352382849

theorem tailTrace_4502073 : CollatzResearch.WordTrace tailWord_4502073 prefixEnd_4502073 2311727390629269352382849 := by
  unfold tailWord_4502073
  simp only [CollatzResearch.WordTrace]
  refine ⟨164204092218765888698822873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109469394812510592465881915 164204092218765888698822873)
  ·
    refine ⟨123153069164074416524117155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164204092218765888698822873 123153069164074416524117155)
    ·
      refine ⟨184729603746111624786175733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123153069164074416524117155 184729603746111624786175733)
      ·
        refine ⟨17318400351197964823703975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 184729603746111624786175733 17318400351197964823703975)
        ·
          refine ⟨25977600526796947235555963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17318400351197964823703975 25977600526796947235555963)
          ·
            refine ⟨38966400790195420853333945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25977600526796947235555963 38966400790195420853333945)
            ·
              refine ⟨29224800592646565640000459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38966400790195420853333945 29224800592646565640000459)
              ·
                refine ⟨43837200888969848460000689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29224800592646565640000459 43837200888969848460000689)
                ·
                  refine ⟨32877900666727386345000517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43837200888969848460000689 32877900666727386345000517)
                  ·
                    refine ⟨6164606375011384939687597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32877900666727386345000517 6164606375011384939687597)
                    ·
                      refine ⟨2311727390629269352382849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164606375011384939687597 2311727390629269352382849)
                      ·
                        rfl

theorem cell23_4502073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4502073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502073 prefixEnd_4502073 := by exact prefixLift 4502073
  have htrace : WordTrace (prefixWord ++ tailWord_4502073) baseStart_4502073 baseEnd_4502073 := by
    simpa [prefixWord, tailWord_4502073, baseEnd_4502073] using wordTrace_append hprefix tailTrace_4502073
  have hstable : (prefixWord ++ tailWord_4502073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502073).length < 2 ^ (prefixWord ++ tailWord_4502073).sum := by decide
  have hdescent : baseEnd_4502073 < baseStart_4502073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502163 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 3]
def baseStart_4502163 : Nat := 118140960795 + 4502163 * 2 ^ 59
def prefixEnd_4502163 : Nat := 4983230072969 + 3 ^ 40 * 4502163 * 2
def baseEnd_4502163 : Nat := 2311773603888174000257435

theorem tailTrace_4502163 : CollatzResearch.WordTrace tailWord_4502163 prefixEnd_4502163 2311773603888174000257435 := by
  unfold tailWord_4502163
  simp only [CollatzResearch.WordTrace]
  refine ⟨164207374788439834069599143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109471583192293222713066095 164207374788439834069599143)
  ·
    refine ⟨246311062182659751104398715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164207374788439834069599143 246311062182659751104398715)
    ·
      refine ⟨369466593273989626656598073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246311062182659751104398715 369466593273989626656598073)
      ·
        refine ⟨277099944955492219992448555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369466593273989626656598073 277099944955492219992448555)
        ·
          refine ⟨415649917433238329988672833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277099944955492219992448555 415649917433238329988672833)
          ·
            refine ⟨311737438074928747491504625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415649917433238329988672833 311737438074928747491504625)
            ·
              refine ⟨233803078556196560618628469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311737438074928747491504625 233803078556196560618628469)
              ·
                refine ⟨21919038614643427557996419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 233803078556196560618628469 21919038614643427557996419)
                ·
                  refine ⟨32878557921965141336994629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21919038614643427557996419 32878557921965141336994629)
                  ·
                    refine ⟨6164729610368464000686493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32878557921965141336994629 6164729610368464000686493)
                    ·
                      refine ⟨2311773603888174000257435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164729610368464000686493 2311773603888174000257435)
                      ·
                        rfl

theorem cell23_4502163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_4502163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502163 prefixEnd_4502163 := by exact prefixLift 4502163
  have htrace : WordTrace (prefixWord ++ tailWord_4502163) baseStart_4502163 baseEnd_4502163 := by
    simpa [prefixWord, tailWord_4502163, baseEnd_4502163] using wordTrace_append hprefix tailTrace_4502163
  have hstable : (prefixWord ++ tailWord_4502163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502163).length < 2 ^ (prefixWord ++ tailWord_4502163).sum := by decide
  have hdescent : baseEnd_4502163 < baseStart_4502163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502173 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4502173 : Nat := 118140960795 + 4502173 * 2 ^ 59
def prefixEnd_4502173 : Nat := 4983230072969 + 3 ^ 40 * 4502173 * 2
def baseEnd_4502173 : Nat := 2311778738694718961132389

theorem tailTrace_4502173 : CollatzResearch.WordTrace tailWord_4502173 prefixEnd_4502173 2311778738694718961132389 := by
  unfold tailWord_4502173
  simp only [CollatzResearch.WordTrace]
  refine ⟨164207739518403605777463173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109471826345602403851642115 164207739518403605777463173)
  ·
    refine ⟨30788951159700676083274345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164207739518403605777463173 30788951159700676083274345)
    ·
      refine ⟨23091713369775507062455759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30788951159700676083274345 23091713369775507062455759)
      ·
        refine ⟨34637570054663260593683639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23091713369775507062455759 34637570054663260593683639)
        ·
          refine ⟨51956355081994890890525459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34637570054663260593683639 51956355081994890890525459)
          ·
            refine ⟨77934532622992336335788189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51956355081994890890525459 77934532622992336335788189)
            ·
              refine ⟨29225449733622126125920571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77934532622992336335788189 29225449733622126125920571)
              ·
                refine ⟨43838174600433189188880857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29225449733622126125920571 43838174600433189188880857)
                ·
                  refine ⟨32878630950324891891660643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43838174600433189188880857 32878630950324891891660643)
                  ·
                    refine ⟨49317946425487337837490965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32878630950324891891660643 49317946425487337837490965)
                    ·
                      refine ⟨2311778738694718961132389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49317946425487337837490965 2311778738694718961132389)
                      ·
                        rfl

theorem cell23_4502173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4502173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502173 prefixEnd_4502173 := by exact prefixLift 4502173
  have htrace : WordTrace (prefixWord ++ tailWord_4502173) baseStart_4502173 baseEnd_4502173 := by
    simpa [prefixWord, tailWord_4502173, baseEnd_4502173] using wordTrace_append hprefix tailTrace_4502173
  have hstable : (prefixWord ++ tailWord_4502173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502173).length < 2 ^ (prefixWord ++ tailWord_4502173).sum := by decide
  have hdescent : baseEnd_4502173 < baseStart_4502173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502180 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_4502180 : Nat := 118140960795 + 4502180 * 2 ^ 59
def prefixEnd_4502180 : Nat := 4983230072969 + 3 ^ 40 * 4502180 * 2
def baseEnd_4502180 : Nat := 2311782333059300433744857

theorem tailTrace_4502180 : CollatzResearch.WordTrace tailWord_4502180 prefixEnd_4502180 2311782333059300433744857 := by
  unfold tailWord_4502180
  simp only [CollatzResearch.WordTrace]
  refine ⟨82103997414689122986483997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109471996552918830648645329 82103997414689122986483997)
  ·
    refine ⟨30788999030508421119931499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82103997414689122986483997 30788999030508421119931499)
    ·
      refine ⟨46183498545762631679897249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30788999030508421119931499 46183498545762631679897249)
      ·
        refine ⟨34637623909321973759922937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46183498545762631679897249 34637623909321973759922937)
        ·
          refine ⟨25978217931991480319942203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34637623909321973759922937 25978217931991480319942203)
          ·
            refine ⟨38967326897987220479913305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25978217931991480319942203 38967326897987220479913305)
            ·
              refine ⟨29225495173490415359934979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38967326897987220479913305 29225495173490415359934979)
              ·
                refine ⟨43838242760235623039902469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29225495173490415359934979 43838242760235623039902469)
                ·
                  refine ⟨8219670517544179319981713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43838242760235623039902469 8219670517544179319981713)
                  ·
                    refine ⟨6164752888158134489986285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8219670517544179319981713 6164752888158134489986285)
                    ·
                      refine ⟨2311782333059300433744857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164752888158134489986285 2311782333059300433744857)
                      ·
                        rfl

theorem cell23_4502180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_4502180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502180 prefixEnd_4502180 := by exact prefixLift 4502180
  have htrace : WordTrace (prefixWord ++ tailWord_4502180) baseStart_4502180 baseEnd_4502180 := by
    simpa [prefixWord, tailWord_4502180, baseEnd_4502180] using wordTrace_append hprefix tailTrace_4502180
  have hstable : (prefixWord ++ tailWord_4502180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502180).length < 2 ^ (prefixWord ++ tailWord_4502180).sum := by decide
  have hdescent : baseEnd_4502180 < baseStart_4502180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502244 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_4502244 : Nat := 118140960795 + 4502244 * 2 ^ 59
def prefixEnd_4502244 : Nat := 4983230072969 + 3 ^ 40 * 4502244 * 2
def baseEnd_4502244 : Nat := 2311815195821188183344563

theorem tailTrace_4502244 : CollatzResearch.WordTrace tailWord_4502244 prefixEnd_4502244 2311815195821188183344563 := by
  unfold tailWord_4502244
  simp only [CollatzResearch.WordTrace]
  refine ⟨82105164550573192451648893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109473552734097589935531857 82105164550573192451648893)
  ·
    refine ⟨30789436706464947169368335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82105164550573192451648893 30789436706464947169368335)
    ·
      refine ⟨46184155059697420754052503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30789436706464947169368335 46184155059697420754052503)
      ·
        refine ⟨69276232589546131131078755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46184155059697420754052503 69276232589546131131078755)
        ·
          refine ⟨103914348884319196696618133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69276232589546131131078755 103914348884319196696618133)
          ·
            refine ⟨4870985103952462345153975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103914348884319196696618133 4870985103952462345153975)
            ·
              refine ⟨7306477655928693517730963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870985103952462345153975 7306477655928693517730963)
              ·
                refine ⟨10959716483893040276596445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7306477655928693517730963 10959716483893040276596445)
                ·
                  refine ⟨4109893681459890103723667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10959716483893040276596445 4109893681459890103723667)
                  ·
                    refine ⟨6164840522189835155585501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109893681459890103723667 6164840522189835155585501)
                    ·
                      refine ⟨2311815195821188183344563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164840522189835155585501 2311815195821188183344563)
                      ·
                        rfl

theorem cell23_4502244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_4502244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502244 prefixEnd_4502244 := by exact prefixLift 4502244
  have htrace : WordTrace (prefixWord ++ tailWord_4502244) baseStart_4502244 baseEnd_4502244 := by
    simpa [prefixWord, tailWord_4502244, baseEnd_4502244] using wordTrace_append hprefix tailTrace_4502244
  have hstable : (prefixWord ++ tailWord_4502244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502244).length < 2 ^ (prefixWord ++ tailWord_4502244).sum := by decide
  have hdescent : baseEnd_4502244 < baseStart_4502244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502250 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_4502250 : Nat := 118140960795 + 4502250 * 2 ^ 59
def prefixEnd_4502250 : Nat := 4983230072969 + 3 ^ 40 * 4502250 * 2
def baseEnd_4502250 : Nat := 2311818276705115159869535

theorem tailTrace_4502250 : CollatzResearch.WordTrace tailWord_4502250 prefixEnd_4502250 2311818276705115159869535 := by
  unfold tailWord_4502250
  simp only [CollatzResearch.WordTrace]
  refine ⟨41052636984781161982004051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109473698626083098618677469 41052636984781161982004051)
  ·
    refine ⟨61578955477171742973006077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41052636984781161982004051 61578955477171742973006077)
    ·
      refine ⟨23092108303939403614877279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61578955477171742973006077 23092108303939403614877279)
      ·
        refine ⟨34638162455909105422315919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23092108303939403614877279 34638162455909105422315919)
        ·
          refine ⟨51957243683863658133473879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34638162455909105422315919 51957243683863658133473879)
          ·
            refine ⟨77935865525795487200210819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51957243683863658133473879 77935865525795487200210819)
            ·
              refine ⟨116903798288693230800316229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77935865525795487200210819 116903798288693230800316229)
              ·
                refine ⟨21919462179129980775059293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116903798288693230800316229 21919462179129980775059293)
                ·
                  refine ⟨8219798317173742790647235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21919462179129980775059293 8219798317173742790647235)
                  ·
                    refine ⟨12329697475760614185970853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8219798317173742790647235 12329697475760614185970853)
                    ·
                      refine ⟨2311818276705115159869535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12329697475760614185970853 2311818276705115159869535)
                      ·
                        rfl

theorem cell23_4502250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_4502250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502250 prefixEnd_4502250 := by exact prefixLift 4502250
  have htrace : WordTrace (prefixWord ++ tailWord_4502250) baseStart_4502250 baseEnd_4502250 := by
    simpa [prefixWord, tailWord_4502250, baseEnd_4502250] using wordTrace_append hprefix tailTrace_4502250
  have hstable : (prefixWord ++ tailWord_4502250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502250).length < 2 ^ (prefixWord ++ tailWord_4502250).sum := by decide
  have hdescent : baseEnd_4502250 < baseStart_4502250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502280 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_4502280 : Nat := 118140960795 + 4502280 * 2 ^ 59
def prefixEnd_4502280 : Nat := 4983230072969 + 3 ^ 40 * 4502280 * 2
def baseEnd_4502280 : Nat := 2311833681124750042494397

theorem tailTrace_4502280 : CollatzResearch.WordTrace tailWord_4502280 prefixEnd_4502280 2311833681124750042494397 := by
  unfold tailWord_4502280
  simp only [CollatzResearch.WordTrace]
  refine ⟨82105821064507981525804147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109474428086010642034405529 82105821064507981525804147)
  ·
    refine ⟨123158731596761972288706221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82105821064507981525804147 123158731596761972288706221)
    ·
      refine ⟨46184524348785739608264833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123158731596761972288706221 46184524348785739608264833)
      ·
        refine ⟨34638393261589304706198625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46184524348785739608264833 34638393261589304706198625)
        ·
          refine ⟨25978794946191978529648969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34638393261589304706198625 25978794946191978529648969)
          ·
            refine ⟨19484096209643983897236727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25978794946191978529648969 19484096209643983897236727)
            ·
              refine ⟨29226144314465975845855091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19484096209643983897236727 29226144314465975845855091)
              ·
                refine ⟨43839216471698963768782637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29226144314465975845855091 43839216471698963768782637)
                ·
                  refine ⟨16439706176887111413293489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43839216471698963768782637 16439706176887111413293489)
                  ·
                    refine ⟨12329779632665333559970117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16439706176887111413293489 12329779632665333559970117)
                    ·
                      refine ⟨2311833681124750042494397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12329779632665333559970117 2311833681124750042494397)
                      ·
                        rfl

theorem cell23_4502280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_4502280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502280 prefixEnd_4502280 := by exact prefixLift 4502280
  have htrace : WordTrace (prefixWord ++ tailWord_4502280) baseStart_4502280 baseEnd_4502280 := by
    simpa [prefixWord, tailWord_4502280, baseEnd_4502280] using wordTrace_append hprefix tailTrace_4502280
  have hstable : (prefixWord ++ tailWord_4502280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502280).length < 2 ^ (prefixWord ++ tailWord_4502280).sum := by decide
  have hdescent : baseEnd_4502280 < baseStart_4502280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502290 : List Nat := [3, 2, 4, 1, 13]
def baseStart_4502290 : Nat := 118140960795 + 4502290 * 2 ^ 59
def prefixEnd_4502290 : Nat := 4983230072969 + 3 ^ 40 * 4502290 * 2
def baseEnd_4502290 : Nat := 3171246661085452679519

theorem tailTrace_4502290 : CollatzResearch.WordTrace tailWord_4502290 prefixEnd_4502290 3171246661085452679519 := by
  unfold tailWord_4502290
  simp only [CollatzResearch.WordTrace]
  refine ⟨41053001714744933689868081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109474671239319823172981549 41053001714744933689868081)
  ·
    refine ⟨30789751286058700267401061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41053001714744933689868081 30789751286058700267401061)
    ·
      refine ⟨5773078366136006300137699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30789751286058700267401061 5773078366136006300137699)
      ·
        refine ⟨8659617549204009450206549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5773078366136006300137699 8659617549204009450206549)
        ·
          refine ⟨3171246661085452679519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8659617549204009450206549 3171246661085452679519)
          ·
            rfl

theorem cell23_4502290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 13].length) (baseStart_4502290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502290 prefixEnd_4502290 := by exact prefixLift 4502290
  have htrace : WordTrace (prefixWord ++ tailWord_4502290) baseStart_4502290 baseEnd_4502290 := by
    simpa [prefixWord, tailWord_4502290, baseEnd_4502290] using wordTrace_append hprefix tailTrace_4502290
  have hstable : (prefixWord ++ tailWord_4502290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502290).length < 2 ^ (prefixWord ++ tailWord_4502290).sum := by decide
  have hdescent : baseEnd_4502290 < baseStart_4502290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502295 : List Nat := [1, 1, 3, 4, 4, 1, 2, 2, 1, 1, 3]
def baseStart_4502295 : Nat := 118140960795 + 4502295 * 2 ^ 59
def prefixEnd_4502295 : Nat := 4983230072969 + 3 ^ 40 * 4502295 * 2
def baseEnd_4502295 : Nat := 2311841383334567483806829

theorem tailTrace_4502295 : CollatzResearch.WordTrace tailWord_4502295 prefixEnd_4502295 2311841383334567483806829 := by
  unfold tailWord_4502295
  simp only [CollatzResearch.WordTrace]
  refine ⟨164212189223961620613404339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109474792815974413742269559 164212189223961620613404339)
  ·
    refine ⟨246318283835942430920106509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164212189223961620613404339 246318283835942430920106509)
    ·
      refine ⟨92369356438478411595039941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246318283835942430920106509 92369356438478411595039941)
      ·
        refine ⟨17319254332214702174069989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92369356438478411595039941 17319254332214702174069989)
        ·
          refine ⟨3247360187290256657638123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17319254332214702174069989 3247360187290256657638123)
          ·
            refine ⟨4871040280935384986457185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247360187290256657638123 4871040280935384986457185)
            ·
              refine ⟨3653280210701538739842889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4871040280935384986457185 3653280210701538739842889)
              ·
                refine ⟨2739960158026154054882167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3653280210701538739842889 2739960158026154054882167)
                ·
                  refine ⟨4109940237039231082323251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739960158026154054882167 4109940237039231082323251)
                  ·
                    refine ⟨6164910355558846623484877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4109940237039231082323251 6164910355558846623484877)
                    ·
                      refine ⟨2311841383334567483806829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164910355558846623484877 2311841383334567483806829)
                      ·
                        rfl

theorem cell23_4502295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_4502295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502295 prefixEnd_4502295 := by exact prefixLift 4502295
  have htrace : WordTrace (prefixWord ++ tailWord_4502295) baseStart_4502295 baseEnd_4502295 := by
    simpa [prefixWord, tailWord_4502295, baseEnd_4502295] using wordTrace_append hprefix tailTrace_4502295
  have hstable : (prefixWord ++ tailWord_4502295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502295).length < 2 ^ (prefixWord ++ tailWord_4502295).sum := by decide
  have hdescent : baseEnd_4502295 < baseStart_4502295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502324 : List Nat := [2, 5, 1, 1, 3, 1, 3, 7]
def baseStart_4502324 : Nat := 118140960795 + 4502324 * 2 ^ 59
def prefixEnd_4502324 : Nat := 4983230072969 + 3 ^ 40 * 4502324 * 2
def baseEnd_4502324 : Nat := 85624306454575847049785

theorem tailTrace_4502324 : CollatzResearch.WordTrace tailWord_4502324 prefixEnd_4502324 85624306454575847049785 := by
  unfold tailWord_4502324
  simp only [CollatzResearch.WordTrace]
  refine ⟨82106623470428279283105013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109475497960571039044140017 82106623470428279283105013)
  ·
    refine ⟨7697495950352651182791095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82106623470428279283105013 7697495950352651182791095)
    ·
      refine ⟨11546243925528976774186643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7697495950352651182791095 11546243925528976774186643)
      ·
        refine ⟨17319365888293465161279965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11546243925528976774186643 17319365888293465161279965)
        ·
          refine ⟨6494762208110049435479987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17319365888293465161279965 6494762208110049435479987)
          ·
            refine ⟨9742143312165074153219981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6494762208110049435479987 9742143312165074153219981)
            ·
              refine ⟨3653303742061902807457493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9742143312165074153219981 3653303742061902807457493)
              ·
                refine ⟨85624306454575847049785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3653303742061902807457493 85624306454575847049785)
                ·
                  rfl

theorem cell23_4502324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 7].length) (baseStart_4502324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502324 prefixEnd_4502324 := by exact prefixLift 4502324
  have htrace : WordTrace (prefixWord ++ tailWord_4502324) baseStart_4502324 baseEnd_4502324 := by
    simpa [prefixWord, tailWord_4502324, baseEnd_4502324] using wordTrace_append hprefix tailTrace_4502324
  have hstable : (prefixWord ++ tailWord_4502324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502324).length < 2 ^ (prefixWord ++ tailWord_4502324).sum := by decide
  have hdescent : baseEnd_4502324 < baseStart_4502324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502327 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 3, 3, 2]
def baseStart_4502327 : Nat := 118140960795 + 4502327 * 2 ^ 59
def prefixEnd_4502327 : Nat := 4983230072969 + 3 ^ 40 * 4502327 * 2
def baseEnd_4502327 : Nat := 2311857814715511358606681

theorem tailTrace_4502327 : CollatzResearch.WordTrace tailWord_4502327 prefixEnd_4502327 2311857814715511358606681 := by
  unfold tailWord_4502327
  simp only [CollatzResearch.WordTrace]
  refine ⟨164213356359845690078569235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109475570906563793385712823 164213356359845690078569235)
  ·
    refine ⟨246320034539768535117853853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164213356359845690078569235 246320034539768535117853853)
    ·
      refine ⟨92370012952413200669195195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246320034539768535117853853 92370012952413200669195195)
      ·
        refine ⟨138555019428619801003792793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92370012952413200669195195 138555019428619801003792793)
        ·
          refine ⟨103916264571464850752844595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138555019428619801003792793 103916264571464850752844595)
          ·
            refine ⟨155874396857197276129266893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103916264571464850752844595 155874396857197276129266893)
            ·
              refine ⟨58452898821448978548475085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155874396857197276129266893 58452898821448978548475085)
              ·
                refine ⟨21919837058043366955678157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58452898821448978548475085 21919837058043366955678157)
                ·
                  refine ⟨8219938896766262608379309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21919837058043366955678157 8219938896766262608379309)
                  ·
                    refine ⟨3082477086287348478142241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8219938896766262608379309 3082477086287348478142241)
                    ·
                      refine ⟨2311857814715511358606681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082477086287348478142241 2311857814715511358606681)
                      ·
                        rfl

theorem cell23_4502327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_4502327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502327 prefixEnd_4502327 := by exact prefixLift 4502327
  have htrace : WordTrace (prefixWord ++ tailWord_4502327) baseStart_4502327 baseEnd_4502327 := by
    simpa [prefixWord, tailWord_4502327, baseEnd_4502327] using wordTrace_append hprefix tailTrace_4502327
  have hstable : (prefixWord ++ tailWord_4502327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502327).length < 2 ^ (prefixWord ++ tailWord_4502327).sum := by decide
  have hdescent : baseEnd_4502327 < baseStart_4502327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502344 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_4502344 : Nat := 118140960795 + 4502344 * 2 ^ 59
def prefixEnd_4502344 : Nat := 4983230072969 + 3 ^ 40 * 4502344 * 2
def baseEnd_4502344 : Nat := 2311866543886637792094103

theorem tailTrace_4502344 : CollatzResearch.WordTrace tailWord_4502344 prefixEnd_4502344 2311866543886637792094103 := by
  unfold tailWord_4502344
  simp only [CollatzResearch.WordTrace]
  refine ⟨82106988200392050990969043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109475984267189401321292057 82106988200392050990969043)
  ·
    refine ⟨123160482300588076486453565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82106988200392050990969043 123160482300588076486453565)
    ·
      refine ⟨46185180862720528682420087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123160482300588076486453565 46185180862720528682420087)
      ·
        refine ⟨69277771294080793023630131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46185180862720528682420087 69277771294080793023630131)
        ·
          refine ⟨103916656941121189535445197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69277771294080793023630131 103916656941121189535445197)
          ·
            refine ⟨38968746352920446075791949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103916656941121189535445197 38968746352920446075791949)
            ·
              refine ⟨14613279882345167278421981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38968746352920446075791949 14613279882345167278421981)
              ·
                refine ⟨5479979955879437729408243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14613279882345167278421981 5479979955879437729408243)
                ·
                  refine ⟨8219969933819156594112365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5479979955879437729408243 8219969933819156594112365)
                  ·
                    refine ⟨3082488725182183722792137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8219969933819156594112365 3082488725182183722792137)
                    ·
                      refine ⟨2311866543886637792094103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082488725182183722792137 2311866543886637792094103)
                      ·
                        rfl

theorem cell23_4502344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_4502344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502344 prefixEnd_4502344 := by exact prefixLift 4502344
  have htrace : WordTrace (prefixWord ++ tailWord_4502344) baseStart_4502344 baseEnd_4502344 := by
    simpa [prefixWord, tailWord_4502344, baseEnd_4502344] using wordTrace_append hprefix tailTrace_4502344
  have hstable : (prefixWord ++ tailWord_4502344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502344).length < 2 ^ (prefixWord ++ tailWord_4502344).sum := by decide
  have hdescent : baseEnd_4502344 < baseStart_4502344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502360 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_4502360 : Nat := 118140960795 + 4502360 * 2 ^ 59
def prefixEnd_4502360 : Nat := 4983230072969 + 3 ^ 40 * 4502360 * 2
def baseEnd_4502360 : Nat := 2311874759577109729494029

theorem tailTrace_4502360 : CollatzResearch.WordTrace tailWord_4502360 prefixEnd_4502360 2311874759577109729494029 := by
  unfold tailWord_4502360
  simp only [CollatzResearch.WordTrace]
  refine ⟨82107279984363068357260267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109476373312484091143013689 82107279984363068357260267)
  ·
    refine ⟨123160919976544602535890401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82107279984363068357260267 123160919976544602535890401)
    ·
      refine ⟨92370689982408451901917801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123160919976544602535890401 92370689982408451901917801)
      ·
        refine ⟨69278017486806338926438351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92370689982408451901917801 69278017486806338926438351)
        ·
          refine ⟨103917026230209508389657527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69278017486806338926438351 103917026230209508389657527)
          ·
            refine ⟨155875539345314262584486291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103917026230209508389657527 155875539345314262584486291)
            ·
              refine ⟨233813309017971393876729437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155875539345314262584486291 233813309017971393876729437)
              ·
                refine ⟨87679990881739272703773539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233813309017971393876729437 87679990881739272703773539)
                ·
                  refine ⟨131519986322608909055660309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87679990881739272703773539 131519986322608909055660309)
                  ·
                    refine ⟨6164999358872292611984077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131519986322608909055660309 6164999358872292611984077)
                    ·
                      refine ⟨2311874759577109729494029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6164999358872292611984077 2311874759577109729494029)
                      ·
                        rfl

theorem cell23_4502360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_4502360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502360 prefixEnd_4502360 := by exact prefixLift 4502360
  have htrace : WordTrace (prefixWord ++ tailWord_4502360) baseStart_4502360 baseEnd_4502360 := by
    simpa [prefixWord, tailWord_4502360, baseEnd_4502360] using wordTrace_append hprefix tailTrace_4502360
  have hstable : (prefixWord ++ tailWord_4502360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502360).length < 2 ^ (prefixWord ++ tailWord_4502360).sum := by decide
  have hdescent : baseEnd_4502360 < baseStart_4502360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502380 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 7]
def baseStart_4502380 : Nat := 118140960795 + 4502380 * 2 ^ 59
def prefixEnd_4502380 : Nat := 4983230072969 + 3 ^ 40 * 4502380 * 2
def baseEnd_4502380 : Nat := 256876114354466627915993

theorem tailTrace_4502380 : CollatzResearch.WordTrace tailWord_4502380 prefixEnd_4502380 256876114354466627915993 := by
  unfold tailWord_4502380
  simp only [CollatzResearch.WordTrace]
  refine ⟨82107644714326840065124297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109476859619102453420165729 82107644714326840065124297)
  ·
    refine ⟨61580733535745130048843223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82107644714326840065124297 61580733535745130048843223)
    ·
      refine ⟨92371100303617695073264835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61580733535745130048843223 92371100303617695073264835)
      ·
        refine ⟨138556650455426542609897253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92371100303617695073264835 138556650455426542609897253)
        ·
          refine ⟨25979371960392476739355735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138556650455426542609897253 25979371960392476739355735)
          ·
            refine ⟨38969057940588715109033603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25979371960392476739355735 38969057940588715109033603)
            ·
              refine ⟨58453586910883072663550405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38969057940588715109033603 58453586910883072663550405)
              ·
                refine ⟨10960047545790576124415701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58453586910883072663550405 10960047545790576124415701)
                ·
                  refine ⟨256876114354466627915993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10960047545790576124415701 256876114354466627915993)
                  ·
                    rfl

theorem cell23_4502380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_4502380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502380 prefixEnd_4502380 := by exact prefixLift 4502380
  have htrace : WordTrace (prefixWord ++ tailWord_4502380) baseStart_4502380 baseEnd_4502380 := by
    simpa [prefixWord, tailWord_4502380, baseEnd_4502380] using wordTrace_append hprefix tailTrace_4502380
  have hstable : (prefixWord ++ tailWord_4502380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502380).length < 2 ^ (prefixWord ++ tailWord_4502380).sum := by decide
  have hdescent : baseEnd_4502380 < baseStart_4502380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502417 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 2, 5, 2]
def baseStart_4502417 : Nat := 118140960795 + 4502417 * 2 ^ 59
def prefixEnd_4502417 : Nat := 4983230072969 + 3 ^ 40 * 4502417 * 2
def baseEnd_4502417 : Nat := 2311904027974416006481267

theorem tailTrace_4502417 : CollatzResearch.WordTrace tailWord_4502417 prefixEnd_4502417 2311904027974416006481267 := by
  unfold tailWord_4502417
  simp only [CollatzResearch.WordTrace]
  refine ⟨164216638929519635449345505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109477759286346423632897003 164216638929519635449345505)
  ·
    refine ⟨123162479197139726587009129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164216638929519635449345505 123162479197139726587009129)
    ·
      refine ⟨92371859397854794940256847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123162479197139726587009129 92371859397854794940256847)
      ·
        refine ⟨138557789096782192410385271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92371859397854794940256847 138557789096782192410385271)
        ·
          refine ⟨207836683645173288615577907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138557789096782192410385271 207836683645173288615577907)
          ·
            refine ⟨311755025467759932923366861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207836683645173288615577907 311755025467759932923366861)
            ·
              refine ⟨116908134550409974846262573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 311755025467759932923366861 116908134550409974846262573)
              ·
                refine ⟨43840550456403740567348465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116908134550409974846262573 43840550456403740567348465)
                ·
                  refine ⟨32880412842302805425511349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43840550456403740567348465 32880412842302805425511349)
                  ·
                    refine ⟨3082538703965888008641689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32880412842302805425511349 3082538703965888008641689)
                    ·
                      refine ⟨2311904027974416006481267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082538703965888008641689 2311904027974416006481267)
                      ·
                        rfl

theorem cell23_4502417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_4502417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502417 prefixEnd_4502417 := by exact prefixLift 4502417
  have htrace : WordTrace (prefixWord ++ tailWord_4502417) baseStart_4502417 baseEnd_4502417 := by
    simpa [prefixWord, tailWord_4502417, baseEnd_4502417] using wordTrace_append hprefix tailTrace_4502417
  have hstable : (prefixWord ++ tailWord_4502417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502417).length < 2 ^ (prefixWord ++ tailWord_4502417).sum := by decide
  have hdescent : baseEnd_4502417 < baseStart_4502417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502447 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 3, 6, 2]
def baseStart_4502447 : Nat := 118140960795 + 4502447 * 2 ^ 59
def prefixEnd_4502447 : Nat := 4983230072969 + 3 ^ 40 * 4502447 * 2
def baseEnd_4502447 : Nat := 2311919432394050889106129

theorem tailTrace_4502447 : CollatzResearch.WordTrace tailWord_4502447 prefixEnd_4502447 2311919432394050889106129 := by
  unfold tailWord_4502447
  simp only [CollatzResearch.WordTrace]
  refine ⟨164217733119410950572937595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109478488746273967048625063 164217733119410950572937595)
  ·
    refine ⟨246326599679116425859406393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164217733119410950572937595 246326599679116425859406393)
    ·
      refine ⟨184744949759337319394554795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246326599679116425859406393 184744949759337319394554795)
      ·
        refine ⟨277117424639005979091832193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184744949759337319394554795 277117424639005979091832193)
        ·
          refine ⟨207838068479254484318874145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277117424639005979091832193 207838068479254484318874145)
          ·
            refine ⟨155878551359440863239155609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207838068479254484318874145 155878551359440863239155609)
            ·
              refine ⟨116908913519580647429366707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155878551359440863239155609 116908913519580647429366707)
              ·
                refine ⟨175363370279370971144050061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116908913519580647429366707 175363370279370971144050061)
                ·
                  refine ⟨65761263854764114179018773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 175363370279370971144050061 65761263854764114179018773)
                  ·
                    refine ⟨3082559243192067852141505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65761263854764114179018773 3082559243192067852141505)
                    ·
                      refine ⟨2311919432394050889106129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082559243192067852141505 2311919432394050889106129)
                      ·
                        rfl

theorem cell23_4502447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 6, 2].length) (baseStart_4502447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502447 prefixEnd_4502447 := by exact prefixLift 4502447
  have htrace : WordTrace (prefixWord ++ tailWord_4502447) baseStart_4502447 baseEnd_4502447 := by
    simpa [prefixWord, tailWord_4502447, baseEnd_4502447] using wordTrace_append hprefix tailTrace_4502447
  have hstable : (prefixWord ++ tailWord_4502447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502447).length < 2 ^ (prefixWord ++ tailWord_4502447).sum := by decide
  have hdescent : baseEnd_4502447 < baseStart_4502447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502450 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4502450 : Nat := 118140960795 + 4502450 * 2 ^ 59
def prefixEnd_4502450 : Nat := 4983230072969 + 3 ^ 40 * 4502450 * 2
def baseEnd_4502450 : Nat := 2311920972836014377368615

theorem tailTrace_4502450 : CollatzResearch.WordTrace tailWord_4502450 prefixEnd_4502450 2311920972836014377368615 := by
  unfold tailWord_4502450
  simp only [CollatzResearch.WordTrace]
  refine ⟨41054460634600020521324201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109478561692266721390197869 41054460634600020521324201)
  ·
    refine ⟨30790845475950015390993151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41054460634600020521324201 30790845475950015390993151)
    ·
      refine ⟨46186268213925023086489727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30790845475950015390993151 46186268213925023086489727)
      ·
        refine ⟨69279402320887534629734591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46186268213925023086489727 69279402320887534629734591)
        ·
          refine ⟨103919103481331301944601887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69279402320887534629734591 103919103481331301944601887)
          ·
            refine ⟨155878655221996952916902831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103919103481331301944601887 155878655221996952916902831)
            ·
              refine ⟨233817982832995429375354247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155878655221996952916902831 233817982832995429375354247)
              ·
                refine ⟨350726974249493144063031371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233817982832995429375354247 350726974249493144063031371)
                ·
                  refine ⟨526090461374239716094547057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350726974249493144063031371 526090461374239716094547057)
                  ·
                    refine ⟨394567846030679787070910293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 526090461374239716094547057 394567846030679787070910293)
                    ·
                      refine ⟨2311920972836014377368615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 394567846030679787070910293 2311920972836014377368615)
                      ·
                        rfl

theorem cell23_4502450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4502450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502450 prefixEnd_4502450 := by exact prefixLift 4502450
  have htrace : WordTrace (prefixWord ++ tailWord_4502450) baseStart_4502450 baseEnd_4502450 := by
    simpa [prefixWord, tailWord_4502450, baseEnd_4502450] using wordTrace_append hprefix tailTrace_4502450
  have hstable : (prefixWord ++ tailWord_4502450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502450).length < 2 ^ (prefixWord ++ tailWord_4502450).sum := by decide
  have hdescent : baseEnd_4502450 < baseStart_4502450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502498 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4502498 : Nat := 118140960795 + 4502498 * 2 ^ 59
def prefixEnd_4502498 : Nat := 4983230072969 + 3 ^ 40 * 4502498 * 2
def baseEnd_4502498 : Nat := 2311945619907430189568395

theorem tailTrace_4502498 : CollatzResearch.WordTrace tailWord_4502498 prefixEnd_4502498 2311945619907430189568395 := by
  unfold tailWord_4502498
  simp only [CollatzResearch.WordTrace]
  refine ⟨41054898310556546570761037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109479728828150790855362765 41054898310556546570761037)
  ·
    refine ⟨15395586866458704964035389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41054898310556546570761037 15395586866458704964035389)
    ·
      refine ⟨5773345074922014361513271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15395586866458704964035389 5773345074922014361513271)
      ·
        refine ⟨8660017612383021542269907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5773345074922014361513271 8660017612383021542269907)
        ·
          refine ⟨12990026418574532313404861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8660017612383021542269907 12990026418574532313404861)
          ·
            refine ⟨4871259906965449617526823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12990026418574532313404861 4871259906965449617526823)
            ·
              refine ⟨7306889860448174426290235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4871259906965449617526823 7306889860448174426290235)
              ·
                refine ⟨10960334790672261639435353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7306889860448174426290235 10960334790672261639435353)
                ·
                  refine ⟨8220251093004196229576515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10960334790672261639435353 8220251093004196229576515)
                  ·
                    refine ⟨12330376639506294344364773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8220251093004196229576515 12330376639506294344364773)
                    ·
                      refine ⟨2311945619907430189568395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12330376639506294344364773 2311945619907430189568395)
                      ·
                        rfl

theorem cell23_4502498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4502498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502498 prefixEnd_4502498 := by exact prefixLift 4502498
  have htrace : WordTrace (prefixWord ++ tailWord_4502498) baseStart_4502498 baseEnd_4502498 := by
    simpa [prefixWord, tailWord_4502498, baseEnd_4502498] using wordTrace_append hprefix tailTrace_4502498
  have hstable : (prefixWord ++ tailWord_4502498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502498).length < 2 ^ (prefixWord ++ tailWord_4502498).sum := by decide
  have hdescent : baseEnd_4502498 < baseStart_4502498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502501 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4502501 : Nat := 118140960795 + 4502501 * 2 ^ 59
def prefixEnd_4502501 : Nat := 4983230072969 + 3 ^ 40 * 4502501 * 2
def baseEnd_4502501 : Nat := 2311947160349393677830881

theorem tailTrace_4502501 : CollatzResearch.WordTrace tailWord_4502501 prefixEnd_4502501 2311947160349393677830881 := by
  unfold tailWord_4502501
  simp only [CollatzResearch.WordTrace]
  refine ⟨164219702661215317795403357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109479801774143545196935571 164219702661215317795403357)
  ·
    refine ⟨61582388497955744173276259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164219702661215317795403357 61582388497955744173276259)
    ·
      refine ⟨92373582746933616259914389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61582388497955744173276259 92373582746933616259914389)
      ·
        refine ⟨4330011691262513262183487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92373582746933616259914389 4330011691262513262183487)
        ·
          refine ⟨6495017536893769893275231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4330011691262513262183487 6495017536893769893275231)
          ·
            refine ⟨9742526305340654839912847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495017536893769893275231 9742526305340654839912847)
            ·
              refine ⟨14613789458010982259869271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9742526305340654839912847 14613789458010982259869271)
              ·
                refine ⟨21920684187016473389803907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14613789458010982259869271 21920684187016473389803907)
                ·
                  refine ⟨32881026280524710084705861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21920684187016473389803907 32881026280524710084705861)
                  ·
                    refine ⟨6165192427598383140882349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32881026280524710084705861 6165192427598383140882349)
                    ·
                      refine ⟨2311947160349393677830881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6165192427598383140882349 2311947160349393677830881)
                      ·
                        rfl

theorem cell23_4502501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4502501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502501 prefixEnd_4502501 := by exact prefixLift 4502501
  have htrace : WordTrace (prefixWord ++ tailWord_4502501) baseStart_4502501 baseEnd_4502501 := by
    simpa [prefixWord, tailWord_4502501, baseEnd_4502501] using wordTrace_append hprefix tailTrace_4502501
  have hstable : (prefixWord ++ tailWord_4502501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502501).length < 2 ^ (prefixWord ++ tailWord_4502501).sum := by decide
  have hdescent : baseEnd_4502501 < baseStart_4502501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502537 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_4502537 : Nat := 118140960795 + 4502537 * 2 ^ 59
def prefixEnd_4502537 : Nat := 4983230072969 + 3 ^ 40 * 4502537 * 2
def baseEnd_4502537 : Nat := 2311965645652955536980715

theorem tailTrace_4502537 : CollatzResearch.WordTrace tailWord_4502537 prefixEnd_4502537 2311965645652955536980715 := by
  unfold tailWord_4502537
  simp only [CollatzResearch.WordTrace]
  refine ⟨164221015689084895943713865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109480677126056597295809243 164221015689084895943713865)
  ·
    refine ⟨123165761766813671957785399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164221015689084895943713865 123165761766813671957785399)
    ·
      refine ⟨184748642650220507936678099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123165761766813671957785399 184748642650220507936678099)
      ·
        refine ⟨277122963975330761905017149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184748642650220507936678099 277122963975330761905017149)
        ·
          refine ⟨103921111490749035714381431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277122963975330761905017149 103921111490749035714381431)
          ·
            refine ⟨155881667236123553571572147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103921111490749035714381431 155881667236123553571572147)
            ·
              refine ⟨233822500854185330357358221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155881667236123553571572147 233822500854185330357358221)
              ·
                refine ⟨87683437820319498884009333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233822500854185330357358221 87683437820319498884009333)
                ·
                  refine ⟨8220322295654953020375875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87683437820319498884009333 8220322295654953020375875)
                  ·
                    refine ⟨12330483443482429530563813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8220322295654953020375875 12330483443482429530563813)
                    ·
                      refine ⟨2311965645652955536980715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12330483443482429530563813 2311965645652955536980715)
                      ·
                        rfl

theorem cell23_4502537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_4502537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502537 prefixEnd_4502537 := by exact prefixLift 4502537
  have htrace : WordTrace (prefixWord ++ tailWord_4502537) baseStart_4502537 baseEnd_4502537 := by
    simpa [prefixWord, tailWord_4502537, baseEnd_4502537] using wordTrace_append hprefix tailTrace_4502537
  have hstable : (prefixWord ++ tailWord_4502537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502537).length < 2 ^ (prefixWord ++ tailWord_4502537).sum := by decide
  have hdescent : baseEnd_4502537 < baseStart_4502537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502551 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 1, 5]
def baseStart_4502551 : Nat := 118140960795 + 4502551 * 2 ^ 59
def prefixEnd_4502551 : Nat := 4983230072969 + 3 ^ 40 * 4502551 * 2
def baseEnd_4502551 : Nat := 770657611460706160735217

theorem tailTrace_4502551 : CollatzResearch.WordTrace tailWord_4502551 prefixEnd_4502551 770657611460706160735217 := by
  unfold tailWord_4502551
  simp only [CollatzResearch.WordTrace]
  refine ⟨164221526311034176334723507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109481017540689450889815671 164221526311034176334723507)
  ·
    refine ⟨246332289466551264502085261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164221526311034176334723507 246332289466551264502085261)
    ·
      refine ⟨92374608549956724188281973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246332289466551264502085261 92374608549956724188281973)
      ·
        refine ⟨8660119551558442892651435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92374608549956724188281973 8660119551558442892651435)
        ·
          refine ⟨12990179327337664338977153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8660119551558442892651435 12990179327337664338977153)
          ·
            refine ⟨9742634495503248254232865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12990179327337664338977153 9742634495503248254232865)
            ·
              refine ⟨7306975871627436190674649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9742634495503248254232865 7306975871627436190674649)
              ·
                refine ⟨5480231903720577143005987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7306975871627436190674649 5480231903720577143005987)
                ·
                  refine ⟨8220347855580865714508981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480231903720577143005987 8220347855580865714508981)
                  ·
                    refine ⟨770657611460706160735217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8220347855580865714508981 770657611460706160735217)
                    ·
                      rfl

theorem cell23_4502551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_4502551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502551 prefixEnd_4502551 := by exact prefixLift 4502551
  have htrace : WordTrace (prefixWord ++ tailWord_4502551) baseStart_4502551 baseEnd_4502551 := by
    simpa [prefixWord, tailWord_4502551, baseEnd_4502551] using wordTrace_append hprefix tailTrace_4502551
  have hstable : (prefixWord ++ tailWord_4502551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502551).length < 2 ^ (prefixWord ++ tailWord_4502551).sum := by decide
  have hdescent : baseEnd_4502551 < baseStart_4502551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502554 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2]
def baseStart_4502554 : Nat := 118140960795 + 4502554 * 2 ^ 59
def prefixEnd_4502554 : Nat := 4983230072969 + 3 ^ 40 * 4502554 * 2
def baseEnd_4502554 : Nat := 2311974374824081970468137

theorem tailTrace_4502554 : CollatzResearch.WordTrace tailWord_4502554 prefixEnd_4502554 2311974374824081970468137 := by
  unfold tailWord_4502554
  simp only [CollatzResearch.WordTrace]
  refine ⟨41055408932505826961770679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109481090486682205231388477 41055408932505826961770679)
  ·
    refine ⟨61583113398758740442656019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41055408932505826961770679 61583113398758740442656019)
    ·
      refine ⟨92374670098138110663984029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61583113398758740442656019 92374670098138110663984029)
      ·
        refine ⟨34640501286801791498994011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92374670098138110663984029 34640501286801791498994011)
        ·
          refine ⟨51960751930202687248491017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34640501286801791498994011 51960751930202687248491017)
          ·
            refine ⟨38970563947652015436368263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51960751930202687248491017 38970563947652015436368263)
            ·
              refine ⟨58455845921478023154552395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38970563947652015436368263 58455845921478023154552395)
              ·
                refine ⟨87683768882217034731828593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58455845921478023154552395 87683768882217034731828593)
                ·
                  refine ⟨65762826661662776048871445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87683768882217034731828593 65762826661662776048871445)
                  ·
                    refine ⟨3082632499765442627290849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65762826661662776048871445 3082632499765442627290849)
                    ·
                      refine ⟨2311974374824081970468137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082632499765442627290849 2311974374824081970468137)
                      ·
                        rfl

theorem cell23_4502554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_4502554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502554 prefixEnd_4502554 := by exact prefixLift 4502554
  have htrace : WordTrace (prefixWord ++ tailWord_4502554) baseStart_4502554 baseEnd_4502554 := by
    simpa [prefixWord, tailWord_4502554, baseEnd_4502554] using wordTrace_append hprefix tailTrace_4502554
  have hstable : (prefixWord ++ tailWord_4502554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502554).length < 2 ^ (prefixWord ++ tailWord_4502554).sum := by decide
  have hdescent : baseEnd_4502554 < baseStart_4502554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502582 : List Nat := [5, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_4502582 : Nat := 118140960795 + 4502582 * 2 ^ 59
def prefixEnd_4502582 : Nat := 4983230072969 + 3 ^ 40 * 4502582 * 2
def baseEnd_4502582 : Nat := 2311988752282407860918009

theorem tailTrace_4502582 : CollatzResearch.WordTrace tailWord_4502582 prefixEnd_4502582 2311988752282407860918009 := by
  unfold tailWord_4502582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10263916060870116789318875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 109481771315947912419401333 10263916060870116789318875)
  ·
    refine ⟨15395874091305175183978313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10263916060870116789318875 15395874091305175183978313)
    ·
      refine ⟨11546905568478881387983735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15395874091305175183978313 11546905568478881387983735)
      ·
        refine ⟨17320358352718322081975603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11546905568478881387983735 17320358352718322081975603)
        ·
          refine ⟨25980537529077483122963405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17320358352718322081975603 25980537529077483122963405)
          ·
            refine ⟨9742701573404056171111277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25980537529077483122963405 9742701573404056171111277)
            ·
              refine ⟨3653513090026521064166729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9742701573404056171111277 3653513090026521064166729)
              ·
                refine ⟨2740134817519890798125047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3653513090026521064166729 2740134817519890798125047)
                ·
                  refine ⟨4110202226279836197187571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740134817519890798125047 4110202226279836197187571)
                  ·
                    refine ⟨6165303339419754295781357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4110202226279836197187571 6165303339419754295781357)
                    ·
                      refine ⟨2311988752282407860918009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6165303339419754295781357 2311988752282407860918009)
                      ·
                        rfl

theorem cell23_4502582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_4502582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502582 prefixEnd_4502582 := by exact prefixLift 4502582
  have htrace : WordTrace (prefixWord ++ tailWord_4502582) baseStart_4502582 baseEnd_4502582 := by
    simpa [prefixWord, tailWord_4502582, baseEnd_4502582] using wordTrace_append hprefix tailTrace_4502582
  have hstable : (prefixWord ++ tailWord_4502582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502582).length < 2 ^ (prefixWord ++ tailWord_4502582).sum := by decide
  have hdescent : baseEnd_4502582 < baseStart_4502582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502587 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 3]
def baseStart_4502587 : Nat := 118140960795 + 4502587 * 2 ^ 59
def prefixEnd_4502587 : Nat := 4983230072969 + 3 ^ 40 * 4502587 * 2
def baseEnd_4502587 : Nat := 2311991319685680341355485

theorem tailTrace_4502587 : CollatzResearch.WordTrace tailWord_4502587 prefixEnd_4502587 2311991319685680341355485 := by
  unfold tailWord_4502587
  simp only [CollatzResearch.WordTrace]
  refine ⟨164222839338903754483034015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109481892892602502988689343 164222839338903754483034015)
  ·
    refine ⟨246334259008355631724551023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164222839338903754483034015 246334259008355631724551023)
    ·
      refine ⟨369501388512533447586826535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246334259008355631724551023 369501388512533447586826535)
      ·
        refine ⟨554252082768800171380239803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369501388512533447586826535 554252082768800171380239803)
        ·
          refine ⟨831378124153200257070359705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554252082768800171380239803 831378124153200257070359705)
          ·
            refine ⟨623533593114900192802769779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831378124153200257070359705 623533593114900192802769779)
            ·
              refine ⟨935300389672350289204154669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623533593114900192802769779 935300389672350289204154669)
              ·
                refine ⟨350737646127131358451558001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 935300389672350289204154669 350737646127131358451558001)
                ·
                  refine ⟨263053234595348518838668501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350737646127131358451558001 263053234595348518838668501)
                  ·
                    refine ⟨6165310185828480910281293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 263053234595348518838668501 6165310185828480910281293)
                    ·
                      refine ⟨2311991319685680341355485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6165310185828480910281293 2311991319685680341355485)
                      ·
                        rfl

theorem cell23_4502587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 3].length) (baseStart_4502587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502587 prefixEnd_4502587 := by exact prefixLift 4502587
  have htrace : WordTrace (prefixWord ++ tailWord_4502587) baseStart_4502587 baseEnd_4502587 := by
    simpa [prefixWord, tailWord_4502587, baseEnd_4502587] using wordTrace_append hprefix tailTrace_4502587
  have hstable : (prefixWord ++ tailWord_4502587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502587).length < 2 ^ (prefixWord ++ tailWord_4502587).sum := by decide
  have hdescent : baseEnd_4502587 < baseStart_4502587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502588 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_4502588 : Nat := 118140960795 + 4502588 * 2 ^ 59
def prefixEnd_4502588 : Nat := 4983230072969 + 3 ^ 40 * 4502588 * 2
def baseEnd_4502588 : Nat := 2311991833166334837442981

theorem tailTrace_4502588 : CollatzResearch.WordTrace tailWord_4502588 prefixEnd_4502588 2311991833166334837442981 := by
  unfold tailWord_4502588
  simp only [CollatzResearch.WordTrace]
  refine ⟨82111437905950065826910209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109481917207933421102546945 82111437905950065826910209)
  ·
    refine ⟨61583578429462549370182657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82111437905950065826910209 61583578429462549370182657)
    ·
      refine ⟨46187683822096912027636993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61583578429462549370182657 46187683822096912027636993)
      ·
        refine ⟨34640762866572684020727745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46187683822096912027636993 34640762866572684020727745)
        ·
          refine ⟨25980572149929513015545809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34640762866572684020727745 25980572149929513015545809)
          ·
            refine ⟨19485429112447134761659357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25980572149929513015545809 19485429112447134761659357)
            ·
              refine ⟨7307035917167675535622259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19485429112447134761659357 7307035917167675535622259)
              ·
                refine ⟨10960553875751513303433389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7307035917167675535622259 10960553875751513303433389)
                ·
                  refine ⟨4110207703406817488787521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10960553875751513303433389 4110207703406817488787521)
                  ·
                    refine ⟨3082655777555113116590641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110207703406817488787521 3082655777555113116590641)
                    ·
                      refine ⟨2311991833166334837442981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082655777555113116590641 2311991833166334837442981)
                      ·
                        rfl

theorem cell23_4502588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_4502588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502588 prefixEnd_4502588 := by exact prefixLift 4502588
  have htrace : WordTrace (prefixWord ++ tailWord_4502588) baseStart_4502588 baseEnd_4502588 := by
    simpa [prefixWord, tailWord_4502588, baseEnd_4502588] using wordTrace_append hprefix tailTrace_4502588
  have hstable : (prefixWord ++ tailWord_4502588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502588).length < 2 ^ (prefixWord ++ tailWord_4502588).sum := by decide
  have hdescent : baseEnd_4502588 < baseStart_4502588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502604 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_4502604 : Nat := 118140960795 + 4502604 * 2 ^ 59
def prefixEnd_4502604 : Nat := 4983230072969 + 3 ^ 40 * 4502604 * 2
def baseEnd_4502604 : Nat := 2312000048856806774842907

theorem tailTrace_4502604 : CollatzResearch.WordTrace tailWord_4502604 prefixEnd_4502604 2312000048856806774842907 := by
  unfold tailWord_4502604
  simp only [CollatzResearch.WordTrace]
  refine ⟨82111729689921083193201433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109482306253228110924268577 82111729689921083193201433)
  ·
    refine ⟨61583797267440812394901075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82111729689921083193201433 61583797267440812394901075)
    ·
      refine ⟨92375695901161218592351613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61583797267440812394901075 92375695901161218592351613)
      ·
        refine ⟨34640885962935456972131855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92375695901161218592351613 34640885962935456972131855)
        ·
          refine ⟨51961328944403185458197783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34640885962935456972131855 51961328944403185458197783)
          ·
            refine ⟨77941993416604778187296675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51961328944403185458197783 77941993416604778187296675)
            ·
              refine ⟨116912990124907167280945013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77941993416604778187296675 116912990124907167280945013)
              ·
                refine ⟨10960592824210046932588595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116912990124907167280945013 10960592824210046932588595)
                ·
                  refine ⟨16440889236315070398882893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10960592824210046932588595 16440889236315070398882893)
                  ·
                    refine ⟨6165333463618151399581085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16440889236315070398882893 6165333463618151399581085)
                    ·
                      refine ⟨2312000048856806774842907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6165333463618151399581085 2312000048856806774842907)
                      ·
                        rfl

theorem cell23_4502604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_4502604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502604 prefixEnd_4502604 := by exact prefixLift 4502604
  have htrace : WordTrace (prefixWord ++ tailWord_4502604) baseStart_4502604 baseEnd_4502604 := by
    simpa [prefixWord, tailWord_4502604, baseEnd_4502604] using wordTrace_append hprefix tailTrace_4502604
  have hstable : (prefixWord ++ tailWord_4502604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502604).length < 2 ^ (prefixWord ++ tailWord_4502604).sum := by decide
  have hdescent : baseEnd_4502604 < baseStart_4502604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502617 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_4502617 : Nat := 118140960795 + 4502617 * 2 ^ 59
def prefixEnd_4502617 : Nat := 4983230072969 + 3 ^ 40 * 4502617 * 2
def baseEnd_4502617 : Nat := 2312006724105315223980347

theorem tailTrace_4502617 : CollatzResearch.WordTrace tailWord_4502617 prefixEnd_4502617 2312006724105315223980347 := by
  unfold tailWord_4502617
  simp only [CollatzResearch.WordTrace]
  refine ⟨164223933528795069606626105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109482622352530046404417403 164223933528795069606626105)
  ·
    refine ⟨123167950146596302204969579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164223933528795069606626105 123167950146596302204969579)
    ·
      refine ⟨184751925219894453307454369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123167950146596302204969579 184751925219894453307454369)
      ·
        refine ⟨138563943914920839980590777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184751925219894453307454369 138563943914920839980590777)
        ·
          refine ⟨103922957936190629985443083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138563943914920839980590777 103922957936190629985443083)
          ·
            refine ⟨155884436904285944978164625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103922957936190629985443083 155884436904285944978164625)
            ·
              refine ⟨116913327678214458733623469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155884436904285944978164625 116913327678214458733623469)
              ·
                refine ⟨43842497879330422025108801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116913327678214458733623469 43842497879330422025108801)
                ·
                  refine ⟨32881873409497816518831601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43842497879330422025108801 32881873409497816518831601)
                  ·
                    refine ⟨24661405057123362389123701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32881873409497816518831601 24661405057123362389123701)
                    ·
                      refine ⟨2312006724105315223980347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24661405057123362389123701 2312006724105315223980347)
                      ·
                        rfl

theorem cell23_4502617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_4502617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502617 prefixEnd_4502617 := by exact prefixLift 4502617
  have htrace : WordTrace (prefixWord ++ tailWord_4502617) baseStart_4502617 baseEnd_4502617 := by
    simpa [prefixWord, tailWord_4502617, baseEnd_4502617] using wordTrace_append hprefix tailTrace_4502617
  have hstable : (prefixWord ++ tailWord_4502617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502617).length < 2 ^ (prefixWord ++ tailWord_4502617).sum := by decide
  have hdescent : baseEnd_4502617 < baseStart_4502617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502622 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_4502622 : Nat := 118140960795 + 4502622 * 2 ^ 59
def prefixEnd_4502622 : Nat := 4983230072969 + 3 ^ 40 * 4502622 * 2
def baseEnd_4502622 : Nat := 2312009291508587704417825

theorem tailTrace_4502622 : CollatzResearch.WordTrace tailWord_4502622 prefixEnd_4502622 2312009291508587704417825 := by
  unfold tailWord_4502622
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528014486722119432569765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109482743929184636973705413 20528014486722119432569765)
  ·
    refine ⟨3849002716260397393606831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20528014486722119432569765 3849002716260397393606831)
    ·
      refine ⟨5773504074390596090410247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3849002716260397393606831 5773504074390596090410247)
      ·
        refine ⟨8660256111585894135615371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5773504074390596090410247 8660256111585894135615371)
        ·
          refine ⟨12990384167378841203423057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8660256111585894135615371 12990384167378841203423057)
          ·
            refine ⟨9742788125534130902567293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12990384167378841203423057 9742788125534130902567293)
            ·
              refine ⟨3653545547075299088462735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9742788125534130902567293 3653545547075299088462735)
              ·
                refine ⟨5480318320612948632694103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653545547075299088462735 5480318320612948632694103)
                ·
                  refine ⟨8220477480919422949041155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480318320612948632694103 8220477480919422949041155)
                  ·
                    refine ⟨12330716221379134423561733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8220477480919422949041155 12330716221379134423561733)
                    ·
                      refine ⟨2312009291508587704417825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12330716221379134423561733 2312009291508587704417825)
                      ·
                        rfl

theorem cell23_4502622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_4502622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502622 prefixEnd_4502622 := by exact prefixLift 4502622
  have htrace : WordTrace (prefixWord ++ tailWord_4502622) baseStart_4502622 baseEnd_4502622 := by
    simpa [prefixWord, tailWord_4502622, baseEnd_4502622] using wordTrace_append hprefix tailTrace_4502622
  have hstable : (prefixWord ++ tailWord_4502622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502622).length < 2 ^ (prefixWord ++ tailWord_4502622).sum := by decide
  have hdescent : baseEnd_4502622 < baseStart_4502622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502638 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_4502638 : Nat := 118140960795 + 4502638 * 2 ^ 59
def prefixEnd_4502638 : Nat := 4983230072969 + 3 ^ 40 * 4502638 * 2
def baseEnd_4502638 : Nat := 2312017507199059641817751

theorem tailTrace_4502638 : CollatzResearch.WordTrace tailWord_4502638 prefixEnd_4502638 2312017507199059641817751 := by
  unfold tailWord_4502638
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528087432714873774142571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109483132974479326795427045 20528087432714873774142571)
  ·
    refine ⟨30792131149072310661213857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20528087432714873774142571 30792131149072310661213857)
    ·
      refine ⟨23094098361804232995910393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30792131149072310661213857 23094098361804232995910393)
      ·
        refine ⟨17320573771353174746932795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23094098361804232995910393 17320573771353174746932795)
        ·
          refine ⟨25980860657029762120399193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17320573771353174746932795 25980860657029762120399193)
          ·
            refine ⟨19485645492772321590299395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25980860657029762120399193 19485645492772321590299395)
            ·
              refine ⟨29228468239158482385449093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19485645492772321590299395 29228468239158482385449093)
              ·
                refine ⟨5480337794842215447271705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29228468239158482385449093 5480337794842215447271705)
                ·
                  refine ⟨4110253346131661585453779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5480337794842215447271705 4110253346131661585453779)
                  ·
                    refine ⟨6165380019197492378180669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4110253346131661585453779 6165380019197492378180669)
                    ·
                      refine ⟨2312017507199059641817751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6165380019197492378180669 2312017507199059641817751)
                      ·
                        rfl

theorem cell23_4502638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_4502638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502638 prefixEnd_4502638 := by exact prefixLift 4502638
  have htrace : WordTrace (prefixWord ++ tailWord_4502638) baseStart_4502638 baseEnd_4502638 := by
    simpa [prefixWord, tailWord_4502638, baseEnd_4502638] using wordTrace_append hprefix tailTrace_4502638
  have hstable : (prefixWord ++ tailWord_4502638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502638).length < 2 ^ (prefixWord ++ tailWord_4502638).sum := by decide
  have hdescent : baseEnd_4502638 < baseStart_4502638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502682 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4502682 : Nat := 118140960795 + 4502682 * 2 ^ 59
def prefixEnd_4502682 : Nat := 4983230072969 + 3 ^ 40 * 4502682 * 2
def baseEnd_4502682 : Nat := 2312040100347857469667549

theorem tailTrace_4502682 : CollatzResearch.WordTrace tailWord_4502682 prefixEnd_4502682 2312040100347857469667549 := by
  unfold tailWord_4502682
  simp only [CollatzResearch.WordTrace]
  refine ⟨41056576068389896426935575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109484202849039723805161533 41056576068389896426935575)
  ·
    refine ⟨61584864102584844640403363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41056576068389896426935575 61584864102584844640403363)
    ·
      refine ⟨92377296153877266960605045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61584864102584844640403363 92377296153877266960605045)
      ·
        refine ⟨8660371514425993777556723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92377296153877266960605045 8660371514425993777556723)
        ·
          refine ⟨12990557271638990666335085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8660371514425993777556723 12990557271638990666335085)
          ·
            refine ⟨4871458976864621499875657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12990557271638990666335085 4871458976864621499875657)
            ·
              refine ⟨3653594232648466124906743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4871458976864621499875657 3653594232648466124906743)
              ·
                refine ⟨5480391348972699187360115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653594232648466124906743 5480391348972699187360115)
                ·
                  refine ⟨8220587023459048781040173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480391348972699187360115 8220587023459048781040173)
                  ·
                    refine ⟨3082720133797143292890065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8220587023459048781040173 3082720133797143292890065)
                    ·
                      refine ⟨2312040100347857469667549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082720133797143292890065 2312040100347857469667549)
                      ·
                        rfl

theorem cell23_4502682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4502682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502682 prefixEnd_4502682 := by exact prefixLift 4502682
  have htrace : WordTrace (prefixWord ++ tailWord_4502682) baseStart_4502682 baseEnd_4502682 := by
    simpa [prefixWord, tailWord_4502682, baseEnd_4502682] using wordTrace_append hprefix tailTrace_4502682
  have hstable : (prefixWord ++ tailWord_4502682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502682).length < 2 ^ (prefixWord ++ tailWord_4502682).sum := by decide
  have hdescent : baseEnd_4502682 < baseStart_4502682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502695 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_4502695 : Nat := 118140960795 + 4502695 * 2 ^ 59
def prefixEnd_4502695 : Nat := 4983230072969 + 3 ^ 40 * 4502695 * 2
def baseEnd_4502695 : Nat := 2312046775596365918804989

theorem tailTrace_4502695 : CollatzResearch.WordTrace tailWord_4502695 prefixEnd_4502695 2312046775596365918804989 := by
  unfold tailWord_4502695
  simp only [CollatzResearch.WordTrace]
  refine ⟨164226778422512488927965539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109484518948341659285310359 164226778422512488927965539)
  ·
    refine ⟨246340167633768733391948309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164226778422512488927965539 246340167633768733391948309)
    ·
      refine ⟨11547195357832909377747577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 246340167633768733391948309 11547195357832909377747577)
      ·
        refine ⟨8660396518374682033310683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11547195357832909377747577 8660396518374682033310683)
        ·
          refine ⟨12990594777562023049966025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8660396518374682033310683 12990594777562023049966025)
          ·
            refine ⟨9742946083171517287474519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12990594777562023049966025 9742946083171517287474519)
            ·
              refine ⟨14614419124757275931211779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9742946083171517287474519 14614419124757275931211779)
              ·
                refine ⟨21921628687135913896817669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14614419124757275931211779 21921628687135913896817669)
                ·
                  refine ⟨4110305378837983855653313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21921628687135913896817669 4110305378837983855653313)
                  ·
                    refine ⟨3082729034128487891739985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110305378837983855653313 3082729034128487891739985)
                    ·
                      refine ⟨2312046775596365918804989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082729034128487891739985 2312046775596365918804989)
                      ·
                        rfl

theorem cell23_4502695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_4502695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502695 prefixEnd_4502695 := by exact prefixLift 4502695
  have htrace : WordTrace (prefixWord ++ tailWord_4502695) baseStart_4502695 baseEnd_4502695 := by
    simpa [prefixWord, tailWord_4502695, baseEnd_4502695] using wordTrace_append hprefix tailTrace_4502695
  have hstable : (prefixWord ++ tailWord_4502695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502695).length < 2 ^ (prefixWord ++ tailWord_4502695).sum := by decide
  have hdescent : baseEnd_4502695 < baseStart_4502695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502697 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 2, 11]
def baseStart_4502697 : Nat := 118140960795 + 4502697 * 2 ^ 59
def prefixEnd_4502697 : Nat := 4983230072969 + 3 ^ 40 * 4502697 * 2
def baseEnd_4502697 : Nat := 770682600852558303659993

theorem tailTrace_4502697 : CollatzResearch.WordTrace tailWord_4502697 prefixEnd_4502697 770682600852558303659993 := by
  unfold tailWord_4502697
  simp only [CollatzResearch.WordTrace]
  refine ⟨164226851368505243269538345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109484567579003495513025563 164226851368505243269538345)
  ·
    refine ⟨123170138526378932452153759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164226851368505243269538345 123170138526378932452153759)
    ·
      refine ⟨184755207789568398678230639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123170138526378932452153759 184755207789568398678230639)
      ·
        refine ⟨277132811684352598017345959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184755207789568398678230639 277132811684352598017345959)
        ·
          refine ⟨415699217526528897026018939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277132811684352598017345959 415699217526528897026018939)
          ·
            refine ⟨623548826289793345539028409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415699217526528897026018939 623548826289793345539028409)
            ·
              refine ⟨467661619717345009154271307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623548826289793345539028409 467661619717345009154271307)
              ·
                refine ⟨701492429576017513731406961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467661619717345009154271307 701492429576017513731406961)
                ·
                  refine ⟨526119322182013135298555221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 701492429576017513731406961 526119322182013135298555221)
                  ·
                    refine ⟨770682600852558303659993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 526119322182013135298555221 770682600852558303659993)
                    ·
                      rfl

theorem cell23_4502697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_4502697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502697 prefixEnd_4502697 := by exact prefixLift 4502697
  have htrace : WordTrace (prefixWord ++ tailWord_4502697) baseStart_4502697 baseEnd_4502697 := by
    simpa [prefixWord, tailWord_4502697, baseEnd_4502697] using wordTrace_append hprefix tailTrace_4502697
  have hstable : (prefixWord ++ tailWord_4502697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502697).length < 2 ^ (prefixWord ++ tailWord_4502697).sum := by decide
  have hdescent : baseEnd_4502697 < baseStart_4502697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502751 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 4, 4, 2]
def baseStart_4502751 : Nat := 118140960795 + 4502751 * 2 ^ 59
def prefixEnd_4502751 : Nat := 4983230072969 + 3 ^ 40 * 4502751 * 2
def baseEnd_4502751 : Nat := 2312075530513017699704731

theorem tailTrace_4502751 : CollatzResearch.WordTrace tailWord_4502751 prefixEnd_4502751 2312075530513017699704731 := by
  unfold tailWord_4502751
  simp only [CollatzResearch.WordTrace]
  refine ⟨164228820910309610492004107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109485880606873073661336071 164228820910309610492004107)
  ·
    refine ⟨246343231365464415738006161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164228820910309610492004107 246343231365464415738006161)
    ·
      refine ⟨184757423524098311803504621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246343231365464415738006161 184757423524098311803504621)
      ·
        refine ⟨69284033821536866926314233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184757423524098311803504621 69284033821536866926314233)
        ·
          refine ⟨51963025366152650194735675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69284033821536866926314233 51963025366152650194735675)
          ·
            refine ⟨77944538049228975292103513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51963025366152650194735675 77944538049228975292103513)
            ·
              refine ⟨58458403536921731469077635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77944538049228975292103513 58458403536921731469077635)
              ·
                refine ⟨87687605305382597203616453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58458403536921731469077635 87687605305382597203616453)
                ·
                  refine ⟨16441425994759236975678085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87687605305382597203616453 16441425994759236975678085)
                  ·
                    refine ⟨3082767374017356932939641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16441425994759236975678085 3082767374017356932939641)
                    ·
                      refine ⟨2312075530513017699704731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082767374017356932939641 2312075530513017699704731)
                      ·
                        rfl

theorem cell23_4502751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_4502751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502751 prefixEnd_4502751 := by exact prefixLift 4502751
  have htrace : WordTrace (prefixWord ++ tailWord_4502751) baseStart_4502751 baseEnd_4502751 := by
    simpa [prefixWord, tailWord_4502751, baseEnd_4502751] using wordTrace_append hprefix tailTrace_4502751
  have hstable : (prefixWord ++ tailWord_4502751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502751).length < 2 ^ (prefixWord ++ tailWord_4502751).sum := by decide
  have hdescent : baseEnd_4502751 < baseStart_4502751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502788 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4502788 : Nat := 118140960795 + 4502788 * 2 ^ 59
def prefixEnd_4502788 : Nat := 4983230072969 + 3 ^ 40 * 4502788 * 2
def baseEnd_4502788 : Nat := 2312094529297234054942061

theorem tailTrace_4502788 : CollatzResearch.WordTrace tailWord_4502788 prefixEnd_4502788 2312094529297234054942061 := by
  unfold tailWord_4502788
  simp only [CollatzResearch.WordTrace]
  refine ⟨82115085205587782905550509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109486780274117043874067345 82115085205587782905550509)
  ·
    refine ⟨30793156952095418589581441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82115085205587782905550509 30793156952095418589581441)
    ·
      refine ⟨23094867714071563942186081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30793156952095418589581441 23094867714071563942186081)
      ·
        refine ⟨17321150785553672956639561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23094867714071563942186081 17321150785553672956639561)
        ·
          refine ⟨12990863089165254717479671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17321150785553672956639561 12990863089165254717479671)
          ·
            refine ⟨19486294633747882076219507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12990863089165254717479671 19486294633747882076219507)
            ·
              refine ⟨29229441950621823114329261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19486294633747882076219507 29229441950621823114329261)
              ·
                refine ⟨10961040731483183667873473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29229441950621823114329261 10961040731483183667873473)
                ·
                  refine ⟨8220780548612387750905105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10961040731483183667873473 8220780548612387750905105)
                  ·
                    refine ⟨6165585411459290813178829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8220780548612387750905105 6165585411459290813178829)
                    ·
                      refine ⟨2312094529297234054942061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6165585411459290813178829 2312094529297234054942061)
                      ·
                        rfl

theorem cell23_4502788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4502788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502788 prefixEnd_4502788 := by exact prefixLift 4502788
  have htrace : WordTrace (prefixWord ++ tailWord_4502788) baseStart_4502788 baseEnd_4502788 := by
    simpa [prefixWord, tailWord_4502788, baseEnd_4502788] using wordTrace_append hprefix tailTrace_4502788
  have hstable : (prefixWord ++ tailWord_4502788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502788).length < 2 ^ (prefixWord ++ tailWord_4502788).sum := by decide
  have hdescent : baseEnd_4502788 < baseStart_4502788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502794 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4502794 : Nat := 118140960795 + 4502794 * 2 ^ 59
def prefixEnd_4502794 : Nat := 4983230072969 + 3 ^ 40 * 4502794 * 2
def baseEnd_4502794 : Nat := 2312097610181161031467033

theorem tailTrace_4502794 : CollatzResearch.WordTrace tailWord_4502794 prefixEnd_4502794 2312097610181161031467033 := by
  unfold tailWord_4502794
  simp only [CollatzResearch.WordTrace]
  refine ⟨41057597312288457208954859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109486926166102552557212957 41057597312288457208954859)
  ·
    refine ⟨61586395968432685813432289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41057597312288457208954859 61586395968432685813432289)
    ·
      refine ⟨46189796976324514360074217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61586395968432685813432289 46189796976324514360074217)
      ·
        refine ⟨34642347732243385770055663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46189796976324514360074217 34642347732243385770055663)
        ·
          refine ⟨51963521598365078655083495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34642347732243385770055663 51963521598365078655083495)
          ·
            refine ⟨77945282397547617982625243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51963521598365078655083495 77945282397547617982625243)
            ·
              refine ⟨116917923596321426973937865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77945282397547617982625243 116917923596321426973937865)
              ·
                refine ⟨87688442697241070230453399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116917923596321426973937865 87688442697241070230453399)
                ·
                  refine ⟨131532664045861605345680099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87688442697241070230453399 131532664045861605345680099)
                  ·
                    refine ⟨197298996068792408018520149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131532664045861605345680099 197298996068792408018520149)
                    ·
                      refine ⟨2312097610181161031467033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 197298996068792408018520149 2312097610181161031467033)
                      ·
                        rfl

theorem cell23_4502794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4502794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502794 prefixEnd_4502794 := by exact prefixLift 4502794
  have htrace : WordTrace (prefixWord ++ tailWord_4502794) baseStart_4502794 baseEnd_4502794 := by
    simpa [prefixWord, tailWord_4502794, baseEnd_4502794] using wordTrace_append hprefix tailTrace_4502794
  have hstable : (prefixWord ++ tailWord_4502794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502794).length < 2 ^ (prefixWord ++ tailWord_4502794).sum := by decide
  have hdescent : baseEnd_4502794 < baseStart_4502794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502811 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 3, 5, 2]
def baseStart_4502811 : Nat := 118140960795 + 4502811 * 2 ^ 59
def prefixEnd_4502811 : Nat := 4983230072969 + 3 ^ 40 * 4502811 * 2
def baseEnd_4502811 : Nat := 2312106339352287464954455

theorem tailTrace_4502811 : CollatzResearch.WordTrace tailWord_4502811 prefixEnd_4502811 2312106339352287464954455 := by
  unfold tailWord_4502811
  simp only [CollatzResearch.WordTrace]
  refine ⟨164231009290092240739188287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109487339526728160492792191 164231009290092240739188287)
  ·
    refine ⟨246346513935138361108782431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164231009290092240739188287 246346513935138361108782431)
    ·
      refine ⟨369519770902707541663173647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246346513935138361108782431 369519770902707541663173647)
      ·
        refine ⟨554279656354061312494760471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369519770902707541663173647 554279656354061312494760471)
        ·
          refine ⟨831419484531091968742140707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554279656354061312494760471 831419484531091968742140707)
          ·
            refine ⟨1247129226796637953113211061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831419484531091968742140707 1247129226796637953113211061)
            ·
              refine ⟨116918365012184808104363537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1247129226796637953113211061 116918365012184808104363537)
              ·
                refine ⟨87688773759138606078272653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116918365012184808104363537 87688773759138606078272653)
                ·
                  refine ⟨32883290159676977279352245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87688773759138606078272653 32883290159676977279352245)
                  ·
                    refine ⟨3082808452469716619939273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32883290159676977279352245 3082808452469716619939273)
                    ·
                      refine ⟨2312106339352287464954455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082808452469716619939273 2312106339352287464954455)
                      ·
                        rfl

theorem cell23_4502811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5, 2].length) (baseStart_4502811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502811 prefixEnd_4502811 := by exact prefixLift 4502811
  have htrace : WordTrace (prefixWord ++ tailWord_4502811) baseStart_4502811 baseEnd_4502811 := by
    simpa [prefixWord, tailWord_4502811, baseEnd_4502811] using wordTrace_append hprefix tailTrace_4502811
  have hstable : (prefixWord ++ tailWord_4502811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502811).length < 2 ^ (prefixWord ++ tailWord_4502811).sum := by decide
  have hdescent : baseEnd_4502811 < baseStart_4502811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502821 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_4502821 : Nat := 118140960795 + 4502821 * 2 ^ 59
def prefixEnd_4502821 : Nat := 4983230072969 + 3 ^ 40 * 4502821 * 2
def baseEnd_4502821 : Nat := 770703824719610808609803

theorem tailTrace_4502821 : CollatzResearch.WordTrace tailWord_4502821 prefixEnd_4502821 770703824719610808609803 := by
  unfold tailWord_4502821
  simp only [CollatzResearch.WordTrace]
  refine ⟨164231374020056012447052317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109487582680037341631368211 164231374020056012447052317)
  ·
    refine ⟨61586765257521004667644619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164231374020056012447052317 61586765257521004667644619)
    ·
      refine ⟨92380147886281507001466929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61586765257521004667644619 92380147886281507001466929)
      ·
        refine ⟨69285110914711130251100197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92380147886281507001466929 69285110914711130251100197)
        ·
          refine ⟨12990958296508336922081287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69285110914711130251100197 12990958296508336922081287)
          ·
            refine ⟨19486437444762505383121931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12990958296508336922081287 19486437444762505383121931)
            ·
              refine ⟨29229656167143758074682897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19486437444762505383121931 29229656167143758074682897)
              ·
                refine ⟨21922242125357818556012173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29229656167143758074682897 21922242125357818556012173)
                ·
                  refine ⟨8220840797009181958504565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21922242125357818556012173 8220840797009181958504565)
                  ·
                    refine ⟨770703824719610808609803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8220840797009181958504565 770703824719610808609803)
                    ·
                      rfl

theorem cell23_4502821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_4502821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502821 prefixEnd_4502821 := by exact prefixLift 4502821
  have htrace : WordTrace (prefixWord ++ tailWord_4502821) baseStart_4502821 baseEnd_4502821 := by
    simpa [prefixWord, tailWord_4502821, baseEnd_4502821] using wordTrace_append hprefix tailTrace_4502821
  have hstable : (prefixWord ++ tailWord_4502821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502821).length < 2 ^ (prefixWord ++ tailWord_4502821).sum := by decide
  have hdescent : baseEnd_4502821 < baseStart_4502821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502851 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 4, 4]
def baseStart_4502851 : Nat := 118140960795 + 4502851 * 2 ^ 59
def prefixEnd_4502851 : Nat := 4983230072969 + 3 ^ 40 * 4502851 * 2
def baseEnd_4502851 : Nat := 770708959526155769484757

theorem tailTrace_4502851 : CollatzResearch.WordTrace tailWord_4502851 prefixEnd_4502851 770708959526155769484757 := by
  unfold tailWord_4502851
  simp only [CollatzResearch.WordTrace]
  refine ⟨164232468209947327570644407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109488312139964885047096271 164232468209947327570644407)
  ·
    refine ⟨246348702314920991355966611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164232468209947327570644407 246348702314920991355966611)
    ·
      refine ⟨369523053472381487033949917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246348702314920991355966611 369523053472381487033949917)
      ·
        refine ⟨138571145052143057637731219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369523053472381487033949917 138571145052143057637731219)
        ·
          refine ⟨207856717578214586456596829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138571145052143057637731219 207856717578214586456596829)
          ·
            refine ⟨77946269091830469921223811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207856717578214586456596829 77946269091830469921223811)
            ·
              refine ⟨116919403637745704881835717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77946269091830469921223811 116919403637745704881835717)
              ·
                refine ⟨21922388182077319665344197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116919403637745704881835717 21922388182077319665344197)
                ·
                  refine ⟨4110447784139497437252037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21922388182077319665344197 4110447784139497437252037)
                  ·
                    refine ⟨770708959526155769484757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4110447784139497437252037 770708959526155769484757)
                    ·
                      rfl

theorem cell23_4502851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 4].length) (baseStart_4502851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502851 prefixEnd_4502851 := by exact prefixLift 4502851
  have htrace : WordTrace (prefixWord ++ tailWord_4502851) baseStart_4502851 baseEnd_4502851 := by
    simpa [prefixWord, tailWord_4502851, baseEnd_4502851] using wordTrace_append hprefix tailTrace_4502851
  have hstable : (prefixWord ++ tailWord_4502851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502851).length < 2 ^ (prefixWord ++ tailWord_4502851).sum := by decide
  have hdescent : baseEnd_4502851 < baseStart_4502851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502855 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 1, 5]
def baseStart_4502855 : Nat := 118140960795 + 4502855 * 2 ^ 59
def prefixEnd_4502855 : Nat := 4983230072969 + 3 ^ 40 * 4502855 * 2
def baseEnd_4502855 : Nat := 770709644167028430934751

theorem tailTrace_4502855 : CollatzResearch.WordTrace tailWord_4502855 prefixEnd_4502855 770709644167028430934751 := by
  unfold tailWord_4502855
  simp only [CollatzResearch.WordTrace]
  refine ⟨164232614101932836253790019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109488409401288557502526679 164232614101932836253790019)
  ·
    refine ⟨246348921152899254380685029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164232614101932836253790019 246348921152899254380685029)
    ·
      refine ⟨46190422716168610196378443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246348921152899254380685029 46190422716168610196378443)
      ·
        refine ⟨69285634074252915294567665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46190422716168610196378443 69285634074252915294567665)
        ·
          refine ⟨51964225555689686470925749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69285634074252915294567665 51964225555689686470925749)
          ·
            refine ⟨4871646145845908106649289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51964225555689686470925749 4871646145845908106649289)
            ·
              refine ⟨3653734609384431079986967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4871646145845908106649289 3653734609384431079986967)
              ·
                refine ⟨5480601914076646619980451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653734609384431079986967 5480601914076646619980451)
                ·
                  refine ⟨8220902871114969929970677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480601914076646619980451 8220902871114969929970677)
                  ·
                    refine ⟨770709644167028430934751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8220902871114969929970677 770709644167028430934751)
                    ·
                      rfl

theorem cell23_4502855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_4502855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502855 prefixEnd_4502855 := by exact prefixLift 4502855
  have htrace : WordTrace (prefixWord ++ tailWord_4502855) baseStart_4502855 baseEnd_4502855 := by
    simpa [prefixWord, tailWord_4502855, baseEnd_4502855] using wordTrace_append hprefix tailTrace_4502855
  have hstable : (prefixWord ++ tailWord_4502855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502855).length < 2 ^ (prefixWord ++ tailWord_4502855).sum := by decide
  have hdescent : baseEnd_4502855 < baseStart_4502855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502864 : List Nat := [2, 1, 1, 1, 1, 5, 12]
def baseStart_4502864 : Nat := 118140960795 + 4502864 * 2 ^ 59
def prefixEnd_4502864 : Nat := 4983230072969 + 3 ^ 40 * 4502864 * 2
def baseEnd_4502864 : Nat := 28544858689221922933231

theorem tailTrace_4502864 : CollatzResearch.WordTrace tailWord_4502864 prefixEnd_4502864 28544858689221922933231 := by
  unfold tailWord_4502864
  simp only [CollatzResearch.WordTrace]
  refine ⟨82116471179450115395433823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109488628239266820527245097 82116471179450115395433823)
  ·
    refine ⟨123174706769175173093150735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82116471179450115395433823 123174706769175173093150735)
    ·
      refine ⟨184762060153762759639726103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123174706769175173093150735 184762060153762759639726103)
      ·
        refine ⟨277143090230644139459589155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184762060153762759639726103 277143090230644139459589155)
        ·
          refine ⟨415714635345966209189383733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277143090230644139459589155 415714635345966209189383733)
          ·
            refine ⟨38973247063684332111504725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 415714635345966209189383733 38973247063684332111504725)
            ·
              refine ⟨28544858689221922933231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 38973247063684332111504725 28544858689221922933231)
              ·
                rfl

theorem cell23_4502864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 12].length) (baseStart_4502864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502864 prefixEnd_4502864 := by exact prefixLift 4502864
  have htrace : WordTrace (prefixWord ++ tailWord_4502864) baseStart_4502864 baseEnd_4502864 := by
    simpa [prefixWord, tailWord_4502864, baseEnd_4502864] using wordTrace_append hprefix tailTrace_4502864
  have hstable : (prefixWord ++ tailWord_4502864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502864).length < 2 ^ (prefixWord ++ tailWord_4502864).sum := by decide
  have hdescent : baseEnd_4502864 < baseStart_4502864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502868 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_4502868 : Nat := 118140960795 + 4502868 * 2 ^ 59
def prefixEnd_4502868 : Nat := 4983230072969 + 3 ^ 40 * 4502868 * 2
def baseEnd_4502868 : Nat := 770711869249864580647231

theorem tailTrace_4502868 : CollatzResearch.WordTrace tailWord_4502868 prefixEnd_4502868 770711869249864580647231 := by
  unfold tailWord_4502868
  simp only [CollatzResearch.WordTrace]
  refine ⟨82116544125442869737006629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109488725500590492982675505 82116544125442869737006629)
  ·
    refine ⟨15396852023520538075688743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82116544125442869737006629 15396852023520538075688743)
    ·
      refine ⟨23095278035280807113533115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15396852023520538075688743 23095278035280807113533115)
      ·
        refine ⟨34642917052921210670299673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23095278035280807113533115 34642917052921210670299673)
        ·
          refine ⟨25982187789690908002724755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34642917052921210670299673 25982187789690908002724755)
          ·
            refine ⟨38973281684536362004087133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25982187789690908002724755 38973281684536362004087133)
            ·
              refine ⟨14614980631701135751532675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38973281684536362004087133 14614980631701135751532675)
              ·
                refine ⟨21922470947551703627299013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14614980631701135751532675 21922470947551703627299013)
                ·
                  refine ⟨4110463302665944430118565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21922470947551703627299013 4110463302665944430118565)
                  ·
                    refine ⟨770711869249864580647231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4110463302665944430118565 770711869249864580647231)
                    ·
                      rfl

theorem cell23_4502868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_4502868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502868 prefixEnd_4502868 := by exact prefixLift 4502868
  have htrace : WordTrace (prefixWord ++ tailWord_4502868) baseStart_4502868 baseEnd_4502868 := by
    simpa [prefixWord, tailWord_4502868, baseEnd_4502868] using wordTrace_append hprefix tailTrace_4502868
  have hstable : (prefixWord ++ tailWord_4502868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502868).length < 2 ^ (prefixWord ++ tailWord_4502868).sum := by decide
  have hdescent : baseEnd_4502868 < baseStart_4502868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502885 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_4502885 : Nat := 118140960795 + 4502885 * 2 ^ 59
def prefixEnd_4502885 : Nat := 4983230072969 + 3 ^ 40 * 4502885 * 2
def baseEnd_4502885 : Nat := 770714778973573391809705

theorem tailTrace_4502885 : CollatzResearch.WordTrace tailWord_4502885 prefixEnd_4502885 770714778973573391809705 := by
  unfold tailWord_4502885
  simp only [CollatzResearch.WordTrace]
  refine ⟨164233708291824151377382109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109489138861216100918254739 164233708291824151377382109)
  ·
    refine ⟨61587640609434056766518291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164233708291824151377382109 61587640609434056766518291)
    ·
      refine ⟨92381460914151085149777437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61587640609434056766518291 92381460914151085149777437)
      ·
        refine ⟨34643047842806656931166539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92381460914151085149777437 34643047842806656931166539)
        ·
          refine ⟨51964571764209985396749809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34643047842806656931166539 51964571764209985396749809)
          ·
            refine ⟨38973428823157489047562357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51964571764209985396749809 38973428823157489047562357)
            ·
              refine ⟨3653758952171014598208971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38973428823157489047562357 3653758952171014598208971)
              ·
                refine ⟨5480638428256521897313457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653758952171014598208971 5480638428256521897313457)
                ·
                  refine ⟨4110478821192391422985093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5480638428256521897313457 4110478821192391422985093)
                  ·
                    refine ⟨770714778973573391809705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4110478821192391422985093 770714778973573391809705)
                    ·
                      rfl

theorem cell23_4502885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_4502885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502885 prefixEnd_4502885 := by exact prefixLift 4502885
  have htrace : WordTrace (prefixWord ++ tailWord_4502885) baseStart_4502885 baseEnd_4502885 := by
    simpa [prefixWord, tailWord_4502885, baseEnd_4502885] using wordTrace_append hprefix tailTrace_4502885
  have hstable : (prefixWord ++ tailWord_4502885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502885).length < 2 ^ (prefixWord ++ tailWord_4502885).sum := by decide
  have hdescent : baseEnd_4502885 < baseStart_4502885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502888 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4502888 : Nat := 118140960795 + 4502888 * 2 ^ 59
def prefixEnd_4502888 : Nat := 4983230072969 + 3 ^ 40 * 4502888 * 2
def baseEnd_4502888 : Nat := 2312145877362683663691601

theorem tailTrace_4502888 : CollatzResearch.WordTrace tailWord_4502888 prefixEnd_4502888 2312145877362683663691601 := by
  unfold tailWord_4502888
  simp only [CollatzResearch.WordTrace]
  refine ⟨82116908855406641444870659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109489211807208855259827545 82116908855406641444870659)
  ·
    refine ⟨123175363283109962167305989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82116908855406641444870659 123175363283109962167305989)
    ·
      refine ⟨23095380615583117906369873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123175363283109962167305989 23095380615583117906369873)
      ·
        refine ⟨17321535461687338429777405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23095380615583117906369873 17321535461687338429777405)
        ·
          refine ⟨6495575798132751911166527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17321535461687338429777405 6495575798132751911166527)
          ·
            refine ⟨9743363697199127866749791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495575798132751911166527 9743363697199127866749791)
            ·
              refine ⟨14615045545798691800124687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9743363697199127866749791 14615045545798691800124687)
              ·
                refine ⟨21922568318698037700187031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14615045545798691800124687 21922568318698037700187031)
                ·
                  refine ⟨32883852478047056550280547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21922568318698037700187031 32883852478047056550280547)
                  ·
                    refine ⟨49325778717070584825420821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32883852478047056550280547 49325778717070584825420821)
                    ·
                      refine ⟨2312145877362683663691601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49325778717070584825420821 2312145877362683663691601)
                      ·
                        rfl

theorem cell23_4502888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4502888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502888 prefixEnd_4502888 := by exact prefixLift 4502888
  have htrace : WordTrace (prefixWord ++ tailWord_4502888) baseStart_4502888 baseEnd_4502888 := by
    simpa [prefixWord, tailWord_4502888, baseEnd_4502888] using wordTrace_append hprefix tailTrace_4502888
  have hstable : (prefixWord ++ tailWord_4502888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502888).length < 2 ^ (prefixWord ++ tailWord_4502888).sum := by decide
  have hdescent : baseEnd_4502888 < baseStart_4502888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502908 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_4502908 : Nat := 118140960795 + 4502908 * 2 ^ 59
def prefixEnd_4502908 : Nat := 4983230072969 + 3 ^ 40 * 4502908 * 2
def baseEnd_4502908 : Nat := 2312156146975773585441509

theorem tailTrace_4502908 : CollatzResearch.WordTrace tailWord_4502908 prefixEnd_4502908 2312156146975773585441509 := by
  unfold tailWord_4502908
  simp only [CollatzResearch.WordTrace]
  refine ⟨82117273585370413152734689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109489698113827217536979585 82117273585370413152734689)
  ·
    refine ⟨61587955189027809864551017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82117273585370413152734689 61587955189027809864551017)
    ·
      refine ⟨46190966391770857398413263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61587955189027809864551017 46190966391770857398413263)
      ·
        refine ⟨69286449587656286097619895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46190966391770857398413263 69286449587656286097619895)
        ·
          refine ⟨103929674381484429146429843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69286449587656286097619895 103929674381484429146429843)
          ·
            refine ⟨155894511572226643719644765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103929674381484429146429843 155894511572226643719644765)
            ·
              refine ⟨58460441839584991394866787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155894511572226643719644765 58460441839584991394866787)
              ·
                refine ⟨87690662759377487092300181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58460441839584991394866787 87690662759377487092300181)
                ·
                  refine ⟨4110499816845819707451571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87690662759377487092300181 4110499816845819707451571)
                  ·
                    refine ⟨6165749725268729561177357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4110499816845819707451571 6165749725268729561177357)
                    ·
                      refine ⟨2312156146975773585441509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6165749725268729561177357 2312156146975773585441509)
                      ·
                        rfl

theorem cell23_4502908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_4502908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502908 prefixEnd_4502908 := by exact prefixLift 4502908
  have htrace : WordTrace (prefixWord ++ tailWord_4502908) baseStart_4502908 baseEnd_4502908 := by
    simpa [prefixWord, tailWord_4502908, baseEnd_4502908] using wordTrace_append hprefix tailTrace_4502908
  have hstable : (prefixWord ++ tailWord_4502908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502908).length < 2 ^ (prefixWord ++ tailWord_4502908).sum := by decide
  have hdescent : baseEnd_4502908 < baseStart_4502908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502926 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4502926 : Nat := 118140960795 + 4502926 * 2 ^ 59
def prefixEnd_4502926 : Nat := 4983230072969 + 3 ^ 40 * 4502926 * 2
def baseEnd_4502926 : Nat := 2312165389627554515016427

theorem tailTrace_4502926 : CollatzResearch.WordTrace tailWord_4502926 prefixEnd_4502926 2312165389627554515016427 := by
  unfold tailWord_4502926
  simp only [CollatzResearch.WordTrace]
  refine ⟨20529400460584451922453079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109490135789783743586416421 20529400460584451922453079)
  ·
    refine ⟨30794100690876677883679619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20529400460584451922453079 30794100690876677883679619)
    ·
      refine ⟨46191151036315016825519429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30794100690876677883679619 46191151036315016825519429)
      ·
        refine ⟨8660840819309065654784893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46191151036315016825519429 8660840819309065654784893)
        ·
          refine ⟨3247815307240899620544335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8660840819309065654784893 3247815307240899620544335)
          ·
            refine ⟨4871722960861349430816503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247815307240899620544335 4871722960861349430816503)
            ·
              refine ⟨7307584441292024146224755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4871722960861349430816503 7307584441292024146224755)
              ·
                refine ⟨10961376661938036219337133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7307584441292024146224755 10961376661938036219337133)
                ·
                  refine ⟨4110516248226763582251425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10961376661938036219337133 4110516248226763582251425)
                  ·
                    refine ⟨3082887186170072686688569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110516248226763582251425 3082887186170072686688569)
                    ·
                      refine ⟨2312165389627554515016427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082887186170072686688569 2312165389627554515016427)
                      ·
                        rfl

theorem cell23_4502926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4502926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502926 prefixEnd_4502926 := by exact prefixLift 4502926
  have htrace : WordTrace (prefixWord ++ tailWord_4502926) baseStart_4502926 baseEnd_4502926 := by
    simpa [prefixWord, tailWord_4502926, baseEnd_4502926] using wordTrace_append hprefix tailTrace_4502926
  have hstable : (prefixWord ++ tailWord_4502926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502926).length < 2 ^ (prefixWord ++ tailWord_4502926).sum := by decide
  have hdescent : baseEnd_4502926 < baseStart_4502926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502965 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_4502965 : Nat := 118140960795 + 4502965 * 2 ^ 59
def prefixEnd_4502965 : Nat := 4983230072969 + 3 ^ 40 * 4502965 * 2
def baseEnd_4502965 : Nat := 2312185415373079862428747

theorem tailTrace_4502965 : CollatzResearch.WordTrace tailWord_4502965 prefixEnd_4502965 2312185415373079862428747 := by
  unfold tailWord_4502965
  simp only [CollatzResearch.WordTrace]
  refine ⟨164236626131534325040294349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109491084087689550026862899 164236626131534325040294349)
  ·
    refine ⟨61588734799325371890110381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164236626131534325040294349 61588734799325371890110381)
    ·
      refine ⟨23095775549747014458791393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61588734799325371890110381 23095775549747014458791393)
      ·
        refine ⟨17321831662310260844093545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23095775549747014458791393 17321831662310260844093545)
        ·
          refine ⟨12991373746732695633070159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17321831662310260844093545 12991373746732695633070159)
          ·
            refine ⟨19487060620099043449605239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12991373746732695633070159 19487060620099043449605239)
            ·
              refine ⟨29230590930148565174407859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19487060620099043449605239 29230590930148565174407859)
              ·
                refine ⟨43845886395222847761611789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29230590930148565174407859 43845886395222847761611789)
                ·
                  refine ⟨16442207398208567910604421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43845886395222847761611789 16442207398208567910604421)
                  ·
                    refine ⟨3082913887164106483238329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16442207398208567910604421 3082913887164106483238329)
                    ·
                      refine ⟨2312185415373079862428747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082913887164106483238329 2312185415373079862428747)
                      ·
                        rfl

theorem cell23_4502965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_4502965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502965 prefixEnd_4502965 := by exact prefixLift 4502965
  have htrace : WordTrace (prefixWord ++ tailWord_4502965) baseStart_4502965 baseEnd_4502965 := by
    simpa [prefixWord, tailWord_4502965, baseEnd_4502965] using wordTrace_append hprefix tailTrace_4502965
  have hstable : (prefixWord ++ tailWord_4502965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502965).length < 2 ^ (prefixWord ++ tailWord_4502965).sum := by decide
  have hdescent : baseEnd_4502965 < baseStart_4502965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4502969 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 1, 3, 2]
def baseStart_4502969 : Nat := 118140960795 + 4502969 * 2 ^ 59
def prefixEnd_4502969 : Nat := 4983230072969 + 3 ^ 40 * 4502969 * 2
def baseEnd_4502969 : Nat := 2312187469295697846778729

theorem tailTrace_4502969 : CollatzResearch.WordTrace tailWord_4502969 prefixEnd_4502969 2312187469295697846778729 := by
  unfold tailWord_4502969
  simp only [CollatzResearch.WordTrace]
  refine ⟨164236772023519833723439961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109491181349013222482293307 164236772023519833723439961)
  ·
    refine ⟨123177579017639875292579971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164236772023519833723439961 123177579017639875292579971)
    ·
      refine ⟨184766368526459812938869957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123177579017639875292579971 184766368526459812938869957)
      ·
        refine ⟨34643694098711214926038117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184766368526459812938869957 34643694098711214926038117)
        ·
          refine ⟨6495692643508352798632147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34643694098711214926038117 6495692643508352798632147)
          ·
            refine ⟨9743538965262529197948221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495692643508352798632147 9743538965262529197948221)
            ·
              refine ⟨3653827111973448449230583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9743538965262529197948221 3653827111973448449230583)
              ·
                refine ⟨5480740667960172673845875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653827111973448449230583 5480740667960172673845875)
                ·
                  refine ⟨8221111001940259010768813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480740667960172673845875 8221111001940259010768813)
                  ·
                    refine ⟨3082916625727597129038305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8221111001940259010768813 3082916625727597129038305)
                    ·
                      refine ⟨2312187469295697846778729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3082916625727597129038305 2312187469295697846778729)
                      ·
                        rfl

theorem cell23_4502969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_4502969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4502969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4502969 prefixEnd_4502969 := by exact prefixLift 4502969
  have htrace : WordTrace (prefixWord ++ tailWord_4502969) baseStart_4502969 baseEnd_4502969 := by
    simpa [prefixWord, tailWord_4502969, baseEnd_4502969] using wordTrace_append hprefix tailTrace_4502969
  have hstable : (prefixWord ++ tailWord_4502969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4502969).length < 2 ^ (prefixWord ++ tailWord_4502969).sum := by decide
  have hdescent : baseEnd_4502969 < baseStart_4502969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4502969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503068 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4503068 : Nat := 118140960795 + 4503068 * 2 ^ 59
def prefixEnd_4503068 : Nat := 4983230072969 + 3 ^ 40 * 4503068 * 2
def baseEnd_4503068 : Nat := 2312238303880492959440773

theorem tailTrace_4503068 : CollatzResearch.WordTrace tailWord_4503068 prefixEnd_4503068 2312238303880492959440773 := by
  unfold tailWord_4503068
  simp only [CollatzResearch.WordTrace]
  refine ⟨82120191425080586815646929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109493588566774115754195905 82120191425080586815646929)
  ·
    refine ⟨61590143568810440111735197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82120191425080586815646929 61590143568810440111735197)
    ·
      refine ⟨23096303838303915041900699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61590143568810440111735197 23096303838303915041900699)
      ·
        refine ⟨34644455757455872562851049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23096303838303915041900699 34644455757455872562851049)
        ·
          refine ⟨25983341818091904422138287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34644455757455872562851049 25983341818091904422138287)
          ·
            refine ⟨38975012727137856633207431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25983341818091904422138287 38975012727137856633207431)
            ·
              refine ⟨58462519090706784949811147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38975012727137856633207431 58462519090706784949811147)
              ·
                refine ⟨87693778636060177424716721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58462519090706784949811147 87693778636060177424716721)
                ·
                  refine ⟨65770333977045133068537541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87693778636060177424716721 65770333977045133068537541)
                  ·
                    refine ⟨12331937620695962450350789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65770333977045133068537541 12331937620695962450350789)
                    ·
                      refine ⟨2312238303880492959440773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12331937620695962450350789 2312238303880492959440773)
                      ·
                        rfl

theorem cell23_4503068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4503068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503068 prefixEnd_4503068 := by exact prefixLift 4503068
  have htrace : WordTrace (prefixWord ++ tailWord_4503068) baseStart_4503068 baseEnd_4503068 := by
    simpa [prefixWord, tailWord_4503068, baseEnd_4503068] using wordTrace_append hprefix tailTrace_4503068
  have hstable : (prefixWord ++ tailWord_4503068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503068).length < 2 ^ (prefixWord ++ tailWord_4503068).sum := by decide
  have hdescent : baseEnd_4503068 < baseStart_4503068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503115 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 6, 3, 2]
def baseStart_4503115 : Nat := 118140960795 + 4503115 * 2 ^ 59
def prefixEnd_4503115 : Nat := 4983230072969 + 3 ^ 40 * 4503115 * 2
def baseEnd_4503115 : Nat := 2312262437471254275553057

theorem tailTrace_4503115 : CollatzResearch.WordTrace tailWord_4503115 prefixEnd_4503115 2312262437471254275553057 := by
  unfold tailWord_4503115
  simp only [CollatzResearch.WordTrace]
  refine ⟨164242097080990900658254799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109494731387327267105503199 164242097080990900658254799)
  ·
    refine ⟨246363145621486350987382199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164242097080990900658254799 246363145621486350987382199)
    ·
      refine ⟨369544718432229526481073299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246363145621486350987382199 369544718432229526481073299)
      ·
        refine ⟨554317077648344289721609949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369544718432229526481073299 554317077648344289721609949)
        ·
          refine ⟨207868904118129108645603731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 554317077648344289721609949 207868904118129108645603731)
          ·
            refine ⟨311803356177193662968405597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207868904118129108645603731 311803356177193662968405597)
            ·
              refine ⟨116926258566447623613152099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 311803356177193662968405597 116926258566447623613152099)
              ·
                refine ⟨175389387849671435419728149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116926258566447623613152099 175389387849671435419728149)
                ·
                  refine ⟨8221377555453348535299757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175389387849671435419728149 8221377555453348535299757)
                  ·
                    refine ⟨3083016583295005700737409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8221377555453348535299757 3083016583295005700737409)
                    ·
                      refine ⟨2312262437471254275553057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083016583295005700737409 2312262437471254275553057)
                      ·
                        rfl

theorem cell23_4503115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 3, 2].length) (baseStart_4503115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503115 prefixEnd_4503115 := by exact prefixLift 4503115
  have htrace : WordTrace (prefixWord ++ tailWord_4503115) baseStart_4503115 baseEnd_4503115 := by
    simpa [prefixWord, tailWord_4503115, baseEnd_4503115] using wordTrace_append hprefix tailTrace_4503115
  have hstable : (prefixWord ++ tailWord_4503115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503115).length < 2 ^ (prefixWord ++ tailWord_4503115).sum := by decide
  have hdescent : baseEnd_4503115 < baseStart_4503115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503145 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 4]
def baseStart_4503145 : Nat := 118140960795 + 4503145 * 2 ^ 59
def prefixEnd_4503145 : Nat := 4983230072969 + 3 ^ 40 * 4503145 * 2
def baseEnd_4503145 : Nat := 2312277841890889158177919

theorem tailTrace_4503145 : CollatzResearch.WordTrace tailWord_4503145 prefixEnd_4503145 2312277841890889158177919 := by
  unfold tailWord_4503145
  simp only [CollatzResearch.WordTrace]
  refine ⟨164243191270882215781846889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109495460847254810521231259 164243191270882215781846889)
  ·
    refine ⟨123182393453161661836385167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164243191270882215781846889 123182393453161661836385167)
    ·
      refine ⟨184773590179742492754577751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123182393453161661836385167 184773590179742492754577751)
      ·
        refine ⟨277160385269613739131866627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184773590179742492754577751 277160385269613739131866627)
        ·
          refine ⟨415740577904420608697799941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277160385269613739131866627 415740577904420608697799941)
          ·
            refine ⟨77951358357078864130837489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 415740577904420608697799941 77951358357078864130837489)
            ·
              refine ⟨58463518767809148098128117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77951358357078864130837489 58463518767809148098128117)
              ·
                refine ⟨5480954884482107634199511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58463518767809148098128117 5480954884482107634199511)
                ·
                  refine ⟨8221432326723161451299267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480954884482107634199511 8221432326723161451299267)
                  ·
                    refine ⟨12332148490084742176948901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8221432326723161451299267 12332148490084742176948901)
                    ·
                      refine ⟨2312277841890889158177919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12332148490084742176948901 2312277841890889158177919)
                      ·
                        rfl

theorem cell23_4503145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_4503145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503145 prefixEnd_4503145 := by exact prefixLift 4503145
  have htrace : WordTrace (prefixWord ++ tailWord_4503145) baseStart_4503145 baseEnd_4503145 := by
    simpa [prefixWord, tailWord_4503145, baseEnd_4503145] using wordTrace_append hprefix tailTrace_4503145
  have hstable : (prefixWord ++ tailWord_4503145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503145).length < 2 ^ (prefixWord ++ tailWord_4503145).sum := by decide
  have hdescent : baseEnd_4503145 < baseStart_4503145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503172 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_4503172 : Nat := 118140960795 + 4503172 * 2 ^ 59
def prefixEnd_4503172 : Nat := 4983230072969 + 3 ^ 40 * 4503172 * 2
def baseEnd_4503172 : Nat := 770763901956186850846765

theorem tailTrace_4503172 : CollatzResearch.WordTrace tailWord_4503172 prefixEnd_4503172 770763901956186850846765 := by
  unfold tailWord_4503172
  simp only [CollatzResearch.WordTrace]
  refine ⟨82122088020892199696539885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109496117361189599595386513 82122088020892199696539885)
  ·
    refine ⟨30795783007834574886202457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82122088020892199696539885 30795783007834574886202457)
    ·
      refine ⟨23096837255875931164651843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30795783007834574886202457 23096837255875931164651843)
      ·
        refine ⟨34645255883813896746977765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23096837255875931164651843 34645255883813896746977765)
        ·
          refine ⟨6495985478215105640058331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34645255883813896746977765 6495985478215105640058331)
          ·
            refine ⟨9743978217322658460087497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495985478215105640058331 9743978217322658460087497)
            ·
              refine ⟨7307983662991993845065623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9743978217322658460087497 7307983662991993845065623)
              ·
                refine ⟨10961975494487990767598435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7307983662991993845065623 10961975494487990767598435)
                ·
                  refine ⟨16442963241731986151397653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10961975494487990767598435 16442963241731986151397653)
                  ·
                    refine ⟨770763901956186850846765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16442963241731986151397653 770763901956186850846765)
                    ·
                      rfl

theorem cell23_4503172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_4503172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503172 prefixEnd_4503172 := by exact prefixLift 4503172
  have htrace : WordTrace (prefixWord ++ tailWord_4503172) baseStart_4503172 baseEnd_4503172 := by
    simpa [prefixWord, tailWord_4503172, baseEnd_4503172] using wordTrace_append hprefix tailTrace_4503172
  have hstable : (prefixWord ++ tailWord_4503172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503172).length < 2 ^ (prefixWord ++ tailWord_4503172).sum := by decide
  have hdescent : baseEnd_4503172 < baseStart_4503172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503175 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4503175 : Nat := 118140960795 + 4503175 * 2 ^ 59
def prefixEnd_4503175 : Nat := 4983230072969 + 3 ^ 40 * 4503175 * 2
def baseEnd_4503175 : Nat := 2312293246310524040802781

theorem tailTrace_4503175 : CollatzResearch.WordTrace tailWord_4503175 prefixEnd_4503175 2312293246310524040802781 := by
  unfold tailWord_4503175
  simp only [CollatzResearch.WordTrace]
  refine ⟨164244285460773530905438979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109496190307182353936959319 164244285460773530905438979)
  ·
    refine ⟨246366428191160296358158469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164244285460773530905438979 246366428191160296358158469)
    ·
      refine ⟨46193705285842555567154713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246366428191160296358158469 46193705285842555567154713)
      ·
        refine ⟨34645278964381916675366035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46193705285842555567154713 34645278964381916675366035)
        ·
          refine ⟨51967918446572875013049053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34645278964381916675366035 51967918446572875013049053)
          ·
            refine ⟨19487969417464828129893395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51967918446572875013049053 19487969417464828129893395)
            ·
              refine ⟨29231954126197242194840093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19487969417464828129893395 29231954126197242194840093)
              ·
                refine ⟨10961982797323965823065035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29231954126197242194840093 10961982797323965823065035)
                ·
                  refine ⟨16442974195985948734597553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10961982797323965823065035 16442974195985948734597553)
                  ·
                    refine ⟨12332230646989461550948165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16442974195985948734597553 12332230646989461550948165)
                    ·
                      refine ⟨2312293246310524040802781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12332230646989461550948165 2312293246310524040802781)
                      ·
                        rfl

theorem cell23_4503175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4503175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503175 prefixEnd_4503175 := by exact prefixLift 4503175
  have htrace : WordTrace (prefixWord ++ tailWord_4503175) baseStart_4503175 baseEnd_4503175 := by
    simpa [prefixWord, tailWord_4503175, baseEnd_4503175] using wordTrace_append hprefix tailTrace_4503175
  have hstable : (prefixWord ++ tailWord_4503175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503175).length < 2 ^ (prefixWord ++ tailWord_4503175).sum := by decide
  have hdescent : baseEnd_4503175 < baseStart_4503175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503182 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_4503182 : Nat := 118140960795 + 4503182 * 2 ^ 59
def prefixEnd_4503182 : Nat := 4983230072969 + 3 ^ 40 * 4503182 * 2
def baseEnd_4503182 : Nat := 2312296840675105513415249

theorem tailTrace_4503182 : CollatzResearch.WordTrace tailWord_4503182 prefixEnd_4503182 2312296840675105513415249 := by
  unfold tailWord_4503182
  simp only [CollatzResearch.WordTrace]
  refine ⟨20530567596468521387617975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109496360514498780733962533 20530567596468521387617975)
  ·
    refine ⟨30795851394702782081426963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20530567596468521387617975 30795851394702782081426963)
    ·
      refine ⟨46193777092054173122140445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30795851394702782081426963 46193777092054173122140445)
      ·
        refine ⟨17322666409520314920802667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46193777092054173122140445 17322666409520314920802667)
        ·
          refine ⟨25983999614280472381204001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17322666409520314920802667 25983999614280472381204001)
          ·
            refine ⟨19487999710710354285903001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25983999614280472381204001 19487999710710354285903001)
            ·
              refine ⟨14615999783032765714427251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19487999710710354285903001 14615999783032765714427251)
              ·
                refine ⟨21923999674549148571640877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14615999783032765714427251 21923999674549148571640877)
                ·
                  refine ⟨8221499877955930714365329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21923999674549148571640877 8221499877955930714365329)
                  ·
                    refine ⟨6166124908466948035773997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8221499877955930714365329 6166124908466948035773997)
                    ·
                      refine ⟨2312296840675105513415249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6166124908466948035773997 2312296840675105513415249)
                      ·
                        rfl

theorem cell23_4503182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_4503182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503182 prefixEnd_4503182 := by exact prefixLift 4503182
  have htrace : WordTrace (prefixWord ++ tailWord_4503182) baseStart_4503182 baseEnd_4503182 := by
    simpa [prefixWord, tailWord_4503182, baseEnd_4503182] using wordTrace_append hprefix tailTrace_4503182
  have hstable : (prefixWord ++ tailWord_4503182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503182).length < 2 ^ (prefixWord ++ tailWord_4503182).sum := by decide
  have hdescent : baseEnd_4503182 < baseStart_4503182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503196 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_4503196 : Nat := 118140960795 + 4503196 * 2 ^ 59
def prefixEnd_4503196 : Nat := 4983230072969 + 3 ^ 40 * 4503196 * 2
def baseEnd_4503196 : Nat := 2312304029404268458640185

theorem tailTrace_4503196 : CollatzResearch.WordTrace tailWord_4503196 prefixEnd_4503196 2312304029404268458640185 := by
  unfold tailWord_4503196
  simp only [CollatzResearch.WordTrace]
  refine ⟨82122525696848725745976721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109496700929131634327968961 82122525696848725745976721)
  ·
    refine ⟨61591894272636544309482541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82122525696848725745976721 61591894272636544309482541)
    ·
      refine ⟨23096960352238704116055953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61591894272636544309482541 23096960352238704116055953)
      ·
        refine ⟨17322720264179028087041965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23096960352238704116055953 17322720264179028087041965)
        ·
          refine ⟨6496020099067135532640737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17322720264179028087041965 6496020099067135532640737)
          ·
            refine ⟨4872015074300351649480553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6496020099067135532640737 4872015074300351649480553)
            ·
              refine ⟨3654011305725263737110415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4872015074300351649480553 3654011305725263737110415)
              ·
                refine ⟨5481016958587895605665623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654011305725263737110415 5481016958587895605665623)
                ·
                  refine ⟨8221525437881843408498435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5481016958587895605665623 8221525437881843408498435)
                  ·
                    refine ⟨12332288156822765112747653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8221525437881843408498435 12332288156822765112747653)
                    ·
                      refine ⟨2312304029404268458640185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12332288156822765112747653 2312304029404268458640185)
                      ·
                        rfl

theorem cell23_4503196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_4503196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503196 prefixEnd_4503196 := by exact prefixLift 4503196
  have htrace : WordTrace (prefixWord ++ tailWord_4503196) baseStart_4503196 baseEnd_4503196 := by
    simpa [prefixWord, tailWord_4503196, baseEnd_4503196] using wordTrace_append hprefix tailTrace_4503196
  have hstable : (prefixWord ++ tailWord_4503196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503196).length < 2 ^ (prefixWord ++ tailWord_4503196).sum := by decide
  have hdescent : baseEnd_4503196 < baseStart_4503196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503202 : List Nat := [3, 3, 1, 4, 1, 1, 10]
def baseStart_4503202 : Nat := 118140960795 + 4503202 * 2 ^ 59
def prefixEnd_4503202 : Nat := 4983230072969 + 3 ^ 40 * 4503202 * 2
def baseEnd_4503202 : Nat := 28547001361582659693397

theorem tailTrace_4503202 : CollatzResearch.WordTrace tailWord_4503202 prefixEnd_4503202 28547001361582659693397 := by
  unfold tailWord_4503202
  simp only [CollatzResearch.WordTrace]
  refine ⟨41061317557918928629167965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109496846821117143011114573 41061317557918928629167965)
  ·
    refine ⟨15397994084219598235937987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41061317557918928629167965 15397994084219598235937987)
    ·
      refine ⟨23096991126329397353906981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15397994084219598235937987 23096991126329397353906981)
      ·
        refine ⟨4330685836186762003857559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23096991126329397353906981 4330685836186762003857559)
        ·
          refine ⟨6496028754280143005786339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4330685836186762003857559 6496028754280143005786339)
          ·
            refine ⟨9744043131420214508679509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496028754280143005786339 9744043131420214508679509)
            ·
              refine ⟨28547001361582659693397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9744043131420214508679509 28547001361582659693397)
              ·
                rfl

theorem cell23_4503202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 10].length) (baseStart_4503202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503202 prefixEnd_4503202 := by exact prefixLift 4503202
  have htrace : WordTrace (prefixWord ++ tailWord_4503202) baseStart_4503202 baseEnd_4503202 := by
    simpa [prefixWord, tailWord_4503202, baseEnd_4503202] using wordTrace_append hprefix tailTrace_4503202
  have hstable : (prefixWord ++ tailWord_4503202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503202).length < 2 ^ (prefixWord ++ tailWord_4503202).sum := by decide
  have hdescent : baseEnd_4503202 < baseStart_4503202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503239 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_4503239 : Nat := 118140960795 + 4503239 * 2 ^ 59
def prefixEnd_4503239 : Nat := 4983230072969 + 3 ^ 40 * 4503239 * 2
def baseEnd_4503239 : Nat := 2312326109072411790402487

theorem tailTrace_4503239 : CollatzResearch.WordTrace tailWord_4503239 prefixEnd_4503239 2312326109072411790402487 := by
  unfold tailWord_4503239
  simp only [CollatzResearch.WordTrace]
  refine ⟨164246619732541669835768771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109497746488361113223845847 164246619732541669835768771)
  ·
    refine ⟨246369929598812504753653157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164246619732541669835768771 246369929598812504753653157)
    ·
      refine ⟨46194361799777344641309967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 246369929598812504753653157 46194361799777344641309967)
      ·
        refine ⟨69291542699666016961964951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46194361799777344641309967 69291542699666016961964951)
        ·
          refine ⟨103937314049499025442947427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69291542699666016961964951 103937314049499025442947427)
          ·
            refine ⟨155905971074248538164421141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103937314049499025442947427 155905971074248538164421141)
            ·
              refine ⟨7308092394105400226457241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155905971074248538164421141 7308092394105400226457241)
              ·
                refine ⟨5481069295579050169842931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7308092394105400226457241 5481069295579050169842931)
                ·
                  refine ⟨8221603943368575254764397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5481069295579050169842931 8221603943368575254764397)
                  ·
                    refine ⟨3083101478763215720536649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8221603943368575254764397 3083101478763215720536649)
                    ·
                      refine ⟨2312326109072411790402487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083101478763215720536649 2312326109072411790402487)
                      ·
                        rfl

theorem cell23_4503239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_4503239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503239 prefixEnd_4503239 := by exact prefixLift 4503239
  have htrace : WordTrace (prefixWord ++ tailWord_4503239) baseStart_4503239 baseEnd_4503239 := by
    simpa [prefixWord, tailWord_4503239, baseEnd_4503239] using wordTrace_append hprefix tailTrace_4503239
  have hstable : (prefixWord ++ tailWord_4503239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503239).length < 2 ^ (prefixWord ++ tailWord_4503239).sum := by decide
  have hdescent : baseEnd_4503239 < baseStart_4503239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503255 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_4503255 : Nat := 118140960795 + 4503255 * 2 ^ 59
def prefixEnd_4503255 : Nat := 4983230072969 + 3 ^ 40 * 4503255 * 2
def baseEnd_4503255 : Nat := 2312334324762883727802413

theorem tailTrace_4503255 : CollatzResearch.WordTrace tailWord_4503255 prefixEnd_4503255 2312334324762883727802413 := by
  unfold tailWord_4503255
  simp only [CollatzResearch.WordTrace]
  refine ⟨164247203300483704568351219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109498135533655803045567479 164247203300483704568351219)
  ·
    refine ⟨246370804950725556852526829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164247203300483704568351219 246370804950725556852526829)
    ·
      refine ⟨92389051856522083819697561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246370804950725556852526829 92389051856522083819697561)
      ·
        refine ⟨69291788892391562864773171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92389051856522083819697561 69291788892391562864773171)
        ·
          refine ⟨103937683338587344297159757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69291788892391562864773171 103937683338587344297159757)
          ·
            refine ⟨38976631251970254111434909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103937683338587344297159757 38976631251970254111434909)
            ·
              refine ⟨14616236719488845291788091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38976631251970254111434909 14616236719488845291788091)
              ·
                refine ⟨21924355079233267937682137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14616236719488845291788091 21924355079233267937682137)
                ·
                  refine ⟨16443266309424950953261603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21924355079233267937682137 16443266309424950953261603)
                  ·
                    refine ⟨24664899464137426429892405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16443266309424950953261603 24664899464137426429892405)
                    ·
                      refine ⟨2312334324762883727802413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24664899464137426429892405 2312334324762883727802413)
                      ·
                        rfl

theorem cell23_4503255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_4503255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503255 prefixEnd_4503255 := by exact prefixLift 4503255
  have htrace : WordTrace (prefixWord ++ tailWord_4503255) baseStart_4503255 baseEnd_4503255 := by
    simpa [prefixWord, tailWord_4503255, baseEnd_4503255] using wordTrace_append hprefix tailTrace_4503255
  have hstable : (prefixWord ++ tailWord_4503255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503255).length < 2 ^ (prefixWord ++ tailWord_4503255).sum := by decide
  have hdescent : baseEnd_4503255 < baseStart_4503255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503269 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 4, 2, 2]
def baseStart_4503269 : Nat := 118140960795 + 4503269 * 2 ^ 59
def prefixEnd_4503269 : Nat := 4983230072969 + 3 ^ 40 * 4503269 * 2
def baseEnd_4503269 : Nat := 2312341513492046673027349

theorem tailTrace_4503269 : CollatzResearch.WordTrace tailWord_4503269 prefixEnd_4503269 2312341513492046673027349 := by
  unfold tailWord_4503269
  simp only [CollatzResearch.WordTrace]
  refine ⟨164247713922432984959360861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109498475948288656639573907 164247713922432984959360861)
  ·
    refine ⟨61592892720912369359760323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164247713922432984959360861 61592892720912369359760323)
    ·
      refine ⟨92389339081368554039640485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61592892720912369359760323 92389339081368554039640485)
      ·
        refine ⟨17323001077756603882432591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92389339081368554039640485 17323001077756603882432591)
        ·
          refine ⟨25984501616634905823648887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17323001077756603882432591 25984501616634905823648887)
          ·
            refine ⟨38976752424952358735473331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25984501616634905823648887 38976752424952358735473331)
            ·
              refine ⟨58465128637428538103209997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38976752424952358735473331 58465128637428538103209997)
              ·
                refine ⟨21924423239035701788703749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58465128637428538103209997 21924423239035701788703749)
                ·
                  refine ⟨4110829357319194085381953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21924423239035701788703749 4110829357319194085381953)
                  ·
                    refine ⟨3083122017989395564036465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4110829357319194085381953 3083122017989395564036465)
                    ·
                      refine ⟨2312341513492046673027349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083122017989395564036465 2312341513492046673027349)
                      ·
                        rfl

theorem cell23_4503269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_4503269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503269 prefixEnd_4503269 := by exact prefixLift 4503269
  have htrace : WordTrace (prefixWord ++ tailWord_4503269) baseStart_4503269 baseEnd_4503269 := by
    simpa [prefixWord, tailWord_4503269, baseEnd_4503269] using wordTrace_append hprefix tailTrace_4503269
  have hstable : (prefixWord ++ tailWord_4503269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503269).length < 2 ^ (prefixWord ++ tailWord_4503269).sum := by decide
  have hdescent : baseEnd_4503269 < baseStart_4503269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503275 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 7]
def baseStart_4503275 : Nat := 118140960795 + 4503275 * 2 ^ 59
def prefixEnd_4503275 : Nat := 4983230072969 + 3 ^ 40 * 4503275 * 2
def baseEnd_4503275 : Nat := 256927177152885961061369

theorem tailTrace_4503275 : CollatzResearch.WordTrace tailWord_4503275 prefixEnd_4503275 256927177152885961061369 := by
  unfold tailWord_4503275
  simp only [CollatzResearch.WordTrace]
  refine ⟨164247932760411247984079279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109498621840274165322719519 164247932760411247984079279)
  ·
    refine ⟨246371899140616871976118919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164247932760411247984079279 246371899140616871976118919)
    ·
      refine ⟨369557848710925307964178379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246371899140616871976118919 369557848710925307964178379)
      ·
        refine ⟨554336773066387961946267569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369557848710925307964178379 554336773066387961946267569)
        ·
          refine ⟨415752579799790971459700677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 554336773066387961946267569 415752579799790971459700677)
          ·
            refine ⟨77953608712460807148693877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 415752579799790971459700677 77953608712460807148693877)
            ·
              refine ⟨7308150816793200670190051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77953608712460807148693877 7308150816793200670190051)
              ·
                refine ⟨10962226225189801005285077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7308150816793200670190051 10962226225189801005285077)
                ·
                  refine ⟨256927177152885961061369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10962226225189801005285077 256927177152885961061369)
                  ·
                    rfl

theorem cell23_4503275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 7].length) (baseStart_4503275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503275 prefixEnd_4503275 := by exact prefixLift 4503275
  have htrace : WordTrace (prefixWord ++ tailWord_4503275) baseStart_4503275 baseEnd_4503275 := by
    simpa [prefixWord, tailWord_4503275, baseEnd_4503275] using wordTrace_append hprefix tailTrace_4503275
  have hstable : (prefixWord ++ tailWord_4503275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503275).length < 2 ^ (prefixWord ++ tailWord_4503275).sum := by decide
  have hdescent : baseEnd_4503275 < baseStart_4503275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503322 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_4503322 : Nat := 118140960795 + 4503322 * 2 ^ 59
def prefixEnd_4503322 : Nat := 4983230072969 + 3 ^ 40 * 4503322 * 2
def baseEnd_4503322 : Nat := 770789575988911655221535

theorem tailTrace_4503322 : CollatzResearch.WordTrace tailWord_4503322 prefixEnd_4503322 770789575988911655221535 := by
  unfold tailWord_4503322
  simp only [CollatzResearch.WordTrace]
  refine ⟨41062411747810243752760055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109499764660827316674026813 41062411747810243752760055)
  ·
    refine ⟨61593617621715365629140083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41062411747810243752760055 61593617621715365629140083)
    ·
      refine ⟨92390426432573048443710125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61593617621715365629140083 92390426432573048443710125)
      ·
        refine ⟨34646409912214893166391297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92390426432573048443710125 34646409912214893166391297)
        ·
          refine ⟨25984807434161169874793473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34646409912214893166391297 25984807434161169874793473)
          ·
            refine ⟨19488605575620877406095105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25984807434161169874793473 19488605575620877406095105)
            ·
              refine ⟨14616454181715658054571329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19488605575620877406095105 14616454181715658054571329)
              ·
                refine ⟨10962340636286743540928497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14616454181715658054571329 10962340636286743540928497)
                ·
                  refine ⟨8221755477215057655696373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10962340636286743540928497 8221755477215057655696373)
                  ·
                    refine ⟨770789575988911655221535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8221755477215057655696373 770789575988911655221535)
                    ·
                      rfl

theorem cell23_4503322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_4503322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503322 prefixEnd_4503322 := by exact prefixLift 4503322
  have htrace : WordTrace (prefixWord ++ tailWord_4503322) baseStart_4503322 baseEnd_4503322 := by
    simpa [prefixWord, tailWord_4503322, baseEnd_4503322] using wordTrace_append hprefix tailTrace_4503322
  have hstable : (prefixWord ++ tailWord_4503322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503322).length < 2 ^ (prefixWord ++ tailWord_4503322).sum := by decide
  have hdescent : baseEnd_4503322 < baseStart_4503322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503332 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4503332 : Nat := 118140960795 + 4503332 * 2 ^ 59
def prefixEnd_4503332 : Nat := 4983230072969 + 3 ^ 40 * 4503332 * 2
def baseEnd_4503332 : Nat := 2312373862773279926539559

theorem tailTrace_4503332 : CollatzResearch.WordTrace tailWord_4503332 prefixEnd_4503332 2312373862773279926539559 := by
  unfold tailWord_4503332
  simp only [CollatzResearch.WordTrace]
  refine ⟨82125005860602373359452125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109500007814136497812602833 82125005860602373359452125)
  ·
    refine ⟨30796877197725890009794547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82125005860602373359452125 30796877197725890009794547)
    ·
      refine ⟨46195315796588835014691821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30796877197725890009794547 46195315796588835014691821)
      ·
        refine ⟨17323243423720813130509433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46195315796588835014691821 17323243423720813130509433)
        ·
          refine ⟨12992432567790609847882075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17323243423720813130509433 12992432567790609847882075)
          ·
            refine ⟨19488648851685914771823113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12992432567790609847882075 19488648851685914771823113)
            ·
              refine ⟨14616486638764436078867335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19488648851685914771823113 14616486638764436078867335)
              ·
                refine ⟨21924729958146654118301003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14616486638764436078867335 21924729958146654118301003)
                ·
                  refine ⟨32887094937219981177451505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21924729958146654118301003 32887094937219981177451505)
                  ·
                    refine ⟨24665321202914985883088629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32887094937219981177451505 24665321202914985883088629)
                    ·
                      refine ⟨2312373862773279926539559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24665321202914985883088629 2312373862773279926539559)
                      ·
                        rfl

theorem cell23_4503332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4503332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503332 prefixEnd_4503332 := by exact prefixLift 4503332
  have htrace : WordTrace (prefixWord ++ tailWord_4503332) baseStart_4503332 baseEnd_4503332 := by
    simpa [prefixWord, tailWord_4503332, baseEnd_4503332] using wordTrace_append hprefix tailTrace_4503332
  have hstable : (prefixWord ++ tailWord_4503332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503332).length < 2 ^ (prefixWord ++ tailWord_4503332).sum := by decide
  have hdescent : baseEnd_4503332 < baseStart_4503332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503352 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 5, 4]
def baseStart_4503352 : Nat := 118140960795 + 4503352 * 2 ^ 59
def prefixEnd_4503352 : Nat := 4983230072969 + 3 ^ 40 * 4503352 * 2
def baseEnd_4503352 : Nat := 770794710795456616096489

theorem tailTrace_4503352 : CollatzResearch.WordTrace tailWord_4503352 prefixEnd_4503352 770794710795456616096489 := by
  unfold tailWord_4503352
  simp only [CollatzResearch.WordTrace]
  refine ⟨82125370590566145067316155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109500494120754860089754873 82125370590566145067316155)
  ·
    refine ⟨123188055885849217600974233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82125370590566145067316155 123188055885849217600974233)
    ·
      refine ⟨92391041914386913200730675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123188055885849217600974233 92391041914386913200730675)
      ·
        refine ⟨138586562871580369801096013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92391041914386913200730675 138586562871580369801096013)
        ·
          refine ⟨51969961076842638675411005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138586562871580369801096013 51969961076842638675411005)
          ·
            refine ⟨19488735403815989503279127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51969961076842638675411005 19488735403815989503279127)
            ·
              refine ⟨29233103105723984254918691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19488735403815989503279127 29233103105723984254918691)
              ·
                refine ⟨43849654658585976382378037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29233103105723984254918691 43849654658585976382378037)
                ·
                  refine ⟨4110905124242435285847941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43849654658585976382378037 4110905124242435285847941)
                  ·
                    refine ⟨770794710795456616096489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4110905124242435285847941 770794710795456616096489)
                    ·
                      rfl

theorem cell23_4503352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_4503352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503352 prefixEnd_4503352 := by exact prefixLift 4503352
  have htrace : WordTrace (prefixWord ++ tailWord_4503352) baseStart_4503352 baseEnd_4503352 := by
    simpa [prefixWord, tailWord_4503352, baseEnd_4503352] using wordTrace_append hprefix tailTrace_4503352
  have hstable : (prefixWord ++ tailWord_4503352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503352).length < 2 ^ (prefixWord ++ tailWord_4503352).sum := by decide
  have hdescent : baseEnd_4503352 < baseStart_4503352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503365 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 8]
def baseStart_4503365 : Nat := 118140960795 + 4503365 * 2 ^ 59
def prefixEnd_4503365 : Nat := 4983230072969 + 3 ^ 40 * 4503365 * 2
def baseEnd_4503365 : Nat := 256932311959430921936323

theorem tailTrace_4503365 : CollatzResearch.WordTrace tailWord_4503365 prefixEnd_4503365 256932311959430921936323 := by
  unfold tailWord_4503365
  simp only [CollatzResearch.WordTrace]
  refine ⟨164251215330085193354855549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109500810220056795569903699 164251215330085193354855549)
  ·
    refine ⟨61594205748781947508070831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164251215330085193354855549 61594205748781947508070831)
    ·
      refine ⟨92391308623172921262106247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61594205748781947508070831 92391308623172921262106247)
      ·
        refine ⟨138586962934759381893159371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92391308623172921262106247 138586962934759381893159371)
        ·
          refine ⟨207880444402139072839739057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138586962934759381893159371 207880444402139072839739057)
          ·
            refine ⟨155910333301604304629804293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207880444402139072839739057 155910333301604304629804293)
            ·
              refine ⟨29233187494050807118088305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155910333301604304629804293 29233187494050807118088305)
              ·
                refine ⟨21924890620538105338566229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29233187494050807118088305 21924890620538105338566229)
                ·
                  refine ⟨256932311959430921936323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21924890620538105338566229 256932311959430921936323)
                  ·
                    rfl

theorem cell23_4503365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_4503365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503365 prefixEnd_4503365 := by exact prefixLift 4503365
  have htrace : WordTrace (prefixWord ++ tailWord_4503365) baseStart_4503365 baseEnd_4503365 := by
    simpa [prefixWord, tailWord_4503365, baseEnd_4503365] using wordTrace_append hprefix tailTrace_4503365
  have hstable : (prefixWord ++ tailWord_4503365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503365).length < 2 ^ (prefixWord ++ tailWord_4503365).sum := by decide
  have hdescent : baseEnd_4503365 < baseStart_4503365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503385 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_4503385 : Nat := 118140960795 + 4503385 * 2 ^ 59
def prefixEnd_4503385 : Nat := 4983230072969 + 3 ^ 40 * 4503385 * 2
def baseEnd_4503385 : Nat := 2312401077247968219176815

theorem tailTrace_4503385 : CollatzResearch.WordTrace tailWord_4503385 prefixEnd_4503385 2312401077247968219176815 := by
  unfold tailWord_4503385
  simp only [CollatzResearch.WordTrace]
  refine ⟨164251944790012736770583609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109501296526675157847055739 164251944790012736770583609)
  ·
    refine ⟨123188958592509552577937707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164251944790012736770583609 123188958592509552577937707)
    ·
      refine ⟨184783437888764328866906561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123188958592509552577937707 184783437888764328866906561)
      ·
        refine ⟨138587578416573246650179921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184783437888764328866906561 138587578416573246650179921)
        ·
          refine ⟨103940683812429934987634941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138587578416573246650179921 103940683812429934987634941)
          ·
            refine ⟨38977756429661225620363103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103940683812429934987634941 38977756429661225620363103)
            ·
              refine ⟨58466634644491838430544655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38977756429661225620363103 58466634644491838430544655)
              ·
                refine ⟨87699951966737757645816983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58466634644491838430544655 87699951966737757645816983)
                ·
                  refine ⟨131549927950106636468725475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87699951966737757645816983 131549927950106636468725475)
                  ·
                    refine ⟨197324891925159954703088213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 131549927950106636468725475 197324891925159954703088213)
                    ·
                      refine ⟨2312401077247968219176815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 197324891925159954703088213 2312401077247968219176815)
                      ·
                        rfl

theorem cell23_4503385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_4503385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503385 prefixEnd_4503385 := by exact prefixLift 4503385
  have htrace : WordTrace (prefixWord ++ tailWord_4503385) baseStart_4503385 baseEnd_4503385 := by
    simpa [prefixWord, tailWord_4503385, baseEnd_4503385] using wordTrace_append hprefix tailTrace_4503385
  have hstable : (prefixWord ++ tailWord_4503385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503385).length < 2 ^ (prefixWord ++ tailWord_4503385).sum := by decide
  have hdescent : baseEnd_4503385 < baseStart_4503385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503399 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 6]
def baseStart_4503399 : Nat := 118140960795 + 4503399 * 2 ^ 59
def prefixEnd_4503399 : Nat := 4983230072969 + 3 ^ 40 * 4503399 * 2
def baseEnd_4503399 : Nat := 256934251775236796044639

theorem tailTrace_4503399 : CollatzResearch.WordTrace tailWord_4503399 prefixEnd_4503399 256934251775236796044639 := by
  unfold tailWord_4503399
  simp only [CollatzResearch.WordTrace]
  refine ⟨164252455411962017161593251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109501636941308011441062167 164252455411962017161593251)
  ·
    refine ⟨246378683117943025742389877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164252455411962017161593251 246378683117943025742389877)
    ·
      refine ⟨23098001542307158663349051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 246378683117943025742389877 23098001542307158663349051)
      ·
        refine ⟨34647002313460737995023577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23098001542307158663349051 34647002313460737995023577)
        ·
          refine ⟨25985251735095553496267683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34647002313460737995023577 25985251735095553496267683)
          ·
            refine ⟨38977877602643330244401525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25985251735095553496267683 38977877602643330244401525)
            ·
              refine ⟨3654176025247812210412643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38977877602643330244401525 3654176025247812210412643)
              ·
                refine ⟨5481264037871718315618965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654176025247812210412643 5481264037871718315618965)
                ·
                  refine ⟨256934251775236796044639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5481264037871718315618965 256934251775236796044639)
                  ·
                    rfl

theorem cell23_4503399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 6].length) (baseStart_4503399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503399 prefixEnd_4503399 := by exact prefixLift 4503399
  have htrace : WordTrace (prefixWord ++ tailWord_4503399) baseStart_4503399 baseEnd_4503399 := by
    simpa [prefixWord, tailWord_4503399, baseEnd_4503399] using wordTrace_append hprefix tailTrace_4503399
  have hstable : (prefixWord ++ tailWord_4503399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503399).length < 2 ^ (prefixWord ++ tailWord_4503399).sum := by decide
  have hdescent : baseEnd_4503399 < baseStart_4503399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503409 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_4503409 : Nat := 118140960795 + 4503409 * 2 ^ 59
def prefixEnd_4503409 : Nat := 4983230072969 + 3 ^ 40 * 4503409 * 2
def baseEnd_4503409 : Nat := 2312413400783676125276705

theorem tailTrace_4503409 : CollatzResearch.WordTrace tailWord_4503409 prefixEnd_4503409 2312413400783676125276705 := by
  unfold tailWord_4503409
  simp only [CollatzResearch.WordTrace]
  refine ⟨164252820141925788869457281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109501880094617192579638187 164252820141925788869457281)
  ·
    refine ⟨123189615106444341652092961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164252820141925788869457281 123189615106444341652092961)
    ·
      refine ⟨92392211329833256239069721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123189615106444341652092961 92392211329833256239069721)
      ·
        refine ⟨69294158497374942179302291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92392211329833256239069721 69294158497374942179302291)
        ·
          refine ⟨103941237746062413268953437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69294158497374942179302291 103941237746062413268953437)
          ·
            refine ⟨38977964154773404975857539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103941237746062413268953437 38977964154773404975857539)
            ·
              refine ⟨58466946232160107463786309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38977964154773404975857539 58466946232160107463786309)
              ·
                refine ⟨10962552418530020149459933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58466946232160107463786309 10962552418530020149459933)
                ·
                  refine ⟨4110957156948757556047475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10962552418530020149459933 4110957156948757556047475)
                  ·
                    refine ⟨6166435735423136334071213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4110957156948757556047475 6166435735423136334071213)
                    ·
                      refine ⟨2312413400783676125276705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6166435735423136334071213 2312413400783676125276705)
                      ·
                        rfl

theorem cell23_4503409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_4503409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503409 prefixEnd_4503409 := by exact prefixLift 4503409
  have htrace : WordTrace (prefixWord ++ tailWord_4503409) baseStart_4503409 baseEnd_4503409 := by
    simpa [prefixWord, tailWord_4503409, baseEnd_4503409] using wordTrace_append hprefix tailTrace_4503409
  have hstable : (prefixWord ++ tailWord_4503409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503409).length < 2 ^ (prefixWord ++ tailWord_4503409).sum := by decide
  have hdescent : baseEnd_4503409 < baseStart_4503409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503419 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 2, 3, 2]
def baseStart_4503419 : Nat := 118140960795 + 4503419 * 2 ^ 59
def prefixEnd_4503419 : Nat := 4983230072969 + 3 ^ 40 * 4503419 * 2
def baseEnd_4503419 : Nat := 2312418535590221086151659

theorem tailTrace_4503419 : CollatzResearch.WordTrace tailWord_4503419 prefixEnd_4503419 2312418535590221086151659 := by
  unfold tailWord_4503419
  simp only [CollatzResearch.WordTrace]
  refine ⟨164253184871889560577321311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109502123247926373718214207 164253184871889560577321311)
  ·
    refine ⟨246379777307834340865981967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164253184871889560577321311 246379777307834340865981967)
    ·
      refine ⟨369569665961751511298972951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246379777307834340865981967 369569665961751511298972951)
      ·
        refine ⟨554354498942627266948459427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369569665961751511298972951 554354498942627266948459427)
        ·
          refine ⟨831531748413940900422689141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554354498942627266948459427 831531748413940900422689141)
          ·
            refine ⟨77956101413806959414627107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 831531748413940900422689141 77956101413806959414627107)
            ·
              refine ⟨116934152120710439121940661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77956101413806959414627107 116934152120710439121940661)
              ·
                refine ⟨10962576761316603667681937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116934152120710439121940661 10962576761316603667681937)
                ·
                  refine ⟨8221932570987452750761453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10962576761316603667681937 8221932570987452750761453)
                  ·
                    refine ⟨3083224714120294781535545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8221932570987452750761453 3083224714120294781535545)
                    ·
                      refine ⟨2312418535590221086151659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083224714120294781535545 2312418535590221086151659)
                      ·
                        rfl

theorem cell23_4503419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 3, 2].length) (baseStart_4503419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503419 prefixEnd_4503419 := by exact prefixLift 4503419
  have htrace : WordTrace (prefixWord ++ tailWord_4503419) baseStart_4503419 baseEnd_4503419 := by
    simpa [prefixWord, tailWord_4503419, baseEnd_4503419] using wordTrace_append hprefix tailTrace_4503419
  have hstable : (prefixWord ++ tailWord_4503419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503419).length < 2 ^ (prefixWord ++ tailWord_4503419).sum := by decide
  have hdescent : baseEnd_4503419 < baseStart_4503419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503486 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_4503486 : Nat := 118140960795 + 4503486 * 2 ^ 59
def prefixEnd_4503486 : Nat := 4983230072969 + 3 ^ 40 * 4503486 * 2
def baseEnd_4503486 : Nat := 2312452938794072324013851

theorem tailTrace_4503486 : CollatzResearch.WordTrace tailWord_4503486 prefixEnd_4503486 2312452938794072324013851 := by
  unfold tailWord_4503486
  simp only [CollatzResearch.WordTrace]
  refine ⟨20531953570330853877501289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109503752375097887346673541 20531953570330853877501289)
  ·
    refine ⟨15398965177748140408125967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20531953570330853877501289 15398965177748140408125967)
    ·
      refine ⟨23098447766622210612188951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15398965177748140408125967 23098447766622210612188951)
      ·
        refine ⟨34647671649933315918283427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23098447766622210612188951 34647671649933315918283427)
        ·
          refine ⟨51971507474899973877425141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34647671649933315918283427 51971507474899973877425141)
          ·
            refine ⟨4872328825771872551008607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51971507474899973877425141 4872328825771872551008607)
            ·
              refine ⟨7308493238657808826512911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4872328825771872551008607 7308493238657808826512911)
              ·
                refine ⟨10962739857986713239769367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7308493238657808826512911 10962739857986713239769367)
                ·
                  refine ⟨16444109786980069859654051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10962739857986713239769367 16444109786980069859654051)
                  ·
                    refine ⟨24666164680470104789481077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16444109786980069859654051 24666164680470104789481077)
                    ·
                      refine ⟨2312452938794072324013851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24666164680470104789481077 2312452938794072324013851)
                      ·
                        rfl

theorem cell23_4503486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_4503486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503486 prefixEnd_4503486 := by exact prefixLift 4503486
  have htrace : WordTrace (prefixWord ++ tailWord_4503486) baseStart_4503486 baseEnd_4503486 := by
    simpa [prefixWord, tailWord_4503486, baseEnd_4503486] using wordTrace_append hprefix tailTrace_4503486
  have hstable : (prefixWord ++ tailWord_4503486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503486).length < 2 ^ (prefixWord ++ tailWord_4503486).sum := by decide
  have hdescent : baseEnd_4503486 < baseStart_4503486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503500 : List Nat := [2, 2, 1, 4, 1, 3, 1, 4, 1, 2, 2]
def baseStart_4503500 : Nat := 118140960795 + 4503500 * 2 ^ 59
def prefixEnd_4503500 : Nat := 4983230072969 + 3 ^ 40 * 4503500 * 2
def baseEnd_4503500 : Nat := 2312460127523235269238787

theorem tailTrace_4503500 : CollatzResearch.WordTrace tailWord_4503500 prefixEnd_4503500 2312460127523235269238787 := by
  unfold tailWord_4503500
  simp only [CollatzResearch.WordTrace]
  refine ⟨82128069592298055705509977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109504092789730740940679969 82128069592298055705509977)
  ·
    refine ⟨61596052194223541779132483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82128069592298055705509977 61596052194223541779132483)
    ·
      refine ⟨92394078291335312668698725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61596052194223541779132483 92394078291335312668698725)
      ·
        refine ⟨17323889679625371125381011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92394078291335312668698725 17323889679625371125381011)
        ·
          refine ⟨25985834519438056688071517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17323889679625371125381011 25985834519438056688071517)
          ·
            refine ⟨9744687944789271258026819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25985834519438056688071517 9744687944789271258026819)
            ·
              refine ⟨14617031917183906887040229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9744687944789271258026819 14617031917183906887040229)
              ·
                refine ⟨2740693484471982541320043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14617031917183906887040229 2740693484471982541320043)
                ·
                  refine ⟨4111040226707973811980065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740693484471982541320043 4111040226707973811980065)
                  ·
                    refine ⟨3083280170030980358985049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111040226707973811980065 3083280170030980358985049)
                    ·
                      refine ⟨2312460127523235269238787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083280170030980358985049 2312460127523235269238787)
                      ·
                        rfl

theorem cell23_4503500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_4503500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503500 prefixEnd_4503500 := by exact prefixLift 4503500
  have htrace : WordTrace (prefixWord ++ tailWord_4503500) baseStart_4503500 baseEnd_4503500 := by
    simpa [prefixWord, tailWord_4503500, baseEnd_4503500] using wordTrace_append hprefix tailTrace_4503500
  have hstable : (prefixWord ++ tailWord_4503500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503500).length < 2 ^ (prefixWord ++ tailWord_4503500).sum := by decide
  have hdescent : baseEnd_4503500 < baseStart_4503500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503502 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_4503502 : Nat := 118140960795 + 4503502 * 2 ^ 59
def prefixEnd_4503502 : Nat := 4983230072969 + 3 ^ 40 * 4503502 * 2
def baseEnd_4503502 : Nat := 770820384828181420471259

theorem tailTrace_4503502 : CollatzResearch.WordTrace tailWord_4503502 prefixEnd_4503502 770820384828181420471259 := by
  unfold tailWord_4503502
  simp only [CollatzResearch.WordTrace]
  refine ⟨20532026516323608219074095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109504141420392577168395173 20532026516323608219074095)
  ·
    refine ⟨30798039774485412328611143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20532026516323608219074095 30798039774485412328611143)
    ·
      refine ⟨46197059661728118492916715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30798039774485412328611143 46197059661728118492916715)
      ·
        refine ⟨69295589492592177739375073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46197059661728118492916715 69295589492592177739375073)
        ·
          refine ⟨51971692119444133304531305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69295589492592177739375073 51971692119444133304531305)
          ·
            refine ⟨38978769089583099978398479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51971692119444133304531305 38978769089583099978398479)
            ·
              refine ⟨58468153634374649967597719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38978769089583099978398479 58468153634374649967597719)
              ·
                refine ⟨87702230451561974951396579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58468153634374649967597719 87702230451561974951396579)
                ·
                  refine ⟨131553345677342962427094869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87702230451561974951396579 131553345677342962427094869)
                  ·
                    refine ⟨770820384828181420471259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 131553345677342962427094869 770820384828181420471259)
                    ·
                      rfl

theorem cell23_4503502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_4503502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503502 prefixEnd_4503502 := by exact prefixLift 4503502
  have htrace : WordTrace (prefixWord ++ tailWord_4503502) baseStart_4503502 baseEnd_4503502 := by
    simpa [prefixWord, tailWord_4503502, baseEnd_4503502] using wordTrace_append hprefix tailTrace_4503502
  have hstable : (prefixWord ++ tailWord_4503502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503502).length < 2 ^ (prefixWord ++ tailWord_4503502).sum := by decide
  have hdescent : baseEnd_4503502 < baseStart_4503502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503506 : List Nat := [3, 2, 2, 3, 2, 2, 1, 8]
def baseStart_4503506 : Nat := 118140960795 + 4503506 * 2 ^ 59
def prefixEnd_4503506 : Nat := 4983230072969 + 3 ^ 40 * 4503506 * 2
def baseEnd_4503506 : Nat := 85646785496561564657917

theorem tailTrace_4503506 : CollatzResearch.WordTrace tailWord_4503506 prefixEnd_4503506 85646785496561564657917 := by
  unfold tailWord_4503506
  simp only [CollatzResearch.WordTrace]
  refine ⟨41064089505643593608934593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109504238681716249623825581 41064089505643593608934593)
  ·
    refine ⟨30798067129232695206700945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41064089505643593608934593 30798067129232695206700945)
    ·
      refine ⟨23098550346924521405025709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30798067129232695206700945 23098550346924521405025709)
      ·
        refine ⟨8661956380096695526884641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23098550346924521405025709 8661956380096695526884641)
        ·
          refine ⟨6496467285072521645163481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8661956380096695526884641 6496467285072521645163481)
          ·
            refine ⟨4872350463804391233872611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6496467285072521645163481 4872350463804391233872611)
            ·
              refine ⟨7308525695706586850808917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4872350463804391233872611 7308525695706586850808917)
              ·
                refine ⟨85646785496561564657917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7308525695706586850808917 85646785496561564657917)
                ·
                  rfl

theorem cell23_4503506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 8].length) (baseStart_4503506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503506 prefixEnd_4503506 := by exact prefixLift 4503506
  have htrace : WordTrace (prefixWord ++ tailWord_4503506) baseStart_4503506 baseEnd_4503506 := by
    simpa [prefixWord, tailWord_4503506, baseEnd_4503506] using wordTrace_append hprefix tailTrace_4503506
  have hstable : (prefixWord ++ tailWord_4503506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503506).length < 2 ^ (prefixWord ++ tailWord_4503506).sum := by decide
  have hdescent : baseEnd_4503506 < baseStart_4503506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503550 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4503550 : Nat := 118140960795 + 4503550 * 2 ^ 59
def prefixEnd_4503550 : Nat := 4983230072969 + 3 ^ 40 * 4503550 * 2
def baseEnd_4503550 : Nat := 2312485801555960073613557

theorem tailTrace_4503550 : CollatzResearch.WordTrace tailWord_4503550 prefixEnd_4503550 2312485801555960073613557 := by
  unfold tailWord_4503550
  simp only [CollatzResearch.WordTrace]
  refine ⟨20532245354301871243792513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109505308556276646633560069 20532245354301871243792513)
  ·
    refine ⟨15399184015726403432844385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20532245354301871243792513 15399184015726403432844385)
    ·
      refine ⟨11549388011794802574633289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15399184015726403432844385 11549388011794802574633289)
      ·
        refine ⟨8662041008846101930974967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11549388011794802574633289 8662041008846101930974967)
        ·
          refine ⟨12993061513269152896462451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8662041008846101930974967 12993061513269152896462451)
          ·
            refine ⟨19489592269903729344693677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12993061513269152896462451 19489592269903729344693677)
            ·
              refine ⟨7308597101213898504260129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19489592269903729344693677 7308597101213898504260129)
              ·
                refine ⟨5481447825910423878195097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7308597101213898504260129 5481447825910423878195097)
                ·
                  refine ⟨4111085869432817908646323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5481447825910423878195097 4111085869432817908646323)
                  ·
                    refine ⟨6166628804149226862969485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4111085869432817908646323 6166628804149226862969485)
                    ·
                      refine ⟨2312485801555960073613557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6166628804149226862969485 2312485801555960073613557)
                      ·
                        rfl

theorem cell23_4503550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4503550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503550 prefixEnd_4503550 := by exact prefixLift 4503550
  have htrace : WordTrace (prefixWord ++ tailWord_4503550) baseStart_4503550 baseEnd_4503550 := by
    simpa [prefixWord, tailWord_4503550, baseEnd_4503550] using wordTrace_append hprefix tailTrace_4503550
  have hstable : (prefixWord ++ tailWord_4503550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503550).length < 2 ^ (prefixWord ++ tailWord_4503550).sum := by decide
  have hdescent : baseEnd_4503550 < baseStart_4503550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503613 : List Nat := [1, 4, 1, 3, 1, 1, 5, 2, 5]
def baseStart_4503613 : Nat := 118140960795 + 4503613 * 2 ^ 59
def prefixEnd_4503613 : Nat := 4983230072969 + 3 ^ 40 * 4503613 * 2
def baseEnd_4503613 : Nat := 256946461204132591902863

theorem tailTrace_4503613 : CollatzResearch.WordTrace tailWord_4503613 prefixEnd_4503613 256946461204132591902863 := by
  unfold tailWord_4503613
  simp only [CollatzResearch.WordTrace]
  refine ⟨164260260633186731709883493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109506840422124487806588995 164260260633186731709883493)
  ·
    refine ⟨30798798868722512195603155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164260260633186731709883493 30798798868722512195603155)
    ·
      refine ⟨46198198303083768293404733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30798798868722512195603155 46198198303083768293404733)
      ·
        refine ⟨17324324363656413110026775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46198198303083768293404733 17324324363656413110026775)
        ·
          refine ⟨25986486545484619665040163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17324324363656413110026775 25986486545484619665040163)
          ·
            refine ⟨38979729818226929497560245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25986486545484619665040163 38979729818226929497560245)
            ·
              refine ⟨3654349670458774640396273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38979729818226929497560245 3654349670458774640396273)
              ·
                refine ⟨2740762252844080980297205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3654349670458774640396273 2740762252844080980297205)
                ·
                  refine ⟨256946461204132591902863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2740762252844080980297205 256946461204132591902863)
                  ·
                    rfl

theorem cell23_4503613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_4503613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503613 prefixEnd_4503613 := by exact prefixLift 4503613
  have htrace : WordTrace (prefixWord ++ tailWord_4503613) baseStart_4503613 baseEnd_4503613 := by
    simpa [prefixWord, tailWord_4503613, baseEnd_4503613] using wordTrace_append hprefix tailTrace_4503613
  have hstable : (prefixWord ++ tailWord_4503613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503613).length < 2 ^ (prefixWord ++ tailWord_4503613).sum := by decide
  have hdescent : baseEnd_4503613 < baseStart_4503613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503700 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4503700 : Nat := 118140960795 + 4503700 * 2 ^ 59
def prefixEnd_4503700 : Nat := 4983230072969 + 3 ^ 40 * 4503700 * 2
def baseEnd_4503700 : Nat := 2312562823654134486737867

theorem tailTrace_4503700 : CollatzResearch.WordTrace tailWord_4503700 prefixEnd_4503700 2312562823654134486737867 := by
  unfold tailWord_4503700
  simp only [CollatzResearch.WordTrace]
  refine ⟨82131716891935772784150277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109508955855914363712200369 82131716891935772784150277)
  ·
    refine ⟨15399696917237957397028177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82131716891935772784150277 15399696917237957397028177)
    ·
      refine ⟨11549772687928468047771133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15399696917237957397028177 11549772687928468047771133)
      ·
        refine ⟨4331164757973175517914175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11549772687928468047771133 4331164757973175517914175)
        ·
          refine ⟨6496747136959763276871263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331164757973175517914175 6496747136959763276871263)
          ·
            refine ⟨9745120705439644915306895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496747136959763276871263 9745120705439644915306895)
            ·
              refine ⟨14617681058159467372960343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9745120705439644915306895 14617681058159467372960343)
              ·
                refine ⟨21926521587239201059440515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14617681058159467372960343 21926521587239201059440515)
                ·
                  refine ⟨32889782380858801589160773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21926521587239201059440515 32889782380858801589160773)
                  ·
                    refine ⟨6166834196411025297967645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32889782380858801589160773 6166834196411025297967645)
                    ·
                      refine ⟨2312562823654134486737867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6166834196411025297967645 2312562823654134486737867)
                      ·
                        rfl

theorem cell23_4503700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4503700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503700 prefixEnd_4503700 := by exact prefixLift 4503700
  have htrace : WordTrace (prefixWord ++ tailWord_4503700) baseStart_4503700 baseEnd_4503700 := by
    simpa [prefixWord, tailWord_4503700, baseEnd_4503700] using wordTrace_append hprefix tailTrace_4503700
  have hstable : (prefixWord ++ tailWord_4503700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503700).length < 2 ^ (prefixWord ++ tailWord_4503700).sum := by decide
  have hdescent : baseEnd_4503700 < baseStart_4503700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503730 : List Nat := [3, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_4503730 : Nat := 118140960795 + 4503730 * 2 ^ 59
def prefixEnd_4503730 : Nat := 4983230072969 + 3 ^ 40 * 4503730 * 2
def baseEnd_4503730 : Nat := 2312578228073769369362729

theorem tailTrace_4503730 : CollatzResearch.WordTrace tailWord_4503730 prefixEnd_4503730 2312578228073769369362729 := by
  unfold tailWord_4503730
  simp only [CollatzResearch.WordTrace]
  refine ⟨41066131993440715172973161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109509685315841907127928429 41066131993440715172973161)
  ·
    refine ⟨30799598995080536379729871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41066131993440715172973161 30799598995080536379729871)
    ·
      refine ⟨46199398492620804569594807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30799598995080536379729871 46199398492620804569594807)
      ·
        refine ⟨69299097738931206854392211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46199398492620804569594807 69299097738931206854392211)
        ·
          refine ⟨103948646608396810281588317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69299097738931206854392211 103948646608396810281588317)
          ·
            refine ⟨38980742478148803855595619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103948646608396810281588317 38980742478148803855595619)
            ·
              refine ⟨58471113717223205783393429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38980742478148803855595619 58471113717223205783393429)
              ·
                refine ⟨2740833455494837771096567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58471113717223205783393429 2740833455494837771096567)
                ·
                  refine ⟨4111250183242256656644851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740833455494837771096567 4111250183242256656644851)
                  ·
                    refine ⟨6166875274863384984967277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4111250183242256656644851 6166875274863384984967277)
                    ·
                      refine ⟨2312578228073769369362729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6166875274863384984967277 2312578228073769369362729)
                      ·
                        rfl

theorem cell23_4503730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_4503730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503730 prefixEnd_4503730 := by exact prefixLift 4503730
  have htrace : WordTrace (prefixWord ++ tailWord_4503730) baseStart_4503730 baseEnd_4503730 := by
    simpa [prefixWord, tailWord_4503730, baseEnd_4503730] using wordTrace_append hprefix tailTrace_4503730
  have hstable : (prefixWord ++ tailWord_4503730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503730).length < 2 ^ (prefixWord ++ tailWord_4503730).sum := by decide
  have hdescent : baseEnd_4503730 < baseStart_4503730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503753 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 5, 2, 2]
def baseStart_4503753 : Nat := 118140960795 + 4503753 * 2 ^ 59
def prefixEnd_4503753 : Nat := 4983230072969 + 3 ^ 40 * 4503753 * 2
def baseEnd_4503753 : Nat := 2312590038128822779375123

theorem tailTrace_4503753 : CollatzResearch.WordTrace tailWord_4503753 prefixEnd_4503753 2312590038128822779375123 := by
  unfold tailWord_4503753
  simp only [CollatzResearch.WordTrace]
  refine ⟨164265366852679535619979913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109510244568453023746653275 164265366852679535619979913)
  ·
    refine ⟨123199025139509651714984935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164265366852679535619979913 123199025139509651714984935)
    ·
      refine ⟨184798537709264477572477403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123199025139509651714984935 184798537709264477572477403)
      ·
        refine ⟨277197806563896716358716105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184798537709264477572477403 277197806563896716358716105)
        ·
          refine ⟨207898354922922537269037079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277197806563896716358716105 207898354922922537269037079)
          ·
            refine ⟨311847532384383805903555619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207898354922922537269037079 311847532384383805903555619)
            ·
              refine ⟨467771298576575708855333429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311847532384383805903555619 467771298576575708855333429)
              ·
                refine ⟨43853559241553972705187509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 467771298576575708855333429 43853559241553972705187509)
                ·
                  refine ⟨4111271178895684941111329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43853559241553972705187509 4111271178895684941111329)
                  ·
                    refine ⟨3083453384171763705833497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111271178895684941111329 3083453384171763705833497)
                    ·
                      refine ⟨2312590038128822779375123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083453384171763705833497 2312590038128822779375123)
                      ·
                        rfl

theorem cell23_4503753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 2, 2].length) (baseStart_4503753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503753 prefixEnd_4503753 := by exact prefixLift 4503753
  have htrace : WordTrace (prefixWord ++ tailWord_4503753) baseStart_4503753 baseEnd_4503753 := by
    simpa [prefixWord, tailWord_4503753, baseEnd_4503753] using wordTrace_append hprefix tailTrace_4503753
  have hstable : (prefixWord ++ tailWord_4503753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503753).length < 2 ^ (prefixWord ++ tailWord_4503753).sum := by decide
  have hdescent : baseEnd_4503753 < baseStart_4503753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503759 : List Nat := [1, 1, 2, 1, 1, 3, 5, 9]
def baseStart_4503759 : Nat := 118140960795 + 4503759 * 2 ^ 59
def prefixEnd_4503759 : Nat := 4983230072969 + 3 ^ 40 * 4503759 * 2
def baseEnd_4503759 : Nat := 85651597000472213181485

theorem tailTrace_4503759 : CollatzResearch.WordTrace tailWord_4503759 prefixEnd_4503759 85651597000472213181485 := by
  unfold tailWord_4503759
  simp only [CollatzResearch.WordTrace]
  refine ⟨164265585690657798644698331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109510390460438532429798887 164265585690657798644698331)
  ·
    refine ⟨246398378535986697967047497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164265585690657798644698331 246398378535986697967047497)
    ·
      refine ⟨184798783901990023475285623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246398378535986697967047497 184798783901990023475285623)
      ·
        refine ⟨277198175852985035212928435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184798783901990023475285623 277198175852985035212928435)
        ·
          refine ⟨415797263779477552819392653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277198175852985035212928435 415797263779477552819392653)
          ·
            refine ⟨155923973917304082307272245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 415797263779477552819392653 155923973917304082307272245)
            ·
              refine ⟨14617872554747257716306773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155923973917304082307272245 14617872554747257716306773)
              ·
                refine ⟨85651597000472213181485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14617872554747257716306773 85651597000472213181485)
                ·
                  rfl

theorem cell23_4503759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 9].length) (baseStart_4503759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503759 prefixEnd_4503759 := by exact prefixLift 4503759
  have htrace : WordTrace (prefixWord ++ tailWord_4503759) baseStart_4503759 baseEnd_4503759 := by
    simpa [prefixWord, tailWord_4503759, baseEnd_4503759] using wordTrace_append hprefix tailTrace_4503759
  have hstable : (prefixWord ++ tailWord_4503759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503759).length < 2 ^ (prefixWord ++ tailWord_4503759).sum := by decide
  have hdescent : baseEnd_4503759 < baseStart_4503759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503773 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4503773 : Nat := 118140960795 + 4503773 * 2 ^ 59
def prefixEnd_4503773 : Nat := 4983230072969 + 3 ^ 40 * 4503773 * 2
def baseEnd_4503773 : Nat := 2312600307741912701125031

theorem tailTrace_4503773 : CollatzResearch.WordTrace tailWord_4503773 prefixEnd_4503773 2312600307741912701125031 := by
  unfold tailWord_4503773
  simp only [CollatzResearch.WordTrace]
  refine ⟨164266096312607079035707973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109510730875071386023805315 164266096312607079035707973)
  ·
    refine ⟨30799893058613827319195245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164266096312607079035707973 30799893058613827319195245)
    ·
      refine ⟨11549959896980185244698217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30799893058613827319195245 11549959896980185244698217)
      ·
        refine ⟨8662469922735138933523663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11549959896980185244698217 8662469922735138933523663)
        ·
          refine ⟨12993704884102708400285495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8662469922735138933523663 12993704884102708400285495)
          ·
            refine ⟨19490557326154062600428243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12993704884102708400285495 19490557326154062600428243)
            ·
              refine ⟨29235835989231093900642365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19490557326154062600428243 29235835989231093900642365)
              ·
                refine ⟨10963438495961660212740887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29235835989231093900642365 10963438495961660212740887)
                ·
                  refine ⟨16445157743942490319111331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10963438495961660212740887 16445157743942490319111331)
                  ·
                    refine ⟨24667736615913735478666997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16445157743942490319111331 24667736615913735478666997)
                    ·
                      refine ⟨2312600307741912701125031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24667736615913735478666997 2312600307741912701125031)
                      ·
                        rfl

theorem cell23_4503773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4503773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503773 prefixEnd_4503773 := by exact prefixLift 4503773
  have htrace : WordTrace (prefixWord ++ tailWord_4503773) baseStart_4503773 baseEnd_4503773 := by
    simpa [prefixWord, tailWord_4503773, baseEnd_4503773] using wordTrace_append hprefix tailTrace_4503773
  have hstable : (prefixWord ++ tailWord_4503773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503773).length < 2 ^ (prefixWord ++ tailWord_4503773).sum := by decide
  have hdescent : baseEnd_4503773 < baseStart_4503773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503836 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_4503836 : Nat := 118140960795 + 4503836 * 2 ^ 59
def prefixEnd_4503836 : Nat := 4983230072969 + 3 ^ 40 * 4503836 * 2
def baseEnd_4503836 : Nat := 770877552341048651545747

theorem tailTrace_4503836 : CollatzResearch.WordTrace tailWord_4503836 prefixEnd_4503836 770877552341048651545747 := by
  unfold tailWord_4503836
  simp only [CollatzResearch.WordTrace]
  refine ⟨82134197055689420397625681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109512262740919227196834241 82134197055689420397625681)
  ·
    refine ⟨61600647791767065298219261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82134197055689420397625681 61600647791767065298219261)
    ·
      refine ⟨23100242921912649486832223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61600647791767065298219261 23100242921912649486832223)
      ·
        refine ⟨34650364382868974230248335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23100242921912649486832223 34650364382868974230248335)
        ·
          refine ⟨51975546574303461345372503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34650364382868974230248335 51975546574303461345372503)
          ·
            refine ⟨77963319861455192018058755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51975546574303461345372503 77963319861455192018058755)
            ·
              refine ⟨116944979792182788027088133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77963319861455192018058755 116944979792182788027088133)
              ·
                refine ⟨21927183711034272755079025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116944979792182788027088133 21927183711034272755079025)
                ·
                  refine ⟨16445387783275704566309269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21927183711034272755079025 16445387783275704566309269)
                  ·
                    refine ⟨770877552341048651545747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16445387783275704566309269 770877552341048651545747)
                    ·
                      rfl

theorem cell23_4503836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_4503836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503836 prefixEnd_4503836 := by exact prefixLift 4503836
  have htrace : WordTrace (prefixWord ++ tailWord_4503836) baseStart_4503836 baseEnd_4503836 := by
    simpa [prefixWord, tailWord_4503836, baseEnd_4503836] using wordTrace_append hprefix tailTrace_4503836
  have hstable : (prefixWord ++ tailWord_4503836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503836).length < 2 ^ (prefixWord ++ tailWord_4503836).sum := by decide
  have hdescent : baseEnd_4503836 < baseStart_4503836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503838 : List Nat := [4, 3, 2, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4503838 : Nat := 118140960795 + 4503838 * 2 ^ 59
def prefixEnd_4503838 : Nat := 4983230072969 + 3 ^ 40 * 4503838 * 2
def baseEnd_4503838 : Nat := 2312633683984454946812233

theorem tailTrace_4503838 : CollatzResearch.WordTrace tailWord_4503838 prefixEnd_4503838 2312633683984454946812233 := by
  unfold tailWord_4503838
  simp only [CollatzResearch.WordTrace]
  refine ⟨20533558382171449392103021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109512311371581063424549445 20533558382171449392103021)
  ·
    refine ⟨7700084393314293522038633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20533558382171449392103021 7700084393314293522038633)
    ·
      refine ⟨5775063294985720141528975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7700084393314293522038633 5775063294985720141528975)
      ·
        refine ⟨8662594942478580212293463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5775063294985720141528975 8662594942478580212293463)
        ·
          refine ⟨12993892413717870318440195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8662594942478580212293463 12993892413717870318440195)
          ·
            refine ⟨19490838620576805477660293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12993892413717870318440195 19490838620576805477660293)
            ·
              refine ⟨3654532241358151027061305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19490838620576805477660293 3654532241358151027061305)
              ·
                refine ⟨2740899181018613270295979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3654532241358151027061305 2740899181018613270295979)
                ·
                  refine ⟨4111348771527919905443969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2740899181018613270295979 4111348771527919905443969)
                  ·
                    refine ⟨3083511578645939929082977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111348771527919905443969 3083511578645939929082977)
                    ·
                      refine ⟨2312633683984454946812233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083511578645939929082977 2312633683984454946812233)
                      ·
                        rfl

theorem cell23_4503838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4503838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503838 prefixEnd_4503838 := by exact prefixLift 4503838
  have htrace : WordTrace (prefixWord ++ tailWord_4503838) baseStart_4503838 baseEnd_4503838 := by
    simpa [prefixWord, tailWord_4503838, baseEnd_4503838] using wordTrace_append hprefix tailTrace_4503838
  have hstable : (prefixWord ++ tailWord_4503838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503838).length < 2 ^ (prefixWord ++ tailWord_4503838).sum := by decide
  have hdescent : baseEnd_4503838 < baseStart_4503838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503843 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 3, 4, 2]
def baseStart_4503843 : Nat := 118140960795 + 4503843 * 2 ^ 59
def prefixEnd_4503843 : Nat := 4983230072969 + 3 ^ 40 * 4503843 * 2
def baseEnd_4503843 : Nat := 2312636251387727427249709

theorem tailTrace_4503843 : CollatzResearch.WordTrace tailWord_4503843 prefixEnd_4503843 2312636251387727427249709 := by
  unfold tailWord_4503843
  simp only [CollatzResearch.WordTrace]
  refine ⟨164268649422353480990756183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109512432948235653993837455 164268649422353480990756183)
  ·
    refine ⟨246402974133530221486134275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164268649422353480990756183 246402974133530221486134275)
    ·
      refine ⟨369604461200295332229201413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246402974133530221486134275 369604461200295332229201413)
      ·
        refine ⟨69300836475055374792975265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 369604461200295332229201413 69300836475055374792975265)
        ·
          refine ⟨51975627356291531094731449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69300836475055374792975265 51975627356291531094731449)
          ·
            refine ⟨38981720517218648321048587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51975627356291531094731449 38981720517218648321048587)
            ·
              refine ⟨58472580775827972481572881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38981720517218648321048587 58472580775827972481572881)
              ·
                refine ⟨43854435581870979361179661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58472580775827972481572881 43854435581870979361179661)
                ·
                  refine ⟨16445413343201617260442373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43854435581870979361179661 16445413343201617260442373)
                  ·
                    refine ⟨3083515001850303236332945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16445413343201617260442373 3083515001850303236332945)
                    ·
                      refine ⟨2312636251387727427249709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083515001850303236332945 2312636251387727427249709)
                      ·
                        rfl

theorem cell23_4503843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_4503843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503843 prefixEnd_4503843 := by exact prefixLift 4503843
  have htrace : WordTrace (prefixWord ++ tailWord_4503843) baseStart_4503843 baseEnd_4503843 := by
    simpa [prefixWord, tailWord_4503843, baseEnd_4503843] using wordTrace_append hprefix tailTrace_4503843
  have hstable : (prefixWord ++ tailWord_4503843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503843).length < 2 ^ (prefixWord ++ tailWord_4503843).sum := by decide
  have hdescent : baseEnd_4503843 < baseStart_4503843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503866 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 9]
def baseStart_4503866 : Nat := 118140960795 + 4503866 * 2 ^ 59
def prefixEnd_4503866 : Nat := 4983230072969 + 3 ^ 40 * 4503866 * 2
def baseEnd_4503866 : Nat := 256960895715864537473567

theorem tailTrace_4503866 : CollatzResearch.WordTrace tailWord_4503866 prefixEnd_4503866 256960895715864537473567 := by
  unfold tailWord_4503866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41067372075317538979710863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109512992200846770612562301 41067372075317538979710863)
  ·
    refine ⟨61601058112976308469566295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41067372075317538979710863 61601058112976308469566295)
    ·
      refine ⟨92401587169464462704349443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61601058112976308469566295 92401587169464462704349443)
      ·
        refine ⟨138602380754196694056524165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92401587169464462704349443 138602380754196694056524165)
        ·
          refine ⟨25987946391411880135598281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138602380754196694056524165 25987946391411880135598281)
          ·
            refine ⟨19490959793558910101698711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25987946391411880135598281 19490959793558910101698711)
            ·
              refine ⟨29236439690338365152548067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19490959793558910101698711 29236439690338365152548067)
              ·
                refine ⟨43854659535507547728822101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29236439690338365152548067 43854659535507547728822101)
                ·
                  refine ⟨256960895715864537473567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43854659535507547728822101 256960895715864537473567)
                  ·
                    rfl

theorem cell23_4503866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_4503866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503866 prefixEnd_4503866 := by exact prefixLift 4503866
  have htrace : WordTrace (prefixWord ++ tailWord_4503866) baseStart_4503866 baseEnd_4503866 := by
    simpa [prefixWord, tailWord_4503866, baseEnd_4503866] using wordTrace_append hprefix tailTrace_4503866
  have hstable : (prefixWord ++ tailWord_4503866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503866).length < 2 ^ (prefixWord ++ tailWord_4503866).sum := by decide
  have hdescent : baseEnd_4503866 < baseStart_4503866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503903 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 7, 2]
def baseStart_4503903 : Nat := 118140960795 + 4503903 * 2 ^ 59
def prefixEnd_4503903 : Nat := 4983230072969 + 3 ^ 40 * 4503903 * 2
def baseEnd_4503903 : Nat := 2312667060226997192499433

theorem tailTrace_4503903 : CollatzResearch.WordTrace tailWord_4503903 prefixEnd_4503903 2312667060226997192499433 := by
  unfold tailWord_4503903
  simp only [CollatzResearch.WordTrace]
  refine ⟨164270837802136111237940363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109513891868090740825293575 164270837802136111237940363)
  ·
    refine ⟨246406256703204166856910545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164270837802136111237940363 246406256703204166856910545)
    ·
      refine ⟨184804692527403125142682909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246406256703204166856910545 184804692527403125142682909)
      ·
        refine ⟨69301759697776171928506091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184804692527403125142682909 69301759697776171928506091)
        ·
          refine ⟨103952639546664257892759137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69301759697776171928506091 103952639546664257892759137)
          ·
            refine ⟨77964479659998193419569353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103952639546664257892759137 77964479659998193419569353)
            ·
              refine ⟨58473359744998645064677015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77964479659998193419569353 58473359744998645064677015)
              ·
                refine ⟨87710039617497967597015523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58473359744998645064677015 87710039617497967597015523)
                ·
                  refine ⟨131565059426246951395523285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87710039617497967597015523 131565059426246951395523285)
                  ·
                    refine ⟨3083556080302662923332577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 131565059426246951395523285 3083556080302662923332577)
                    ·
                      refine ⟨2312667060226997192499433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083556080302662923332577 2312667060226997192499433)
                      ·
                        rfl

theorem cell23_4503903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_4503903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503903 prefixEnd_4503903 := by exact prefixLift 4503903
  have htrace : WordTrace (prefixWord ++ tailWord_4503903) baseStart_4503903 baseEnd_4503903 := by
    simpa [prefixWord, tailWord_4503903, baseEnd_4503903] using wordTrace_append hprefix tailTrace_4503903
  have hstable : (prefixWord ++ tailWord_4503903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503903).length < 2 ^ (prefixWord ++ tailWord_4503903).sum := by decide
  have hdescent : baseEnd_4503903 < baseStart_4503903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503933 : List Nat := [1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4503933 : Nat := 118140960795 + 4503933 * 2 ^ 59
def prefixEnd_4503933 : Nat := 4983230072969 + 3 ^ 40 * 4503933 * 2
def baseEnd_4503933 : Nat := 2312682464646632075124295

theorem tailTrace_4503933 : CollatzResearch.WordTrace tailWord_4503933 prefixEnd_4503933 2312682464646632075124295 := by
  unfold tailWord_4503933
  simp only [CollatzResearch.WordTrace]
  refine ⟨164271931992027426361532453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109514621328018284241021635 164271931992027426361532453)
  ·
    refine ⟨30800987248505142442787335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164271931992027426361532453 30800987248505142442787335)
    ·
      refine ⟨46201480872757713664181003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30800987248505142442787335 46201480872757713664181003)
      ·
        refine ⟨69302221309136570496271505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46201480872757713664181003 69302221309136570496271505)
        ·
          refine ⟨51976665981852427872203629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69302221309136570496271505 51976665981852427872203629)
          ·
            refine ⟨19491249743194660452076361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51976665981852427872203629 19491249743194660452076361)
            ·
              refine ⟨14618437307395995339057271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19491249743194660452076361 14618437307395995339057271)
              ·
                refine ⟨21927655961093993008585907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14618437307395995339057271 21927655961093993008585907)
                ·
                  refine ⟨32891483941640989512878861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21927655961093993008585907 32891483941640989512878861)
                  ·
                    refine ⟨12334306478115371067329573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32891483941640989512878861 12334306478115371067329573)
                    ·
                      refine ⟨2312682464646632075124295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12334306478115371067329573 2312682464646632075124295)
                      ·
                        rfl

theorem cell23_4503933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4503933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503933 prefixEnd_4503933 := by exact prefixLift 4503933
  have htrace : WordTrace (prefixWord ++ tailWord_4503933) baseStart_4503933 baseEnd_4503933 := by
    simpa [prefixWord, tailWord_4503933, baseEnd_4503933] using wordTrace_append hprefix tailTrace_4503933
  have hstable : (prefixWord ++ tailWord_4503933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503933).length < 2 ^ (prefixWord ++ tailWord_4503933).sum := by decide
  have hdescent : baseEnd_4503933 < baseStart_4503933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503936 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_4503936 : Nat := 118140960795 + 4503936 * 2 ^ 59
def prefixEnd_4503936 : Nat := 4983230072969 + 3 ^ 40 * 4503936 * 2
def baseEnd_4503936 : Nat := 2312684005088595563386781

theorem tailTrace_4503936 : CollatzResearch.WordTrace tailWord_4503936 prefixEnd_4503936 2312684005088595563386781 := by
  unfold tailWord_4503936
  simp only [CollatzResearch.WordTrace]
  refine ⟨82136020705508278936945831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109514694274011038582594441 82136020705508278936945831)
  ·
    refine ⟨123204031058262418405418747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82136020705508278936945831 123204031058262418405418747)
    ·
      refine ⟨184806046587393627608128121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123204031058262418405418747 184806046587393627608128121)
      ·
        refine ⟨138604534940545220706096091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184806046587393627608128121 138604534940545220706096091)
        ·
          refine ⟨207906802410817831059144137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138604534940545220706096091 207906802410817831059144137)
          ·
            refine ⟨155930101808113373294358103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207906802410817831059144137 155930101808113373294358103)
            ·
              refine ⟨233895152712170059941537155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155930101808113373294358103 233895152712170059941537155)
              ·
                refine ⟨350842729068255089912305733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233895152712170059941537155 350842729068255089912305733)
                ·
                  refine ⟨65783011700297829358557325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350842729068255089912305733 65783011700297829358557325)
                  ·
                    refine ⟨24668629387611686009458997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65783011700297829358557325 24668629387611686009458997)
                    ·
                      refine ⟨2312684005088595563386781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24668629387611686009458997 2312684005088595563386781)
                      ·
                        rfl

theorem cell23_4503936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_4503936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503936 prefixEnd_4503936 := by exact prefixLift 4503936
  have htrace : WordTrace (prefixWord ++ tailWord_4503936) baseStart_4503936 baseEnd_4503936 := by
    simpa [prefixWord, tailWord_4503936, baseEnd_4503936] using wordTrace_append hprefix tailTrace_4503936
  have hstable : (prefixWord ++ tailWord_4503936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503936).length < 2 ^ (prefixWord ++ tailWord_4503936).sum := by decide
  have hdescent : baseEnd_4503936 < baseStart_4503936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503950 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4503950 : Nat := 118140960795 + 4503950 * 2 ^ 59
def prefixEnd_4503950 : Nat := 4983230072969 + 3 ^ 40 * 4503950 * 2
def baseEnd_4503950 : Nat := 2312691193817758508611717

theorem tailTrace_4503950 : CollatzResearch.WordTrace tailWord_4503950 prefixEnd_4503950 2312691193817758508611717 := by
  unfold tailWord_4503950
  simp only [CollatzResearch.WordTrace]
  refine ⟨20534069004120729783112663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109515034688643892176600869 20534069004120729783112663)
  ·
    refine ⟨30801103506181094674668995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20534069004120729783112663 30801103506181094674668995)
    ·
      refine ⟨46201655259271642012003493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30801103506181094674668995 46201655259271642012003493)
      ·
        refine ⟨8662810361113432877250655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46201655259271642012003493 8662810361113432877250655)
        ·
          refine ⟨12994215541670149315875983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8662810361113432877250655 12994215541670149315875983)
          ·
            refine ⟨19491323312505223973813975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12994215541670149315875983 19491323312505223973813975)
            ·
              refine ⟨29236984968757835960720963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19491323312505223973813975 29236984968757835960720963)
              ·
                refine ⟨43855477453136753941081445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29236984968757835960720963 43855477453136753941081445)
                ·
                  refine ⟨8222902022463141363952771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43855477453136753941081445 8222902022463141363952771)
                  ·
                    refine ⟨12334353033694712045929157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8222902022463141363952771 12334353033694712045929157)
                    ·
                      refine ⟨2312691193817758508611717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12334353033694712045929157 2312691193817758508611717)
                      ·
                        rfl

theorem cell23_4503950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4503950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503950 prefixEnd_4503950 := by exact prefixLift 4503950
  have htrace : WordTrace (prefixWord ++ tailWord_4503950) baseStart_4503950 baseEnd_4503950 := by
    simpa [prefixWord, tailWord_4503950, baseEnd_4503950] using wordTrace_append hprefix tailTrace_4503950
  have hstable : (prefixWord ++ tailWord_4503950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503950).length < 2 ^ (prefixWord ++ tailWord_4503950).sum := by decide
  have hdescent : baseEnd_4503950 < baseStart_4503950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503970 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_4503970 : Nat := 118140960795 + 4503970 * 2 ^ 59
def prefixEnd_4503970 : Nat := 4983230072969 + 3 ^ 40 * 4503970 * 2
def baseEnd_4503970 : Nat := 2312701463430848430361625

theorem tailTrace_4503970 : CollatzResearch.WordTrace tailWord_4503970 prefixEnd_4503970 2312701463430848430361625 := by
  unfold tailWord_4503970
  simp only [CollatzResearch.WordTrace]
  refine ⟨41068320373223345420157341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109515520995262254453752909 41068320373223345420157341)
  ·
    refine ⟨15400620139958754532559003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41068320373223345420157341 15400620139958754532559003)
    ·
      refine ⟨23100930209938131798838505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15400620139958754532559003 23100930209938131798838505)
      ·
        refine ⟨17325697657453598849128879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23100930209938131798838505 17325697657453598849128879)
        ·
          refine ⟨25988546486180398273693319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17325697657453598849128879 25988546486180398273693319)
          ·
            refine ⟨38982819729270597410539979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25988546486180398273693319 38982819729270597410539979)
            ·
              refine ⟨58474229593905896115809969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38982819729270597410539979 58474229593905896115809969)
              ·
                refine ⟨43855672195429422086857477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58474229593905896115809969 43855672195429422086857477)
                ·
                  refine ⟨8222938536643016641285777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43855672195429422086857477 8222938536643016641285777)
                  ·
                    refine ⟨6167203902482262480964333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8222938536643016641285777 6167203902482262480964333)
                    ·
                      refine ⟨2312701463430848430361625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6167203902482262480964333 2312701463430848430361625)
                      ·
                        rfl

theorem cell23_4503970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_4503970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503970 prefixEnd_4503970 := by exact prefixLift 4503970
  have htrace : WordTrace (prefixWord ++ tailWord_4503970) baseStart_4503970 baseEnd_4503970 := by
    simpa [prefixWord, tailWord_4503970, baseEnd_4503970] using wordTrace_append hprefix tailTrace_4503970
  have hstable : (prefixWord ++ tailWord_4503970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503970).length < 2 ^ (prefixWord ++ tailWord_4503970).sum := by decide
  have hdescent : baseEnd_4503970 < baseStart_4503970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4503973 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 6]
def baseStart_4503973 : Nat := 118140960795 + 4503973 * 2 ^ 59
def prefixEnd_4503973 : Nat := 4983230072969 + 3 ^ 40 * 4503973 * 2
def baseEnd_4503973 : Nat := 256967000430312435402679

theorem tailTrace_4503973 : CollatzResearch.WordTrace tailWord_4503973 prefixEnd_4503973 256967000430312435402679 := by
  unfold tailWord_4503973
  simp only [CollatzResearch.WordTrace]
  refine ⟨164273390911882513192988573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109515593941255008795325715 164273390911882513192988573)
  ·
    refine ⟨61602521591955942447370715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164273390911882513192988573 61602521591955942447370715)
    ·
      refine ⟨92403782387933913671056073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61602521591955942447370715 92403782387933913671056073)
      ·
        refine ⟨69302836790950435253292055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92403782387933913671056073 69302836790950435253292055)
        ·
          refine ⟨103954255186425652879938083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69302836790950435253292055 103954255186425652879938083)
          ·
            refine ⟨155931382779638479319907125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103954255186425652879938083 155931382779638479319907125)
            ·
              refine ⟨14618567135591107436241293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 155931382779638479319907125 14618567135591107436241293)
              ·
                refine ⟨5481962675846665288590485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14618567135591107436241293 5481962675846665288590485)
                ·
                  refine ⟨256967000430312435402679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5481962675846665288590485 256967000430312435402679)
                  ·
                    rfl

theorem cell23_4503973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_4503973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4503973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4503973 prefixEnd_4503973 := by exact prefixLift 4503973
  have htrace : WordTrace (prefixWord ++ tailWord_4503973) baseStart_4503973 baseEnd_4503973 := by
    simpa [prefixWord, tailWord_4503973, baseEnd_4503973] using wordTrace_append hprefix tailTrace_4503973
  have hstable : (prefixWord ++ tailWord_4503973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4503973).length < 2 ^ (prefixWord ++ tailWord_4503973).sum := by decide
  have hdescent : baseEnd_4503973 < baseStart_4503973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4503973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504020 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4504020 : Nat := 118140960795 + 4504020 * 2 ^ 59
def prefixEnd_4504020 : Nat := 4983230072969 + 3 ^ 40 * 4504020 * 2
def baseEnd_4504020 : Nat := 770909045821191078245465

theorem tailTrace_4504020 : CollatzResearch.WordTrace tailWord_4504020 prefixEnd_4504020 770909045821191078245465 := by
  unfold tailWord_4504020
  simp only [CollatzResearch.WordTrace]
  refine ⟨82137552571356120109974757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109516736761808160146633009 82137552571356120109974757)
  ·
    refine ⟨15400791107129272520620267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82137552571356120109974757 15400791107129272520620267)
    ·
      refine ⟨23101186660693908780930401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15400791107129272520620267 23101186660693908780930401)
      ·
        refine ⟨17325889995520431585697801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23101186660693908780930401 17325889995520431585697801)
        ·
          refine ⟨12994417496640323689273351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17325889995520431585697801 12994417496640323689273351)
          ·
            refine ⟨19491626244960485533910027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12994417496640323689273351 19491626244960485533910027)
            ·
              refine ⟨29237439367440728300865041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19491626244960485533910027 29237439367440728300865041)
              ·
                refine ⟨21928079525580546225648781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29237439367440728300865041 21928079525580546225648781)
                ·
                  refine ⟨8223029822092704834618293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21928079525580546225648781 8223029822092704834618293)
                  ·
                    refine ⟨770909045821191078245465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8223029822092704834618293 770909045821191078245465)
                    ·
                      rfl

theorem cell23_4504020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4504020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504020 prefixEnd_4504020 := by exact prefixLift 4504020
  have htrace : WordTrace (prefixWord ++ tailWord_4504020) baseStart_4504020 baseEnd_4504020 := by
    simpa [prefixWord, tailWord_4504020, baseEnd_4504020] using wordTrace_append hprefix tailTrace_4504020
  have hstable : (prefixWord ++ tailWord_4504020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504020).length < 2 ^ (prefixWord ++ tailWord_4504020).sum := by decide
  have hdescent : baseEnd_4504020 < baseStart_4504020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504040 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4504040 : Nat := 118140960795 + 4504040 * 2 ^ 59
def prefixEnd_4504040 : Nat := 4983230072969 + 3 ^ 40 * 4504040 * 2
def baseEnd_4504040 : Nat := 2312737407076663156486303

theorem tailTrace_4504040 : CollatzResearch.WordTrace tailWord_4504040 prefixEnd_4504040 2312737407076663156486303 := by
  unfold tailWord_4504040
  simp only [CollatzResearch.WordTrace]
  refine ⟨82137917301319891817838787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109517223068426522423785049 82137917301319891817838787)
  ·
    refine ⟨123206875951979837726758181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82137917301319891817838787 123206875951979837726758181)
    ·
      refine ⟨23101289240996219573767159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123206875951979837726758181 23101289240996219573767159)
      ·
        refine ⟨34651933861494329360650739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23101289240996219573767159 34651933861494329360650739)
        ·
          refine ⟨51977900792241494040976109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34651933861494329360650739 51977900792241494040976109)
          ·
            refine ⟨19491712797090560265366041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51977900792241494040976109 19491712797090560265366041)
            ·
              refine ⟨14618784597817920199024531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19491712797090560265366041 14618784597817920199024531)
              ·
                refine ⟨21928176896726880298536797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14618784597817920199024531 21928176896726880298536797)
                ·
                  refine ⟨8223066336272580111951299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21928176896726880298536797 8223066336272580111951299)
                  ·
                    refine ⟨12334599504408870167926949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8223066336272580111951299 12334599504408870167926949)
                    ·
                      refine ⟨2312737407076663156486303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12334599504408870167926949 2312737407076663156486303)
                      ·
                        rfl

theorem cell23_4504040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4504040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504040 prefixEnd_4504040 := by exact prefixLift 4504040
  have htrace : WordTrace (prefixWord ++ tailWord_4504040) baseStart_4504040 baseEnd_4504040 := by
    simpa [prefixWord, tailWord_4504040, baseEnd_4504040] using wordTrace_append hprefix tailTrace_4504040
  have hstable : (prefixWord ++ tailWord_4504040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504040).length < 2 ^ (prefixWord ++ tailWord_4504040).sum := by decide
  have hdescent : baseEnd_4504040 < baseStart_4504040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504057 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 1, 1, 4]
def baseStart_4504057 : Nat := 118140960795 + 4504057 * 2 ^ 59
def prefixEnd_4504057 : Nat := 4983230072969 + 3 ^ 40 * 4504057 * 2
def baseEnd_4504057 : Nat := 2312746136247789589973725

theorem tailTrace_4504057 : CollatzResearch.WordTrace tailWord_4504057 prefixEnd_4504057 2312746136247789589973725 := by
  unfold tailWord_4504057
  simp only [CollatzResearch.WordTrace]
  refine ⟨164276454643578195539046425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109517636429052130359364283 164276454643578195539046425)
  ·
    refine ⟨123207340982683646654284819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164276454643578195539046425 123207340982683646654284819)
    ·
      refine ⟨184811011474025469981427229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123207340982683646654284819 184811011474025469981427229)
      ·
        refine ⟨69304129302759551243035211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184811011474025469981427229 69304129302759551243035211)
        ·
          refine ⟨103956193954139326864552817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69304129302759551243035211 103956193954139326864552817)
          ·
            refine ⟨77967145465604495148414613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103956193954139326864552817 77967145465604495148414613)
            ·
              refine ⟨3654709943700210710081935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77967145465604495148414613 3654709943700210710081935)
              ·
                refine ⟨5482064915550316065122903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654709943700210710081935 5482064915550316065122903)
                ·
                  refine ⟨8223097373325474097684355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5482064915550316065122903 8223097373325474097684355)
                  ·
                    refine ⟨12334646059988211146526533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8223097373325474097684355 12334646059988211146526533)
                    ·
                      refine ⟨2312746136247789589973725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12334646059988211146526533 2312746136247789589973725)
                      ·
                        rfl

theorem cell23_4504057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_4504057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504057 prefixEnd_4504057 := by exact prefixLift 4504057
  have htrace : WordTrace (prefixWord ++ tailWord_4504057) baseStart_4504057 baseEnd_4504057 := by
    simpa [prefixWord, tailWord_4504057, baseEnd_4504057] using wordTrace_append hprefix tailTrace_4504057
  have hstable : (prefixWord ++ tailWord_4504057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504057).length < 2 ^ (prefixWord ++ tailWord_4504057).sum := by decide
  have hdescent : baseEnd_4504057 < baseStart_4504057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504074 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_4504074 : Nat := 118140960795 + 4504074 * 2 ^ 59
def prefixEnd_4504074 : Nat := 4983230072969 + 3 ^ 40 * 4504074 * 2
def baseEnd_4504074 : Nat := 2312754865418916023461147

theorem tailTrace_4504074 : CollatzResearch.WordTrace tailWord_4504074 prefixEnd_4504074 2312754865418916023461147 := by
  unfold tailWord_4504074
  simp only [CollatzResearch.WordTrace]
  refine ⟨41069268671129151860603819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109518049789677738294943517 41069268671129151860603819)
  ·
    refine ⟨61603903006693727790905729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41069268671129151860603819 61603903006693727790905729)
    ·
      refine ⟨46202927255020295843179297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61603903006693727790905729 46202927255020295843179297)
      ·
        refine ⟨34652195441265221882384473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46202927255020295843179297 34652195441265221882384473)
        ·
          refine ⟨25989146580948916411788355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34652195441265221882384473 25989146580948916411788355)
          ·
            refine ⟨38983719871423374617682533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25989146580948916411788355 38983719871423374617682533)
            ·
              refine ⟨7309447475891882740815475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38983719871423374617682533 7309447475891882740815475)
              ·
                refine ⟨10964171213837824111223213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7309447475891882740815475 10964171213837824111223213)
                ·
                  refine ⟨4111564205189184041708705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10964171213837824111223213 4111564205189184041708705)
                  ·
                    refine ⟨3083673153891888031281529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111564205189184041708705 3083673153891888031281529)
                    ·
                      refine ⟨2312754865418916023461147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083673153891888031281529 2312754865418916023461147)
                      ·
                        rfl

theorem cell23_4504074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_4504074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504074 prefixEnd_4504074 := by exact prefixLift 4504074
  have htrace : WordTrace (prefixWord ++ tailWord_4504074) baseStart_4504074 baseEnd_4504074 := by
    simpa [prefixWord, tailWord_4504074, baseEnd_4504074] using wordTrace_append hprefix tailTrace_4504074
  have hstable : (prefixWord ++ tailWord_4504074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504074).length < 2 ^ (prefixWord ++ tailWord_4504074).sum := by decide
  have hdescent : baseEnd_4504074 < baseStart_4504074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504084 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4504084 : Nat := 118140960795 + 4504084 * 2 ^ 59
def prefixEnd_4504084 : Nat := 4983230072969 + 3 ^ 40 * 4504084 * 2
def baseEnd_4504084 : Nat := 770920000075153661445367

theorem tailTrace_4504084 : CollatzResearch.WordTrace tailWord_4504084 prefixEnd_4504084 770920000075153661445367 := by
  unfold tailWord_4504084
  simp only [CollatzResearch.WordTrace]
  refine ⟨82138719707240189575139653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109518292942986919433519537 82138719707240189575139653)
  ·
    refine ⟨15401009945107535545338685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82138719707240189575139653 15401009945107535545338685)
    ·
      refine ⟨5775378729415325829502007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15401009945107535545338685 5775378729415325829502007)
      ·
        refine ⟨8663068094122988744253011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5775378729415325829502007 8663068094122988744253011)
        ·
          refine ⟨12994602141184483116379517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8663068094122988744253011 12994602141184483116379517)
          ·
            refine ⟨4872975802944181168642319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12994602141184483116379517 4872975802944181168642319)
            ·
              refine ⟨7309463704416271752963479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4872975802944181168642319 7309463704416271752963479)
              ·
                refine ⟨10964195556624407629445219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7309463704416271752963479 10964195556624407629445219)
                ·
                  refine ⟨16446293334936611444167829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10964195556624407629445219 16446293334936611444167829)
                  ·
                    refine ⟨770920000075153661445367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16446293334936611444167829 770920000075153661445367)
                    ·
                      rfl

theorem cell23_4504084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4504084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504084 prefixEnd_4504084 := by exact prefixLift 4504084
  have htrace : WordTrace (prefixWord ++ tailWord_4504084) baseStart_4504084 baseEnd_4504084 := by
    simpa [prefixWord, tailWord_4504084, baseEnd_4504084] using wordTrace_append hprefix tailTrace_4504084
  have hstable : (prefixWord ++ tailWord_4504084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504084).length < 2 ^ (prefixWord ++ tailWord_4504084).sum := by decide
  have hdescent : baseEnd_4504084 < baseStart_4504084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504087 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4504087 : Nat := 118140960795 + 4504087 * 2 ^ 59
def prefixEnd_4504087 : Nat := 4983230072969 + 3 ^ 40 * 4504087 * 2
def baseEnd_4504087 : Nat := 2312761540667424472598587

theorem tailTrace_4504087 : CollatzResearch.WordTrace tailWord_4504087 prefixEnd_4504087 2312761540667424472598587 := by
  unfold tailWord_4504087
  simp only [CollatzResearch.WordTrace]
  refine ⟨164277548833469510662638515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109518365888979673775092343 164277548833469510662638515)
  ·
    refine ⟨246416323250204265993957773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164277548833469510662638515 246416323250204265993957773)
    ·
      refine ⟨92406121218826599747734165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246416323250204265993957773 92406121218826599747734165)
      ·
        refine ⟨4331536932132496863175039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92406121218826599747734165 4331536932132496863175039)
        ·
          refine ⟨6497305398198745294762559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331536932132496863175039 6497305398198745294762559)
          ·
            refine ⟨9745958097298117942143839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6497305398198745294762559 9745958097298117942143839)
            ·
              refine ⟨14618937145947176913215759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9745958097298117942143839 14618937145947176913215759)
              ·
                refine ⟨21928405718920765369823639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14618937145947176913215759 21928405718920765369823639)
                ·
                  refine ⟨32892608578381148054735459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21928405718920765369823639 32892608578381148054735459)
                  ·
                    refine ⟨49338912867571722082103189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32892608578381148054735459 49338912867571722082103189)
                    ·
                      refine ⟨2312761540667424472598587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49338912867571722082103189 2312761540667424472598587)
                      ·
                        rfl

theorem cell23_4504087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4504087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504087 prefixEnd_4504087 := by exact prefixLift 4504087
  have htrace : WordTrace (prefixWord ++ tailWord_4504087) baseStart_4504087 baseEnd_4504087 := by
    simpa [prefixWord, tailWord_4504087, baseEnd_4504087] using wordTrace_append hprefix tailTrace_4504087
  have hstable : (prefixWord ++ tailWord_4504087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504087).length < 2 ^ (prefixWord ++ tailWord_4504087).sum := by decide
  have hdescent : baseEnd_4504087 < baseStart_4504087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504141 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_4504141 : Nat := 118140960795 + 4504141 * 2 ^ 59
def prefixEnd_4504141 : Nat := 4983230072969 + 3 ^ 40 * 4504141 * 2
def baseEnd_4504141 : Nat := 2312789268622767261323339

theorem tailTrace_4504141 : CollatzResearch.WordTrace tailWord_4504141 prefixEnd_4504141 2312789268622767261323339 := by
  unfold tailWord_4504141
  simp only [CollatzResearch.WordTrace]
  refine ⟨164279518375273877885104277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109519678916849251923402851 164279518375273877885104277)
  ·
    refine ⟨7700602423840963025864263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164279518375273877885104277 7700602423840963025864263)
    ·
      refine ⟨11550903635761444538796395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7700602423840963025864263 11550903635761444538796395)
      ·
        refine ⟨17326355453642166808194593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11550903635761444538796395 17326355453642166808194593)
        ·
          refine ⟨12994766590231625106145945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17326355453642166808194593 12994766590231625106145945)
          ·
            refine ⟨9746074942673718829609459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12994766590231625106145945 9746074942673718829609459)
            ·
              refine ⟨14619112414010578244414189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9746074942673718829609459 14619112414010578244414189)
              ·
                refine ⟨5482167155253966841655321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14619112414010578244414189 5482167155253966841655321)
                ·
                  refine ⟨4111625366440475131241491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5482167155253966841655321 4111625366440475131241491)
                  ·
                    refine ⟨6167438049660712696862237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4111625366440475131241491 6167438049660712696862237)
                    ·
                      refine ⟨2312789268622767261323339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6167438049660712696862237 2312789268622767261323339)
                      ·
                        rfl

theorem cell23_4504141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_4504141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504141 prefixEnd_4504141 := by exact prefixLift 4504141
  have htrace : WordTrace (prefixWord ++ tailWord_4504141) baseStart_4504141 baseEnd_4504141 := by
    simpa [prefixWord, tailWord_4504141, baseEnd_4504141] using wordTrace_append hprefix tailTrace_4504141
  have hstable : (prefixWord ++ tailWord_4504141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504141).length < 2 ^ (prefixWord ++ tailWord_4504141).sum := by decide
  have hdescent : baseEnd_4504141 < baseStart_4504141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504158 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4504158 : Nat := 118140960795 + 4504158 * 2 ^ 59
def prefixEnd_4504158 : Nat := 4983230072969 + 3 ^ 40 * 4504158 * 2
def baseEnd_4504158 : Nat := 2312797997793893694810761

theorem tailTrace_4504158 : CollatzResearch.WordTrace tailWord_4504158 prefixEnd_4504158 2312797997793893694810761 := by
  unfold tailWord_4504158
  simp only [CollatzResearch.WordTrace]
  refine ⟨20535017302026536223559141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109520092277474859858982085 20535017302026536223559141)
  ·
    refine ⟨3850315744129975541917339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20535017302026536223559141 3850315744129975541917339)
    ·
      refine ⟨5775473616194963312876009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3850315744129975541917339 5775473616194963312876009)
      ·
        refine ⟨4331605212146222484657007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5775473616194963312876009 4331605212146222484657007)
        ·
          refine ⟨6497407818219333726985511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4331605212146222484657007 6497407818219333726985511)
          ·
            refine ⟨9746111727329000590478267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6497407818219333726985511 9746111727329000590478267)
            ·
              refine ⟨14619167590993500885717401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9746111727329000590478267 14619167590993500885717401)
              ·
                refine ⟨10964375693245125664288051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14619167590993500885717401 10964375693245125664288051)
                ·
                  refine ⟨16446563539867688496432077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10964375693245125664288051 16446563539867688496432077)
                  ·
                    refine ⟨6167461327450383186162029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16446563539867688496432077 6167461327450383186162029)
                    ·
                      refine ⟨2312797997793893694810761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6167461327450383186162029 2312797997793893694810761)
                      ·
                        rfl

theorem cell23_4504158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4504158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504158 prefixEnd_4504158 := by exact prefixLift 4504158
  have htrace : WordTrace (prefixWord ++ tailWord_4504158) baseStart_4504158 baseEnd_4504158 := by
    simpa [prefixWord, tailWord_4504158, baseEnd_4504158] using wordTrace_append hprefix tailTrace_4504158
  have hstable : (prefixWord ++ tailWord_4504158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504158).length < 2 ^ (prefixWord ++ tailWord_4504158).sum := by decide
  have hdescent : baseEnd_4504158 < baseStart_4504158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504168 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4504168 : Nat := 118140960795 + 4504168 * 2 ^ 59
def prefixEnd_4504168 : Nat := 4983230072969 + 3 ^ 40 * 4504168 * 2
def baseEnd_4504168 : Nat := 2312803132600438655685715

theorem tailTrace_4504168 : CollatzResearch.WordTrace tailWord_4504168 prefixEnd_4504168 2312803132600438655685715 := by
  unfold tailWord_4504168
  simp only [CollatzResearch.WordTrace]
  refine ⟨82140251573088030748168579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109520335430784040997558105 82140251573088030748168579)
  ·
    refine ⟨123210377359632046122252869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82140251573088030748168579 123210377359632046122252869)
    ·
      refine ⟨23101945754931008647922413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123210377359632046122252869 23101945754931008647922413)
      ·
        refine ⟨8663229658099128242970905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23101945754931008647922413 8663229658099128242970905)
        ·
          refine ⟨6497422243574346182228179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8663229658099128242970905 6497422243574346182228179)
          ·
            refine ⟨9746133365361519273342269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6497422243574346182228179 9746133365361519273342269)
            ·
              refine ⟨3654800012010569727503351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9746133365361519273342269 3654800012010569727503351)
              ·
                refine ⟨5482200018015854591255027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3654800012010569727503351 5482200018015854591255027)
                ·
                  refine ⟨8223300027023781886882541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5482200018015854591255027 8223300027023781886882541)
                  ·
                    refine ⟨3083737510133918207580953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8223300027023781886882541 3083737510133918207580953)
                    ·
                      refine ⟨2312803132600438655685715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083737510133918207580953 2312803132600438655685715)
                      ·
                        rfl

theorem cell23_4504168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4504168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504168 prefixEnd_4504168 := by exact prefixLift 4504168
  have htrace : WordTrace (prefixWord ++ tailWord_4504168) baseStart_4504168 baseEnd_4504168 := by
    simpa [prefixWord, tailWord_4504168, baseEnd_4504168] using wordTrace_append hprefix tailTrace_4504168
  have hstable : (prefixWord ++ tailWord_4504168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504168).length < 2 ^ (prefixWord ++ tailWord_4504168).sum := by decide
  have hdescent : baseEnd_4504168 < baseStart_4504168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504197 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_4504197 : Nat := 118140960795 + 4504197 * 2 ^ 59
def prefixEnd_4504197 : Nat := 4983230072969 + 3 ^ 40 * 4504197 * 2
def baseEnd_4504197 : Nat := 2312818023539419042223081

theorem tailTrace_4504197 : CollatzResearch.WordTrace tailWord_4504197 prefixEnd_4504197 2312818023539419042223081 := by
  unfold tailWord_4504197
  simp only [CollatzResearch.WordTrace]
  refine ⟨164281560863070999449142845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109521040575380666299428563 164281560863070999449142845)
  ·
    refine ⟨61605585323651624793428567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164281560863070999449142845 61605585323651624793428567)
    ·
      refine ⟨92408377985477437190142851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61605585323651624793428567 92408377985477437190142851)
      ·
        refine ⟨138612566978216155785214277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92408377985477437190142851 138612566978216155785214277)
        ·
          refine ⟨25989856308415529209727677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138612566978216155785214277 25989856308415529209727677)
          ·
            refine ⟨9746196115655823453647879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25989856308415529209727677 9746196115655823453647879)
            ·
              refine ⟨14619294173483735180471819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9746196115655823453647879 14619294173483735180471819)
              ·
                refine ⟨21928941260225602770707729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14619294173483735180471819 21928941260225602770707729)
                ·
                  refine ⟨16446705945169202078030797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21928941260225602770707729 16446705945169202078030797)
                  ·
                    refine ⟨6167514729438450779261549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16446705945169202078030797 6167514729438450779261549)
                    ·
                      refine ⟨2312818023539419042223081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6167514729438450779261549 2312818023539419042223081)
                      ·
                        rfl

theorem cell23_4504197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_4504197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504197 prefixEnd_4504197 := by exact prefixLift 4504197
  have htrace : WordTrace (prefixWord ++ tailWord_4504197) baseStart_4504197 baseEnd_4504197 := by
    simpa [prefixWord, tailWord_4504197, baseEnd_4504197] using wordTrace_append hprefix tailTrace_4504197
  have hstable : (prefixWord ++ tailWord_4504197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504197).length < 2 ^ (prefixWord ++ tailWord_4504197).sum := by decide
  have hdescent : baseEnd_4504197 < baseStart_4504197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504250 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_4504250 : Nat := 118140960795 + 4504250 * 2 ^ 59
def prefixEnd_4504250 : Nat := 4983230072969 + 3 ^ 40 * 4504250 * 2
def baseEnd_4504250 : Nat := 2312845238014107334860337

theorem tailTrace_4504250 : CollatzResearch.WordTrace tailWord_4504250 prefixEnd_4504250 2312845238014107334860337 := by
  unfold tailWord_4504250
  simp only [CollatzResearch.WordTrace]
  refine ⟨41070873482969747375205551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109522329287919326333881469 41070873482969747375205551)
  ·
    refine ⟨61606310224454621062808327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41070873482969747375205551 61606310224454621062808327)
    ·
      refine ⟨92409465336681931594212491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61606310224454621062808327 92409465336681931594212491)
      ·
        refine ⟨138614198005022897391318737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92409465336681931594212491 138614198005022897391318737)
        ·
          refine ⟨103960648503767173043489053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138614198005022897391318737 103960648503767173043489053)
          ·
            refine ⟨38985243188912689891308395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103960648503767173043489053 38985243188912689891308395)
            ·
              refine ⟨58477864783369034836962593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38985243188912689891308395 58477864783369034836962593)
              ·
                refine ⟨43858398587526776127721945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58477864783369034836962593 43858398587526776127721945)
                ·
                  refine ⟨32893798940645082095791459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43858398587526776127721945 32893798940645082095791459)
                  ·
                    refine ⟨49340698410967623143687189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32893798940645082095791459 49340698410967623143687189)
                    ·
                      refine ⟨2312845238014107334860337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49340698410967623143687189 2312845238014107334860337)
                      ·
                        rfl

theorem cell23_4504250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_4504250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504250 prefixEnd_4504250 := by exact prefixLift 4504250
  have htrace : WordTrace (prefixWord ++ tailWord_4504250) baseStart_4504250 baseEnd_4504250 := by
    simpa [prefixWord, tailWord_4504250, baseEnd_4504250] using wordTrace_append hprefix tailTrace_4504250
  have hstable : (prefixWord ++ tailWord_4504250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504250).length < 2 ^ (prefixWord ++ tailWord_4504250).sum := by decide
  have hdescent : baseEnd_4504250 < baseStart_4504250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504254 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_4504254 : Nat := 118140960795 + 4504254 * 2 ^ 59
def prefixEnd_4504254 : Nat := 4983230072969 + 3 ^ 40 * 4504254 * 2
def baseEnd_4504254 : Nat := 2312847291936725319210319

theorem tailTrace_4504254 : CollatzResearch.WordTrace tailWord_4504254 prefixEnd_4504254 2312847291936725319210319 := by
  unfold tailWord_4504254
  simp only [CollatzResearch.WordTrace]
  refine ⟨20535454977983062272995977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109522426549242998789311877 20535454977983062272995977)
  ·
    refine ⟨15401591233487296704746983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20535454977983062272995977 15401591233487296704746983)
    ·
      refine ⟨23102386850230945057120475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15401591233487296704746983 23102386850230945057120475)
      ·
        refine ⟨34653580275346417585680713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23102386850230945057120475 34653580275346417585680713)
        ·
          refine ⟨25990185206509813189260535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34653580275346417585680713 25990185206509813189260535)
          ·
            refine ⟨38985277809764719783890803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25990185206509813189260535 38985277809764719783890803)
            ·
              refine ⟨58477916714647079675836205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38985277809764719783890803 58477916714647079675836205)
              ·
                refine ⟨21929218767992654878438577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58477916714647079675836205 21929218767992654878438577)
                ·
                  refine ⟨16446914075994491158828933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21929218767992654878438577 16446914075994491158828933)
                  ·
                    refine ⟨3083796389248967092280425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16446914075994491158828933 3083796389248967092280425)
                    ·
                      refine ⟨2312847291936725319210319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083796389248967092280425 2312847291936725319210319)
                      ·
                        rfl

theorem cell23_4504254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_4504254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504254 prefixEnd_4504254 := by exact prefixLift 4504254
  have htrace : WordTrace (prefixWord ++ tailWord_4504254) baseStart_4504254 baseEnd_4504254 := by
    simpa [prefixWord, tailWord_4504254, baseEnd_4504254] using wordTrace_append hprefix tailTrace_4504254
  have hstable : (prefixWord ++ tailWord_4504254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504254).length < 2 ^ (prefixWord ++ tailWord_4504254).sum := by decide
  have hdescent : baseEnd_4504254 < baseStart_4504254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504300 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_4504300 : Nat := 118140960795 + 4504300 * 2 ^ 59
def prefixEnd_4504300 : Nat := 4983230072969 + 3 ^ 40 * 4504300 * 2
def baseEnd_4504300 : Nat := 2312870912046832139235107

theorem tailTrace_4504300 : CollatzResearch.WordTrace tailWord_4504300 prefixEnd_4504300 2312870912046832139235107 := by
  unfold tailWord_4504300
  simp only [CollatzResearch.WordTrace]
  refine ⟨82142658790848924020071177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109523545054465232026761569 82142658790848924020071177)
  ·
    refine ⟨61606994093136693015053383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82142658790848924020071177 61606994093136693015053383)
    ·
      refine ⟨92410491139705039522580075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61606994093136693015053383 92410491139705039522580075)
      ·
        refine ⟨138615736709557559283870113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92410491139705039522580075 138615736709557559283870113)
        ·
          refine ⟨103961802532168169462902585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138615736709557559283870113 103961802532168169462902585)
          ·
            refine ⟨77971351899126127097176939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103961802532168169462902585 77971351899126127097176939)
            ·
              refine ⟨116957027848689190645765409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77971351899126127097176939 116957027848689190645765409)
              ·
                refine ⟨87717770886516892984324057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116957027848689190645765409 87717770886516892984324057)
                ·
                  refine ⟨65788328164887669738243043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87717770886516892984324057 65788328164887669738243043)
                  ·
                    refine ⟨98682492247331504607364565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65788328164887669738243043 98682492247331504607364565)
                    ·
                      refine ⟨2312870912046832139235107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98682492247331504607364565 2312870912046832139235107)
                      ·
                        rfl

theorem cell23_4504300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_4504300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504300 prefixEnd_4504300 := by exact prefixLift 4504300
  have htrace : WordTrace (prefixWord ++ tailWord_4504300) baseStart_4504300 baseEnd_4504300 := by
    simpa [prefixWord, tailWord_4504300, baseEnd_4504300] using wordTrace_append hprefix tailTrace_4504300
  have hstable : (prefixWord ++ tailWord_4504300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504300).length < 2 ^ (prefixWord ++ tailWord_4504300).sum := by decide
  have hdescent : baseEnd_4504300 < baseStart_4504300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504337 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 6, 4]
def baseStart_4504337 : Nat := 118140960795 + 4504337 * 2 ^ 59
def prefixEnd_4504337 : Nat := 4983230072969 + 3 ^ 40 * 4504337 * 2
def baseEnd_4504337 : Nat := 770963303610349498157479

theorem tailTrace_4504337 : CollatzResearch.WordTrace tailWord_4504337 prefixEnd_4504337 770963303610349498157479 := by
  unfold tailWord_4504337
  simp only [CollatzResearch.WordTrace]
  refine ⟨164286667082563803359239265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109524444721709202239492843 164286667082563803359239265)
  ·
    refine ⟨123215000311922852519429449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164286667082563803359239265 123215000311922852519429449)
    ·
      refine ⟨92411250233942139389572087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123215000311922852519429449 92411250233942139389572087)
      ·
        refine ⟨138616875350913209084358131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92411250233942139389572087 138616875350913209084358131)
        ·
          refine ⟨207925313026369813626537197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138616875350913209084358131 207925313026369813626537197)
          ·
            refine ⟨77971992384888680109951449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207925313026369813626537197 77971992384888680109951449)
            ·
              refine ⟨58478994288666510082463587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77971992384888680109951449 58478994288666510082463587)
              ·
                refine ⟨87718491432999765123695381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58478994288666510082463587 87718491432999765123695381)
                ·
                  refine ⟨4111804285921863990173221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87718491432999765123695381 4111804285921863990173221)
                  ·
                    refine ⟨770963303610349498157479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4111804285921863990173221 770963303610349498157479)
                    ·
                      rfl

theorem cell23_4504337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_4504337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504337 prefixEnd_4504337 := by exact prefixLift 4504337
  have htrace : WordTrace (prefixWord ++ tailWord_4504337) baseStart_4504337 baseEnd_4504337 := by
    simpa [prefixWord, tailWord_4504337, baseEnd_4504337] using wordTrace_append hprefix tailTrace_4504337
  have hstable : (prefixWord ++ tailWord_4504337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504337).length < 2 ^ (prefixWord ++ tailWord_4504337).sum := by decide
  have hdescent : baseEnd_4504337 < baseStart_4504337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504347 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 3]
def baseStart_4504347 : Nat := 118140960795 + 4504347 * 2 ^ 59
def prefixEnd_4504347 : Nat := 4983230072969 + 3 ^ 40 * 4504347 * 2
def baseEnd_4504347 : Nat := 2312895045637593455347391

theorem tailTrace_4504347 : CollatzResearch.WordTrace tailWord_4504347 prefixEnd_4504347 2312895045637593455347391 := by
  unfold tailWord_4504347
  simp only [CollatzResearch.WordTrace]
  refine ⟨164287031812527575067103295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109524687875018383378068863 164287031812527575067103295)
  ·
    refine ⟨246430547718791362600654943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164287031812527575067103295 246430547718791362600654943)
    ·
      refine ⟨369645821578187043900982415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246430547718791362600654943 369645821578187043900982415)
      ·
        refine ⟨554468732367280565851473623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369645821578187043900982415 554468732367280565851473623)
        ·
          refine ⟨831703098550920848777210435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554468732367280565851473623 831703098550920848777210435)
          ·
            refine ⟨1247554647826381273165815653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831703098550920848777210435 1247554647826381273165815653)
            ·
              refine ⟨233916496467446488718590435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1247554647826381273165815653 233916496467446488718590435)
              ·
                refine ⟨350874744701169733077885653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233916496467446488718590435 350874744701169733077885653)
                ·
                  refine ⟨8223626828933665619012945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 350874744701169733077885653 8223626828933665619012945)
                  ·
                    refine ⟨6167720121700249214259709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8223626828933665619012945 6167720121700249214259709)
                    ·
                      refine ⟨2312895045637593455347391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6167720121700249214259709 2312895045637593455347391)
                      ·
                        rfl

theorem cell23_4504347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 3].length) (baseStart_4504347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504347 prefixEnd_4504347 := by exact prefixLift 4504347
  have htrace : WordTrace (prefixWord ++ tailWord_4504347) baseStart_4504347 baseEnd_4504347 := by
    simpa [prefixWord, tailWord_4504347, baseEnd_4504347] using wordTrace_append hprefix tailTrace_4504347
  have hstable : (prefixWord ++ tailWord_4504347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504347).length < 2 ^ (prefixWord ++ tailWord_4504347).sum := by decide
  have hdescent : baseEnd_4504347 < baseStart_4504347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504357 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_4504357 : Nat := 118140960795 + 4504357 * 2 ^ 59
def prefixEnd_4504357 : Nat := 4983230072969 + 3 ^ 40 * 4504357 * 2
def baseEnd_4504357 : Nat := 2312900180444138416222345

theorem tailTrace_4504357 : CollatzResearch.WordTrace tailWord_4504357 prefixEnd_4504357 2312900180444138416222345 := by
  unfold tailWord_4504357
  simp only [CollatzResearch.WordTrace]
  refine ⟨164287396542491346774967325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109524931028327564516644883 164287396542491346774967325)
  ·
    refine ⟨61607773703434255040612747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164287396542491346774967325 61607773703434255040612747)
    ·
      refine ⟨92411660555151382560919121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61607773703434255040612747 92411660555151382560919121)
      ·
        refine ⟨69308745416363536920689341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92411660555151382560919121 69308745416363536920689341)
        ·
          refine ⟨25990779531136326345258503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69308745416363536920689341 25990779531136326345258503)
          ·
            refine ⟨38986169296704489517887755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25990779531136326345258503 38986169296704489517887755)
            ·
              refine ⟨58479253945056734276831633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38986169296704489517887755 58479253945056734276831633)
              ·
                refine ⟨43859440458792550707623725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58479253945056734276831633 43859440458792550707623725)
                ·
                  refine ⟨16447290172047206515358897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43859440458792550707623725 16447290172047206515358897)
                  ·
                    refine ⟨12335467629035404886519173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16447290172047206515358897 12335467629035404886519173)
                    ·
                      refine ⟨2312900180444138416222345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12335467629035404886519173 2312900180444138416222345)
                      ·
                        rfl

theorem cell23_4504357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_4504357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504357 prefixEnd_4504357 := by exact prefixLift 4504357
  have htrace : WordTrace (prefixWord ++ tailWord_4504357) baseStart_4504357 baseEnd_4504357 := by
    simpa [prefixWord, tailWord_4504357, baseEnd_4504357] using wordTrace_append hprefix tailTrace_4504357
  have hstable : (prefixWord ++ tailWord_4504357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504357).length < 2 ^ (prefixWord ++ tailWord_4504357).sum := by decide
  have hdescent : baseEnd_4504357 < baseStart_4504357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504378 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2]
def baseStart_4504378 : Nat := 118140960795 + 4504378 * 2 ^ 59
def prefixEnd_4504378 : Nat := 4983230072969 + 3 ^ 40 * 4504378 * 2
def baseEnd_4504378 : Nat := 2312910963537882834059749

theorem tailTrace_4504378 : CollatzResearch.WordTrace tailWord_4504378 prefixEnd_4504378 2312910963537882834059749 := by
  unfold tailWord_4504378
  simp only [CollatzResearch.WordTrace]
  refine ⟨41072040618853816840370447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109525441650276844907654525 41072040618853816840370447)
  ·
    refine ⟨61608060928280725260555671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41072040618853816840370447 61608060928280725260555671)
    ·
      refine ⟨92412091392421087890833507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61608060928280725260555671 92412091392421087890833507)
      ·
        refine ⟨138618137088631631836250261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92412091392421087890833507 138618137088631631836250261)
        ·
          refine ⟨6497725176029607742324231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 138618137088631631836250261 6497725176029607742324231)
          ·
            refine ⟨9746587764044411613486347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6497725176029607742324231 9746587764044411613486347)
            ·
              refine ⟨14619881646066617420229521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9746587764044411613486347 14619881646066617420229521)
              ·
                refine ⟨10964911234549963065172141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14619881646066617420229521 10964911234549963065172141)
                ·
                  refine ⟨4111841712956236149439553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10964911234549963065172141 4111841712956236149439553)
                  ·
                    refine ⟨3083881284717177112079665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111841712956236149439553 3083881284717177112079665)
                    ·
                      refine ⟨2312910963537882834059749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083881284717177112079665 2312910963537882834059749)
                      ·
                        rfl

theorem cell23_4504378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_4504378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504378 prefixEnd_4504378 := by exact prefixLift 4504378
  have htrace : WordTrace (prefixWord ++ tailWord_4504378) baseStart_4504378 baseEnd_4504378 := by
    simpa [prefixWord, tailWord_4504378, baseEnd_4504378] using wordTrace_append hprefix tailTrace_4504378
  have hstable : (prefixWord ++ tailWord_4504378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504378).length < 2 ^ (prefixWord ++ tailWord_4504378).sum := by decide
  have hdescent : baseEnd_4504378 < baseStart_4504378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504417 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_4504417 : Nat := 118140960795 + 4504417 * 2 ^ 59
def prefixEnd_4504417 : Nat := 4983230072969 + 3 ^ 40 * 4504417 * 2
def baseEnd_4504417 : Nat := 2312930989283408181472069

theorem tailTrace_4504417 : CollatzResearch.WordTrace tailWord_4504417 prefixEnd_4504417 2312930989283408181472069 := by
  unfold tailWord_4504417
  simp only [CollatzResearch.WordTrace]
  refine ⟨164289584922273977022151505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109526389948182651348101003 164289584922273977022151505)
  ·
    refine ⟨123217188691705482766613629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164289584922273977022151505 123217188691705482766613629)
    ·
      refine ⟨46206445759389556037480111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123217188691705482766613629 46206445759389556037480111)
      ·
        refine ⟨69309668639084334056220167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46206445759389556037480111 69309668639084334056220167)
        ·
          refine ⟨103964502958626501084330251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69309668639084334056220167 103964502958626501084330251)
          ·
            refine ⟨155946754437939751626495377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103964502958626501084330251 155946754437939751626495377)
            ·
              refine ⟨116960065828454813719871533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155946754437939751626495377 116960065828454813719871533)
              ·
                refine ⟨43860024685670555144951825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116960065828454813719871533 43860024685670555144951825)
                ·
                  refine ⟨32895018514252916358713869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43860024685670555144951825 32895018514252916358713869)
                  ·
                    refine ⟨12335631942844843634517701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32895018514252916358713869 12335631942844843634517701)
                    ·
                      refine ⟨2312930989283408181472069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12335631942844843634517701 2312930989283408181472069)
                      ·
                        rfl

theorem cell23_4504417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_4504417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504417 prefixEnd_4504417 := by exact prefixLift 4504417
  have htrace : WordTrace (prefixWord ++ tailWord_4504417) baseStart_4504417 baseEnd_4504417 := by
    simpa [prefixWord, tailWord_4504417, baseEnd_4504417] using wordTrace_append hprefix tailTrace_4504417
  have hstable : (prefixWord ++ tailWord_4504417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504417).length < 2 ^ (prefixWord ++ tailWord_4504417).sum := by decide
  have hdescent : baseEnd_4504417 < baseStart_4504417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504427 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 2, 6]
def baseStart_4504427 : Nat := 118140960795 + 4504427 * 2 ^ 59
def prefixEnd_4504427 : Nat := 4983230072969 + 3 ^ 40 * 4504427 * 2
def baseEnd_4504427 : Nat := 770978708029984380782341

theorem tailTrace_4504427 : CollatzResearch.WordTrace tailWord_4504427 prefixEnd_4504427 770978708029984380782341 := by
  unfold tailWord_4504427
  simp only [CollatzResearch.WordTrace]
  refine ⟨164289949652237748730015535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109526633101491832486677023 164289949652237748730015535)
  ·
    refine ⟨246434924478356623095023303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164289949652237748730015535 246434924478356623095023303)
    ·
      refine ⟨369652386717534934642534955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246434924478356623095023303 369652386717534934642534955)
      ·
        refine ⟨554478580076302401963802433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369652386717534934642534955 554478580076302401963802433)
        ·
          refine ⟨415858935057226801472851825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 554478580076302401963802433 415858935057226801472851825)
          ·
            refine ⟨311894201292920101104638869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415858935057226801472851825 311894201292920101104638869)
            ·
              refine ⟨14620040685605629739279947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 311894201292920101104638869 14620040685605629739279947)
              ·
                refine ⟨21930061028408444608919921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14620040685605629739279947 21930061028408444608919921)
                ·
                  refine ⟨16447545771306333456689941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21930061028408444608919921 16447545771306333456689941)
                  ·
                    refine ⟨770978708029984380782341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16447545771306333456689941 770978708029984380782341)
                    ·
                      rfl

theorem cell23_4504427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 6].length) (baseStart_4504427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504427 prefixEnd_4504427 := by exact prefixLift 4504427
  have htrace : WordTrace (prefixWord ++ tailWord_4504427) baseStart_4504427 baseEnd_4504427 := by
    simpa [prefixWord, tailWord_4504427, baseEnd_4504427] using wordTrace_append hprefix tailTrace_4504427
  have hstable : (prefixWord ++ tailWord_4504427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504427).length < 2 ^ (prefixWord ++ tailWord_4504427).sum := by decide
  have hdescent : baseEnd_4504427 < baseStart_4504427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504428 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 3]
def baseStart_4504428 : Nat := 118140960795 + 4504428 * 2 ^ 59
def prefixEnd_4504428 : Nat := 4983230072969 + 3 ^ 40 * 4504428 * 2
def baseEnd_4504428 : Nat := 2312936637570607638434519

theorem tailTrace_4504428 : CollatzResearch.WordTrace tailWord_4504428 prefixEnd_4504428 2312936637570607638434519 := by
  unfold tailWord_4504428
  simp only [CollatzResearch.WordTrace]
  refine ⟨82144993062617062950400969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109526657416822750600534625 82144993062617062950400969)
  ·
    refine ⟨61608744796962797212800727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82144993062617062950400969 61608744796962797212800727)
    ·
      refine ⟨92413117195444195819201091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61608744796962797212800727 92413117195444195819201091)
      ·
        refine ⟨138619675793166293728801637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92413117195444195819201091 138619675793166293728801637)
        ·
          refine ⟨25991189211218680074150307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138619675793166293728801637 25991189211218680074150307)
          ·
            refine ⟨38986783816828020111225461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25991189211218680074150307 38986783816828020111225461)
            ·
              refine ⟨3655010982827626885427387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38986783816828020111225461 3655010982827626885427387)
              ·
                refine ⟨5482516474241440328141081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3655010982827626885427387 5482516474241440328141081)
                ·
                  refine ⟨4111887355681080246105811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5482516474241440328141081 4111887355681080246105811)
                  ·
                    refine ⟨6167831033521620369158717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4111887355681080246105811 6167831033521620369158717)
                    ·
                      refine ⟨2312936637570607638434519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6167831033521620369158717 2312936637570607638434519)
                      ·
                        rfl

theorem cell23_4504428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_4504428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504428 prefixEnd_4504428 := by exact prefixLift 4504428
  have htrace : WordTrace (prefixWord ++ tailWord_4504428) baseStart_4504428 baseEnd_4504428 := by
    simpa [prefixWord, tailWord_4504428, baseEnd_4504428] using wordTrace_append hprefix tailTrace_4504428
  have hstable : (prefixWord ++ tailWord_4504428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504428).length < 2 ^ (prefixWord ++ tailWord_4504428).sum := by decide
  have hdescent : baseEnd_4504428 < baseStart_4504428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504446 : List Nat := [4, 2, 3, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4504446 : Nat := 118140960795 + 4504446 * 2 ^ 59
def prefixEnd_4504446 : Nat := 4983230072969 + 3 ^ 40 * 4504446 * 2
def baseEnd_4504446 : Nat := 2312945880222388568009437

theorem tailTrace_4504446 : CollatzResearch.WordTrace tailWord_4504446 prefixEnd_4504446 2312945880222388568009437 := by
  unfold tailWord_4504446
  simp only [CollatzResearch.WordTrace]
  refine ⟨20536330329896114371869649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109527095092779276649971461 20536330329896114371869649)
  ·
    refine ⟨15402247747422085778902237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20536330329896114371869649 15402247747422085778902237)
    ·
      refine ⟨5775842905283282167088339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15402247747422085778902237 5775842905283282167088339)
      ·
        refine ⟨8663764357924923250632509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5775842905283282167088339 8663764357924923250632509)
        ·
          refine ⟨3248911634221846218987191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8663764357924923250632509 3248911634221846218987191)
          ·
            refine ⟨4873367451332769328480787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248911634221846218987191 4873367451332769328480787)
            ·
              refine ⟨7310051176999153992721181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4873367451332769328480787 7310051176999153992721181)
              ·
                refine ⟨2741269191374682747270443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7310051176999153992721181 2741269191374682747270443)
                ·
                  refine ⟨4111903787062024120905665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741269191374682747270443 4111903787062024120905665)
                  ·
                    refine ⟨3083927840296518090679249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111903787062024120905665 3083927840296518090679249)
                    ·
                      refine ⟨2312945880222388568009437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083927840296518090679249 2312945880222388568009437)
                      ·
                        rfl

theorem cell23_4504446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4504446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504446 prefixEnd_4504446 := by exact prefixLift 4504446
  have htrace : WordTrace (prefixWord ++ tailWord_4504446) baseStart_4504446 baseEnd_4504446 := by
    simpa [prefixWord, tailWord_4504446, baseEnd_4504446] using wordTrace_append hprefix tailTrace_4504446
  have hstable : (prefixWord ++ tailWord_4504446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504446).length < 2 ^ (prefixWord ++ tailWord_4504446).sum := by decide
  have hdescent : baseEnd_4504446 < baseStart_4504446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504447 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_4504447 : Nat := 118140960795 + 4504447 * 2 ^ 59
def prefixEnd_4504447 : Nat := 4983230072969 + 3 ^ 40 * 4504447 * 2
def baseEnd_4504447 : Nat := 2312946393703043064096931

theorem tailTrace_4504447 : CollatzResearch.WordTrace tailWord_4504447 prefixEnd_4504447 2312946393703043064096931 := by
  unfold tailWord_4504447
  simp only [CollatzResearch.WordTrace]
  refine ⟨164290679112165292145743595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109527119408110194763829063 164290679112165292145743595)
  ·
    refine ⟨246436018668247938218615393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164290679112165292145743595 246436018668247938218615393)
    ·
      refine ⟨184827014001185953663961545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246436018668247938218615393 184827014001185953663961545)
      ·
        refine ⟨138620260500889465247971159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184827014001185953663961545 138620260500889465247971159)
        ·
          refine ⟨207930390751334197871956739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138620260500889465247971159 207930390751334197871956739)
          ·
            refine ⟨311895586127001296807935109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207930390751334197871956739 311895586127001296807935109)
            ·
              refine ⟨58480422398812743151487833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 311895586127001296807935109 58480422398812743151487833)
              ·
                refine ⟨43860316799109557363615875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58480422398812743151487833 43860316799109557363615875)
                ·
                  refine ⟨65790475198664336045423813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43860316799109557363615875 65790475198664336045423813)
                  ·
                    refine ⟨12335714099749563008516965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65790475198664336045423813 12335714099749563008516965)
                    ·
                      refine ⟨2312946393703043064096931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12335714099749563008516965 2312946393703043064096931)
                      ·
                        rfl

theorem cell23_4504447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_4504447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504447 prefixEnd_4504447 := by exact prefixLift 4504447
  have htrace : WordTrace (prefixWord ++ tailWord_4504447) baseStart_4504447 baseEnd_4504447 := by
    simpa [prefixWord, tailWord_4504447, baseEnd_4504447] using wordTrace_append hprefix tailTrace_4504447
  have hstable : (prefixWord ++ tailWord_4504447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504447).length < 2 ^ (prefixWord ++ tailWord_4504447).sum := by decide
  have hdescent : baseEnd_4504447 < baseStart_4504447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504451 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 6, 2, 2]
def baseStart_4504451 : Nat := 118140960795 + 4504451 * 2 ^ 59
def prefixEnd_4504451 : Nat := 4983230072969 + 3 ^ 40 * 4504451 * 2
def baseEnd_4504451 : Nat := 2312948447625661048446913

theorem tailTrace_4504451 : CollatzResearch.WordTrace tailWord_4504451 prefixEnd_4504451 2312948447625661048446913 := by
  unfold tailWord_4504451
  simp only [CollatzResearch.WordTrace]
  refine ⟨164290825004150800828889207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109527216669433867219259471 164290825004150800828889207)
  ·
    refine ⟨246436237506226201243333811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164290825004150800828889207 246436237506226201243333811)
    ·
      refine ⟨369654356259339301865000717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246436237506226201243333811 369654356259339301865000717)
      ·
        refine ⟨138620383597252238199375269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369654356259339301865000717 138620383597252238199375269)
        ·
          refine ⟨25991321924484794662382863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138620383597252238199375269 25991321924484794662382863)
          ·
            refine ⟨38986982886727191993574295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25991321924484794662382863 38986982886727191993574295)
            ·
              refine ⟨58480474330090787990361443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38986982886727191993574295 58480474330090787990361443)
              ·
                refine ⟨87720711495136181985542165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58480474330090787990361443 87720711495136181985542165)
                ·
                  refine ⟨4111908351334508530572289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87720711495136181985542165 4111908351334508530572289)
                  ·
                    refine ⟨3083931263500881397929217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111908351334508530572289 3083931263500881397929217)
                    ·
                      refine ⟨2312948447625661048446913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083931263500881397929217 2312948447625661048446913)
                      ·
                        rfl

theorem cell23_4504451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_4504451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504451 prefixEnd_4504451 := by exact prefixLift 4504451
  have htrace : WordTrace (prefixWord ++ tailWord_4504451) baseStart_4504451 baseEnd_4504451 := by
    simpa [prefixWord, tailWord_4504451, baseEnd_4504451] using wordTrace_append hprefix tailTrace_4504451
  have hstable : (prefixWord ++ tailWord_4504451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504451).length < 2 ^ (prefixWord ++ tailWord_4504451).sum := by decide
  have hdescent : baseEnd_4504451 < baseStart_4504451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504468 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_4504468 : Nat := 118140960795 + 4504468 * 2 ^ 59
def prefixEnd_4504468 : Nat := 4983230072969 + 3 ^ 40 * 4504468 * 2
def baseEnd_4504468 : Nat := 2312957176796787481934335

theorem tailTrace_4504468 : CollatzResearch.WordTrace tailWord_4504468 prefixEnd_4504468 2312957176796787481934335 := by
  unfold tailWord_4504468
  simp only [CollatzResearch.WordTrace]
  refine ⟨82145722522544606366129029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109527630030059475154838705 82145722522544606366129029)
  ·
    refine ⟨15402322972977113693649193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82145722522544606366129029 15402322972977113693649193)
    ·
      refine ⟨11551742229732835270236895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15402322972977113693649193 11551742229732835270236895)
      ·
        refine ⟨17327613344599252905355343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11551742229732835270236895 17327613344599252905355343)
        ·
          refine ⟨25991420016898879358033015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17327613344599252905355343 25991420016898879358033015)
          ·
            refine ⟨38987130025348319037049523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25991420016898879358033015 38987130025348319037049523)
            ·
              refine ⟨58480695038022478555574285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38987130025348319037049523 58480695038022478555574285)
              ·
                refine ⟨21930260639258429458340357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58480695038022478555574285 21930260639258429458340357)
                ·
                  refine ⟨4111923869860955523438817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21930260639258429458340357 4111923869860955523438817)
                  ·
                    refine ⟨3083942902395716642579113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4111923869860955523438817 3083942902395716642579113)
                    ·
                      refine ⟨2312957176796787481934335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3083942902395716642579113 2312957176796787481934335)
                      ·
                        rfl

theorem cell23_4504468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_4504468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504468 prefixEnd_4504468 := by exact prefixLift 4504468
  have htrace : WordTrace (prefixWord ++ tailWord_4504468) baseStart_4504468 baseEnd_4504468 := by
    simpa [prefixWord, tailWord_4504468, baseEnd_4504468] using wordTrace_append hprefix tailTrace_4504468
  have hstable : (prefixWord ++ tailWord_4504468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504468).length < 2 ^ (prefixWord ++ tailWord_4504468).sum := by decide
  have hdescent : baseEnd_4504468 < baseStart_4504468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504484 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_4504484 : Nat := 118140960795 + 4504484 * 2 ^ 59
def prefixEnd_4504484 : Nat := 4983230072969 + 3 ^ 40 * 4504484 * 2
def baseEnd_4504484 : Nat := 2312965392487259419334261

theorem tailTrace_4504484 : CollatzResearch.WordTrace tailWord_4504484 prefixEnd_4504484 2312965392487259419334261 := by
  unfold tailWord_4504484
  simp only [CollatzResearch.WordTrace]
  refine ⟨82146014306515623732420253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109528019075354164976560337 82146014306515623732420253)
  ·
    refine ⟨30804755364943358899657595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82146014306515623732420253 30804755364943358899657595)
    ·
      refine ⟨46207133047415038349486393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30804755364943358899657595 46207133047415038349486393)
      ·
        refine ⟨34655349785561278762114795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46207133047415038349486393 34655349785561278762114795)
        ·
          refine ⟨51983024678341918143172193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34655349785561278762114795 51983024678341918143172193)
          ·
            refine ⟨38987268508756438607379145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51983024678341918143172193 38987268508756438607379145)
            ·
              refine ⟨29240451381567328955534359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38987268508756438607379145 29240451381567328955534359)
              ·
                refine ⟨43860677072350993433301539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29240451381567328955534359 43860677072350993433301539)
                ·
                  refine ⟨65791015608526490149952309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43860677072350993433301539 65791015608526490149952309)
                  ·
                    refine ⟨6167907713299358451558029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65791015608526490149952309 6167907713299358451558029)
                    ·
                      refine ⟨2312965392487259419334261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6167907713299358451558029 2312965392487259419334261)
                      ·
                        rfl

theorem cell23_4504484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_4504484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504484 prefixEnd_4504484 := by exact prefixLift 4504484
  have htrace : WordTrace (prefixWord ++ tailWord_4504484) baseStart_4504484 baseEnd_4504484 := by
    simpa [prefixWord, tailWord_4504484, baseEnd_4504484] using wordTrace_append hprefix tailTrace_4504484
  have hstable : (prefixWord ++ tailWord_4504484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504484).length < 2 ^ (prefixWord ++ tailWord_4504484).sum := by decide
  have hdescent : baseEnd_4504484 < baseStart_4504484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504504 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 2, 5]
def baseStart_4504504 : Nat := 118140960795 + 4504504 * 2 ^ 59
def prefixEnd_4504504 : Nat := 4983230072969 + 3 ^ 40 * 4504504 * 2
def baseEnd_4504504 : Nat := 770991887366783113694723

theorem tailTrace_4504504 : CollatzResearch.WordTrace tailWord_4504504 prefixEnd_4504504 770991887366783113694723 := by
  unfold tailWord_4504504
  simp only [CollatzResearch.WordTrace]
  refine ⟨82146379036479395440284283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109528505381972527253712377 82146379036479395440284283)
  ·
    refine ⟨123219568554719093160426425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82146379036479395440284283 123219568554719093160426425)
    ·
      refine ⟨92414676416039319870319819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123219568554719093160426425 92414676416039319870319819)
      ·
        refine ⟨138622014624058979805479729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92414676416039319870319819 138622014624058979805479729)
        ·
          refine ⟨103966510968044234854109797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138622014624058979805479729 103966510968044234854109797)
          ·
            refine ⟨19493720806508294035145587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103966510968044234854109797 19493720806508294035145587)
            ·
              refine ⟨29240581209762441052718381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19493720806508294035145587 29240581209762441052718381)
              ·
                refine ⟨10965217953660915394769393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29240581209762441052718381 10965217953660915394769393)
                ·
                  refine ⟨8223913465245686546077045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10965217953660915394769393 8223913465245686546077045)
                  ·
                    refine ⟨770991887366783113694723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8223913465245686546077045 770991887366783113694723)
                    ·
                      rfl

theorem cell23_4504504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_4504504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504504 prefixEnd_4504504 := by exact prefixLift 4504504
  have htrace : WordTrace (prefixWord ++ tailWord_4504504) baseStart_4504504 baseEnd_4504504 := by
    simpa [prefixWord, tailWord_4504504, baseEnd_4504504] using wordTrace_append hprefix tailTrace_4504504
  have hstable : (prefixWord ++ tailWord_4504504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504504).length < 2 ^ (prefixWord ++ tailWord_4504504).sum := by decide
  have hdescent : baseEnd_4504504 < baseStart_4504504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504517 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_4504517 : Nat := 118140960795 + 4504517 * 2 ^ 59
def prefixEnd_4504517 : Nat := 4983230072969 + 3 ^ 40 * 4504517 * 2
def baseEnd_4504517 : Nat := 770994112449619263407203

theorem tailTrace_4504517 : CollatzResearch.WordTrace tailWord_4504517 prefixEnd_4504517 770994112449619263407203 := by
  unfold tailWord_4504517
  simp only [CollatzResearch.WordTrace]
  refine ⟨164293232221911694100791805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109528821481274462733861203 164293232221911694100791805)
  ·
    refine ⟨61609962083216885287796927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164293232221911694100791805 61609962083216885287796927)
    ·
      refine ⟨92414943124825327931695391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61609962083216885287796927 92414943124825327931695391)
      ·
        refine ⟨138622414687237991897543087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92414943124825327931695391 138622414687237991897543087)
        ·
          refine ⟨207933622030856987846314631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138622414687237991897543087 207933622030856987846314631)
          ·
            refine ⟨311900433046285481769471947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207933622030856987846314631 311900433046285481769471947)
            ·
              refine ⟨467850649569428222654207921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311900433046285481769471947 467850649569428222654207921)
              ·
                refine ⟨350887987177071166990655941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467850649569428222654207921 350887987177071166990655941)
                ·
                  refine ⟨65791497595700843810747989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 350887987177071166990655941 65791497595700843810747989)
                  ·
                    refine ⟨770994112449619263407203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65791497595700843810747989 770994112449619263407203)
                    ·
                      rfl

theorem cell23_4504517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_4504517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504517 prefixEnd_4504517 := by exact prefixLift 4504517
  have htrace : WordTrace (prefixWord ++ tailWord_4504517) baseStart_4504517 baseEnd_4504517 := by
    simpa [prefixWord, tailWord_4504517, baseEnd_4504517] using wordTrace_append hprefix tailTrace_4504517
  have hstable : (prefixWord ++ tailWord_4504517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504517).length < 2 ^ (prefixWord ++ tailWord_4504517).sum := by decide
  have hdescent : baseEnd_4504517 < baseStart_4504517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504551 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 5, 4]
def baseStart_4504551 : Nat := 118140960795 + 4504551 * 2 ^ 59
def prefixEnd_4504551 : Nat := 4983230072969 + 3 ^ 40 * 4504551 * 2
def baseEnd_4504551 : Nat := 770999931897036885732151

theorem tailTrace_4504551 : CollatzResearch.WordTrace tailWord_4504551 prefixEnd_4504551 770999931897036885732151 := by
  unfold tailWord_4504551
  simp only [CollatzResearch.WordTrace]
  refine ⟨164294472303788517907529507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109529648202525678605019671 164294472303788517907529507)
  ·
    refine ⟨246441708455682776861294261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164294472303788517907529507 246441708455682776861294261)
    ·
      refine ⟨23103910167720260330746337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 246441708455682776861294261 23103910167720260330746337)
      ·
        refine ⟨17327932625790195248059753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23103910167720260330746337 17327932625790195248059753)
        ·
          refine ⟨12995949469342646436044815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17327932625790195248059753 12995949469342646436044815)
          ·
            refine ⟨19493924204013969654067223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12995949469342646436044815 19493924204013969654067223)
            ·
              refine ⟨29240886306020954481100835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19493924204013969654067223 29240886306020954481100835)
              ·
                refine ⟨43861329459031431721651253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29240886306020954481100835 43861329459031431721651253)
                ·
                  refine ⟨4111999636784196723904805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43861329459031431721651253 4111999636784196723904805)
                  ·
                    refine ⟨770999931897036885732151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4111999636784196723904805 770999931897036885732151)
                    ·
                      rfl

theorem cell23_4504551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_4504551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504551 prefixEnd_4504551 := by exact prefixLift 4504551
  have htrace : WordTrace (prefixWord ++ tailWord_4504551) baseStart_4504551 baseEnd_4504551 := by
    simpa [prefixWord, tailWord_4504551, baseEnd_4504551] using wordTrace_append hprefix tailTrace_4504551
  have hstable : (prefixWord ++ tailWord_4504551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504551).length < 2 ^ (prefixWord ++ tailWord_4504551).sum := by decide
  have hdescent : baseEnd_4504551 < baseStart_4504551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504561 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_4504561 : Nat := 118140960795 + 4504561 * 2 ^ 59
def prefixEnd_4504561 : Nat := 4983230072969 + 3 ^ 40 * 4504561 * 2
def baseEnd_4504561 : Nat := 2313004930497655618071407

theorem tailTrace_4504561 : CollatzResearch.WordTrace tailWord_4504561 prefixEnd_4504561 2313004930497655618071407 := by
  unfold tailWord_4504561
  simp only [CollatzResearch.WordTrace]
  refine ⟨164294837033752289615393537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109529891355834859743595691 164294837033752289615393537)
  ·
    refine ⟨123221127775314217211545153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164294837033752289615393537 123221127775314217211545153)
    ·
      refine ⟨92415845831485662908658865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123221127775314217211545153 92415845831485662908658865)
      ·
        refine ⟨69311884373614247181494149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92415845831485662908658865 69311884373614247181494149)
        ·
          refine ⟨12995978320052671346530153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69311884373614247181494149 12995978320052671346530153)
          ·
            refine ⟨9746983740039503509897615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12995978320052671346530153 9746983740039503509897615)
            ·
              refine ⟨14620475610059255264846423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9746983740039503509897615 14620475610059255264846423)
              ·
                refine ⟨21930713415088882897269635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14620475610059255264846423 21930713415088882897269635)
                ·
                  refine ⟨32896070122633324345904453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21930713415088882897269635 32896070122633324345904453)
                  ·
                    refine ⟨6168013147993748314857085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32896070122633324345904453 6168013147993748314857085)
                    ·
                      refine ⟨2313004930497655618071407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168013147993748314857085 2313004930497655618071407)
                      ·
                        rfl

theorem cell23_4504561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_4504561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504561 prefixEnd_4504561 := by exact prefixLift 4504561
  have htrace : WordTrace (prefixWord ++ tailWord_4504561) baseStart_4504561 baseEnd_4504561 := by
    simpa [prefixWord, tailWord_4504561, baseEnd_4504561] using wordTrace_append hprefix tailTrace_4504561
  have hstable : (prefixWord ++ tailWord_4504561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504561).length < 2 ^ (prefixWord ++ tailWord_4504561).sum := by decide
  have hdescent : baseEnd_4504561 < baseStart_4504561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504584 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_4504584 : Nat := 118140960795 + 4504584 * 2 ^ 59
def prefixEnd_4504584 : Nat := 4983230072969 + 3 ^ 40 * 4504584 * 2
def baseEnd_4504584 : Nat := 2313016740552709028083801

theorem tailTrace_4504584 : CollatzResearch.WordTrace tailWord_4504584 prefixEnd_4504584 2313016740552709028083801 := by
  unfold tailWord_4504584
  simp only [CollatzResearch.WordTrace]
  refine ⟨82147837956334482271740403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109530450608445976362320537 82147837956334482271740403)
  ·
    refine ⟨123221756934501723407610605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82147837956334482271740403 123221756934501723407610605)
    ·
      refine ⟨46208158850438146277853977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123221756934501723407610605 46208158850438146277853977)
      ·
        refine ⟨34656119137828609708390483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46208158850438146277853977 34656119137828609708390483)
        ·
          refine ⟨51984178706742914562585725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34656119137828609708390483 51984178706742914562585725)
          ·
            refine ⟨19494067015028592960969647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51984178706742914562585725 19494067015028592960969647)
            ·
              refine ⟨29241100522542889441454471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19494067015028592960969647 29241100522542889441454471)
              ·
                refine ⟨43861650783814334162181707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29241100522542889441454471 43861650783814334162181707)
                ·
                  refine ⟨65792476175721501243272561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43861650783814334162181707 65792476175721501243272561)
                  ·
                    refine ⟨49344357131791125932454421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65792476175721501243272561 49344357131791125932454421)
                    ·
                      refine ⟨2313016740552709028083801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49344357131791125932454421 2313016740552709028083801)
                      ·
                        rfl

theorem cell23_4504584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_4504584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504584 prefixEnd_4504584 := by exact prefixLift 4504584
  have htrace : WordTrace (prefixWord ++ tailWord_4504584) baseStart_4504584 baseEnd_4504584 := by
    simpa [prefixWord, tailWord_4504584, baseEnd_4504584] using wordTrace_append hprefix tailTrace_4504584
  have hstable : (prefixWord ++ tailWord_4504584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504584).length < 2 ^ (prefixWord ++ tailWord_4504584).sum := by decide
  have hdescent : baseEnd_4504584 < baseStart_4504584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504601 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 1, 5, 2]
def baseStart_4504601 : Nat := 118140960795 + 4504601 * 2 ^ 59
def prefixEnd_4504601 : Nat := 4983230072969 + 3 ^ 40 * 4504601 * 2
def baseEnd_4504601 : Nat := 2313025469723835461571223

theorem tailTrace_4504601 : CollatzResearch.WordTrace tailWord_4504601 prefixEnd_4504601 2313025469723835461571223 := by
  unfold tailWord_4504601
  simp only [CollatzResearch.WordTrace]
  refine ⟨164296295953607376446849657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109530863969071584297899771 164296295953607376446849657)
  ·
    refine ⟨123222221965205532335137243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164296295953607376446849657 123222221965205532335137243)
    ·
      refine ⟨184833332947808298502705865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123222221965205532335137243 184833332947808298502705865)
      ·
        refine ⟨138624999710856223877029399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184833332947808298502705865 138624999710856223877029399)
        ·
          refine ⟨207937499566284335815544099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138624999710856223877029399 207937499566284335815544099)
          ·
            refine ⟨311906249349426503723316149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207937499566284335815544099 311906249349426503723316149)
            ·
              refine ⟨29241210876508734724060889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 311906249349426503723316149 29241210876508734724060889)
              ·
                refine ⟨21930908157381551043045667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29241210876508734724060889 21930908157381551043045667)
                ·
                  refine ⟨32896362236072326564568501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21930908157381551043045667 32896362236072326564568501)
                  ·
                    refine ⟨3084033959631780615428297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32896362236072326564568501 3084033959631780615428297)
                    ·
                      refine ⟨2313025469723835461571223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084033959631780615428297 2313025469723835461571223)
                      ·
                        rfl

theorem cell23_4504601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_4504601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504601 prefixEnd_4504601 := by exact prefixLift 4504601
  have htrace : WordTrace (prefixWord ++ tailWord_4504601) baseStart_4504601 baseEnd_4504601 := by
    simpa [prefixWord, tailWord_4504601, baseEnd_4504601] using wordTrace_append hprefix tailTrace_4504601
  have hstable : (prefixWord ++ tailWord_4504601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504601).length < 2 ^ (prefixWord ++ tailWord_4504601).sum := by decide
  have hdescent : baseEnd_4504601 < baseStart_4504601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504611 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 1, 5]
def baseStart_4504611 : Nat := 118140960795 + 4504611 * 2 ^ 59
def prefixEnd_4504611 : Nat := 4983230072969 + 3 ^ 40 * 4504611 * 2
def baseEnd_4504611 : Nat := 771010201510126807482059

theorem tailTrace_4504611 : CollatzResearch.WordTrace tailWord_4504611 prefixEnd_4504611 771010201510126807482059 := by
  unfold tailWord_4504611
  simp only [CollatzResearch.WordTrace]
  refine ⟨164296660683571148154713687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109531107122380765436475791 164296660683571148154713687)
  ·
    refine ⟨246444991025356722232070531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164296660683571148154713687 246444991025356722232070531)
    ·
      refine ⟨369667486538035083348105797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246444991025356722232070531 369667486538035083348105797)
      ·
        refine ⟨69312653725881578127769837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 369667486538035083348105797 69312653725881578127769837)
        ·
          refine ⟨25992245147205591797913689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69312653725881578127769837 25992245147205591797913689)
          ·
            refine ⟨19494183860404193848435267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25992245147205591797913689 19494183860404193848435267)
            ·
              refine ⟨29241275790606290772652901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19494183860404193848435267 29241275790606290772652901)
              ·
                refine ⟨5482739210738679519872419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29241275790606290772652901 5482739210738679519872419)
                ·
                  refine ⟨8224108816108019279808629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5482739210738679519872419 8224108816108019279808629)
                  ·
                    refine ⟨771010201510126807482059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8224108816108019279808629 771010201510126807482059)
                    ·
                      rfl

theorem cell23_4504611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 5].length) (baseStart_4504611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504611 prefixEnd_4504611 := by exact prefixLift 4504611
  have htrace : WordTrace (prefixWord ++ tailWord_4504611) baseStart_4504611 baseEnd_4504611 := by
    simpa [prefixWord, tailWord_4504611, baseEnd_4504611] using wordTrace_append hprefix tailTrace_4504611
  have hstable : (prefixWord ++ tailWord_4504611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504611).length < 2 ^ (prefixWord ++ tailWord_4504611).sum := by decide
  have hdescent : baseEnd_4504611 < baseStart_4504611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504624 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 3, 6]
def baseStart_4504624 : Nat := 118140960795 + 4504624 * 2 ^ 59
def prefixEnd_4504624 : Nat := 4983230072969 + 3 ^ 40 * 4504624 * 2
def baseEnd_4504624 : Nat := 771012426592962957194539

theorem tailTrace_4504624 : CollatzResearch.WordTrace tailWord_4504624 prefixEnd_4504624 771012426592962957194539 := by
  unfold tailWord_4504624
  simp only [CollatzResearch.WordTrace]
  refine ⟨82148567416262025687468463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109531423221682700916624617 82148567416262025687468463)
  ·
    refine ⟨123222851124393038531202695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82148567416262025687468463 123222851124393038531202695)
    ·
      refine ⟨184834276686589557796804043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123222851124393038531202695 184834276686589557796804043)
      ·
        refine ⟨277251415029884336695206065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184834276686589557796804043 277251415029884336695206065)
        ·
          refine ⟨207938561272413252521404549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277251415029884336695206065 207938561272413252521404549)
          ·
            refine ⟨38988480238577484847763353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207938561272413252521404549 38988480238577484847763353)
            ·
              refine ⟨29241360178933113635822515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38988480238577484847763353 29241360178933113635822515)
              ·
                refine ⟨43862040268399670453733773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29241360178933113635822515 43862040268399670453733773)
                ·
                  refine ⟨16448265100649876420150165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43862040268399670453733773 16448265100649876420150165)
                  ·
                    refine ⟨771012426592962957194539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16448265100649876420150165 771012426592962957194539)
                    ·
                      rfl

theorem cell23_4504624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_4504624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504624 prefixEnd_4504624 := by exact prefixLift 4504624
  have htrace : WordTrace (prefixWord ++ tailWord_4504624) baseStart_4504624 baseEnd_4504624 := by
    simpa [prefixWord, tailWord_4504624, baseEnd_4504624] using wordTrace_append hprefix tailTrace_4504624
  have hstable : (prefixWord ++ tailWord_4504624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504624).length < 2 ^ (prefixWord ++ tailWord_4504624).sum := by decide
  have hdescent : baseEnd_4504624 < baseStart_4504624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504661 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4504661 : Nat := 118140960795 + 4504661 * 2 ^ 59
def prefixEnd_4504661 : Nat := 4983230072969 + 3 ^ 40 * 4504661 * 2
def baseEnd_4504661 : Nat := 2313056278563105226820947

theorem tailTrace_4504661 : CollatzResearch.WordTrace tailWord_4504661 prefixEnd_4504661 2313056278563105226820947 := by
  unfold tailWord_4504661
  simp only [CollatzResearch.WordTrace]
  refine ⟨164298484333390006694033837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109532322888926671129355891 164298484333390006694033837)
  ·
    refine ⟨61611931625021252510262689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164298484333390006694033837 61611931625021252510262689)
    ·
      refine ⟨46208948718765939382697017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61611931625021252510262689 46208948718765939382697017)
      ·
        refine ⟨34656711539074454537022763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46208948718765939382697017 34656711539074454537022763)
        ·
          refine ⟨51985067308611681805534145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34656711539074454537022763 51985067308611681805534145)
          ·
            refine ⟨38988800481458761354150609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51985067308611681805534145 38988800481458761354150609)
            ·
              refine ⟨29241600361094071015612957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38988800481458761354150609 29241600361094071015612957)
              ·
                refine ⟨10965600135410276630854859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29241600361094071015612957 10965600135410276630854859)
                ·
                  refine ⟨16448400203115414946282289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10965600135410276630854859 16448400203115414946282289)
                  ·
                    refine ⟨12336300152336561209711717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16448400203115414946282289 12336300152336561209711717)
                    ·
                      refine ⟨2313056278563105226820947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12336300152336561209711717 2313056278563105226820947)
                      ·
                        rfl

theorem cell23_4504661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4504661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504661 prefixEnd_4504661 := by exact prefixLift 4504661
  have htrace : WordTrace (prefixWord ++ tailWord_4504661) baseStart_4504661 baseEnd_4504661 := by
    simpa [prefixWord, tailWord_4504661, baseEnd_4504661] using wordTrace_append hprefix tailTrace_4504661
  have hstable : (prefixWord ++ tailWord_4504661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504661).length < 2 ^ (prefixWord ++ tailWord_4504661).sum := by decide
  have hdescent : baseEnd_4504661 < baseStart_4504661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504668 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_4504668 : Nat := 118140960795 + 4504668 * 2 ^ 59
def prefixEnd_4504668 : Nat := 4983230072969 + 3 ^ 40 * 4504668 * 2
def baseEnd_4504668 : Nat := 2313059872927686699433415

theorem tailTrace_4504668 : CollatzResearch.WordTrace tailWord_4504668 prefixEnd_4504668 2313059872927686699433415 := by
  unfold tailWord_4504668
  simp only [CollatzResearch.WordTrace]
  refine ⟨82149369822182323444769329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109532493096243097926359105 82149369822182323444769329)
  ·
    refine ⟨61612027366636742583576997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82149369822182323444769329 61612027366636742583576997)
    ·
      refine ⟨11552255131244389234420687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61612027366636742583576997 11552255131244389234420687)
      ·
        refine ⟨17328382696866583851631031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11552255131244389234420687 17328382696866583851631031)
        ·
          refine ⟨25992574045299875777446547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17328382696866583851631031 25992574045299875777446547)
          ·
            refine ⟨38988861067949813666169821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25992574045299875777446547 38988861067949813666169821)
            ·
              refine ⟨14620822900481180124813683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38988861067949813666169821 14620822900481180124813683)
              ·
                refine ⟨21931234350721770187220525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14620822900481180124813683 21931234350721770187220525)
                ·
                  refine ⟨8224212881520663820207697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21931234350721770187220525 8224212881520663820207697)
                  ·
                    refine ⟨6168159661140497865155773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8224212881520663820207697 6168159661140497865155773)
                    ·
                      refine ⟨2313059872927686699433415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168159661140497865155773 2313059872927686699433415)
                      ·
                        rfl

theorem cell23_4504668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_4504668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504668 prefixEnd_4504668 := by exact prefixLift 4504668
  have htrace : WordTrace (prefixWord ++ tailWord_4504668) baseStart_4504668 baseEnd_4504668 := by
    simpa [prefixWord, tailWord_4504668, baseEnd_4504668] using wordTrace_append hprefix tailTrace_4504668
  have hstable : (prefixWord ++ tailWord_4504668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504668).length < 2 ^ (prefixWord ++ tailWord_4504668).sum := by decide
  have hdescent : baseEnd_4504668 < baseStart_4504668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504681 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 3]
def baseStart_4504681 : Nat := 118140960795 + 4504681 * 2 ^ 59
def prefixEnd_4504681 : Nat := 4983230072969 + 3 ^ 40 * 4504681 * 2
def baseEnd_4504681 : Nat := 2313066548176195148570855

theorem tailTrace_4504681 : CollatzResearch.WordTrace tailWord_4504681 prefixEnd_4504681 2313066548176195148570855 := by
  unfold tailWord_4504681
  simp only [CollatzResearch.WordTrace]
  refine ⟨164299213793317550109761897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109532809195545033406507931 164299213793317550109761897)
  ·
    refine ⟨123224410344988162582321423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164299213793317550109761897 123224410344988162582321423)
    ·
      refine ⟨184836615517482243873482135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123224410344988162582321423 184836615517482243873482135)
      ·
        refine ⟨277254923276223365810223203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184836615517482243873482135 277254923276223365810223203)
        ·
          refine ⟨415882384914335048715334805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277254923276223365810223203 415882384914335048715334805)
          ·
            refine ⟨19494486792859455408531319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 415882384914335048715334805 19494486792859455408531319)
            ·
              refine ⟨29241730189289183112796979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19494486792859455408531319 29241730189289183112796979)
              ·
                refine ⟨43862595283933774669195469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29241730189289183112796979 43862595283933774669195469)
                ·
                  refine ⟨16448473231475165500948301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43862595283933774669195469 16448473231475165500948301)
                  ·
                    refine ⟨6168177461803187062855613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16448473231475165500948301 6168177461803187062855613)
                    ·
                      refine ⟨2313066548176195148570855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168177461803187062855613 2313066548176195148570855)
                      ·
                        rfl

theorem cell23_4504681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_4504681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504681 prefixEnd_4504681 := by exact prefixLift 4504681
  have htrace : WordTrace (prefixWord ++ tailWord_4504681) baseStart_4504681 baseEnd_4504681 := by
    simpa [prefixWord, tailWord_4504681, baseEnd_4504681] using wordTrace_append hprefix tailTrace_4504681
  have hstable : (prefixWord ++ tailWord_4504681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504681).length < 2 ^ (prefixWord ++ tailWord_4504681).sum := by decide
  have hdescent : baseEnd_4504681 < baseStart_4504681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504693 : List Nat := [1, 3, 4, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4504693 : Nat := 118140960795 + 4504693 * 2 ^ 59
def prefixEnd_4504693 : Nat := 4983230072969 + 3 ^ 40 * 4504693 * 2
def baseEnd_4504693 : Nat := 2313072709944049101620801

theorem tailTrace_4504693 : CollatzResearch.WordTrace tailWord_4504693 prefixEnd_4504693 2313072709944049101620801 := by
  unfold tailWord_4504693
  simp only [CollatzResearch.WordTrace]
  refine ⟨164299651469274076159198733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109533100979516050772799155 164299651469274076159198733)
  ·
    refine ⟨61612369300977778559699525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164299651469274076159198733 61612369300977778559699525)
    ·
      refine ⟨11552319243933333479943661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61612369300977778559699525 11552319243933333479943661)
      ·
        refine ⟨4332119716475000054978873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11552319243933333479943661 4332119716475000054978873)
        ·
          refine ⟨3249089787356250041234155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4332119716475000054978873 3249089787356250041234155)
          ·
            refine ⟨4873634681034375061851233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249089787356250041234155 4873634681034375061851233)
            ·
              refine ⟨3655226010775781296388425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4873634681034375061851233 3655226010775781296388425)
              ·
                refine ⟨2741419508081835972291319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655226010775781296388425 2741419508081835972291319)
                ·
                  refine ⟨4112129262122753958436979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741419508081835972291319 4112129262122753958436979)
                  ·
                    refine ⟨6168193893184130937655469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4112129262122753958436979 6168193893184130937655469)
                    ·
                      refine ⟨2313072709944049101620801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168193893184130937655469 2313072709944049101620801)
                      ·
                        rfl

theorem cell23_4504693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4504693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504693 prefixEnd_4504693 := by exact prefixLift 4504693
  have htrace : WordTrace (prefixWord ++ tailWord_4504693) baseStart_4504693 baseEnd_4504693 := by
    simpa [prefixWord, tailWord_4504693, baseEnd_4504693] using wordTrace_append hprefix tailTrace_4504693
  have hstable : (prefixWord ++ tailWord_4504693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504693).length < 2 ^ (prefixWord ++ tailWord_4504693).sum := by decide
  have hdescent : baseEnd_4504693 < baseStart_4504693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504749 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_4504749 : Nat := 118140960795 + 4504749 * 2 ^ 59
def prefixEnd_4504749 : Nat := 4983230072969 + 3 ^ 40 * 4504749 * 2
def baseEnd_4504749 : Nat := 2313101464860700882520543

theorem tailTrace_4504749 : CollatzResearch.WordTrace tailWord_4504749 prefixEnd_4504749 2313101464860700882520543 := by
  unfold tailWord_4504749
  simp only [CollatzResearch.WordTrace]
  refine ⟨164301693957071197723237301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109534462638047465148824867 164301693957071197723237301)
  ·
    refine ⟨15403283808475424786553497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 164301693957071197723237301 15403283808475424786553497)
    ·
      refine ⟨11552462856356568589915123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15403283808475424786553497 11552462856356568589915123)
      ·
        refine ⟨17328694284534852884872685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11552462856356568589915123 17328694284534852884872685)
        ·
          refine ⟨6498260356700569831827257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17328694284534852884872685 6498260356700569831827257)
          ·
            refine ⟨4873695267525427373870443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6498260356700569831827257 4873695267525427373870443)
            ·
              refine ⟨7310542901288141060805665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4873695267525427373870443 7310542901288141060805665)
              ·
                refine ⟨5482907175966105795604249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7310542901288141060805665 5482907175966105795604249)
                ·
                  refine ⟨4112180381974579346703187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5482907175966105795604249 4112180381974579346703187)
                  ·
                    refine ⟨6168270572961869020054781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4112180381974579346703187 6168270572961869020054781)
                    ·
                      refine ⟨2313101464860700882520543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168270572961869020054781 2313101464860700882520543)
                      ·
                        rfl

theorem cell23_4504749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_4504749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504749 prefixEnd_4504749 := by exact prefixLift 4504749
  have htrace : WordTrace (prefixWord ++ tailWord_4504749) baseStart_4504749 baseEnd_4504749 := by
    simpa [prefixWord, tailWord_4504749, baseEnd_4504749] using wordTrace_append hprefix tailTrace_4504749
  have hstable : (prefixWord ++ tailWord_4504749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504749).length < 2 ^ (prefixWord ++ tailWord_4504749).sum := by decide
  have hdescent : baseEnd_4504749 < baseStart_4504749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504751 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_4504751 : Nat := 118140960795 + 4504751 * 2 ^ 59
def prefixEnd_4504751 : Nat := 4983230072969 + 3 ^ 40 * 4504751 * 2
def baseEnd_4504751 : Nat := 2313102491822009874695533

theorem tailTrace_4504751 : CollatzResearch.WordTrace tailWord_4504751 prefixEnd_4504751 2313102491822009874695533 := by
  unfold tailWord_4504751
  simp only [CollatzResearch.WordTrace]
  refine ⟨164301766903063952064810107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109534511268709301376540071 164301766903063952064810107)
  ·
    refine ⟨246452650354595928097215161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164301766903063952064810107 246452650354595928097215161)
    ·
      refine ⟨184839487765946946072911371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246452650354595928097215161 184839487765946946072911371)
      ·
        refine ⟨277259231648920419109367057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184839487765946946072911371 277259231648920419109367057)
        ·
          refine ⟨207944423736690314332025293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277259231648920419109367057 207944423736690314332025293)
          ·
            refine ⟨77979158901258867874509485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207944423736690314332025293 77979158901258867874509485)
            ·
              refine ⟨29242184587972075452941057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77979158901258867874509485 29242184587972075452941057)
              ·
                refine ⟨21931638440979056589705793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29242184587972075452941057 21931638440979056589705793)
                ·
                  refine ⟨16448728830734292442279345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21931638440979056589705793 16448728830734292442279345)
                  ·
                    refine ⟨12336546623050719331709509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16448728830734292442279345 12336546623050719331709509)
                    ·
                      refine ⟨2313102491822009874695533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12336546623050719331709509 2313102491822009874695533)
                      ·
                        rfl

theorem cell23_4504751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_4504751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504751 prefixEnd_4504751 := by exact prefixLift 4504751
  have htrace : WordTrace (prefixWord ++ tailWord_4504751) baseStart_4504751 baseEnd_4504751 := by
    simpa [prefixWord, tailWord_4504751, baseEnd_4504751] using wordTrace_append hprefix tailTrace_4504751
  have hstable : (prefixWord ++ tailWord_4504751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504751).length < 2 ^ (prefixWord ++ tailWord_4504751).sum := by decide
  have hdescent : baseEnd_4504751 < baseStart_4504751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504761 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 7]
def baseStart_4504761 : Nat := 118140960795 + 4504761 * 2 ^ 59
def prefixEnd_4504761 : Nat := 4983230072969 + 3 ^ 40 * 4504761 * 2
def baseEnd_4504761 : Nat := 257011958514283870618943

theorem tailTrace_4504761 : CollatzResearch.WordTrace tailWord_4504761 prefixEnd_4504761 257011958514283870618943 := by
  unfold tailWord_4504761
  simp only [CollatzResearch.WordTrace]
  refine ⟨164302131633027723772674137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109534754422018482515116091 164302131633027723772674137)
  ·
    refine ⟨123226598724770792829505603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164302131633027723772674137 123226598724770792829505603)
    ·
      refine ⟨184839898087156189244258405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123226598724770792829505603 184839898087156189244258405)
      ·
        refine ⟨34657480891341785483298451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184839898087156189244258405 34657480891341785483298451)
        ·
          refine ⟨51986221337012678224947677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34657480891341785483298451 51986221337012678224947677)
          ·
            refine ⟨19494833001379754334355379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51986221337012678224947677 19494833001379754334355379)
            ·
              refine ⟨29242249502069631501533069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19494833001379754334355379 29242249502069631501533069)
              ·
                refine ⟨10965843563276111813074901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29242249502069631501533069 10965843563276111813074901)
                ·
                  refine ⟨257011958514283870618943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10965843563276111813074901 257011958514283870618943)
                  ·
                    rfl

theorem cell23_4504761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_4504761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504761 prefixEnd_4504761 := by exact prefixLift 4504761
  have htrace : WordTrace (prefixWord ++ tailWord_4504761) baseStart_4504761 baseEnd_4504761 := by
    simpa [prefixWord, tailWord_4504761, baseEnd_4504761] using wordTrace_append hprefix tailTrace_4504761
  have hstable : (prefixWord ++ tailWord_4504761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504761).length < 2 ^ (prefixWord ++ tailWord_4504761).sum := by decide
  have hdescent : baseEnd_4504761 < baseStart_4504761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504771 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 3]
def baseStart_4504771 : Nat := 118140960795 + 4504771 * 2 ^ 59
def prefixEnd_4504771 : Nat := 4983230072969 + 3 ^ 40 * 4504771 * 2
def baseEnd_4504771 : Nat := 2313112761435099796445441

theorem tailTrace_4504771 : CollatzResearch.WordTrace tailWord_4504771 prefixEnd_4504771 2313112761435099796445441 := by
  unfold tailWord_4504771
  simp only [CollatzResearch.WordTrace]
  refine ⟨164302496362991495480538167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109534997575327663653692111 164302496362991495480538167)
  ·
    refine ⟨246453744544487243220807251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164302496362991495480538167 246453744544487243220807251)
    ·
      refine ⟨369680616816730864831210877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246453744544487243220807251 369680616816730864831210877)
      ·
        refine ⟨138630231306274074311704079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369680616816730864831210877 138630231306274074311704079)
        ·
          refine ⟨207945346959411111467556119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138630231306274074311704079 207945346959411111467556119)
          ·
            refine ⟨311918020439116667201334179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207945346959411111467556119 311918020439116667201334179)
            ·
              refine ⟨467877030658675000802001269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311918020439116667201334179 467877030658675000802001269)
              ·
                refine ⟨43863471624250781325187619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 467877030658675000802001269 43863471624250781325187619)
                ·
                  refine ⟨65795207436376171987781429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43863471624250781325187619 65795207436376171987781429)
                  ·
                    refine ⟨6168300697160266123854509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65795207436376171987781429 6168300697160266123854509)
                    ·
                      refine ⟨2313112761435099796445441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168300697160266123854509 2313112761435099796445441)
                      ·
                        rfl

theorem cell23_4504771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_4504771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504771 prefixEnd_4504771 := by exact prefixLift 4504771
  have htrace : WordTrace (prefixWord ++ tailWord_4504771) baseStart_4504771 baseEnd_4504771 := by
    simpa [prefixWord, tailWord_4504771, baseEnd_4504771] using wordTrace_append hprefix tailTrace_4504771
  have hstable : (prefixWord ++ tailWord_4504771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504771).length < 2 ^ (prefixWord ++ tailWord_4504771).sum := by decide
  have hdescent : baseEnd_4504771 < baseStart_4504771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504791 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 1, 7]
def baseStart_4504791 : Nat := 118140960795 + 4504791 * 2 ^ 59
def prefixEnd_4504791 : Nat := 4983230072969 + 3 ^ 40 * 4504791 * 2
def baseEnd_4504791 : Nat := 771041010349396572731783

theorem tailTrace_4504791 : CollatzResearch.WordTrace tailWord_4504791 prefixEnd_4504791 771041010349396572731783 := by
  unfold tailWord_4504791
  simp only [CollatzResearch.WordTrace]
  refine ⟨164303225822919038896266227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109535483881946025930844151 164303225822919038896266227)
  ·
    refine ⟨246454838734378558344399341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164303225822919038896266227 246454838734378558344399341)
    ·
      refine ⟨92420564525391959379149753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246454838734378558344399341 92420564525391959379149753)
      ·
        refine ⟨69315423394043969534362315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92420564525391959379149753 69315423394043969534362315)
        ·
          refine ⟨103973135091065954301543473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69315423394043969534362315 103973135091065954301543473)
          ·
            refine ⟨77979851318299465726157605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103973135091065954301543473 77979851318299465726157605)
            ·
              refine ⟨14621222122181149823654551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77979851318299465726157605 14621222122181149823654551)
              ·
                refine ⟨21931833183271724735481827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14621222122181149823654551 21931833183271724735481827)
                ·
                  refine ⟨32897749774907587103222741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21931833183271724735481827 32897749774907587103222741)
                  ·
                    refine ⟨771041010349396572731783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32897749774907587103222741 771041010349396572731783)
                    ·
                      rfl

theorem cell23_4504791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_4504791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504791 prefixEnd_4504791 := by exact prefixLift 4504791
  have htrace : WordTrace (prefixWord ++ tailWord_4504791) baseStart_4504791 baseEnd_4504791 := by
    simpa [prefixWord, tailWord_4504791, baseEnd_4504791] using wordTrace_append hprefix tailTrace_4504791
  have hstable : (prefixWord ++ tailWord_4504791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504791).length < 2 ^ (prefixWord ++ tailWord_4504791).sum := by decide
  have hdescent : baseEnd_4504791 < baseStart_4504791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504808 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 2, 5]
def baseStart_4504808 : Nat := 118140960795 + 4504808 * 2 ^ 59
def prefixEnd_4504808 : Nat := 4983230072969 + 3 ^ 40 * 4504808 * 2
def baseEnd_4504808 : Nat := 771043920073105383894257

theorem tailTrace_4504808 : CollatzResearch.WordTrace tailWord_4504808 prefixEnd_4504808 771043920073105383894257 := by
  unfold tailWord_4504808
  simp only [CollatzResearch.WordTrace]
  refine ⟨82151922931928725399817539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109535897242571633866423385 82151922931928725399817539)
  ·
    refine ⟨123227884397893088099726309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82151922931928725399817539 123227884397893088099726309)
    ·
      refine ⟨23105228324604954018698683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123227884397893088099726309 23105228324604954018698683)
      ·
        refine ⟨34657842486907431028048025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23105228324604954018698683 34657842486907431028048025)
        ·
          refine ⟨25993381865180573271036019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34657842486907431028048025 25993381865180573271036019)
          ·
            refine ⟨38990072797770859906554029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25993381865180573271036019 38990072797770859906554029)
            ·
              refine ⟨14621277299164072464957761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38990072797770859906554029 14621277299164072464957761)
              ·
                refine ⟨10965957974373054348718321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14621277299164072464957761 10965957974373054348718321)
                ·
                  refine ⟨8224468480779790761538741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10965957974373054348718321 8224468480779790761538741)
                  ·
                    refine ⟨771043920073105383894257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8224468480779790761538741 771043920073105383894257)
                    ·
                      rfl

theorem cell23_4504808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_4504808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504808 prefixEnd_4504808 := by exact prefixLift 4504808
  have htrace : WordTrace (prefixWord ++ tailWord_4504808) baseStart_4504808 baseEnd_4504808 := by
    simpa [prefixWord, tailWord_4504808, baseEnd_4504808] using wordTrace_append hprefix tailTrace_4504808
  have hstable : (prefixWord ++ tailWord_4504808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504808).length < 2 ^ (prefixWord ++ tailWord_4504808).sum := by decide
  have hdescent : baseEnd_4504808 < baseStart_4504808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504891 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5]
def baseStart_4504891 : Nat := 118140960795 + 4504891 * 2 ^ 59
def prefixEnd_4504891 : Nat := 4983230072969 + 3 ^ 40 * 4504891 * 2
def baseEnd_4504891 : Nat := 2313174379113639326944889

theorem tailTrace_4504891 : CollatzResearch.WordTrace tailWord_4504891 prefixEnd_4504891 2313174379113639326944889 := by
  unfold tailWord_4504891
  simp only [CollatzResearch.WordTrace]
  refine ⟨164306873122556755974906527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109537915415037837316604351 164306873122556755974906527)
  ·
    refine ⟨246460309683835133962359791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164306873122556755974906527 246460309683835133962359791)
    ·
      refine ⟨369690464525752700943539687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246460309683835133962359791 369690464525752700943539687)
      ·
        refine ⟨554535696788629051415309531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369690464525752700943539687 554535696788629051415309531)
        ·
          refine ⟨831803545182943577122964297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554535696788629051415309531 831803545182943577122964297)
          ·
            refine ⟨623852658887207682842223223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831803545182943577122964297 623852658887207682842223223)
            ·
              refine ⟨935778988330811524263334835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623852658887207682842223223 935778988330811524263334835)
              ·
                refine ⟨1403668482496217286395002253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935778988330811524263334835 1403668482496217286395002253)
                ·
                  refine ⟨526375680936081482398125845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1403668482496217286395002253 526375680936081482398125845)
                  ·
                    refine ⟨24673860043878819487412149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 526375680936081482398125845 24673860043878819487412149)
                    ·
                      refine ⟨2313174379113639326944889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24673860043878819487412149 2313174379113639326944889)
                      ·
                        rfl

theorem cell23_4504891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_4504891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504891 prefixEnd_4504891 := by exact prefixLift 4504891
  have htrace : WordTrace (prefixWord ++ tailWord_4504891) baseStart_4504891 baseEnd_4504891 := by
    simpa [prefixWord, tailWord_4504891, baseEnd_4504891] using wordTrace_append hprefix tailTrace_4504891
  have hstable : (prefixWord ++ tailWord_4504891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504891).length < 2 ^ (prefixWord ++ tailWord_4504891).sum := by decide
  have hdescent : baseEnd_4504891 < baseStart_4504891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504895 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 3]
def baseStart_4504895 : Nat := 118140960795 + 4504895 * 2 ^ 59
def prefixEnd_4504895 : Nat := 4983230072969 + 3 ^ 40 * 4504895 * 2
def baseEnd_4504895 : Nat := 2313176433036257311294871

theorem tailTrace_4504895 : CollatzResearch.WordTrace tailWord_4504895 prefixEnd_4504895 2313176433036257311294871 := by
  unfold tailWord_4504895
  simp only [CollatzResearch.WordTrace]
  refine ⟨164307019014542264658052139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109538012676361509772034759 164307019014542264658052139)
  ·
    refine ⟨246460528521813396987078209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164307019014542264658052139 246460528521813396987078209)
    ·
      refine ⟨184845396391360047740308657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246460528521813396987078209 184845396391360047740308657)
      ·
        refine ⟨138634047293520035805231493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184845396391360047740308657 138634047293520035805231493)
        ·
          refine ⟨25993883867535006713480905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138634047293520035805231493 25993883867535006713480905)
          ·
            refine ⟨19495412900651255035110679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25993883867535006713480905 19495412900651255035110679)
            ·
              refine ⟨29243119350976882552666019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19495412900651255035110679 29243119350976882552666019)
              ·
                refine ⟨43864679026465323828999029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29243119350976882552666019 43864679026465323828999029)
                ·
                  refine ⟨4112313658731124108968659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43864679026465323828999029 4112313658731124108968659)
                  ·
                    refine ⟨6168470488096686163452989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4112313658731124108968659 6168470488096686163452989)
                    ·
                      refine ⟨2313176433036257311294871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168470488096686163452989 2313176433036257311294871)
                      ·
                        rfl

theorem cell23_4504895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_4504895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504895 prefixEnd_4504895 := by exact prefixLift 4504895
  have htrace : WordTrace (prefixWord ++ tailWord_4504895) baseStart_4504895 baseEnd_4504895 := by
    simpa [prefixWord, tailWord_4504895, baseEnd_4504895] using wordTrace_append hprefix tailTrace_4504895
  have hstable : (prefixWord ++ tailWord_4504895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504895).length < 2 ^ (prefixWord ++ tailWord_4504895).sum := by decide
  have hdescent : baseEnd_4504895 < baseStart_4504895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504911 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 10]
def baseStart_4504911 : Nat := 118140960795 + 4504911 * 2 ^ 59
def prefixEnd_4504911 : Nat := 4983230072969 + 3 ^ 40 * 4504911 * 2
def baseEnd_4504911 : Nat := 771061549575576416231599

theorem tailTrace_4504911 : CollatzResearch.WordTrace tailWord_4504911 prefixEnd_4504911 771061549575576416231599 := by
  unfold tailWord_4504911
  simp only [CollatzResearch.WordTrace]
  refine ⟨164307602582484299390634587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109538401721656199593756391 164307602582484299390634587)
  ·
    refine ⟨246461403873726449085951881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164307602582484299390634587 246461403873726449085951881)
    ·
      refine ⟨184846052905294836814463911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246461403873726449085951881 184846052905294836814463911)
      ·
        refine ⟨277269079357942255221695867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184846052905294836814463911 277269079357942255221695867)
        ·
          refine ⟨415903619036913382832543801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277269079357942255221695867 415903619036913382832543801)
          ·
            refine ⟨311927714277685037124407851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 415903619036913382832543801 311927714277685037124407851)
            ·
              refine ⟨467891571416527555686611777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311927714277685037124407851 467891571416527555686611777)
              ·
                refine ⟨350918678562395666764958833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467891571416527555686611777 350918678562395666764958833)
                ·
                  refine ⟨263189008921796750073719125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350918678562395666764958833 263189008921796750073719125)
                  ·
                    refine ⟨771061549575576416231599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 263189008921796750073719125 771061549575576416231599)
                    ·
                      rfl

theorem cell23_4504911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_4504911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504911 prefixEnd_4504911 := by exact prefixLift 4504911
  have htrace : WordTrace (prefixWord ++ tailWord_4504911) baseStart_4504911 baseEnd_4504911 := by
    simpa [prefixWord, tailWord_4504911, baseEnd_4504911] using wordTrace_append hprefix tailTrace_4504911
  have hstable : (prefixWord ++ tailWord_4504911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504911).length < 2 ^ (prefixWord ++ tailWord_4504911).sum := by decide
  have hdescent : baseEnd_4504911 < baseStart_4504911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4504945 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 2, 4]
def baseStart_4504945 : Nat := 118140960795 + 4504945 * 2 ^ 59
def prefixEnd_4504945 : Nat := 4983230072969 + 3 ^ 40 * 4504945 * 2
def baseEnd_4504945 : Nat := 771067369022994038556547

theorem tailTrace_4504945 : CollatzResearch.WordTrace tailWord_4504945 prefixEnd_4504945 771067369022994038556547 := by
  unfold tailWord_4504945
  simp only [CollatzResearch.WordTrace]
  refine ⟨164308842664361123197372289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109539228442907415464914859 164308842664361123197372289)
  ·
    refine ⟨123231631998270842398029217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164308842664361123197372289 123231631998270842398029217)
    ·
      refine ⟨92423723998703131798521913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123231631998270842398029217 92423723998703131798521913)
      ·
        refine ⟨69317792999027348848891435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92423723998703131798521913 69317792999027348848891435)
        ·
          refine ⟨103976689498541023273337153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69317792999027348848891435 103976689498541023273337153)
          ·
            refine ⟨77982517123905767455002865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103976689498541023273337153 77982517123905767455002865)
            ·
              refine ⟨58486887842929325591252149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77982517123905767455002865 58486887842929325591252149)
              ·
                refine ⟨5483145735274624274179889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58486887842929325591252149 5483145735274624274179889)
                ·
                  refine ⟨4112359301455968205634917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5483145735274624274179889 4112359301455968205634917)
                  ·
                    refine ⟨771067369022994038556547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4112359301455968205634917 771067369022994038556547)
                    ·
                      rfl

theorem cell23_4504945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_4504945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4504945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4504945 prefixEnd_4504945 := by exact prefixLift 4504945
  have htrace : WordTrace (prefixWord ++ tailWord_4504945) baseStart_4504945 baseEnd_4504945 := by
    simpa [prefixWord, tailWord_4504945, baseEnd_4504945] using wordTrace_append hprefix tailTrace_4504945
  have hstable : (prefixWord ++ tailWord_4504945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4504945).length < 2 ^ (prefixWord ++ tailWord_4504945).sum := by decide
  have hdescent : baseEnd_4504945 < baseStart_4504945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4504945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505008 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_4505008 : Nat := 118140960795 + 4505008 * 2 ^ 59
def prefixEnd_4505008 : Nat := 4983230072969 + 3 ^ 40 * 4505008 * 2
def baseEnd_4505008 : Nat := 2313234456350215369181851

theorem tailTrace_4505008 : CollatzResearch.WordTrace tailWord_4505008 prefixEnd_4505008 2313234456350215369181851 := by
  unfold tailWord_4505008
  simp only [CollatzResearch.WordTrace]
  refine ⟨82155570231566442478457839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109540760308755256637943785 82155570231566442478457839)
  ·
    refine ⟨123233355347349663717686759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82155570231566442478457839 123233355347349663717686759)
    ·
      refine ⟨184850033021024495576530139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123233355347349663717686759 184850033021024495576530139)
      ·
        refine ⟨277275049531536743364795209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184850033021024495576530139 277275049531536743364795209)
        ·
          refine ⟨207956287148652557523596407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277275049531536743364795209 207956287148652557523596407)
          ·
            refine ⟨311934430722978836285394611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207956287148652557523596407 311934430722978836285394611)
            ·
              refine ⟨467901646084468254428091917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311934430722978836285394611 467901646084468254428091917)
              ·
                refine ⟨175463117281675595410534469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 467901646084468254428091917 175463117281675595410534469)
                ·
                  refine ⟨32899334490314174139475213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175463117281675595410534469 32899334490314174139475213)
                  ·
                    refine ⟨12337250433867815302303205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32899334490314174139475213 12337250433867815302303205)
                    ·
                      refine ⟨2313234456350215369181851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12337250433867815302303205 2313234456350215369181851)
                      ·
                        rfl

theorem cell23_4505008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_4505008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505008 prefixEnd_4505008 := by exact prefixLift 4505008
  have htrace : WordTrace (prefixWord ++ tailWord_4505008) baseStart_4505008 baseEnd_4505008 := by
    simpa [prefixWord, tailWord_4505008, baseEnd_4505008] using wordTrace_append hprefix tailTrace_4505008
  have hstable : (prefixWord ++ tailWord_4505008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505008).length < 2 ^ (prefixWord ++ tailWord_4505008).sum := by decide
  have hdescent : baseEnd_4505008 < baseStart_4505008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505018 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_4505018 : Nat := 118140960795 + 4505018 * 2 ^ 59
def prefixEnd_4505018 : Nat := 4983230072969 + 3 ^ 40 * 4505018 * 2
def baseEnd_4505018 : Nat := 771079863718920110018935

theorem tailTrace_4505018 : CollatzResearch.WordTrace tailWord_4505018 prefixEnd_4505018 771079863718920110018935 := by
  unfold tailWord_4505018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41077876298274164166194927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109541003462064437776519805 41077876298274164166194927)
  ·
    refine ⟨61616814447411246249292391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41077876298274164166194927 61616814447411246249292391)
    ·
      refine ⟨92425221671116869373938587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61616814447411246249292391 92425221671116869373938587)
      ·
        refine ⟨138637832506675304060907881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92425221671116869373938587 138637832506675304060907881)
        ·
          refine ⟨103978374380006478045680911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138637832506675304060907881 103978374380006478045680911)
          ·
            refine ⟨155967561570009717068521367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103978374380006478045680911 155967561570009717068521367)
            ·
              refine ⟨233951342355014575602782051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155967561570009717068521367 233951342355014575602782051)
              ·
                refine ⟨350927013532521863404173077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233951342355014575602782051 350927013532521863404173077)
                ·
                  refine ⟨16449703759336962347070613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 350927013532521863404173077 16449703759336962347070613)
                  ·
                    refine ⟨771079863718920110018935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16449703759336962347070613 771079863718920110018935)
                    ·
                      rfl

theorem cell23_4505018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_4505018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505018 prefixEnd_4505018 := by exact prefixLift 4505018
  have htrace : WordTrace (prefixWord ++ tailWord_4505018) baseStart_4505018 baseEnd_4505018 := by
    simpa [prefixWord, tailWord_4505018, baseEnd_4505018] using wordTrace_append hprefix tailTrace_4505018
  have hstable : (prefixWord ++ tailWord_4505018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505018).length < 2 ^ (prefixWord ++ tailWord_4505018).sum := by decide
  have hdescent : baseEnd_4505018 < baseStart_4505018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505026 : List Nat := [3, 5, 2, 1, 2, 10]
def baseStart_4505026 : Nat := 118140960795 + 4505026 * 2 ^ 59
def prefixEnd_4505026 : Nat := 4983230072969 + 3 ^ 40 * 4505026 * 2
def baseEnd_4505026 : Nat := 9519521395069943616283

theorem tailTrace_4505026 : CollatzResearch.WordTrace tailWord_4505026 prefixEnd_4505026 9519521395069943616283 := by
  unfold tailWord_4505026
  simp only [CollatzResearch.WordTrace]
  refine ⟨41077949244266918507767733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109541197984711782687380621 41077949244266918507767733)
  ·
    refine ⟨3851057741650023610103225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41077949244266918507767733 3851057741650023610103225)
    ·
      refine ⟨2888293306237517707577419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3851057741650023610103225 2888293306237517707577419)
      ·
        refine ⟨4332439959356276561366129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888293306237517707577419 4332439959356276561366129)
        ·
          refine ⟨3249329969517207421024597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4332439959356276561366129 3249329969517207421024597)
          ·
            refine ⟨9519521395069943616283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3249329969517207421024597 9519521395069943616283)
            ·
              rfl

theorem cell23_4505026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 10].length) (baseStart_4505026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505026 prefixEnd_4505026 := by exact prefixLift 4505026
  have htrace : WordTrace (prefixWord ++ tailWord_4505026) baseStart_4505026 baseEnd_4505026 := by
    simpa [prefixWord, tailWord_4505026, baseEnd_4505026] using wordTrace_append hprefix tailTrace_4505026
  have hstable : (prefixWord ++ tailWord_4505026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505026).length < 2 ^ (prefixWord ++ tailWord_4505026).sum := by decide
  have hdescent : baseEnd_4505026 < baseStart_4505026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505045 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4505045 : Nat := 118140960795 + 4505045 * 2 ^ 59
def prefixEnd_4505045 : Nat := 4983230072969 + 3 ^ 40 * 4505045 * 2
def baseEnd_4505045 : Nat := 2313253455134431724419181

theorem tailTrace_4505045 : CollatzResearch.WordTrace tailWord_4505045 prefixEnd_4505045 2313253455134431724419181 := by
  unfold tailWord_4505045
  simp only [CollatzResearch.WordTrace]
  refine ⟨164312489963998840276012589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109541659975999226850675059 164312489963998840276012589)
  ·
    refine ⟨61617183736499565103504721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 164312489963998840276012589 61617183736499565103504721)
    ·
      refine ⟨46212887802374673827628541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61617183736499565103504721 46212887802374673827628541)
      ·
        refine ⟨17329832925890502685360703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46212887802374673827628541 17329832925890502685360703)
        ·
          refine ⟨25994749388835754028041055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17329832925890502685360703 25994749388835754028041055)
          ·
            refine ⟨38992124083253631042061583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25994749388835754028041055 38992124083253631042061583)
            ·
              refine ⟨58488186124880446563092375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38992124083253631042061583 58488186124880446563092375)
              ·
                refine ⟨87732279187320669844638563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58488186124880446563092375 87732279187320669844638563)
                ·
                  refine ⟨131598418780981004766957845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87732279187320669844638563 131598418780981004766957845)
                  ·
                    refine ⟨6168675880358484598451149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 131598418780981004766957845 6168675880358484598451149)
                    ·
                      refine ⟨2313253455134431724419181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168675880358484598451149 2313253455134431724419181)
                      ·
                        rfl

theorem cell23_4505045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4505045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505045 prefixEnd_4505045 := by exact prefixLift 4505045
  have htrace : WordTrace (prefixWord ++ tailWord_4505045) baseStart_4505045 baseEnd_4505045 := by
    simpa [prefixWord, tailWord_4505045, baseEnd_4505045] using wordTrace_append hprefix tailTrace_4505045
  have hstable : (prefixWord ++ tailWord_4505045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505045).length < 2 ^ (prefixWord ++ tailWord_4505045).sum := by decide
  have hdescent : baseEnd_4505045 < baseStart_4505045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505055 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_4505055 : Nat := 118140960795 + 4505055 * 2 ^ 59
def prefixEnd_4505055 : Nat := 4983230072969 + 3 ^ 40 * 4505055 * 2
def baseEnd_4505055 : Nat := 2313258589940976685294135

theorem tailTrace_4505055 : CollatzResearch.WordTrace tailWord_4505055 prefixEnd_4505055 2313258589940976685294135 := by
  unfold tailWord_4505055
  simp only [CollatzResearch.WordTrace]
  refine ⟨164312854693962611983876619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109541903129308407989251079 164312854693962611983876619)
  ·
    refine ⟨246469282040943917975814929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164312854693962611983876619 246469282040943917975814929)
    ·
      refine ⟨184851961530707938481861197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246469282040943917975814929 184851961530707938481861197)
      ·
        refine ⟨69319485574015476930697949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184851961530707938481861197 69319485574015476930697949)
        ·
          refine ⟨25994807090255803849011731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69319485574015476930697949 25994807090255803849011731)
          ·
            refine ⟨38992210635383705773517597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25994807090255803849011731 38992210635383705773517597)
            ·
              refine ⟨14622078988268889665069099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38992210635383705773517597 14622078988268889665069099)
              ·
                refine ⟨21933118482403334497603649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14622078988268889665069099 21933118482403334497603649)
                ·
                  refine ⟨16449838861802500873202737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21933118482403334497603649 16449838861802500873202737)
                  ·
                    refine ⟨12337379146351875654902053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16449838861802500873202737 12337379146351875654902053)
                    ·
                      refine ⟨2313258589940976685294135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12337379146351875654902053 2313258589940976685294135)
                      ·
                        rfl

theorem cell23_4505055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_4505055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505055 prefixEnd_4505055 := by exact prefixLift 4505055
  have htrace : WordTrace (prefixWord ++ tailWord_4505055) baseStart_4505055 baseEnd_4505055 := by
    simpa [prefixWord, tailWord_4505055, baseEnd_4505055] using wordTrace_append hprefix tailTrace_4505055
  have hstable : (prefixWord ++ tailWord_4505055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505055).length < 2 ^ (prefixWord ++ tailWord_4505055).sum := by decide
  have hdescent : baseEnd_4505055 < baseStart_4505055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505059 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 1, 4, 2]
def baseStart_4505059 : Nat := 118140960795 + 4505059 * 2 ^ 59
def prefixEnd_4505059 : Nat := 4983230072969 + 3 ^ 40 * 4505059 * 2
def baseEnd_4505059 : Nat := 2313260643863594669644117

theorem tailTrace_4505059 : CollatzResearch.WordTrace tailWord_4505059 prefixEnd_4505059 2313260643863594669644117 := by
  unfold tailWord_4505059
  simp only [CollatzResearch.WordTrace]
  refine ⟨164313000585948120667022231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109542000390632080444681487 164313000585948120667022231)
  ·
    refine ⟨246469500878922181000533347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164313000585948120667022231 246469500878922181000533347)
    ·
      refine ⟨369704251318383271500800021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246469500878922181000533347 369704251318383271500800021)
      ·
        refine ⟨17329886780549215851600001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 369704251318383271500800021 17329886780549215851600001)
        ·
          refine ⟨12997415085411911888700001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17329886780549215851600001 12997415085411911888700001)
          ·
            refine ⟨9748061314058933916525001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12997415085411911888700001 9748061314058933916525001)
            ·
              refine ⟨7311045985544200437393751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9748061314058933916525001 7311045985544200437393751)
              ·
                refine ⟨10966568978316300656090627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7311045985544200437393751 10966568978316300656090627)
                ·
                  refine ⟨16449853467474450984135941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10966568978316300656090627 16449853467474450984135941)
                  ·
                    refine ⟨3084347525151459559525489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16449853467474450984135941 3084347525151459559525489)
                    ·
                      refine ⟨2313260643863594669644117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084347525151459559525489 2313260643863594669644117)
                      ·
                        rfl

theorem cell23_4505059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_4505059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505059 prefixEnd_4505059 := by exact prefixLift 4505059
  have htrace : WordTrace (prefixWord ++ tailWord_4505059) baseStart_4505059 baseEnd_4505059 := by
    simpa [prefixWord, tailWord_4505059, baseEnd_4505059] using wordTrace_append hprefix tailTrace_4505059
  have hstable : (prefixWord ++ tailWord_4505059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505059).length < 2 ^ (prefixWord ++ tailWord_4505059).sum := by decide
  have hdescent : baseEnd_4505059 < baseStart_4505059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505082 : List Nat := [3, 1, 1, 1, 1, 2, 6, 3, 5]
def baseStart_4505082 : Nat := 118140960795 + 4505082 * 2 ^ 59
def prefixEnd_4505082 : Nat := 4983230072969 + 3 ^ 40 * 4505082 * 2
def baseEnd_4505082 : Nat := 257030272657627564406279

theorem tailTrace_4505082 : CollatzResearch.WordTrace tailWord_4505082 prefixEnd_4505082 257030272657627564406279 := by
  unfold tailWord_4505082
  simp only [CollatzResearch.WordTrace]
  refine ⟨41078459866216198898777375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109542559643243197063406333 41078459866216198898777375)
  ·
    refine ⟨61617689799324298348166063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41078459866216198898777375 61617689799324298348166063)
    ·
      refine ⟨92426534698986447522249095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61617689799324298348166063 92426534698986447522249095)
      ·
        refine ⟨138639802048479671283373643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92426534698986447522249095 138639802048479671283373643)
        ·
          refine ⟨207959703072719506925060465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138639802048479671283373643 207959703072719506925060465)
          ·
            refine ⟨155969777304539630193795349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207959703072719506925060465 155969777304539630193795349)
            ·
              refine ⟨7311083311150295165334157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155969777304539630193795349 7311083311150295165334157)
              ·
                refine ⟨2741656241681360687000309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7311083311150295165334157 2741656241681360687000309)
                ·
                  refine ⟨257030272657627564406279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2741656241681360687000309 257030272657627564406279)
                  ·
                    rfl

theorem cell23_4505082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_4505082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505082 prefixEnd_4505082 := by exact prefixLift 4505082
  have htrace : WordTrace (prefixWord ++ tailWord_4505082) baseStart_4505082 baseEnd_4505082 := by
    simpa [prefixWord, tailWord_4505082, baseEnd_4505082] using wordTrace_append hprefix tailTrace_4505082
  have hstable : (prefixWord ++ tailWord_4505082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505082).length < 2 ^ (prefixWord ++ tailWord_4505082).sum := by decide
  have hdescent : baseEnd_4505082 < baseStart_4505082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505149 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4505149 : Nat := 118140960795 + 4505149 * 2 ^ 59
def prefixEnd_4505149 : Nat := 4983230072969 + 3 ^ 40 * 4505149 * 2
def baseEnd_4505149 : Nat := 2313306857122499317518703

theorem tailTrace_4505149 : CollatzResearch.WordTrace tailWord_4505149 prefixEnd_4505149 2313306857122499317518703 := by
  unfold tailWord_4505149
  simp only [CollatzResearch.WordTrace]
  refine ⟨164316283155622066037798501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109544188770414710691865667 164316283155622066037798501)
  ·
    refine ⟨30809303091679137382087219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164316283155622066037798501 30809303091679137382087219)
    ·
      refine ⟨46213954637518706073130829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30809303091679137382087219 46213954637518706073130829)
      ·
        refine ⟨17330232989069514777424061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46213954637518706073130829 17330232989069514777424061)
        ·
          refine ⟨6498837370901068041534023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17330232989069514777424061 6498837370901068041534023)
          ·
            refine ⟨9748256056351602062301035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6498837370901068041534023 9748256056351602062301035)
            ·
              refine ⟨14622384084527403093451553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9748256056351602062301035 14622384084527403093451553)
              ·
                refine ⟨10966788063395552320088665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14622384084527403093451553 10966788063395552320088665)
                ·
                  refine ⟨8225091047546664240066499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10966788063395552320088665 8225091047546664240066499)
                  ·
                    refine ⟨12337636571319996360099749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8225091047546664240066499 12337636571319996360099749)
                    ·
                      refine ⟨2313306857122499317518703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12337636571319996360099749 2313306857122499317518703)
                      ·
                        rfl

theorem cell23_4505149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4505149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505149 prefixEnd_4505149 := by exact prefixLift 4505149
  have htrace : WordTrace (prefixWord ++ tailWord_4505149) baseStart_4505149 baseEnd_4505149 := by
    simpa [prefixWord, tailWord_4505149, baseEnd_4505149] using wordTrace_append hprefix tailTrace_4505149
  have hstable : (prefixWord ++ tailWord_4505149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505149).length < 2 ^ (prefixWord ++ tailWord_4505149).sum := by decide
  have hdescent : baseEnd_4505149 < baseStart_4505149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505172 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 6]
def baseStart_4505172 : Nat := 118140960795 + 4505172 * 2 ^ 59
def prefixEnd_4505172 : Nat := 4983230072969 + 3 ^ 40 * 4505172 * 2
def baseEnd_4505172 : Nat := 257035407464172525281233

theorem tailTrace_4505172 : CollatzResearch.WordTrace tailWord_4505172 prefixEnd_4505172 257035407464172525281233 := by
  unfold tailWord_4505172
  simp only [CollatzResearch.WordTrace]
  refine ⟨82158561017269370482942885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109544748023025827310590513 82158561017269370482942885)
  ·
    refine ⟨15404730190738006965551791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82158561017269370482942885 15404730190738006965551791)
    ·
      refine ⟨23107095286107010448327687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15404730190738006965551791 23107095286107010448327687)
      ·
        refine ⟨34660642929160515672491531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23107095286107010448327687 34660642929160515672491531)
        ·
          refine ⟨51990964393740773508737297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34660642929160515672491531 51990964393740773508737297)
          ·
            refine ⟨38993223295305580131552973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51990964393740773508737297 38993223295305580131552973)
            ·
              refine ⟨14622458735739592549332365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38993223295305580131552973 14622458735739592549332365)
              ·
                refine ⟨5483422025902347205999637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14622458735739592549332365 5483422025902347205999637)
                ·
                  refine ⟨257035407464172525281233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5483422025902347205999637 257035407464172525281233)
                  ·
                    rfl

theorem cell23_4505172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_4505172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505172 prefixEnd_4505172 := by exact prefixLift 4505172
  have htrace : WordTrace (prefixWord ++ tailWord_4505172) baseStart_4505172 baseEnd_4505172 := by
    simpa [prefixWord, tailWord_4505172, baseEnd_4505172] using wordTrace_append hprefix tailTrace_4505172
  have hstable : (prefixWord ++ tailWord_4505172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505172).length < 2 ^ (prefixWord ++ tailWord_4505172).sum := by decide
  have hdescent : baseEnd_4505172 < baseStart_4505172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505209 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 2, 3, 2]
def baseStart_4505209 : Nat := 118140960795 + 4505209 * 2 ^ 59
def prefixEnd_4505209 : Nat := 4983230072969 + 3 ^ 40 * 4505209 * 2
def baseEnd_4505209 : Nat := 2313337665961769082768427

theorem tailTrace_4505209 : CollatzResearch.WordTrace tailWord_4505209 prefixEnd_4505209 2313337665961769082768427 := by
  unfold tailWord_4505209
  simp only [CollatzResearch.WordTrace]
  refine ⟨164318471535404696284982681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109545647690269797523321787 164318471535404696284982681)
  ·
    refine ⟨123238853651553522213737011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164318471535404696284982681 123238853651553522213737011)
    ·
      refine ⟨184858280477330283320605517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123238853651553522213737011 184858280477330283320605517)
      ·
        refine ⟨69321855178998856245227069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184858280477330283320605517 69321855178998856245227069)
        ·
          refine ⟨25995695692124571091960151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69321855178998856245227069 25995695692124571091960151)
          ·
            refine ⟨38993543538186856637940227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25995695692124571091960151 38993543538186856637940227)
            ·
              refine ⟨58490315307280284956910341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38993543538186856637940227 58490315307280284956910341)
              ·
                refine ⟨10966934120115053429420689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58490315307280284956910341 10966934120115053429420689)
                ·
                  refine ⟨8225200590086290072065517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10966934120115053429420689 8225200590086290072065517)
                  ·
                    refine ⟨3084450221282358777024569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8225200590086290072065517 3084450221282358777024569)
                    ·
                      refine ⟨2313337665961769082768427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084450221282358777024569 2313337665961769082768427)
                      ·
                        rfl

theorem cell23_4505209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_4505209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505209 prefixEnd_4505209 := by exact prefixLift 4505209
  have htrace : WordTrace (prefixWord ++ tailWord_4505209) baseStart_4505209 baseEnd_4505209 := by
    simpa [prefixWord, tailWord_4505209, baseEnd_4505209] using wordTrace_append hprefix tailTrace_4505209
  have hstable : (prefixWord ++ tailWord_4505209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505209).length < 2 ^ (prefixWord ++ tailWord_4505209).sum := by decide
  have hdescent : baseEnd_4505209 < baseStart_4505209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505216 : List Nat := [2, 1, 1, 2, 1, 4, 3, 4, 1, 1, 3]
def baseStart_4505216 : Nat := 118140960795 + 4505216 * 2 ^ 59
def prefixEnd_4505216 : Nat := 4983230072969 + 3 ^ 40 * 4505216 * 2
def baseEnd_4505216 : Nat := 2313341260326350555380895

theorem tailTrace_4505216 : CollatzResearch.WordTrace tailWord_4505216 prefixEnd_4505216 2313341260326350555380895 := by
  unfold tailWord_4505216
  simp only [CollatzResearch.WordTrace]
  refine ⟨82159363423189668240243751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109545817897586224320325001 82159363423189668240243751)
  ·
    refine ⟨123239045134784502360365627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82159363423189668240243751 123239045134784502360365627)
    ·
      refine ⟨184858567702176753540548441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123239045134784502360365627 184858567702176753540548441)
      ·
        refine ⟨138643925776632565155411331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184858567702176753540548441 138643925776632565155411331)
        ·
          refine ⟨207965888664948847733116997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138643925776632565155411331 207965888664948847733116997)
          ·
            refine ⟨38993604124677908949959437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207965888664948847733116997 38993604124677908949959437)
            ·
              refine ⟨14622601546754215856234789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38993604124677908949959437 14622601546754215856234789)
              ·
                refine ⟨2741737790016415473044023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14622601546754215856234789 2741737790016415473044023)
                ·
                  refine ⟨4112606685024623209566035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741737790016415473044023 4112606685024623209566035)
                  ·
                    refine ⟨6168910027536934814349053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4112606685024623209566035 6168910027536934814349053)
                    ·
                      refine ⟨2313341260326350555380895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168910027536934814349053 2313341260326350555380895)
                      ·
                        rfl

theorem cell23_4505216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_4505216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505216 prefixEnd_4505216 := by exact prefixLift 4505216
  have htrace : WordTrace (prefixWord ++ tailWord_4505216) baseStart_4505216 baseEnd_4505216 := by
    simpa [prefixWord, tailWord_4505216, baseEnd_4505216] using wordTrace_append hprefix tailTrace_4505216
  have hstable : (prefixWord ++ tailWord_4505216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505216).length < 2 ^ (prefixWord ++ tailWord_4505216).sum := by decide
  have hdescent : baseEnd_4505216 < baseStart_4505216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505272 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_4505272 : Nat := 118140960795 + 4505272 * 2 ^ 59
def prefixEnd_4505272 : Nat := 4983230072969 + 3 ^ 40 * 4505272 * 2
def baseEnd_4505272 : Nat := 2313370015243002336280637

theorem tailTrace_4505272 : CollatzResearch.WordTrace tailWord_4505272 prefixEnd_4505272 2313370015243002336280637 := by
  unfold tailWord_4505272
  simp only [CollatzResearch.WordTrace]
  refine ⟨82160384667088229022263035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109547179556117638696350713 82160384667088229022263035)
  ·
    refine ⟨123240577000632343533394553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82160384667088229022263035 123240577000632343533394553)
    ·
      refine ⟨92430432750474257650045915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123240577000632343533394553 92430432750474257650045915)
      ·
        refine ⟨138645649125711386475068873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92430432750474257650045915 138645649125711386475068873)
        ·
          refine ⟨103984236844283539856301655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138645649125711386475068873 103984236844283539856301655)
          ·
            refine ⟨155976355266425309784452483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103984236844283539856301655 155976355266425309784452483)
            ·
              refine ⟨233964532899637964676678725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155976355266425309784452483 233964532899637964676678725)
              ·
                refine ⟨43868349918682118376877261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233964532899637964676678725 43868349918682118376877261)
                ·
                  refine ⟨16450631219505794391328973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43868349918682118376877261 16450631219505794391328973)
                  ·
                    refine ⟨6168986707314672896748365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16450631219505794391328973 6168986707314672896748365)
                    ·
                      refine ⟨2313370015243002336280637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6168986707314672896748365 2313370015243002336280637)
                      ·
                        rfl

theorem cell23_4505272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_4505272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505272 prefixEnd_4505272 := by exact prefixLift 4505272
  have htrace : WordTrace (prefixWord ++ tailWord_4505272) baseStart_4505272 baseEnd_4505272 := by
    simpa [prefixWord, tailWord_4505272, baseEnd_4505272] using wordTrace_append hprefix tailTrace_4505272
  have hstable : (prefixWord ++ tailWord_4505272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505272).length < 2 ^ (prefixWord ++ tailWord_4505272).sum := by decide
  have hdescent : baseEnd_4505272 < baseStart_4505272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505273 : List Nat := [1, 2, 1, 4, 1, 1, 4, 4, 1, 2, 2]
def baseStart_4505273 : Nat := 118140960795 + 4505273 * 2 ^ 59
def prefixEnd_4505273 : Nat := 4983230072969 + 3 ^ 40 * 4505273 * 2
def baseEnd_4505273 : Nat := 2313370528723656832368133

theorem tailTrace_4505273 : CollatzResearch.WordTrace tailWord_4505273 prefixEnd_4505273 2313370528723656832368133 := by
  unfold tailWord_4505273
  simp only [CollatzResearch.WordTrace]
  refine ⟨164320805807172835215312473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109547203871448556810208315 164320805807172835215312473)
  ·
    refine ⟨123240604355379626411484355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164320805807172835215312473 123240604355379626411484355)
    ·
      refine ⟨184860906533069439617226533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123240604355379626411484355 184860906533069439617226533)
      ·
        refine ⟨34661419974950519928229975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184860906533069439617226533 34661419974950519928229975)
        ·
          refine ⟨51992129962425779892344963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34661419974950519928229975 51992129962425779892344963)
          ·
            refine ⟨77988194943638669838517445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51992129962425779892344963 77988194943638669838517445)
            ·
              refine ⟨14622786551932250594722021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77988194943638669838517445 14622786551932250594722021)
              ·
                refine ⟨2741772478487296986510379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14622786551932250594722021 2741772478487296986510379)
                ·
                  refine ⟨4112658717730945479765569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741772478487296986510379 4112658717730945479765569)
                  ·
                    refine ⟨3084494038298209109824177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4112658717730945479765569 3084494038298209109824177)
                    ·
                      refine ⟨2313370528723656832368133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084494038298209109824177 2313370528723656832368133)
                      ·
                        rfl

theorem cell23_4505273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_4505273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505273 prefixEnd_4505273 := by exact prefixLift 4505273
  have htrace : WordTrace (prefixWord ++ tailWord_4505273) baseStart_4505273 baseEnd_4505273 := by
    simpa [prefixWord, tailWord_4505273, baseEnd_4505273] using wordTrace_append hprefix tailTrace_4505273
  have hstable : (prefixWord ++ tailWord_4505273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505273).length < 2 ^ (prefixWord ++ tailWord_4505273).sum := by decide
  have hdescent : baseEnd_4505273 < baseStart_4505273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505275 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 1, 9]
def baseStart_4505275 : Nat := 118140960795 + 4505275 * 2 ^ 59
def prefixEnd_4505275 : Nat := 4983230072969 + 3 ^ 40 * 4505275 * 2
def baseEnd_4505275 : Nat := 771123851894988608181041

theorem tailTrace_4505275 : CollatzResearch.WordTrace tailWord_4505275 prefixEnd_4505275 771123851894988608181041 := by
  unfold tailWord_4505275
  simp only [CollatzResearch.WordTrace]
  refine ⟨164320878753165589556885279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109547252502110393037923519 164320878753165589556885279)
  ·
    refine ⟨246481318129748384335327919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164320878753165589556885279 246481318129748384335327919)
    ·
      refine ⟨369721977194622576502991879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246481318129748384335327919 369721977194622576502991879)
      ·
        refine ⟨554582965791933864754487819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369721977194622576502991879 554582965791933864754487819)
        ·
          refine ⟨831874448687900797131731729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554582965791933864754487819 831874448687900797131731729)
          ·
            refine ⟨623905836515925597848798797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831874448687900797131731729 623905836515925597848798797)
            ·
              refine ⟨233964688693472099193299549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 623905836515925597848798797 233964688693472099193299549)
              ·
                refine ⟨87736758260052037197487331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233964688693472099193299549 87736758260052037197487331)
                ·
                  refine ⟨131605137390078055796230997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87736758260052037197487331 131605137390078055796230997)
                  ·
                    refine ⟨771123851894988608181041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 131605137390078055796230997 771123851894988608181041)
                    ·
                      rfl

theorem cell23_4505275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_4505275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505275 prefixEnd_4505275 := by exact prefixLift 4505275
  have htrace : WordTrace (prefixWord ++ tailWord_4505275) baseStart_4505275 baseEnd_4505275 := by
    simpa [prefixWord, tailWord_4505275, baseEnd_4505275] using wordTrace_append hprefix tailTrace_4505275
  have hstable : (prefixWord ++ tailWord_4505275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505275).length < 2 ^ (prefixWord ++ tailWord_4505275).sum := by decide
  have hdescent : baseEnd_4505275 < baseStart_4505275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505293 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4505293 : Nat := 118140960795 + 4505293 * 2 ^ 59
def prefixEnd_4505293 : Nat := 4983230072969 + 3 ^ 40 * 4505293 * 2
def baseEnd_4505293 : Nat := 2313380798336746754118041

theorem tailTrace_4505293 : CollatzResearch.WordTrace tailWord_4505293 prefixEnd_4505293 2313380798336746754118041 := by
  unfold tailWord_4505293
  simp only [CollatzResearch.WordTrace]
  refine ⟨164321535267100378631040533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109547690178066919087360355 164321535267100378631040533)
  ·
    refine ⟨7702571965645330248330025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 164321535267100378631040533 7702571965645330248330025)
    ·
      refine ⟨5776928974233997686247519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7702571965645330248330025 5776928974233997686247519)
      ·
        refine ⟨8665393461350996529371279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5776928974233997686247519 8665393461350996529371279)
        ·
          refine ⟨12998090192026494794056919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8665393461350996529371279 12998090192026494794056919)
          ·
            refine ⟨19497135288039742191085379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12998090192026494794056919 19497135288039742191085379)
            ·
              refine ⟨29245702932059613286628069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19497135288039742191085379 29245702932059613286628069)
              ·
                refine ⟨5483569299761177491242763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29245702932059613286628069 5483569299761177491242763)
                ·
                  refine ⟨8225353949641766236864145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5483569299761177491242763 8225353949641766236864145)
                  ·
                    refine ⟨6169015462231324677648109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8225353949641766236864145 6169015462231324677648109)
                    ·
                      refine ⟨2313380798336746754118041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169015462231324677648109 2313380798336746754118041)
                      ·
                        rfl

theorem cell23_4505293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4505293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505293 prefixEnd_4505293 := by exact prefixLift 4505293
  have htrace : WordTrace (prefixWord ++ tailWord_4505293) baseStart_4505293 baseEnd_4505293 := by
    simpa [prefixWord, tailWord_4505293, baseEnd_4505293] using wordTrace_append hprefix tailTrace_4505293
  have hstable : (prefixWord ++ tailWord_4505293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505293).length < 2 ^ (prefixWord ++ tailWord_4505293).sum := by decide
  have hdescent : baseEnd_4505293 < baseStart_4505293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505316 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_4505316 : Nat := 118140960795 + 4505316 * 2 ^ 59
def prefixEnd_4505316 : Nat := 4983230072969 + 3 ^ 40 * 4505316 * 2
def baseEnd_4505316 : Nat := 2313392608391800164130435

theorem tailTrace_4505316 : CollatzResearch.WordTrace tailWord_4505316 prefixEnd_4505316 2313392608391800164130435 := by
  unfold tailWord_4505316
  simp only [CollatzResearch.WordTrace]
  refine ⟨82161187073008526779563901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109548249430678035706085201 82161187073008526779563901)
  ·
    refine ⟨30810445152378197542336463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82161187073008526779563901 30810445152378197542336463)
    ·
      refine ⟨46215667728567296313504695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30810445152378197542336463 46215667728567296313504695)
      ·
        refine ⟨69323501592850944470257043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46215667728567296313504695 69323501592850944470257043)
        ·
          refine ⟨103985252389276416705385565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69323501592850944470257043 103985252389276416705385565)
          ·
            refine ⟨38994469645978656264519587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103985252389276416705385565 38994469645978656264519587)
            ·
              refine ⟨58491704468967984396779381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38994469645978656264519587 58491704468967984396779381)
              ·
                refine ⟨5483597293965748537198067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58491704468967984396779381 5483597293965748537198067)
                ·
                  refine ⟨8225395940948622805797101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5483597293965748537198067 8225395940948622805797101)
                  ·
                    refine ⟨3084523477855733552173913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8225395940948622805797101 3084523477855733552173913)
                    ·
                      refine ⟨2313392608391800164130435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084523477855733552173913 2313392608391800164130435)
                      ·
                        rfl

theorem cell23_4505316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_4505316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505316 prefixEnd_4505316 := by exact prefixLift 4505316
  have htrace : WordTrace (prefixWord ++ tailWord_4505316) baseStart_4505316 baseEnd_4505316 := by
    simpa [prefixWord, tailWord_4505316, baseEnd_4505316] using wordTrace_append hprefix tailTrace_4505316
  have hstable : (prefixWord ++ tailWord_4505316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505316).length < 2 ^ (prefixWord ++ tailWord_4505316).sum := by decide
  have hdescent : baseEnd_4505316 < baseStart_4505316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505322 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_4505322 : Nat := 118140960795 + 4505322 * 2 ^ 59
def prefixEnd_4505322 : Nat := 4983230072969 + 3 ^ 40 * 4505322 * 2
def baseEnd_4505322 : Nat := 771131896425242380218469

theorem tailTrace_4505322 : CollatzResearch.WordTrace tailWord_4505322 prefixEnd_4505322 771131896425242380218469 := by
  unfold tailWord_4505322
  simp only [CollatzResearch.WordTrace]
  refine ⟨41080648245998829145961555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109548395322663544389230813 41080648245998829145961555)
  ·
    refine ⟨61620972368998243718942333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41080648245998829145961555 61620972368998243718942333)
    ·
      refine ⟨23107864638374341394603375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61620972368998243718942333 23107864638374341394603375)
      ·
        refine ⟨34661796957561512091905063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23107864638374341394603375 34661796957561512091905063)
        ·
          refine ⟨51992695436342268137857595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34661796957561512091905063 51992695436342268137857595)
          ·
            refine ⟨77989043154513402206786393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51992695436342268137857595 77989043154513402206786393)
            ·
              refine ⟨58491782365885051655089795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77989043154513402206786393 58491782365885051655089795)
              ·
                refine ⟨87737673548827577482634693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58491782365885051655089795 87737673548827577482634693)
                ·
                  refine ⟨16450813790405170777994005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87737673548827577482634693 16450813790405170777994005)
                  ·
                    refine ⟨771131896425242380218469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16450813790405170777994005 771131896425242380218469)
                    ·
                      rfl

theorem cell23_4505322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_4505322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505322 prefixEnd_4505322 := by exact prefixLift 4505322
  have htrace : WordTrace (prefixWord ++ tailWord_4505322) baseStart_4505322 baseEnd_4505322 := by
    simpa [prefixWord, tailWord_4505322, baseEnd_4505322] using wordTrace_append hprefix tailTrace_4505322
  have hstable : (prefixWord ++ tailWord_4505322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505322).length < 2 ^ (prefixWord ++ tailWord_4505322).sum := by decide
  have hdescent : baseEnd_4505322 < baseStart_4505322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505352 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 9]
def baseStart_4505352 : Nat := 118140960795 + 4505352 * 2 ^ 59
def prefixEnd_4505352 : Nat := 4983230072969 + 3 ^ 40 * 4505352 * 2
def baseEnd_4505352 : Nat := 257045677077262447031141

theorem tailTrace_4505352 : CollatzResearch.WordTrace tailWord_4505352 prefixEnd_4505352 257045677077262447031141 := by
  unfold tailWord_4505352
  simp only [CollatzResearch.WordTrace]
  refine ⟨82161843586943315853719155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109549124782591087804958873 82161843586943315853719155)
  ·
    refine ⟨123242765380414973780578733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82161843586943315853719155 123242765380414973780578733)
    ·
      refine ⟨46216037017655615167717025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123242765380414973780578733 46216037017655615167717025)
      ·
        refine ⟨34662027763241711375787769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46216037017655615167717025 34662027763241711375787769)
        ·
          refine ⟨25996520822431283531840827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34662027763241711375787769 25996520822431283531840827)
          ·
            refine ⟨38994781233646925297761241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25996520822431283531840827 38994781233646925297761241)
            ·
              refine ⟨29246085925235193973320931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38994781233646925297761241 29246085925235193973320931)
              ·
                refine ⟨43869128887852790959981397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29246085925235193973320931 43869128887852790959981397)
                ·
                  refine ⟨257045677077262447031141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43869128887852790959981397 257045677077262447031141)
                  ·
                    rfl

theorem cell23_4505352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 9].length) (baseStart_4505352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505352 prefixEnd_4505352 := by exact prefixLift 4505352
  have htrace : WordTrace (prefixWord ++ tailWord_4505352) baseStart_4505352 baseEnd_4505352 := by
    simpa [prefixWord, tailWord_4505352, baseEnd_4505352] using wordTrace_append hprefix tailTrace_4505352
  have hstable : (prefixWord ++ tailWord_4505352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505352).length < 2 ^ (prefixWord ++ tailWord_4505352).sum := by decide
  have hdescent : baseEnd_4505352 < baseStart_4505352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505357 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4505357 : Nat := 118140960795 + 4505357 * 2 ^ 59
def prefixEnd_4505357 : Nat := 4983230072969 + 3 ^ 40 * 4505357 * 2
def baseEnd_4505357 : Nat := 2313413661098634503717747

theorem tailTrace_4505357 : CollatzResearch.WordTrace tailWord_4505357 prefixEnd_4505357 2313413661098634503717747 := by
  unfold tailWord_4505357
  simp only [CollatzResearch.WordTrace]
  refine ⟨164323869538868517561370325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109549246359245678374246883 164323869538868517561370325)
  ·
    refine ⟨3851340692317230880344617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 164323869538868517561370325 3851340692317230880344617)
    ·
      refine ⟨2888505519237923160258463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3851340692317230880344617 2888505519237923160258463)
      ·
        refine ⟨4332758278856884740387695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888505519237923160258463 4332758278856884740387695)
        ·
          refine ⟨6499137418285327110581543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332758278856884740387695 6499137418285327110581543)
          ·
            refine ⟨9748706127427990665872315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6499137418285327110581543 9748706127427990665872315)
            ·
              refine ⟨14623059191141985998808473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9748706127427990665872315 14623059191141985998808473)
              ·
                refine ⟨10967294393356489499106355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14623059191141985998808473 10967294393356489499106355)
                ·
                  refine ⟨16450941590034734248659533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10967294393356489499106355 16450941590034734248659533)
                  ·
                    refine ⟨6169103096263025343247325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16450941590034734248659533 6169103096263025343247325)
                    ·
                      refine ⟨2313413661098634503717747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169103096263025343247325 2313413661098634503717747)
                      ·
                        rfl

theorem cell23_4505357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4505357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505357 prefixEnd_4505357 := by exact prefixLift 4505357
  have htrace : WordTrace (prefixWord ++ tailWord_4505357) baseStart_4505357 baseEnd_4505357 := by
    simpa [prefixWord, tailWord_4505357, baseEnd_4505357] using wordTrace_append hprefix tailTrace_4505357
  have hstable : (prefixWord ++ tailWord_4505357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505357).length < 2 ^ (prefixWord ++ tailWord_4505357).sum := by decide
  have hdescent : baseEnd_4505357 < baseStart_4505357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505380 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_4505380 : Nat := 118140960795 + 4505380 * 2 ^ 59
def prefixEnd_4505380 : Nat := 4983230072969 + 3 ^ 40 * 4505380 * 2
def baseEnd_4505380 : Nat := 2313425471153687913730141

theorem tailTrace_4505380 : CollatzResearch.WordTrace tailWord_4505380 prefixEnd_4505380 2313425471153687913730141 := by
  unfold tailWord_4505380
  simp only [CollatzResearch.WordTrace]
  refine ⟨82162354208892596244728797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109549805611856794992971729 82162354208892596244728797)
  ·
    refine ⟨30810882828334723591773299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82162354208892596244728797 30810882828334723591773299)
    ·
      refine ⟨46216324242502085387659949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30810882828334723591773299 46216324242502085387659949)
      ·
        refine ⟨17331121590938282020372481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46216324242502085387659949 17331121590938282020372481)
        ·
          refine ⟨12998341193203711515279361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17331121590938282020372481 12998341193203711515279361)
          ·
            refine ⟨9748755894902783636459521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12998341193203711515279361 9748755894902783636459521)
            ·
              refine ⟨7311566921177087727344641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9748755894902783636459521 7311566921177087727344641)
              ·
                refine ⟨5483675190882815795508481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7311566921177087727344641 5483675190882815795508481)
                ·
                  refine ⟨4112756393162111846631361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5483675190882815795508481 4112756393162111846631361)
                  ·
                    refine ⟨3084567294871583884973521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4112756393162111846631361 3084567294871583884973521)
                    ·
                      refine ⟨2313425471153687913730141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084567294871583884973521 2313425471153687913730141)
                      ·
                        rfl

theorem cell23_4505380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_4505380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505380 prefixEnd_4505380 := by exact prefixLift 4505380
  have htrace : WordTrace (prefixWord ++ tailWord_4505380) baseStart_4505380 baseEnd_4505380 := by
    simpa [prefixWord, tailWord_4505380, baseEnd_4505380] using wordTrace_append hprefix tailTrace_4505380
  have hstable : (prefixWord ++ tailWord_4505380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505380).length < 2 ^ (prefixWord ++ tailWord_4505380).sum := by decide
  have hdescent : baseEnd_4505380 < baseStart_4505380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505396 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_4505396 : Nat := 118140960795 + 4505396 * 2 ^ 59
def prefixEnd_4505396 : Nat := 4983230072969 + 3 ^ 40 * 4505396 * 2
def baseEnd_4505396 : Nat := 2313433686844159851130067

theorem tailTrace_4505396 : CollatzResearch.WordTrace tailWord_4505396 prefixEnd_4505396 2313433686844159851130067 := by
  unfold tailWord_4505396
  simp only [CollatzResearch.WordTrace]
  refine ⟨82162645992863613611020021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109550194657151484814693361 82162645992863613611020021)
  ·
    refine ⟨7702748061830963776033127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82162645992863613611020021 7702748061830963776033127)
    ·
      refine ⟨11554122092746445664049691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7702748061830963776033127 11554122092746445664049691)
      ·
        refine ⟨17331183139119668496074537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11554122092746445664049691 17331183139119668496074537)
        ·
          refine ⟨12998387354339751372055903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17331183139119668496074537 12998387354339751372055903)
          ·
            refine ⟨19497581031509627058083855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12998387354339751372055903 19497581031509627058083855)
            ·
              refine ⟨29246371547264440587125783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19497581031509627058083855 29246371547264440587125783)
              ·
                refine ⟨43869557320896660880688675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29246371547264440587125783 43869557320896660880688675)
                ·
                  refine ⟨65804335981344991321033013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43869557320896660880688675 65804335981344991321033013)
                  ·
                    refine ⟨6169156498251092936346845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65804335981344991321033013 6169156498251092936346845)
                    ·
                      refine ⟨2313433686844159851130067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169156498251092936346845 2313433686844159851130067)
                      ·
                        rfl

theorem cell23_4505396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_4505396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505396 prefixEnd_4505396 := by exact prefixLift 4505396
  have htrace : WordTrace (prefixWord ++ tailWord_4505396) baseStart_4505396 baseEnd_4505396 := by
    simpa [prefixWord, tailWord_4505396, baseEnd_4505396] using wordTrace_append hprefix tailTrace_4505396
  have hstable : (prefixWord ++ tailWord_4505396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505396).length < 2 ^ (prefixWord ++ tailWord_4505396).sum := by decide
  have hdescent : baseEnd_4505396 < baseStart_4505396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505416 : List Nat := [2, 1, 3, 1, 1, 6, 1, 1, 2, 5]
def baseStart_4505416 : Nat := 118140960795 + 4505416 * 2 ^ 59
def prefixEnd_4505416 : Nat := 4983230072969 + 3 ^ 40 * 4505416 * 2
def baseEnd_4505416 : Nat := 771147985485749924293325

theorem tailTrace_4505416 : CollatzResearch.WordTrace tailWord_4505416 prefixEnd_4505416 771147985485749924293325 := by
  unfold tailWord_4505416
  simp only [CollatzResearch.WordTrace]
  refine ⟨82163010722827385318884051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109550680963769847091845401 82163010722827385318884051)
  ·
    refine ⟨123244516084241077978326077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82163010722827385318884051 123244516084241077978326077)
    ·
      refine ⟨46216693531590404241872279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123244516084241077978326077 46216693531590404241872279)
      ·
        refine ⟨69325040297385606362808419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46216693531590404241872279 69325040297385606362808419)
        ·
          refine ⟨103987560446078409544212629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69325040297385606362808419 103987560446078409544212629)
          ·
            refine ⟨4874416895909925447384967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103987560446078409544212629 4874416895909925447384967)
            ·
              refine ⟨7311625343864888171077451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4874416895909925447384967 7311625343864888171077451)
              ·
                refine ⟨10967438015797332256616177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7311625343864888171077451 10967438015797332256616177)
                ·
                  refine ⟨8225578511847999192462133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10967438015797332256616177 8225578511847999192462133)
                  ·
                    refine ⟨771147985485749924293325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8225578511847999192462133 771147985485749924293325)
                    ·
                      rfl

theorem cell23_4505416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_4505416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505416 prefixEnd_4505416 := by exact prefixLift 4505416
  have htrace : WordTrace (prefixWord ++ tailWord_4505416) baseStart_4505416 baseEnd_4505416 := by
    simpa [prefixWord, tailWord_4505416, baseEnd_4505416] using wordTrace_append hprefix tailTrace_4505416
  have hstable : (prefixWord ++ tailWord_4505416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505416).length < 2 ^ (prefixWord ++ tailWord_4505416).sum := by decide
  have hdescent : baseEnd_4505416 < baseStart_4505416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505469 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_4505469 : Nat := 118140960795 + 4505469 * 2 ^ 59
def prefixEnd_4505469 : Nat := 4983230072969 + 3 ^ 40 * 4505469 * 2
def baseEnd_4505469 : Nat := 2313471170931938065517231

theorem tailTrace_4505469 : CollatzResearch.WordTrace tailWord_4505469 prefixEnd_4505469 2313471170931938065517231 := by
  unfold tailWord_4505469
  simp only [CollatzResearch.WordTrace]
  refine ⟨164327954514462760689447461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109551969676308507126298307 164327954514462760689447461)
  ·
    refine ⟨30811491471461767629271399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 164327954514462760689447461 30811491471461767629271399)
    ·
      refine ⟨46217237207192651443907099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30811491471461767629271399 46217237207192651443907099)
      ·
        refine ⟨69325855810788977165860649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46217237207192651443907099 69325855810788977165860649)
        ·
          refine ⟨51994391858091732874395487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69325855810788977165860649 51994391858091732874395487)
          ·
            refine ⟨77991587787137599311593231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51994391858091732874395487 77991587787137599311593231)
            ·
              refine ⟨116987381680706398967389847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77991587787137599311593231 116987381680706398967389847)
              ·
                refine ⟨175481072521059598451084771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116987381680706398967389847 175481072521059598451084771)
                ·
                  refine ⟨263221608781589397676627157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175481072521059598451084771 263221608781589397676627157)
                  ·
                    refine ⟨6169256455818501508045949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 263221608781589397676627157 6169256455818501508045949)
                    ·
                      refine ⟨2313471170931938065517231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169256455818501508045949 2313471170931938065517231)
                      ·
                        rfl

theorem cell23_4505469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_4505469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505469 prefixEnd_4505469 := by exact prefixLift 4505469
  have htrace : WordTrace (prefixWord ++ tailWord_4505469) baseStart_4505469 baseEnd_4505469 := by
    simpa [prefixWord, tailWord_4505469, baseEnd_4505469] using wordTrace_append hprefix tailTrace_4505469
  have hstable : (prefixWord ++ tailWord_4505469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505469).length < 2 ^ (prefixWord ++ tailWord_4505469).sum := by decide
  have hdescent : baseEnd_4505469 < baseStart_4505469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505519 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 1, 6]
def baseStart_4505519 : Nat := 118140960795 + 4505519 * 2 ^ 59
def prefixEnd_4505519 : Nat := 4983230072969 + 3 ^ 40 * 4505519 * 2
def baseEnd_4505519 : Nat := 771165614988220956630667

theorem tailTrace_4505519 : CollatzResearch.WordTrace tailWord_4505519 prefixEnd_4505519 771165614988220956630667 := by
  unfold tailWord_4505519
  simp only [CollatzResearch.WordTrace]
  refine ⟨164329778164281619228767611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109553185442854412819178407 164329778164281619228767611)
  ·
    refine ⟨246494667246422428843151417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164329778164281619228767611 246494667246422428843151417)
    ·
      refine ⟨184871000434816821632363563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246494667246422428843151417 184871000434816821632363563)
      ·
        refine ⟨277306500652225232448545345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184871000434816821632363563 277306500652225232448545345)
        ·
          refine ⟨207979875489168924336409009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277306500652225232448545345 207979875489168924336409009)
          ·
            refine ⟨155984906616876693252306757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207979875489168924336409009 155984906616876693252306757)
            ·
              refine ⟨29247169990664379984807517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155984906616876693252306757 29247169990664379984807517)
              ·
                refine ⟨10967688746499142494302819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29247169990664379984807517 10967688746499142494302819)
                ·
                  refine ⟨16451533119748713741454229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10967688746499142494302819 16451533119748713741454229)
                  ·
                    refine ⟨771165614988220956630667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16451533119748713741454229 771165614988220956630667)
                    ·
                      rfl

theorem cell23_4505519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_4505519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505519 prefixEnd_4505519 := by exact prefixLift 4505519
  have htrace : WordTrace (prefixWord ++ tailWord_4505519) baseStart_4505519 baseEnd_4505519 := by
    simpa [prefixWord, tailWord_4505519, baseEnd_4505519] using wordTrace_append hprefix tailTrace_4505519
  have hstable : (prefixWord ++ tailWord_4505519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505519).length < 2 ^ (prefixWord ++ tailWord_4505519).sum := by decide
  have hdescent : baseEnd_4505519 < baseStart_4505519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505546 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_4505546 : Nat := 118140960795 + 4505546 * 2 ^ 59
def prefixEnd_4505546 : Nat := 4983230072969 + 3 ^ 40 * 4505546 * 2
def baseEnd_4505546 : Nat := 2313510708942334264254377

theorem tailTrace_4505546 : CollatzResearch.WordTrace tailWord_4505546 prefixEnd_4505546 2313510708942334264254377 := by
  unfold tailWord_4505546
  simp only [CollatzResearch.WordTrace]
  refine ⟨41082690733795950710000123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109553841956789201893333661 41082690733795950710000123)
  ·
    refine ⟨61624036100693926065000185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41082690733795950710000123 61624036100693926065000185)
    ·
      refine ⟨46218027075520444548750139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61624036100693926065000185 46218027075520444548750139)
      ·
        refine ⟨69327040613280666823125209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46218027075520444548750139 69327040613280666823125209)
        ·
          refine ⟨51995280459960500117343907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69327040613280666823125209 51995280459960500117343907)
          ·
            refine ⟨77992920689940750176015861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51995280459960500117343907 77992920689940750176015861)
            ·
              refine ⟨7311836314681945329001487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77992920689940750176015861 7311836314681945329001487)
              ·
                refine ⟨10967754472022917993502231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7311836314681945329001487 10967754472022917993502231)
                ·
                  refine ⟨16451631708034376990253347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10967754472022917993502231 16451631708034376990253347)
                  ·
                    refine ⟨24677447562051565485380021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16451631708034376990253347 24677447562051565485380021)
                    ·
                      refine ⟨2313510708942334264254377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24677447562051565485380021 2313510708942334264254377)
                      ·
                        rfl

theorem cell23_4505546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_4505546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505546 prefixEnd_4505546 := by exact prefixLift 4505546
  have htrace : WordTrace (prefixWord ++ tailWord_4505546) baseStart_4505546 baseEnd_4505546 := by
    simpa [prefixWord, tailWord_4505546, baseEnd_4505546] using wordTrace_append hprefix tailTrace_4505546
  have hstable : (prefixWord ++ tailWord_4505546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505546).length < 2 ^ (prefixWord ++ tailWord_4505546).sum := by decide
  have hdescent : baseEnd_4505546 < baseStart_4505546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505556 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4505556 : Nat := 118140960795 + 4505556 * 2 ^ 59
def prefixEnd_4505556 : Nat := 4983230072969 + 3 ^ 40 * 4505556 * 2
def baseEnd_4505556 : Nat := 2313515843748879225129331

theorem tailTrace_4505556 : CollatzResearch.WordTrace tailWord_4505556 prefixEnd_4505556 2313515843748879225129331 := by
  unfold tailWord_4505556
  simp only [CollatzResearch.WordTrace]
  refine ⟨82165563832573787273932261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109554085110098383031909681 82165563832573787273932261)
  ·
    refine ⟨15406043218607585113862299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82165563832573787273932261 15406043218607585113862299)
    ·
      refine ⟨23109064827911377670793449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15406043218607585113862299 23109064827911377670793449)
      ·
        refine ⟨17331798620933533253095087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23109064827911377670793449 17331798620933533253095087)
        ·
          refine ⟨25997697931400299879642631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17331798620933533253095087 25997697931400299879642631)
          ·
            refine ⟨38996546897100449819463947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25997697931400299879642631 38996546897100449819463947)
            ·
              refine ⟨58494820345650674729195921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38996546897100449819463947 58494820345650674729195921)
              ·
                refine ⟨43871115259238006046896941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58494820345650674729195921 43871115259238006046896941)
                ·
                  refine ⟨16451668222214252267586353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43871115259238006046896941 16451668222214252267586353)
                  ·
                    refine ⟨12338751166660689200689765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16451668222214252267586353 12338751166660689200689765)
                    ·
                      refine ⟨2313515843748879225129331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12338751166660689200689765 2313515843748879225129331)
                      ·
                        rfl

theorem cell23_4505556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4505556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505556 prefixEnd_4505556 := by exact prefixLift 4505556
  have htrace : WordTrace (prefixWord ++ tailWord_4505556) baseStart_4505556 baseEnd_4505556 := by
    simpa [prefixWord, tailWord_4505556, baseEnd_4505556] using wordTrace_append hprefix tailTrace_4505556
  have hstable : (prefixWord ++ tailWord_4505556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505556).length < 2 ^ (prefixWord ++ tailWord_4505556).sum := by decide
  have hdescent : baseEnd_4505556 < baseStart_4505556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505569 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_4505569 : Nat := 118140960795 + 4505569 * 2 ^ 59
def prefixEnd_4505569 : Nat := 4983230072969 + 3 ^ 40 * 4505569 * 2
def baseEnd_4505569 : Nat := 2313522518997387674266771

theorem tailTrace_4505569 : CollatzResearch.WordTrace tailWord_4505569 prefixEnd_4505569 2313522518997387674266771 := by
  unfold tailWord_4505569
  simp only [CollatzResearch.WordTrace]
  refine ⟨164331601814100477768087761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109554401209400318512058507 164331601814100477768087761)
  ·
    refine ⟨123248701360575358326065821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164331601814100477768087761 123248701360575358326065821)
    ·
      refine ⟨46218263010215759372274683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123248701360575358326065821 46218263010215759372274683)
      ·
        refine ⟨69327394515323639058412025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46218263010215759372274683 69327394515323639058412025)
        ·
          refine ⟨51995545886492729293809019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69327394515323639058412025 51995545886492729293809019)
          ·
            refine ⟨77993318829739093940713529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51995545886492729293809019 77993318829739093940713529)
            ·
              refine ⟨58494989122304320455535147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77993318829739093940713529 58494989122304320455535147)
              ·
                refine ⟨87742483683456480683302721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58494989122304320455535147 87742483683456480683302721)
                ·
                  refine ⟨65806862762592360512477041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87742483683456480683302721 65806862762592360512477041)
                  ·
                    refine ⟨49355147071944270384357781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65806862762592360512477041 49355147071944270384357781)
                    ·
                      refine ⟨2313522518997387674266771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49355147071944270384357781 2313522518997387674266771)
                      ·
                        rfl

theorem cell23_4505569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_4505569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505569 prefixEnd_4505569 := by exact prefixLift 4505569
  have htrace : WordTrace (prefixWord ++ tailWord_4505569) baseStart_4505569 baseEnd_4505569 := by
    simpa [prefixWord, tailWord_4505569, baseEnd_4505569] using wordTrace_append hprefix tailTrace_4505569
  have hstable : (prefixWord ++ tailWord_4505569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505569).length < 2 ^ (prefixWord ++ tailWord_4505569).sum := by decide
  have hdescent : baseEnd_4505569 < baseStart_4505569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505570 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_4505570 : Nat := 118140960795 + 4505570 * 2 ^ 59
def prefixEnd_4505570 : Nat := 4983230072969 + 3 ^ 40 * 4505570 * 2
def baseEnd_4505570 : Nat := 771174344159347390118089

theorem tailTrace_4505570 : CollatzResearch.WordTrace tailWord_4505570 prefixEnd_4505570 771174344159347390118089 := by
  unfold tailWord_4505570
  simp only [CollatzResearch.WordTrace]
  refine ⟨41082909571774213734718541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109554425524731236625916109 41082909571774213734718541)
  ·
    refine ⟨15406091089415330150519453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41082909571774213734718541 15406091089415330150519453)
    ·
      refine ⟨5777284158530748806444795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15406091089415330150519453 5777284158530748806444795)
      ·
        refine ⟨8665926237796123209667193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5777284158530748806444795 8665926237796123209667193)
        ·
          refine ⟨6499444678347092407250395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8665926237796123209667193 6499444678347092407250395)
          ·
            refine ⟨9749167017520638610875593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6499444678347092407250395 9749167017520638610875593)
            ·
              refine ⟨7311875263140478958156695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9749167017520638610875593 7311875263140478958156695)
              ·
                refine ⟨10967812894710718437235043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7311875263140478958156695 10967812894710718437235043)
                ·
                  refine ⟨16451719342066077655852565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10967812894710718437235043 16451719342066077655852565)
                  ·
                    refine ⟨771174344159347390118089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16451719342066077655852565 771174344159347390118089)
                    ·
                      rfl

theorem cell23_4505570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_4505570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505570 prefixEnd_4505570 := by exact prefixLift 4505570
  have htrace : WordTrace (prefixWord ++ tailWord_4505570) baseStart_4505570 baseEnd_4505570 := by
    simpa [prefixWord, tailWord_4505570, baseEnd_4505570] using wordTrace_append hprefix tailTrace_4505570
  have hstable : (prefixWord ++ tailWord_4505570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505570).length < 2 ^ (prefixWord ++ tailWord_4505570).sum := by decide
  have hdescent : baseEnd_4505570 < baseStart_4505570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505604 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_4505604 : Nat := 118140960795 + 4505604 * 2 ^ 59
def prefixEnd_4505604 : Nat := 4983230072969 + 3 ^ 40 * 4505604 * 2
def baseEnd_4505604 : Nat := 771180163606765012443037

theorem tailTrace_4505604 : CollatzResearch.WordTrace tailWord_4505604 prefixEnd_4505604 771180163606765012443037 := by
  unfold tailWord_4505604
  simp only [CollatzResearch.WordTrace]
  refine ⟨82166439184486839372805933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109555252245982452497074577 82166439184486839372805933)
  ·
    refine ⟨30812414694182564764802225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82166439184486839372805933 30812414694182564764802225)
    ·
      refine ⟨23109311020636923573601669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30812414694182564764802225 23109311020636923573601669)
      ·
        refine ⟨4332995816369423170050313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23109311020636923573601669 4332995816369423170050313)
        ·
          refine ⟨3249746862277067377537735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4332995816369423170050313 3249746862277067377537735)
          ·
            refine ⟨4874620293415601066306603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249746862277067377537735 4874620293415601066306603)
            ·
              refine ⟨7311930440123401599459905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4874620293415601066306603 7311930440123401599459905)
              ·
                refine ⟨5483947830092551199594929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7311930440123401599459905 5483947830092551199594929)
                ·
                  refine ⟨4112960872569413399696197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5483947830092551199594929 4112960872569413399696197)
                  ·
                    refine ⟨771180163606765012443037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4112960872569413399696197 771180163606765012443037)
                    ·
                      rfl

theorem cell23_4505604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_4505604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505604 prefixEnd_4505604 := by exact prefixLift 4505604
  have htrace : WordTrace (prefixWord ++ tailWord_4505604) baseStart_4505604 baseEnd_4505604 := by
    simpa [prefixWord, tailWord_4505604, baseEnd_4505604] using wordTrace_append hprefix tailTrace_4505604
  have hstable : (prefixWord ++ tailWord_4505604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505604).length < 2 ^ (prefixWord ++ tailWord_4505604).sum := by decide
  have hdescent : baseEnd_4505604 < baseStart_4505604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505610 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_4505610 : Nat := 118140960795 + 4505610 * 2 ^ 59
def prefixEnd_4505610 : Nat := 4983230072969 + 3 ^ 40 * 4505610 * 2
def baseEnd_4505610 : Nat := 2313543571704222013854083

theorem tailTrace_4505610 : CollatzResearch.WordTrace tailWord_4505610 prefixEnd_4505610 2313543571704222013854083 := by
  unfold tailWord_4505610
  simp only [CollatzResearch.WordTrace]
  refine ⟨41083274301737985442582571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109555398137967961180220189 41083274301737985442582571)
  ·
    refine ⟨61624911452606978163873857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41083274301737985442582571 61624911452606978163873857)
    ·
      refine ⟨46218683589455233622905393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61624911452606978163873857 46218683589455233622905393)
      ·
        refine ⟨34664012692091425217179045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46218683589455233622905393 34664012692091425217179045)
        ·
          refine ⟨6499502379767142228221071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34664012692091425217179045 6499502379767142228221071)
          ·
            refine ⟨9749253569650713342331607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6499502379767142228221071 9749253569650713342331607)
            ·
              refine ⟨14623880354476070013497411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9749253569650713342331607 14623880354476070013497411)
              ·
                refine ⟨21935820531714105020246117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14623880354476070013497411 21935820531714105020246117)
                ·
                  refine ⟨4112966349696394691296147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21935820531714105020246117 4112966349696394691296147)
                  ·
                    refine ⟨6169449524544592036944221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4112966349696394691296147 6169449524544592036944221)
                    ·
                      refine ⟨2313543571704222013854083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169449524544592036944221 2313543571704222013854083)
                      ·
                        rfl

theorem cell23_4505610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_4505610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505610 prefixEnd_4505610 := by exact prefixLift 4505610
  have htrace : WordTrace (prefixWord ++ tailWord_4505610) baseStart_4505610 baseEnd_4505610 := by
    simpa [prefixWord, tailWord_4505610, baseEnd_4505610] using wordTrace_append hprefix tailTrace_4505610
  have hstable : (prefixWord ++ tailWord_4505610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505610).length < 2 ^ (prefixWord ++ tailWord_4505610).sum := by decide
  have hdescent : baseEnd_4505610 < baseStart_4505610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505626 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_4505626 : Nat := 118140960795 + 4505626 * 2 ^ 59
def prefixEnd_4505626 : Nat := 4983230072969 + 3 ^ 40 * 4505626 * 2
def baseEnd_4505626 : Nat := 771183929131564650418003

theorem tailTrace_4505626 : CollatzResearch.WordTrace tailWord_4505626 prefixEnd_4505626 771183929131564650418003 := by
  unfold tailWord_4505626
  simp only [CollatzResearch.WordTrace]
  refine ⟨41083420193723494125728183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109555787183262651001941821 41083420193723494125728183)
  ·
    refine ⟨61625130290585241188592275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41083420193723494125728183 61625130290585241188592275)
    ·
      refine ⟨92437695435877861782888413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61625130290585241188592275 92437695435877861782888413)
      ·
        refine ⟨34664135788454198168583155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92437695435877861782888413 34664135788454198168583155)
        ·
          refine ⟨51996203682681297252874733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34664135788454198168583155 51996203682681297252874733)
          ·
            refine ⟨19498576381005486469828025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51996203682681297252874733 19498576381005486469828025)
            ·
              refine ⟨14623932285754114852371019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19498576381005486469828025 14623932285754114852371019)
              ·
                refine ⟨21935898428631172278556529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14623932285754114852371019 21935898428631172278556529)
                ·
                  refine ⟨16451923821473379208917397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21935898428631172278556529 16451923821473379208917397)
                  ·
                    refine ⟨771183929131564650418003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16451923821473379208917397 771183929131564650418003)
                    ·
                      rfl

theorem cell23_4505626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_4505626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505626 prefixEnd_4505626 := by exact prefixLift 4505626
  have htrace : WordTrace (prefixWord ++ tailWord_4505626) baseStart_4505626 baseEnd_4505626 := by
    simpa [prefixWord, tailWord_4505626, baseEnd_4505626] using wordTrace_append hprefix tailTrace_4505626
  have hstable : (prefixWord ++ tailWord_4505626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505626).length < 2 ^ (prefixWord ++ tailWord_4505626).sum := by decide
  have hdescent : baseEnd_4505626 < baseStart_4505626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505650 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_4505650 : Nat := 118140960795 + 4505650 * 2 ^ 59
def prefixEnd_4505650 : Nat := 4983230072969 + 3 ^ 40 * 4505650 * 2
def baseEnd_4505650 : Nat := 2313564110930401857353899

theorem tailTrace_4505650 : CollatzResearch.WordTrace tailWord_4505650 prefixEnd_4505650 2313564110930401857353899 := by
  unfold tailWord_4505650
  simp only [CollatzResearch.WordTrace]
  refine ⟨41083639031701757150446601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109556370751204685734524269 41083639031701757150446601)
  ·
    refine ⟨30812729273776317862834951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41083639031701757150446601 30812729273776317862834951)
    ·
      refine ⟨46219093910664476794252427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30812729273776317862834951 46219093910664476794252427)
      ·
        refine ⟨69328640865996715191378641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46219093910664476794252427 69328640865996715191378641)
        ·
          refine ⟨51996480649497536393533981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69328640865996715191378641 51996480649497536393533981)
          ·
            refine ⟨19498680243561576147575243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51996480649497536393533981 19498680243561576147575243)
            ·
              refine ⟨29248020365342364221362865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19498680243561576147575243 29248020365342364221362865)
              ·
                refine ⟨21936015274006773166022149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29248020365342364221362865 21936015274006773166022149)
                ·
                  refine ⟨4113002863876269968629153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21936015274006773166022149 4113002863876269968629153)
                  ·
                    refine ⟨3084752147907202476471865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4113002863876269968629153 3084752147907202476471865)
                    ·
                      refine ⟨2313564110930401857353899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084752147907202476471865 2313564110930401857353899)
                      ·
                        rfl

theorem cell23_4505650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_4505650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505650 prefixEnd_4505650 := by exact prefixLift 4505650
  have htrace : WordTrace (prefixWord ++ tailWord_4505650) baseStart_4505650 baseEnd_4505650 := by
    simpa [prefixWord, tailWord_4505650, baseEnd_4505650] using wordTrace_append hprefix tailTrace_4505650
  have hstable : (prefixWord ++ tailWord_4505650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505650).length < 2 ^ (prefixWord ++ tailWord_4505650).sum := by decide
  have hdescent : baseEnd_4505650 < baseStart_4505650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505670 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4505670 : Nat := 118140960795 + 4505670 * 2 ^ 59
def prefixEnd_4505670 : Nat := 4983230072969 + 3 ^ 40 * 4505670 * 2
def baseEnd_4505670 : Nat := 2313574380543491779103807

theorem tailTrace_4505670 : CollatzResearch.WordTrace tailWord_4505670 prefixEnd_4505670 2313574380543491779103807 := by
  unfold tailWord_4505670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135477674585455375547327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 109556857057823048011676309 5135477674585455375547327)
  ·
    refine ⟨7703216511878183063320991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5135477674585455375547327 7703216511878183063320991)
    ·
      refine ⟨11554824767817274594981487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7703216511878183063320991 11554824767817274594981487)
      ·
        refine ⟨17332237151725911892472231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11554824767817274594981487 17332237151725911892472231)
        ·
          refine ⟨25998355727588867838708347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17332237151725911892472231 25998355727588867838708347)
          ·
            refine ⟨38997533591383301758062521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25998355727588867838708347 38997533591383301758062521)
            ·
              refine ⟨29248150193537476318546891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38997533591383301758062521 29248150193537476318546891)
              ·
                refine ⟨43872225290306214477820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29248150193537476318546891 43872225290306214477820337)
                ·
                  refine ⟨32904168967729660858365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43872225290306214477820337 32904168967729660858365253)
                  ·
                    refine ⟨6169531681449311410943485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32904168967729660858365253 6169531681449311410943485)
                    ·
                      refine ⟨2313574380543491779103807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169531681449311410943485 2313574380543491779103807)
                      ·
                        rfl

theorem cell23_4505670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4505670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505670 prefixEnd_4505670 := by exact prefixLift 4505670
  have htrace : WordTrace (prefixWord ++ tailWord_4505670) baseStart_4505670 baseEnd_4505670 := by
    simpa [prefixWord, tailWord_4505670, baseEnd_4505670] using wordTrace_append hprefix tailTrace_4505670
  have hstable : (prefixWord ++ tailWord_4505670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505670).length < 2 ^ (prefixWord ++ tailWord_4505670).sum := by decide
  have hdescent : baseEnd_4505670 < baseStart_4505670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505703 : List Nat := [1, 1, 5, 1, 1, 2, 4, 1, 2, 5]
def baseStart_4505703 : Nat := 118140960795 + 4505703 * 2 ^ 59
def prefixEnd_4505703 : Nat := 4983230072969 + 3 ^ 40 * 4505703 * 2
def baseEnd_4505703 : Nat := 771197108468363383330385

theorem tailTrace_4505703 : CollatzResearch.WordTrace tailWord_4505703 prefixEnd_4505703 771197108468363383330385 := by
  unfold tailWord_4505703
  simp only [CollatzResearch.WordTrace]
  refine ⟨164336489195615018653465763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109557659463743345768977175 164336489195615018653465763)
  ·
    refine ⟨246504733793422527980198645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164336489195615018653465763 246504733793422527980198645)
    ·
      refine ⟨23109818793133361998143623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 246504733793422527980198645 23109818793133361998143623)
      ·
        refine ⟨34664728189700042997215435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23109818793133361998143623 34664728189700042997215435)
        ·
          refine ⟨51997092284550064495823153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34664728189700042997215435 51997092284550064495823153)
          ·
            refine ⟨38997819213412548371867365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51997092284550064495823153 38997819213412548371867365)
            ·
              refine ⟨7312091102514852819725131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38997819213412548371867365 7312091102514852819725131)
              ·
                refine ⟨10968136653772279229587697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7312091102514852819725131 10968136653772279229587697)
                ·
                  refine ⟨8226102490329209422190773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10968136653772279229587697 8226102490329209422190773)
                  ·
                    refine ⟨771197108468363383330385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8226102490329209422190773 771197108468363383330385)
                    ·
                      rfl

theorem cell23_4505703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_4505703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505703 prefixEnd_4505703 := by exact prefixLift 4505703
  have htrace : WordTrace (prefixWord ++ tailWord_4505703) baseStart_4505703 baseEnd_4505703 := by
    simpa [prefixWord, tailWord_4505703, baseEnd_4505703] using wordTrace_append hprefix tailTrace_4505703
  have hstable : (prefixWord ++ tailWord_4505703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505703).length < 2 ^ (prefixWord ++ tailWord_4505703).sum := by decide
  have hdescent : baseEnd_4505703 < baseStart_4505703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505760 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3]
def baseStart_4505760 : Nat := 118140960795 + 4505760 * 2 ^ 59
def prefixEnd_4505760 : Nat := 4983230072969 + 3 ^ 40 * 4505760 * 2
def baseEnd_4505760 : Nat := 2313620593802396426978393

theorem tailTrace_4505760 : CollatzResearch.WordTrace tailWord_4505760 prefixEnd_4505760 2313620593802396426978393 := by
  unfold tailWord_4505760
  simp only [CollatzResearch.WordTrace]
  refine ⟨82169284078204258694145367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109559045437605678258860489 82169284078204258694145367)
  ·
    refine ⟨123253926117306388041218051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82169284078204258694145367 123253926117306388041218051)
    ·
      refine ⟨184880889175959582061827077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123253926117306388041218051 184880889175959582061827077)
      ·
        refine ⟨34665166720492421636592577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 184880889175959582061827077 34665166720492421636592577)
        ·
          refine ⟨25998875040369316227444433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34665166720492421636592577 25998875040369316227444433)
          ·
            refine ⟨19499156280276987170583325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25998875040369316227444433 19499156280276987170583325)
            ·
              refine ⟨7312183605103870188968747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19499156280276987170583325 7312183605103870188968747)
              ·
                refine ⟨10968275407655805283453121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7312183605103870188968747 10968275407655805283453121)
                ·
                  refine ⟨8226206555741853962589841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10968275407655805283453121 8226206555741853962589841)
                  ·
                    refine ⟨6169654916806390471942381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8226206555741853962589841 6169654916806390471942381)
                    ·
                      refine ⟨2313620593802396426978393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169654916806390471942381 2313620593802396426978393)
                      ·
                        rfl

theorem cell23_4505760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_4505760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505760 prefixEnd_4505760 := by exact prefixLift 4505760
  have htrace : WordTrace (prefixWord ++ tailWord_4505760) baseStart_4505760 baseEnd_4505760 := by
    simpa [prefixWord, tailWord_4505760, baseEnd_4505760] using wordTrace_append hprefix tailTrace_4505760
  have hstable : (prefixWord ++ tailWord_4505760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505760).length < 2 ^ (prefixWord ++ tailWord_4505760).sum := by decide
  have hdescent : baseEnd_4505760 < baseStart_4505760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505810 : List Nat := [3, 2, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_4505810 : Nat := 118140960795 + 4505810 * 2 ^ 59
def prefixEnd_4505810 : Nat := 4983230072969 + 3 ^ 40 * 4505810 * 2
def baseEnd_4505810 : Nat := 771215422611707077117721

theorem tailTrace_4505810 : CollatzResearch.WordTrace tailWord_4505810 prefixEnd_4505810 771215422611707077117721 := by
  unfold tailWord_4505810
  simp only [CollatzResearch.WordTrace]
  refine ⟨41085097951556843981902721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109560261204151583951740589 41085097951556843981902721)
  ·
    refine ⟨30813823463667632986427041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41085097951556843981902721 30813823463667632986427041)
    ·
      refine ⟨23110367597750724739820281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30813823463667632986427041 23110367597750724739820281)
      ·
        refine ⟨17332775698313043554865211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23110367597750724739820281 17332775698313043554865211)
        ·
          refine ⟨25999163547469565332297817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17332775698313043554865211 25999163547469565332297817)
          ·
            refine ⟨19499372660602173999223363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25999163547469565332297817 19499372660602173999223363)
            ·
              refine ⟨29249058990903260998835045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19499372660602173999223363 29249058990903260998835045)
              ·
                refine ⟨5484198560794361437281571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29249058990903260998835045 5484198560794361437281571)
                ·
                  refine ⟨8226297841191542155922357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484198560794361437281571 8226297841191542155922357)
                  ·
                    refine ⟨771215422611707077117721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8226297841191542155922357 771215422611707077117721)
                    ·
                      rfl

theorem cell23_4505810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_4505810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505810 prefixEnd_4505810 := by exact prefixLift 4505810
  have htrace : WordTrace (prefixWord ++ tailWord_4505810) baseStart_4505810 baseEnd_4505810 := by
    simpa [prefixWord, tailWord_4505810, baseEnd_4505810] using wordTrace_append hprefix tailTrace_4505810
  have hstable : (prefixWord ++ tailWord_4505810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505810).length < 2 ^ (prefixWord ++ tailWord_4505810).sum := by decide
  have hdescent : baseEnd_4505810 < baseStart_4505810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505880 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_4505880 : Nat := 118140960795 + 4505880 * 2 ^ 59
def prefixEnd_4505880 : Nat := 4983230072969 + 3 ^ 40 * 4505880 * 2
def baseEnd_4505880 : Nat := 2313682211480935957477841

theorem tailTrace_4505880 : CollatzResearch.WordTrace tailWord_4505880 prefixEnd_4505880 2313682211480935957477841 := by
  unfold tailWord_4505880
  simp only [CollatzResearch.WordTrace]
  refine ⟨82171472457986888941329547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109561963277315851921772729 82171472457986888941329547)
  ·
    refine ⟨123257208686980333411994321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82171472457986888941329547 123257208686980333411994321)
    ·
      refine ⟨92442906515235250058995741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123257208686980333411994321 92442906515235250058995741)
      ·
        refine ⟨34666089943213218772123403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92442906515235250058995741 34666089943213218772123403)
        ·
          refine ⟨51999134914819828158185105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34666089943213218772123403 51999134914819828158185105)
          ·
            refine ⟨38999351186114871118638829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51999134914819828158185105 38999351186114871118638829)
            ·
              refine ⟨14624756694793076669489561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38999351186114871118638829 14624756694793076669489561)
              ·
                refine ⟨10968567521094807502117171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14624756694793076669489561 10968567521094807502117171)
                ·
                  refine ⟨16452851281642211253175757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10968567521094807502117171 16452851281642211253175757)
                  ·
                    refine ⟨6169819230615829219940909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16452851281642211253175757 6169819230615829219940909)
                    ·
                      refine ⟨2313682211480935957477841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169819230615829219940909 2313682211480935957477841)
                      ·
                        rfl

theorem cell23_4505880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_4505880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505880 prefixEnd_4505880 := by exact prefixLift 4505880
  have htrace : WordTrace (prefixWord ++ tailWord_4505880) baseStart_4505880 baseEnd_4505880 := by
    simpa [prefixWord, tailWord_4505880, baseEnd_4505880] using wordTrace_append hprefix tailTrace_4505880
  have hstable : (prefixWord ++ tailWord_4505880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505880).length < 2 ^ (prefixWord ++ tailWord_4505880).sum := by decide
  have hdescent : baseEnd_4505880 < baseStart_4505880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505898 : List Nat := [3, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4505898 : Nat := 118140960795 + 4505898 * 2 ^ 59
def prefixEnd_4505898 : Nat := 4983230072969 + 3 ^ 40 * 4505898 * 2
def baseEnd_4505898 : Nat := 2313691454132716887052759

theorem tailTrace_4505898 : CollatzResearch.WordTrace tailWord_4505898 prefixEnd_4505898 2313691454132716887052759 := by
  unfold tailWord_4505898
  simp only [CollatzResearch.WordTrace]
  refine ⟨41085900357477141739203587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109562400953272377971209565 41085900357477141739203587)
  ·
    refine ⟨61628850536215712608805381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41085900357477141739203587 61628850536215712608805381)
    ·
      refine ⟨11555409475540446114151009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61628850536215712608805381 11555409475540446114151009)
      ·
        refine ⟨8666557106655334585613257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11555409475540446114151009 8666557106655334585613257)
        ·
          refine ⟨6499917829991500939209943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8666557106655334585613257 6499917829991500939209943)
          ·
            refine ⟨9749876744987251408814915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6499917829991500939209943 9749876744987251408814915)
            ·
              refine ⟨14624815117480877113222373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9749876744987251408814915 14624815117480877113222373)
              ·
                refine ⟨2742152834527664458729195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14624815117480877113222373 2742152834527664458729195)
                ·
                  refine ⟨4113229251791496688093793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2742152834527664458729195 4113229251791496688093793)
                  ·
                    refine ⟨3084921938843622516070345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4113229251791496688093793 3084921938843622516070345)
                    ·
                      refine ⟨2313691454132716887052759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084921938843622516070345 2313691454132716887052759)
                      ·
                        rfl

theorem cell23_4505898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4505898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505898 prefixEnd_4505898 := by exact prefixLift 4505898
  have htrace : WordTrace (prefixWord ++ tailWord_4505898) baseStart_4505898 baseEnd_4505898 := by
    simpa [prefixWord, tailWord_4505898, baseEnd_4505898] using wordTrace_append hprefix tailTrace_4505898
  have hstable : (prefixWord ++ tailWord_4505898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505898).length < 2 ^ (prefixWord ++ tailWord_4505898).sum := by decide
  have hdescent : baseEnd_4505898 < baseStart_4505898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505903 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_4505903 : Nat := 118140960795 + 4505903 * 2 ^ 59
def prefixEnd_4505903 : Nat := 4983230072969 + 3 ^ 40 * 4505903 * 2
def baseEnd_4505903 : Nat := 2313694021535989367490235

theorem tailTrace_4505903 : CollatzResearch.WordTrace tailWord_4505903 prefixEnd_4505903 2313694021535989367490235 := by
  unfold tailWord_4505903
  simp only [CollatzResearch.WordTrace]
  refine ⟨164343783794890452810746363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109562522529926968540497575 164343783794890452810746363)
  ·
    refine ⟨246515675692335679216119545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164343783794890452810746363 246515675692335679216119545)
    ·
      refine ⟨184886756769251759412089659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246515675692335679216119545 184886756769251759412089659)
      ·
        refine ⟨277330135153877639118134489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184886756769251759412089659 277330135153877639118134489)
        ·
          refine ⟨207997601365408229338600867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277330135153877639118134489 207997601365408229338600867)
          ·
            refine ⟨311996402048112344007901301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207997601365408229338600867 311996402048112344007901301)
            ·
              refine ⟨29249662692010532250740747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 311996402048112344007901301 29249662692010532250740747)
              ·
                refine ⟨43874494038015798376111121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29249662692010532250740747 43874494038015798376111121)
                ·
                  refine ⟨32905870528511848782083341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43874494038015798376111121 32905870528511848782083341)
                  ·
                    refine ⟨12339701448191943293281253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32905870528511848782083341 12339701448191943293281253)
                    ·
                      refine ⟨2313694021535989367490235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12339701448191943293281253 2313694021535989367490235)
                      ·
                        rfl

theorem cell23_4505903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_4505903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505903 prefixEnd_4505903 := by exact prefixLift 4505903
  have htrace : WordTrace (prefixWord ++ tailWord_4505903) baseStart_4505903 baseEnd_4505903 := by
    simpa [prefixWord, tailWord_4505903, baseEnd_4505903] using wordTrace_append hprefix tailTrace_4505903
  have hstable : (prefixWord ++ tailWord_4505903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505903).length < 2 ^ (prefixWord ++ tailWord_4505903).sum := by decide
  have hdescent : baseEnd_4505903 < baseStart_4505903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505923 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5]
def baseStart_4505923 : Nat := 118140960795 + 4505923 * 2 ^ 59
def prefixEnd_4505923 : Nat := 4983230072969 + 3 ^ 40 * 4505923 * 2
def baseEnd_4505923 : Nat := 2313704291149079289240143

theorem tailTrace_4505923 : CollatzResearch.WordTrace tailWord_4505923 prefixEnd_4505923 2313704291149079289240143 := by
  unfold tailWord_4505923
  simp only [CollatzResearch.WordTrace]
  refine ⟨164344513254817996226474423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109563008836545330817649615 164344513254817996226474423)
  ·
    refine ⟨246516769882226994339711635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164344513254817996226474423 246516769882226994339711635)
    ·
      refine ⟨369775154823340491509567453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246516769882226994339711635 369775154823340491509567453)
      ·
        refine ⟨138665683058752684316087795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369775154823340491509567453 138665683058752684316087795)
        ·
          refine ⟨207998524588129026474131693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138665683058752684316087795 207998524588129026474131693)
          ·
            refine ⟨77999446720548384927799385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207998524588129026474131693 77999446720548384927799385)
            ·
              refine ⟨58499585040411288695849539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77999446720548384927799385 58499585040411288695849539)
              ·
                refine ⟨87749377560616933043774309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58499585040411288695849539 87749377560616933043774309)
                ·
                  refine ⟨16453008292615674945707683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87749377560616933043774309 16453008292615674945707683)
                  ·
                    refine ⟨24679512438923512418561525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16453008292615674945707683 24679512438923512418561525)
                    ·
                      refine ⟨2313704291149079289240143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24679512438923512418561525 2313704291149079289240143)
                      ·
                        rfl

theorem cell23_4505923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_4505923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505923 prefixEnd_4505923 := by exact prefixLift 4505923
  have htrace : WordTrace (prefixWord ++ tailWord_4505923) baseStart_4505923 baseEnd_4505923 := by
    simpa [prefixWord, tailWord_4505923, baseEnd_4505923] using wordTrace_append hprefix tailTrace_4505923
  have hstable : (prefixWord ++ tailWord_4505923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505923).length < 2 ^ (prefixWord ++ tailWord_4505923).sum := by decide
  have hdescent : baseEnd_4505923 < baseStart_4505923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505937 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 1, 4, 2]
def baseStart_4505937 : Nat := 118140960795 + 4505937 * 2 ^ 59
def prefixEnd_4505937 : Nat := 4983230072969 + 3 ^ 40 * 4505937 * 2
def baseEnd_4505937 : Nat := 2313711479878242234465079

theorem tailTrace_4505937 : CollatzResearch.WordTrace tailWord_4505937 prefixEnd_4505937 2313711479878242234465079 := by
  unfold tailWord_4505937
  simp only [CollatzResearch.WordTrace]
  refine ⟨164345023876767276617484065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109563349251178184411656043 164345023876767276617484065)
  ·
    refine ⟨123258767907575457463113049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164345023876767276617484065 123258767907575457463113049)
    ·
      refine ⟨92444075930681593097334787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123258767907575457463113049 92444075930681593097334787)
      ·
        refine ⟨138666113896022389646002181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92444075930681593097334787 138666113896022389646002181)
        ·
          refine ⟨25999896355504198058625409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138666113896022389646002181 25999896355504198058625409)
          ·
            refine ⟨19499922266628148543969057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25999896355504198058625409 19499922266628148543969057)
            ·
              refine ⟨14624941699971111407976793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19499922266628148543969057 14624941699971111407976793)
              ·
                refine ⟨10968706274978333555982595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14624941699971111407976793 10968706274978333555982595)
                ·
                  refine ⟨16453059412467500333973893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10968706274978333555982595 16453059412467500333973893)
                  ·
                    refine ⟨3084948639837656312620105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16453059412467500333973893 3084948639837656312620105)
                    ·
                      refine ⟨2313711479878242234465079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3084948639837656312620105 2313711479878242234465079)
                      ·
                        rfl

theorem cell23_4505937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_4505937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505937 prefixEnd_4505937 := by exact prefixLift 4505937
  have htrace : WordTrace (prefixWord ++ tailWord_4505937) baseStart_4505937 baseEnd_4505937 := by
    simpa [prefixWord, tailWord_4505937, baseEnd_4505937] using wordTrace_append hprefix tailTrace_4505937
  have hstable : (prefixWord ++ tailWord_4505937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505937).length < 2 ^ (prefixWord ++ tailWord_4505937).sum := by decide
  have hdescent : baseEnd_4505937 < baseStart_4505937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505943 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 9]
def baseStart_4505943 : Nat := 118140960795 + 4505943 * 2 ^ 59
def prefixEnd_4505943 : Nat := 4983230072969 + 3 ^ 40 * 4505943 * 2
def baseEnd_4505943 : Nat := 257079395640241023443339

theorem tailTrace_4505943 : CollatzResearch.WordTrace tailWord_4505943 prefixEnd_4505943 257079395640241023443339 := by
  unfold tailWord_4505943
  simp only [CollatzResearch.WordTrace]
  refine ⟨164345242714745539642202483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109563495143163693094801655 164345242714745539642202483)
  ·
    refine ⟨246517864072118309463303725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164345242714745539642202483 246517864072118309463303725)
    ·
      refine ⟨92444199027044366048738897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246517864072118309463303725 92444199027044366048738897)
      ·
        refine ⟨69333149270283274536554173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92444199027044366048738897 69333149270283274536554173)
        ·
          refine ⟨25999930976356227951207815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69333149270283274536554173 25999930976356227951207815)
          ·
            refine ⟨38999896464534341926811723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25999930976356227951207815 38999896464534341926811723)
            ·
              refine ⟨58499844696801512890217585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38999896464534341926811723 58499844696801512890217585)
              ·
                refine ⟨43874883522601134667663189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58499844696801512890217585 43874883522601134667663189)
                ·
                  refine ⟨257079395640241023443339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43874883522601134667663189 257079395640241023443339)
                  ·
                    rfl

theorem cell23_4505943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 9].length) (baseStart_4505943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505943 prefixEnd_4505943 := by exact prefixLift 4505943
  have htrace : WordTrace (prefixWord ++ tailWord_4505943) baseStart_4505943 baseEnd_4505943 := by
    simpa [prefixWord, tailWord_4505943, baseEnd_4505943] using wordTrace_append hprefix tailTrace_4505943
  have hstable : (prefixWord ++ tailWord_4505943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505943).length < 2 ^ (prefixWord ++ tailWord_4505943).sum := by decide
  have hdescent : baseEnd_4505943 < baseStart_4505943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505948 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4505948 : Nat := 118140960795 + 4505948 * 2 ^ 59
def prefixEnd_4505948 : Nat := 4983230072969 + 3 ^ 40 * 4505948 * 2
def baseEnd_4505948 : Nat := 2313717128165441691427529

theorem tailTrace_4505948 : CollatzResearch.WordTrace tailWord_4505948 prefixEnd_4505948 2313717128165441691427529 := by
  unfold tailWord_4505948
  simp only [CollatzResearch.WordTrace]
  refine ⟨82172712539863712748067249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109563616719818283664089665 82172712539863712748067249)
  ·
    refine ⟨61629534404897784561050437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82172712539863712748067249 61629534404897784561050437)
    ·
      refine ⟨11555537700918334605196957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61629534404897784561050437 11555537700918334605196957)
      ·
        refine ⟨4333326637844375476948859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11555537700918334605196957 4333326637844375476948859)
        ·
          refine ⟨6499989956766563215423289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333326637844375476948859 6499989956766563215423289)
          ·
            refine ⟨4874992467574922411567467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6499989956766563215423289 4874992467574922411567467)
            ·
              refine ⟨7312488701362383617351201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4874992467574922411567467 7312488701362383617351201)
              ·
                refine ⟨5484366526021787713013401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7312488701362383617351201 5484366526021787713013401)
                ·
                  refine ⟨4113274894516340784760051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5484366526021787713013401 4113274894516340784760051)
                  ·
                    refine ⟨6169912341774511177140077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4113274894516340784760051 6169912341774511177140077)
                    ·
                      refine ⟨2313717128165441691427529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6169912341774511177140077 2313717128165441691427529)
                      ·
                        rfl

theorem cell23_4505948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4505948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505948 prefixEnd_4505948 := by exact prefixLift 4505948
  have htrace : WordTrace (prefixWord ++ tailWord_4505948) baseStart_4505948 baseEnd_4505948 := by
    simpa [prefixWord, tailWord_4505948, baseEnd_4505948] using wordTrace_append hprefix tailTrace_4505948
  have hstable : (prefixWord ++ tailWord_4505948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505948).length < 2 ^ (prefixWord ++ tailWord_4505948).sum := by decide
  have hdescent : baseEnd_4505948 < baseStart_4505948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505960 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 7]
def baseStart_4505960 : Nat := 118140960795 + 4505960 * 2 ^ 59
def prefixEnd_4505960 : Nat := 4983230072969 + 3 ^ 40 * 4505960 * 2
def baseEnd_4505960 : Nat := 257080365548143960497497

theorem tailTrace_4505960 : CollatzResearch.WordTrace tailWord_4505960 prefixEnd_4505960 257080365548143960497497 := by
  unfold tailWord_4505960
  simp only [CollatzResearch.WordTrace]
  refine ⟨82172931377841975772785667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109563908503789301030380889 82172931377841975772785667)
  ·
    refine ⟨123259397066762963659178501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82172931377841975772785667 123259397066762963659178501)
    ·
      refine ⟨23111136950018055686095969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123259397066762963659178501 23111136950018055686095969)
      ·
        refine ⟨17333352712513541764571977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23111136950018055686095969 17333352712513541764571977)
        ·
          refine ⟨13000014534385156323428983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17333352712513541764571977 13000014534385156323428983)
          ·
            refine ⟨19500021801577734485143475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13000014534385156323428983 19500021801577734485143475)
            ·
              refine ⟨29250032702366601727715213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19500021801577734485143475 29250032702366601727715213)
              ·
                refine ⟨10968762263387475647893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29250032702366601727715213 10968762263387475647893205)
                ·
                  refine ⟨257080365548143960497497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10968762263387475647893205 257080365548143960497497)
                  ·
                    rfl

theorem cell23_4505960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 7].length) (baseStart_4505960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505960 prefixEnd_4505960 := by exact prefixLift 4505960
  have htrace : WordTrace (prefixWord ++ tailWord_4505960) baseStart_4505960 baseEnd_4505960 := by
    simpa [prefixWord, tailWord_4505960, baseEnd_4505960] using wordTrace_append hprefix tailTrace_4505960
  have hstable : (prefixWord ++ tailWord_4505960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505960).length < 2 ^ (prefixWord ++ tailWord_4505960).sum := by decide
  have hdescent : baseEnd_4505960 < baseStart_4505960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4505983 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_4505983 : Nat := 118140960795 + 4505983 * 2 ^ 59
def prefixEnd_4505983 : Nat := 4983230072969 + 3 ^ 40 * 4505983 * 2
def baseEnd_4505983 : Nat := 2313735099988349054489867

theorem tailTrace_4505983 : CollatzResearch.WordTrace tailWord_4505983 prefixEnd_4505983 2313735099988349054489867 := by
  unfold tailWord_4505983
  simp only [CollatzResearch.WordTrace]
  refine ⟨164346701634600626473658603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109564467756400417649105735 164346701634600626473658603)
  ·
    refine ⟨246520052451900939710487905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164346701634600626473658603 246520052451900939710487905)
    ·
      refine ⟨184890039338925704782865929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246520052451900939710487905 184890039338925704782865929)
      ·
        refine ⟨138667529504194278587149447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184890039338925704782865929 138667529504194278587149447)
        ·
          refine ⟨208001294256291417880724171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138667529504194278587149447 208001294256291417880724171)
          ·
            refine ⟨312001941384437126821086257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208001294256291417880724171 312001941384437126821086257)
            ·
              refine ⟨234001456038327845115814693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312001941384437126821086257 234001456038327845115814693)
              ·
                refine ⟨43875273007186470959215255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234001456038327845115814693 43875273007186470959215255)
                ·
                  refine ⟨65812909510779706438822883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43875273007186470959215255 65812909510779706438822883)
                  ·
                    refine ⟨98719364266169559658234325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65812909510779706438822883 98719364266169559658234325)
                    ·
                      refine ⟨2313735099988349054489867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98719364266169559658234325 2313735099988349054489867)
                      ·
                        rfl

theorem cell23_4505983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_4505983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4505983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4505983 prefixEnd_4505983 := by exact prefixLift 4505983
  have htrace : WordTrace (prefixWord ++ tailWord_4505983) baseStart_4505983 baseEnd_4505983 := by
    simpa [prefixWord, tailWord_4505983, baseEnd_4505983] using wordTrace_append hprefix tailTrace_4505983
  have hstable : (prefixWord ++ tailWord_4505983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4505983).length < 2 ^ (prefixWord ++ tailWord_4505983).sum := by decide
  have hdescent : baseEnd_4505983 < baseStart_4505983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4505983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506044 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_4506044 : Nat := 118140960795 + 4506044 * 2 ^ 59
def prefixEnd_4506044 : Nat := 4983230072969 + 3 ^ 40 * 4506044 * 2
def baseEnd_4506044 : Nat := 2313766422308273315827087

theorem tailTrace_4506044 : CollatzResearch.WordTrace tailWord_4506044 prefixEnd_4506044 2313766422308273315827087 := by
  unfold tailWord_4506044
  simp only [CollatzResearch.WordTrace]
  refine ⟨82174463243689816945814593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109565950991586422594419457 82174463243689816945814593)
  ·
    refine ⟨61630847432767362709360945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82174463243689816945814593 61630847432767362709360945)
    ·
      refine ⟨46223135574575522032020709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61630847432767362709360945 46223135574575522032020709)
      ·
        refine ⟨8666837920232910381003883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46223135574575522032020709 8666837920232910381003883)
        ·
          refine ⟨13000256880349365571505825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8666837920232910381003883 13000256880349365571505825)
          ·
            refine ⟨9750192660262024178629369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13000256880349365571505825 9750192660262024178629369)
            ·
              refine ⟨7312644495196518133972027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9750192660262024178629369 7312644495196518133972027)
              ·
                refine ⟨10968966742794777200958041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7312644495196518133972027 10968966742794777200958041)
                ·
                  refine ⟨8226725057096082900718531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10968966742794777200958041 8226725057096082900718531)
                  ·
                    refine ⟨12340087585644124351077797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8226725057096082900718531 12340087585644124351077797)
                    ·
                      refine ⟨2313766422308273315827087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12340087585644124351077797 2313766422308273315827087)
                      ·
                        rfl

theorem cell23_4506044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_4506044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506044 prefixEnd_4506044 := by exact prefixLift 4506044
  have htrace : WordTrace (prefixWord ++ tailWord_4506044) baseStart_4506044 baseEnd_4506044 := by
    simpa [prefixWord, tailWord_4506044, baseEnd_4506044] using wordTrace_append hprefix tailTrace_4506044
  have hstable : (prefixWord ++ tailWord_4506044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506044).length < 2 ^ (prefixWord ++ tailWord_4506044).sum := by decide
  have hdescent : baseEnd_4506044 < baseStart_4506044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506080 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 5, 5]
def baseStart_4506080 : Nat := 118140960795 + 4506080 * 2 ^ 59
def prefixEnd_4506080 : Nat := 4983230072969 + 3 ^ 40 * 4506080 * 2
def baseEnd_4506080 : Nat := 771261635870611724992307

theorem tailTrace_4506080 : CollatzResearch.WordTrace tailWord_4506080 prefixEnd_4506080 771261635870611724992307 := by
  unfold tailWord_4506080
  simp only [CollatzResearch.WordTrace]
  refine ⟨82175119757624606019969847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 109566826343499474693293129 82175119757624606019969847)
  ·
    refine ⟨123262679636436909029954771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82175119757624606019969847 123262679636436909029954771)
    ·
      refine ⟨184894019454655363544932157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123262679636436909029954771 184894019454655363544932157)
      ·
        refine ⟨69335257295495761329349559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184894019454655363544932157 69335257295495761329349559)
        ·
          refine ⟨104002885943243641994024339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69335257295495761329349559 104002885943243641994024339)
          ·
            refine ⟨156004328914865462991036509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104002885943243641994024339 156004328914865462991036509)
            ·
              refine ⟨58501623343074548621638691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156004328914865462991036509 58501623343074548621638691)
              ·
                refine ⟨87752435014611822932458037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58501623343074548621638691 87752435014611822932458037)
                ·
                  refine ⟨8226790782619858399917941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87752435014611822932458037 8226790782619858399917941)
                  ·
                    refine ⟨771261635870611724992307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8226790782619858399917941 771261635870611724992307)
                    ·
                      rfl

theorem cell23_4506080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_4506080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506080 prefixEnd_4506080 := by exact prefixLift 4506080
  have htrace : WordTrace (prefixWord ++ tailWord_4506080) baseStart_4506080 baseEnd_4506080 := by
    simpa [prefixWord, tailWord_4506080, baseEnd_4506080] using wordTrace_append hprefix tailTrace_4506080
  have hstable : (prefixWord ++ tailWord_4506080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506080).length < 2 ^ (prefixWord ++ tailWord_4506080).sum := by decide
  have hdescent : baseEnd_4506080 < baseStart_4506080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506094 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_4506094 : Nat := 118140960795 + 4506094 * 2 ^ 59
def prefixEnd_4506094 : Nat := 4983230072969 + 3 ^ 40 * 4506094 * 2
def baseEnd_4506094 : Nat := 2313792096340998120201857

theorem tailTrace_4506094 : CollatzResearch.WordTrace tailWord_4506094 prefixEnd_4506094 2313792096340998120201857 := by
  unfold tailWord_4506094
  simp only [CollatzResearch.WordTrace]
  refine ⟨20543843767149811553868667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 109567166758132328287299557 20543843767149811553868667)
  ·
    refine ⟨30815765650724717330803001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20543843767149811553868667 30815765650724717330803001)
    ·
      refine ⟨23111824238043537998102251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30815765650724717330803001 23111824238043537998102251)
      ·
        refine ⟨34667736357065306997153377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23111824238043537998102251 34667736357065306997153377)
        ·
          refine ⟨26000802267798980247865033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34667736357065306997153377 26000802267798980247865033)
          ·
            refine ⟨19500601700849235185898775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26000802267798980247865033 19500601700849235185898775)
            ·
              refine ⟨29250902551273852778848163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19500601700849235185898775 29250902551273852778848163)
              ·
                refine ⟨43876353826910779168272245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29250902551273852778848163 43876353826910779168272245)
                ·
                  refine ⟨4113408171272885547025523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43876353826910779168272245 4113408171272885547025523)
                  ·
                    refine ⟨6170112256909328320538285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4113408171272885547025523 6170112256909328320538285)
                    ·
                      refine ⟨2313792096340998120201857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6170112256909328320538285 2313792096340998120201857)
                      ·
                        rfl

theorem cell23_4506094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_4506094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506094 prefixEnd_4506094 := by exact prefixLift 4506094
  have htrace : WordTrace (prefixWord ++ tailWord_4506094) baseStart_4506094 baseEnd_4506094 := by
    simpa [prefixWord, tailWord_4506094, baseEnd_4506094] using wordTrace_append hprefix tailTrace_4506094
  have hstable : (prefixWord ++ tailWord_4506094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506094).length < 2 ^ (prefixWord ++ tailWord_4506094).sum := by decide
  have hdescent : baseEnd_4506094 < baseStart_4506094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506097 : List Nat := [1, 2, 2, 2, 3, 1, 2, 4, 1, 5]
def baseStart_4506097 : Nat := 118140960795 + 4506097 * 2 ^ 59
def prefixEnd_4506097 : Nat := 4983230072969 + 3 ^ 40 * 4506097 * 2
def baseEnd_4506097 : Nat := 771264545594320536154781

theorem tailTrace_4506097 : CollatzResearch.WordTrace tailWord_4506097 prefixEnd_4506097 771264545594320536154781 := by
  unfold tailWord_4506097
  simp only [CollatzResearch.WordTrace]
  refine ⟨164350859556187623943308545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109567239704125082628872363 164350859556187623943308545)
  ·
    refine ⟨123263144667140717957481409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164350859556187623943308545 123263144667140717957481409)
    ·
      refine ⟨92447358500355538468111057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123263144667140717957481409 92447358500355538468111057)
      ·
        refine ⟨69335518875266653851083293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92447358500355538468111057 69335518875266653851083293)
        ·
          refine ⟨26000819578224995194156235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69335518875266653851083293 26000819578224995194156235)
          ·
            refine ⟨39001229367337492791234353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26000819578224995194156235 39001229367337492791234353)
            ·
              refine ⟨29250922025503119593425765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39001229367337492791234353 29250922025503119593425765)
              ·
                refine ⟨5484547879781834923767331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29250922025503119593425765 5484547879781834923767331)
                ·
                  refine ⟨8226821819672752385650997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5484547879781834923767331 8226821819672752385650997)
                  ·
                    refine ⟨771264545594320536154781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8226821819672752385650997 771264545594320536154781)
                    ·
                      rfl

theorem cell23_4506097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_4506097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506097 prefixEnd_4506097 := by exact prefixLift 4506097
  have htrace : WordTrace (prefixWord ++ tailWord_4506097) baseStart_4506097 baseEnd_4506097 := by
    simpa [prefixWord, tailWord_4506097, baseEnd_4506097] using wordTrace_append hprefix tailTrace_4506097
  have hstable : (prefixWord ++ tailWord_4506097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506097).length < 2 ^ (prefixWord ++ tailWord_4506097).sum := by decide
  have hdescent : baseEnd_4506097 < baseStart_4506097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506098 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_4506098 : Nat := 118140960795 + 4506098 * 2 ^ 59
def prefixEnd_4506098 : Nat := 4983230072969 + 3 ^ 40 * 4506098 * 2
def baseEnd_4506098 : Nat := 2313794150263616104551839

theorem tailTrace_4506098 : CollatzResearch.WordTrace tailWord_4506098 prefixEnd_4506098 2313794150263616104551839 := by
  unfold tailWord_4506098
  simp only [CollatzResearch.WordTrace]
  refine ⟨41087724007296000278523737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 109567264019456000742729965 41087724007296000278523737)
  ·
    refine ⟨30815793005472000208892803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41087724007296000278523737 30815793005472000208892803)
    ·
      refine ⟨46223689508208000313339205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30815793005472000208892803 46223689508208000313339205)
      ·
        refine ⟨8666941782789000058751101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46223689508208000313339205 8666941782789000058751101)
        ·
          refine ⟨3250103168545875022031663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8666941782789000058751101 3250103168545875022031663)
          ·
            refine ⟨4875154752818812533047495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3250103168545875022031663 4875154752818812533047495)
            ·
              refine ⟨7312732129228218799571243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4875154752818812533047495 7312732129228218799571243)
              ·
                refine ⟨10969098193842328199356865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7312732129228218799571243 10969098193842328199356865)
                ·
                  refine ⟨8226823645381746149517649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10969098193842328199356865 8226823645381746149517649)
                  ·
                    refine ⟨6170117734036309612138237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8226823645381746149517649 6170117734036309612138237)
                    ·
                      refine ⟨2313794150263616104551839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6170117734036309612138237 2313794150263616104551839)
                      ·
                        rfl

theorem cell23_4506098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_4506098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506098 prefixEnd_4506098 := by exact prefixLift 4506098
  have htrace : WordTrace (prefixWord ++ tailWord_4506098) baseStart_4506098 baseEnd_4506098 := by
    simpa [prefixWord, tailWord_4506098, baseEnd_4506098] using wordTrace_append hprefix tailTrace_4506098
  have hstable : (prefixWord ++ tailWord_4506098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506098).length < 2 ^ (prefixWord ++ tailWord_4506098).sum := by decide
  have hdescent : baseEnd_4506098 < baseStart_4506098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4506111 : List Nat := [1, 1, 2, 2, 1, 2, 6, 3, 1, 1, 3]
def baseStart_4506111 : Nat := 118140960795 + 4506111 * 2 ^ 59
def prefixEnd_4506111 : Nat := 4983230072969 + 3 ^ 40 * 4506111 * 2
def baseEnd_4506111 : Nat := 2313800825512124553689279

theorem tailTrace_4506111 : CollatzResearch.WordTrace tailWord_4506111 prefixEnd_4506111 2313800825512124553689279 := by
  unfold tailWord_4506111
  simp only [CollatzResearch.WordTrace]
  refine ⟨164351370178136904334318187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 109567580118757936222878791 164351370178136904334318187)
  ·
    refine ⟨246527055267205356501477281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164351370178136904334318187 246527055267205356501477281)
    ·
      refine ⟨184895291450404017376107961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 246527055267205356501477281 184895291450404017376107961)
      ·
        refine ⟨138671468587803013032080971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184895291450404017376107961 138671468587803013032080971)
        ·
          refine ⟨208007202881704519548121457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138671468587803013032080971 208007202881704519548121457)
          ·
            refine ⟨156005402161278389661091093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208007202881704519548121457 156005402161278389661091093)
            ·
              refine ⟨7312753226309924515363645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 156005402161278389661091093 7312753226309924515363645)
              ·
                refine ⟨2742282459866221693261367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7312753226309924515363645 2742282459866221693261367)
                ·
                  refine ⟨4113423689799332539892051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2742282459866221693261367 4113423689799332539892051)
                  ·
                    refine ⟨6170135534698998809838077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4113423689799332539892051 6170135534698998809838077)
                    ·
                      refine ⟨2313800825512124553689279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6170135534698998809838077 2313800825512124553689279)
                      ·
                        rfl

theorem cell23_4506111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_4506111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4506111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4506111 prefixEnd_4506111 := by exact prefixLift 4506111
  have htrace : WordTrace (prefixWord ++ tailWord_4506111) baseStart_4506111 baseEnd_4506111 := by
    simpa [prefixWord, tailWord_4506111, baseEnd_4506111] using wordTrace_append hprefix tailTrace_4506111
  have hstable : (prefixWord ++ tailWord_4506111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4506111).length < 2 ^ (prefixWord ++ tailWord_4506111).sum := by decide
  have hdescent : baseEnd_4506111 < baseStart_4506111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4506111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
