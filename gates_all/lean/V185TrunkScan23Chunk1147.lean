import V185TrunkScan23Chunk1146

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6794190 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_6794190 : Nat := 118140960795 + 6794190 * 2 ^ 59
def prefixEnd_6794190 : Nat := 4983230072969 + 3 ^ 40 * 6794190 * 2
def baseEnd_6794190 : Nat := 3488685127970877934079095

theorem tailTrace_6794190 : CollatzResearch.WordTrace tailWord_6794190 prefixEnd_6794190 3488685127970877934079095 := by
  unfold tailWord_6794190
  simp only [CollatzResearch.WordTrace]
  refine ⟨30975558406977182514563503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165202978170544973411005349 30975558406977182514563503)
  ·
    refine ⟨46463337610465773771845255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30975558406977182514563503 46463337610465773771845255)
    ·
      refine ⟨69695006415698660657767883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46463337610465773771845255 69695006415698660657767883)
      ·
        refine ⟨104542509623547990986651825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69695006415698660657767883 104542509623547990986651825)
        ·
          refine ⟨78406882217660993239988869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104542509623547990986651825 78406882217660993239988869)
          ·
            refine ⟨14701290415811436232497913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78406882217660993239988869 14701290415811436232497913)
            ·
              refine ⟨11025967811858577174373435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14701290415811436232497913 11025967811858577174373435)
              ·
                refine ⟨16538951717787865761560153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11025967811858577174373435 16538951717787865761560153)
                ·
                  refine ⟨12404213788340899321170115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16538951717787865761560153 12404213788340899321170115)
                  ·
                    refine ⟨18606320682511348981755173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12404213788340899321170115 18606320682511348981755173)
                    ·
                      refine ⟨3488685127970877934079095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18606320682511348981755173 3488685127970877934079095)
                      ·
                        rfl

theorem cell23_6794190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_6794190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794190 prefixEnd_6794190 := by exact prefixLift 6794190
  have htrace : WordTrace (prefixWord ++ tailWord_6794190) baseStart_6794190 baseEnd_6794190 := by
    simpa [prefixWord, tailWord_6794190, baseEnd_6794190] using wordTrace_append hprefix tailTrace_6794190
  have hstable : (prefixWord ++ tailWord_6794190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794190).length < 2 ^ (prefixWord ++ tailWord_6794190).sum := by decide
  have hdescent : baseEnd_6794190 < baseStart_6794190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794230 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_6794230 : Nat := 118140960795 + 6794230 * 2 ^ 59
def prefixEnd_6794230 : Nat := 4983230072969 + 3 ^ 40 * 6794230 * 2
def baseEnd_6794230 : Nat := 387633963021895308619879

theorem tailTrace_6794230 : CollatzResearch.WordTrace tailWord_6794230 prefixEnd_6794230 387633963021895308619879 := by
  unfold tailWord_6794230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15487870385979534184247759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165203950783781697965309429 15487870385979534184247759)
  ·
    refine ⟨23231805578969301276371639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15487870385979534184247759 23231805578969301276371639)
    ·
      refine ⟨34847708368453951914557459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23231805578969301276371639 34847708368453951914557459)
      ·
        refine ⟨52271562552680927871836189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34847708368453951914557459 52271562552680927871836189)
        ·
          refine ⟨19601835957255347951938571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52271562552680927871836189 19601835957255347951938571)
          ·
            refine ⟨29402753935883021927907857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19601835957255347951938571 29402753935883021927907857)
            ·
              refine ⟨22052065451912266445930893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29402753935883021927907857 22052065451912266445930893)
              ·
                refine ⟨8269524544467099917224085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22052065451912266445930893 8269524544467099917224085)
                ·
                  refine ⟨387633963021895308619879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8269524544467099917224085 387633963021895308619879)
                  ·
                    rfl

theorem cell23_6794230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_6794230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794230 prefixEnd_6794230 := by exact prefixLift 6794230
  have htrace : WordTrace (prefixWord ++ tailWord_6794230) baseStart_6794230 baseEnd_6794230 := by
    simpa [prefixWord, tailWord_6794230, baseEnd_6794230] using wordTrace_append hprefix tailTrace_6794230
  have hstable : (prefixWord ++ tailWord_6794230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794230).length < 2 ^ (prefixWord ++ tailWord_6794230).sum := by decide
  have hdescent : baseEnd_6794230 < baseStart_6794230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794274 : List Nat := [3, 3, 1, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_6794274 : Nat := 118140960795 + 6794274 * 2 ^ 59
def prefixEnd_6794274 : Nat := 4983230072969 + 3 ^ 40 * 6794274 * 2
def baseEnd_6794274 : Nat := 3488728260345855605428709

theorem tailTrace_6794274 : CollatzResearch.WordTrace tailWord_6794274 prefixEnd_6794274 3488728260345855605428709 := by
  unfold tailWord_6794274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61951882746878285615641469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165205020658342094975043917 61951882746878285615641469)
  ·
    refine ⟨23231956030079357105865551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61951882746878285615641469 23231956030079357105865551)
    ·
      refine ⟨34847934045119035658798327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23231956030079357105865551 34847934045119035658798327)
      ·
        refine ⟨52271901067678553488197491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34847934045119035658798327 52271901067678553488197491)
        ·
          refine ⟨78407851601517830232296237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52271901067678553488197491 78407851601517830232296237)
          ·
            refine ⟨29402944350569186337111089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78407851601517830232296237 29402944350569186337111089)
            ·
              refine ⟨22052208262926889752833317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29402944350569186337111089 22052208262926889752833317)
              ·
                refine ⟨4134789049298791828656247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22052208262926889752833317 4134789049298791828656247)
                ·
                  refine ⟨6202183573948187742984371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4134789049298791828656247 6202183573948187742984371)
                  ·
                    refine ⟨9303275360922281614476557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6202183573948187742984371 9303275360922281614476557)
                    ·
                      refine ⟨3488728260345855605428709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9303275360922281614476557 3488728260345855605428709)
                      ·
                        rfl

theorem cell23_6794274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_6794274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794274 prefixEnd_6794274 := by exact prefixLift 6794274
  have htrace : WordTrace (prefixWord ++ tailWord_6794274) baseStart_6794274 baseEnd_6794274 := by
    simpa [prefixWord, tailWord_6794274, baseEnd_6794274] using wordTrace_append hprefix tailTrace_6794274
  have hstable : (prefixWord ++ tailWord_6794274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794274).length < 2 ^ (prefixWord ++ tailWord_6794274).sum := by decide
  have hdescent : baseEnd_6794274 < baseStart_6794274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794283 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5]
def baseStart_6794283 : Nat := 118140960795 + 6794283 * 2 ^ 59
def prefixEnd_6794283 : Nat := 4983230072969 + 3 ^ 40 * 6794283 * 2
def baseEnd_6794283 : Nat := 3488732881671746070216167

theorem tailTrace_6794283 : CollatzResearch.WordTrace tailWord_6794283 prefixEnd_6794283 3488732881671746070216167 := by
  unfold tailWord_6794283
  simp only [CollatzResearch.WordTrace]
  refine ⟨247807859244480536999643503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165205239496320357999762335 247807859244480536999643503)
  ·
    refine ⟨371711788866720805499465255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247807859244480536999643503 371711788866720805499465255)
    ·
      refine ⟨557567683300081208249197883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371711788866720805499465255 557567683300081208249197883)
      ·
        refine ⟨836351524950121812373796825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557567683300081208249197883 836351524950121812373796825)
        ·
          refine ⟨627263643712591359280347619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836351524950121812373796825 627263643712591359280347619)
          ·
            refine ⟨940895465568887038920521429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627263643712591359280347619 940895465568887038920521429)
            ·
              refine ⟨22052237474270789974699721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 940895465568887038920521429 22052237474270789974699721)
              ·
                refine ⟨16539178105703092481024791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22052237474270789974699721 16539178105703092481024791)
                ·
                  refine ⟨24808767158554638721537187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16539178105703092481024791 24808767158554638721537187)
                  ·
                    refine ⟨37213150737831958082305781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24808767158554638721537187 37213150737831958082305781)
                    ·
                      refine ⟨3488732881671746070216167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37213150737831958082305781 3488732881671746070216167)
                      ·
                        rfl

theorem cell23_6794283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 5].length) (baseStart_6794283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794283 prefixEnd_6794283 := by exact prefixLift 6794283
  have htrace : WordTrace (prefixWord ++ tailWord_6794283) baseStart_6794283 baseEnd_6794283 := by
    simpa [prefixWord, tailWord_6794283, baseEnd_6794283] using wordTrace_append hprefix tailTrace_6794283
  have hstable : (prefixWord ++ tailWord_6794283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794283).length < 2 ^ (prefixWord ++ tailWord_6794283).sum := by decide
  have hdescent : baseEnd_6794283 < baseStart_6794283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794297 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6794297 : Nat := 118140960795 + 6794297 * 2 ^ 59
def prefixEnd_6794297 : Nat := 4983230072969 + 3 ^ 40 * 6794297 * 2
def baseEnd_6794297 : Nat := 3488740070400909015441103

theorem tailTrace_6794297 : CollatzResearch.WordTrace tailWord_6794297 prefixEnd_6794297 3488740070400909015441103 := by
  unfold tailWord_6794297
  simp only [CollatzResearch.WordTrace]
  refine ⟨247808369866429817390653145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165205579910953211593768763 247808369866429817390653145)
  ·
    refine ⟨185856277399822363042989859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247808369866429817390653145 185856277399822363042989859)
    ·
      refine ⟨278784416099733544564484789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185856277399822363042989859 278784416099733544564484789)
      ·
        refine ⟨26136039009350019802920449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278784416099733544564484789 26136039009350019802920449)
        ·
          refine ⟨19602029257012514852190337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26136039009350019802920449 19602029257012514852190337)
          ·
            refine ⟨14701521942759386139142753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19602029257012514852190337 14701521942759386139142753)
            ·
              refine ⟨11026141457069539604357065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14701521942759386139142753 11026141457069539604357065)
              ·
                refine ⟨8269606092802154703267799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11026141457069539604357065 8269606092802154703267799)
                ·
                  refine ⟨12404409139203232054901699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8269606092802154703267799 12404409139203232054901699)
                  ·
                    refine ⟨18606613708804848082352549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12404409139203232054901699 18606613708804848082352549)
                    ·
                      refine ⟨3488740070400909015441103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18606613708804848082352549 3488740070400909015441103)
                      ·
                        rfl

theorem cell23_6794297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6794297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794297 prefixEnd_6794297 := by exact prefixLift 6794297
  have htrace : WordTrace (prefixWord ++ tailWord_6794297) baseStart_6794297 baseEnd_6794297 := by
    simpa [prefixWord, tailWord_6794297, baseEnd_6794297] using wordTrace_append hprefix tailTrace_6794297
  have hstable : (prefixWord ++ tailWord_6794297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794297).length < 2 ^ (prefixWord ++ tailWord_6794297).sum := by decide
  have hdescent : baseEnd_6794297 < baseStart_6794297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794317 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_6794317 : Nat := 118140960795 + 6794317 * 2 ^ 59
def prefixEnd_6794317 : Nat := 4983230072969 + 3 ^ 40 * 6794317 * 2
def baseEnd_6794317 : Nat := 3488750340013998937191011

theorem tailTrace_6794317 : CollatzResearch.WordTrace tailWord_6794317 prefixEnd_6794317 3488750340013998937191011 := by
  unfold tailWord_6794317
  simp only [CollatzResearch.WordTrace]
  refine ⟨247809099326357360806381205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165206066217571573870920803 247809099326357360806381205)
  ·
    refine ⟨11616051530923001287799119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247809099326357360806381205 11616051530923001287799119)
    ·
      refine ⟨17424077296384501931698679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11616051530923001287799119 17424077296384501931698679)
      ·
        refine ⟨26136115944576752897548019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17424077296384501931698679 26136115944576752897548019)
        ·
          refine ⟨39204173916865129346322029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26136115944576752897548019 39204173916865129346322029)
          ·
            refine ⟨14701565218824423504870761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39204173916865129346322029 14701565218824423504870761)
            ·
              refine ⟨11026173914118317628653071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14701565218824423504870761 11026173914118317628653071)
              ·
                refine ⟨16539260871177476442979607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026173914118317628653071 16539260871177476442979607)
                ·
                  refine ⟨24808891306766214664469411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16539260871177476442979607 24808891306766214664469411)
                  ·
                    refine ⟨37213336960149321996704117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24808891306766214664469411 37213336960149321996704117)
                    ·
                      refine ⟨3488750340013998937191011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37213336960149321996704117 3488750340013998937191011)
                      ·
                        rfl

theorem cell23_6794317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_6794317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794317 prefixEnd_6794317 := by exact prefixLift 6794317
  have htrace : WordTrace (prefixWord ++ tailWord_6794317) baseStart_6794317 baseEnd_6794317 := by
    simpa [prefixWord, tailWord_6794317, baseEnd_6794317] using wordTrace_append hprefix tailTrace_6794317
  have hstable : (prefixWord ++ tailWord_6794317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794317).length < 2 ^ (prefixWord ++ tailWord_6794317).sum := by decide
  have hdescent : baseEnd_6794317 < baseStart_6794317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794334 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6794334 : Nat := 118140960795 + 6794334 * 2 ^ 59
def prefixEnd_6794334 : Nat := 4983230072969 + 3 ^ 40 * 6794334 * 2
def baseEnd_6794334 : Nat := 3488759069185125370678433

theorem tailTrace_6794334 : CollatzResearch.WordTrace tailWord_6794334 prefixEnd_6794334 3488759069185125370678433 := by
  unfold tailWord_6794334
  simp only [CollatzResearch.WordTrace]
  refine ⟨30976214920911971588718757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165206479578197181806500037 30976214920911971588718757)
  ·
    refine ⟨5808040297670994672884767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30976214920911971588718757 5808040297670994672884767)
    ·
      refine ⟨8712060446506492009327151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5808040297670994672884767 8712060446506492009327151)
      ·
        refine ⟨13068090669759738013990727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712060446506492009327151 13068090669759738013990727)
        ·
          refine ⟨19602136004639607020986091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13068090669759738013990727 19602136004639607020986091)
          ·
            refine ⟨29403204006959410531479137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19602136004639607020986091 29403204006959410531479137)
            ·
              refine ⟨22052403005219557898609353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29403204006959410531479137 22052403005219557898609353)
              ·
                refine ⟨16539302253914668423957015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22052403005219557898609353 16539302253914668423957015)
                ·
                  refine ⟨24808953380872002635935523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16539302253914668423957015 24808953380872002635935523)
                  ·
                    refine ⟨37213430071308003953903285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24808953380872002635935523 37213430071308003953903285)
                    ·
                      refine ⟨3488759069185125370678433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37213430071308003953903285 3488759069185125370678433)
                      ·
                        rfl

theorem cell23_6794334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6794334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794334 prefixEnd_6794334 := by exact prefixLift 6794334
  have htrace : WordTrace (prefixWord ++ tailWord_6794334) baseStart_6794334 baseEnd_6794334 := by
    simpa [prefixWord, tailWord_6794334, baseEnd_6794334] using wordTrace_append hprefix tailTrace_6794334
  have hstable : (prefixWord ++ tailWord_6794334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794334).length < 2 ^ (prefixWord ++ tailWord_6794334).sum := by decide
  have hdescent : baseEnd_6794334 < baseStart_6794334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794340 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_6794340 : Nat := 118140960795 + 6794340 * 2 ^ 59
def prefixEnd_6794340 : Nat := 4983230072969 + 3 ^ 40 * 6794340 * 2
def baseEnd_6794340 : Nat := 3488762150069052347203405

theorem tailTrace_6794340 : CollatzResearch.WordTrace tailWord_6794340 prefixEnd_6794340 3488762150069052347203405 := by
  unfold tailWord_6794340
  simp only [CollatzResearch.WordTrace]
  refine ⟨123904969102637017867234237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165206625470182690489645649 123904969102637017867234237)
  ·
    refine ⟨46464363413488881700212839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123904969102637017867234237 46464363413488881700212839)
    ·
      refine ⟨69696545120233322550319259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46464363413488881700212839 69696545120233322550319259)
      ·
        refine ⟨104544817680349983825478889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69696545120233322550319259 104544817680349983825478889)
        ·
          refine ⟨78408613260262487869109167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104544817680349983825478889 78408613260262487869109167)
          ·
            refine ⟨117612919890393731803663751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78408613260262487869109167 117612919890393731803663751)
            ·
              refine ⟨176419379835590597705495627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117612919890393731803663751 176419379835590597705495627)
              ·
                refine ⟨264629069753385896558243441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176419379835590597705495627 264629069753385896558243441)
                ·
                  refine ⟨198471802315039422418682581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264629069753385896558243441 198471802315039422418682581)
                  ·
                    refine ⟨4651682866758736462937873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198471802315039422418682581 4651682866758736462937873)
                    ·
                      refine ⟨3488762150069052347203405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651682866758736462937873 3488762150069052347203405)
                      ·
                        rfl

theorem cell23_6794340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_6794340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794340 prefixEnd_6794340 := by exact prefixLift 6794340
  have htrace : WordTrace (prefixWord ++ tailWord_6794340) baseStart_6794340 baseEnd_6794340 := by
    simpa [prefixWord, tailWord_6794340, baseEnd_6794340] using wordTrace_append hprefix tailTrace_6794340
  have hstable : (prefixWord ++ tailWord_6794340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794340).length < 2 ^ (prefixWord ++ tailWord_6794340).sum := by decide
  have hdescent : baseEnd_6794340 < baseStart_6794340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794353 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_6794353 : Nat := 118140960795 + 6794353 * 2 ^ 59
def prefixEnd_6794353 : Nat := 4983230072969 + 3 ^ 40 * 6794353 * 2
def baseEnd_6794353 : Nat := 3488768825317560796340845

theorem tailTrace_6794353 : CollatzResearch.WordTrace tailWord_6794353 prefixEnd_6794353 3488768825317560796340845 := by
  unfold tailWord_6794353
  simp only [CollatzResearch.WordTrace]
  refine ⟨247810412354226938954691713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165206941569484625969794475 247810412354226938954691713)
  ·
    refine ⟨185857809265670204216018785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247810412354226938954691713 185857809265670204216018785)
    ·
      refine ⟨139393356949252653162014089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185857809265670204216018785 139393356949252653162014089)
      ·
        refine ⟨104545017711939489871510567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139393356949252653162014089 104545017711939489871510567)
        ·
          refine ⟨156817526567909234807265851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104545017711939489871510567 156817526567909234807265851)
          ·
            refine ⟨235226289851863852210898777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156817526567909234807265851 235226289851863852210898777)
            ·
              refine ⟨176419717388897889158174083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235226289851863852210898777 176419717388897889158174083)
              ·
                refine ⟨264629576083346833737261125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176419717388897889158174083 264629576083346833737261125)
                ·
                  refine ⟨49618045515627531325736461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264629576083346833737261125 49618045515627531325736461)
                  ·
                    refine ⟨18606767068360324247151173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49618045515627531325736461 18606767068360324247151173)
                    ·
                      refine ⟨3488768825317560796340845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18606767068360324247151173 3488768825317560796340845)
                      ·
                        rfl

theorem cell23_6794353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_6794353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794353 prefixEnd_6794353 := by exact prefixLift 6794353
  have htrace : WordTrace (prefixWord ++ tailWord_6794353) baseStart_6794353 baseEnd_6794353 := by
    simpa [prefixWord, tailWord_6794353, baseEnd_6794353] using wordTrace_append hprefix tailTrace_6794353
  have hstable : (prefixWord ++ tailWord_6794353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794353).length < 2 ^ (prefixWord ++ tailWord_6794353).sum := by decide
  have hdescent : baseEnd_6794353 < baseStart_6794353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794387 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 4, 2, 2]
def baseStart_6794387 : Nat := 118140960795 + 6794387 * 2 ^ 59
def prefixEnd_6794387 : Nat := 4983230072969 + 3 ^ 40 * 6794387 * 2
def baseEnd_6794387 : Nat := 3488786283659813663315689

theorem tailTrace_6794387 : CollatzResearch.WordTrace tailWord_6794387 prefixEnd_6794387 3488786283659813663315689 := by
  unfold tailWord_6794387
  simp only [CollatzResearch.WordTrace]
  refine ⟨247811652436103762761429415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165207768290735841840952943 247811652436103762761429415)
  ·
    refine ⟨371717478654155644142144123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247811652436103762761429415 371717478654155644142144123)
    ·
      refine ⟨557576217981233466213216185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371717478654155644142144123 557576217981233466213216185)
      ·
        refine ⟨418182163485925099659912139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557576217981233466213216185 418182163485925099659912139)
        ·
          refine ⟨627273245228887649489868209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418182163485925099659912139 627273245228887649489868209)
          ·
            refine ⟨470454933921665737117401157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627273245228887649489868209 470454933921665737117401157)
            ·
              refine ⟨88210300110312325709512717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 470454933921665737117401157 88210300110312325709512717)
              ·
                refine ⟨33078862541367122141067269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88210300110312325709512717 33078862541367122141067269)
                ·
                  refine ⟨6202286726506335401450113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33078862541367122141067269 6202286726506335401450113)
                  ·
                    refine ⟨4651715044879751551087585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6202286726506335401450113 4651715044879751551087585)
                    ·
                      refine ⟨3488786283659813663315689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651715044879751551087585 3488786283659813663315689)
                      ·
                        rfl

theorem cell23_6794387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 2, 2].length) (baseStart_6794387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794387 prefixEnd_6794387 := by exact prefixLift 6794387
  have htrace : WordTrace (prefixWord ++ tailWord_6794387) baseStart_6794387 baseEnd_6794387 := by
    simpa [prefixWord, tailWord_6794387, baseEnd_6794387] using wordTrace_append hprefix tailTrace_6794387
  have hstable : (prefixWord ++ tailWord_6794387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794387).length < 2 ^ (prefixWord ++ tailWord_6794387).sum := by decide
  have hdescent : baseEnd_6794387 < baseStart_6794387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794400 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_6794400 : Nat := 118140960795 + 6794400 * 2 ^ 59
def prefixEnd_6794400 : Nat := 4983230072969 + 3 ^ 40 * 6794400 * 2
def baseEnd_6794400 : Nat := 3488792958908322112453129

theorem tailTrace_6794400 : CollatzResearch.WordTrace tailWord_6794400 prefixEnd_6794400 3488792958908322112453129 := by
  unfold tailWord_6794400
  simp only [CollatzResearch.WordTrace]
  refine ⟨123906063292528332990826327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165208084390037777321101769 123906063292528332990826327)
  ·
    refine ⟨185859094938792499486239491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123906063292528332990826327 185859094938792499486239491)
    ·
      refine ⟨278788642408188749229359237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185859094938792499486239491 278788642408188749229359237)
      ·
        refine ⟨52272870451535390480504857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278788642408188749229359237 52272870451535390480504857)
        ·
          refine ⟨39204652838651542860378643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52272870451535390480504857 39204652838651542860378643)
          ·
            refine ⟨58806979257977314290567965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39204652838651542860378643 58806979257977314290567965)
            ·
              refine ⟨22052617221741492858962987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58806979257977314290567965 22052617221741492858962987)
              ·
                refine ⟨33078925832612239288444481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22052617221741492858962987 33078925832612239288444481)
                ·
                  refine ⟨24809194374459179466333361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33078925832612239288444481 24809194374459179466333361)
                  ·
                    refine ⟨18606895780844384599750021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24809194374459179466333361 18606895780844384599750021)
                    ·
                      refine ⟨3488792958908322112453129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18606895780844384599750021 3488792958908322112453129)
                      ·
                        rfl

theorem cell23_6794400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_6794400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794400 prefixEnd_6794400 := by exact prefixLift 6794400
  have htrace : WordTrace (prefixWord ++ tailWord_6794400) baseStart_6794400 baseEnd_6794400 := by
    simpa [prefixWord, tailWord_6794400, baseEnd_6794400] using wordTrace_append hprefix tailTrace_6794400
  have hstable : (prefixWord ++ tailWord_6794400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794400).length < 2 ^ (prefixWord ++ tailWord_6794400).sum := by decide
  have hdescent : baseEnd_6794400 < baseStart_6794400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794404 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_6794404 : Nat := 118140960795 + 6794404 * 2 ^ 59
def prefixEnd_6794404 : Nat := 4983230072969 + 3 ^ 40 * 6794404 * 2
def baseEnd_6794404 : Nat := 3488795012830940096803111

theorem tailTrace_6794404 : CollatzResearch.WordTrace tailWord_6794404 prefixEnd_6794404 3488795012830940096803111 := by
  unfold tailWord_6794404
  simp only [CollatzResearch.WordTrace]
  refine ⟨123906136238521087332399133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165208181651361449776532177 123906136238521087332399133)
  ·
    refine ⟨46464801089445407749649675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123906136238521087332399133 46464801089445407749649675)
    ·
      refine ⟨69697201634168111624474513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46464801089445407749649675 69697201634168111624474513)
      ·
        refine ⟨52272901225626083718355885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69697201634168111624474513 52272901225626083718355885)
        ·
          refine ⟨19602337959609781394383457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52272901225626083718355885 19602337959609781394383457)
          ·
            refine ⟨14701753469707336045787593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19602337959609781394383457 14701753469707336045787593)
            ·
              refine ⟨11026315102280502034340695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14701753469707336045787593 11026315102280502034340695)
              ·
                refine ⟨16539472653420753051511043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026315102280502034340695 16539472653420753051511043)
                ·
                  refine ⟨24809208980131129577266565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16539472653420753051511043 24809208980131129577266565)
                  ·
                    refine ⟨4651726683774586795737481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24809208980131129577266565 4651726683774586795737481)
                    ·
                      refine ⟨3488795012830940096803111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651726683774586795737481 3488795012830940096803111)
                      ·
                        rfl

theorem cell23_6794404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_6794404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794404 prefixEnd_6794404 := by exact prefixLift 6794404
  have htrace : WordTrace (prefixWord ++ tailWord_6794404) baseStart_6794404 baseEnd_6794404 := by
    simpa [prefixWord, tailWord_6794404, baseEnd_6794404] using wordTrace_append hprefix tailTrace_6794404
  have hstable : (prefixWord ++ tailWord_6794404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794404).length < 2 ^ (prefixWord ++ tailWord_6794404).sum := by decide
  have hdescent : baseEnd_6794404 < baseStart_6794404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794440 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 2, 5]
def baseStart_6794440 : Nat := 118140960795 + 6794440 * 2 ^ 59
def prefixEnd_6794440 : Nat := 4983230072969 + 3 ^ 40 * 6794440 * 2
def baseEnd_6794440 : Nat := 1162937832711500651984315

theorem tailTrace_6794440 : CollatzResearch.WordTrace tailWord_6794440 prefixEnd_6794440 1162937832711500651984315 := by
  unfold tailWord_6794440
  simp only [CollatzResearch.WordTrace]
  refine ⟨123906792752455876406554387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165209057003274501875405849 123906792752455876406554387)
  ·
    refine ⟨185860189128683814609831581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123906792752455876406554387 185860189128683814609831581)
    ·
      refine ⟨69697570923256430478686843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185860189128683814609831581 69697570923256430478686843)
      ·
        refine ⟨104546356384884645718030265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69697570923256430478686843 104546356384884645718030265)
        ·
          refine ⟨78409767288663484288522699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104546356384884645718030265 78409767288663484288522699)
          ·
            refine ⟨117614650932995226432784049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78409767288663484288522699 117614650932995226432784049)
            ·
              refine ⟨88210988199746419824588037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117614650932995226432784049 88210988199746419824588037)
              ·
                refine ⟨16539560287452453717110257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88210988199746419824588037 16539560287452453717110257)
                ·
                  refine ⟨12404670215589340287832693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16539560287452453717110257 12404670215589340287832693)
                  ·
                    refine ⟨1162937832711500651984315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12404670215589340287832693 1162937832711500651984315)
                    ·
                      rfl

theorem cell23_6794440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_6794440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794440 prefixEnd_6794440 := by exact prefixLift 6794440
  have htrace : WordTrace (prefixWord ++ tailWord_6794440) baseStart_6794440 baseEnd_6794440 := by
    simpa [prefixWord, tailWord_6794440, baseEnd_6794440] using wordTrace_append hprefix tailTrace_6794440
  have hstable : (prefixWord ++ tailWord_6794440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794440).length < 2 ^ (prefixWord ++ tailWord_6794440).sum := by decide
  have hdescent : baseEnd_6794440 < baseStart_6794440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794450 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6794450 : Nat := 118140960795 + 6794450 * 2 ^ 59
def prefixEnd_6794450 : Nat := 4983230072969 + 3 ^ 40 * 6794450 * 2
def baseEnd_6794450 : Nat := 3488818632941046916827899

theorem tailTrace_6794450 : CollatzResearch.WordTrace tailWord_6794450 prefixEnd_6794450 3488818632941046916827899 := by
  unfold tailWord_6794450
  simp only [CollatzResearch.WordTrace]
  refine ⟨61953487558718881130243201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165209300156583683013981869 61953487558718881130243201)
  ·
    refine ⟨46465115669039160847682401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61953487558718881130243201 46465115669039160847682401)
    ·
      refine ⟨34848836751779370635761801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46465115669039160847682401 34848836751779370635761801)
      ·
        refine ⟨26136627563834527976821351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34848836751779370635761801 26136627563834527976821351)
        ·
          refine ⟨39204941345751791965232027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26136627563834527976821351 39204941345751791965232027)
          ·
            refine ⟨58807412018627687947848041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39204941345751791965232027 58807412018627687947848041)
            ·
              refine ⟨44105559013970765960886031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58807412018627687947848041 44105559013970765960886031)
              ·
                refine ⟨66158338520956148941329047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44105559013970765960886031 66158338520956148941329047)
                ·
                  refine ⟨99237507781434223411993571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66158338520956148941329047 99237507781434223411993571)
                  ·
                    refine ⟨148856261672151335117990357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99237507781434223411993571 148856261672151335117990357)
                    ·
                      refine ⟨3488818632941046916827899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148856261672151335117990357 3488818632941046916827899)
                      ·
                        rfl

theorem cell23_6794450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6794450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794450 prefixEnd_6794450 := by exact prefixLift 6794450
  have htrace : WordTrace (prefixWord ++ tailWord_6794450) baseStart_6794450 baseEnd_6794450 := by
    simpa [prefixWord, tailWord_6794450, baseEnd_6794450] using wordTrace_append hprefix tailTrace_6794450
  have hstable : (prefixWord ++ tailWord_6794450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794450).length < 2 ^ (prefixWord ++ tailWord_6794450).sum := by decide
  have hdescent : baseEnd_6794450 < baseStart_6794450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794477 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6794477 : Nat := 118140960795 + 6794477 * 2 ^ 59
def prefixEnd_6794477 : Nat := 4983230072969 + 3 ^ 40 * 6794477 * 2
def baseEnd_6794477 : Nat := 3488832496918718311190275

theorem tailTrace_6794477 : CollatzResearch.WordTrace tailWord_6794477 prefixEnd_6794477 3488832496918718311190275 := by
  unfold tailWord_6794477
  simp only [CollatzResearch.WordTrace]
  refine ⟨247814935005777708132205685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165209956670518472088137123 247814935005777708132205685)
  ·
    refine ⟨23232650156791660137394283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247814935005777708132205685 23232650156791660137394283)
    ·
      refine ⟨34848975235187490206091425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23232650156791660137394283 34848975235187490206091425)
      ·
        refine ⟨26136731426390617654568569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34848975235187490206091425 26136731426390617654568569)
        ·
          refine ⟨19602548569792963240926427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26136731426390617654568569 19602548569792963240926427)
          ·
            refine ⟨29403822854689444861389641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19602548569792963240926427 29403822854689444861389641)
            ·
              refine ⟨22052867141017083646042231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29403822854689444861389641 22052867141017083646042231)
              ·
                refine ⟨33079300711525625469063347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22052867141017083646042231 33079300711525625469063347)
                ·
                  refine ⟨49618951067288438203595021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33079300711525625469063347 49618951067288438203595021)
                  ·
                    refine ⟨18607106650233164326348133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49618951067288438203595021 18607106650233164326348133)
                    ·
                      refine ⟨3488832496918718311190275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18607106650233164326348133 3488832496918718311190275)
                      ·
                        rfl

theorem cell23_6794477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6794477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794477 prefixEnd_6794477 := by exact prefixLift 6794477
  have htrace : WordTrace (prefixWord ++ tailWord_6794477) baseStart_6794477 baseEnd_6794477 := by
    simpa [prefixWord, tailWord_6794477, baseEnd_6794477] using wordTrace_append hprefix tailTrace_6794477
  have hstable : (prefixWord ++ tailWord_6794477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794477).length < 2 ^ (prefixWord ++ tailWord_6794477).sum := by decide
  have hdescent : baseEnd_6794477 < baseStart_6794477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794494 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6794494 : Nat := 118140960795 + 6794494 * 2 ^ 59
def prefixEnd_6794494 : Nat := 4983230072969 + 3 ^ 40 * 6794494 * 2
def baseEnd_6794494 : Nat := 3488841226089844744677697

theorem tailTrace_6794494 : CollatzResearch.WordTrace tailWord_6794494 prefixEnd_6794494 3488841226089844744677697 := by
  unfold tailWord_6794494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30976944380839515004446817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165210370031144080023716357 30976944380839515004446817)
  ·
    refine ⟨23232708285629636253335113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30976944380839515004446817 23232708285629636253335113)
    ·
      refine ⟨17424531214222227190001335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23232708285629636253335113 17424531214222227190001335)
      ·
        refine ⟨26136796821333340785002003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17424531214222227190001335 26136796821333340785002003)
        ·
          refine ⟨39205195232000011177503005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26136796821333340785002003 39205195232000011177503005)
          ·
            refine ⟨14701948212000004191563627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39205195232000011177503005 14701948212000004191563627)
            ·
              refine ⟨22052922318000006287345441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14701948212000004191563627 22052922318000006287345441)
              ·
                refine ⟨16539691738500004715509081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22052922318000006287345441 16539691738500004715509081)
                ·
                  refine ⟨12404768803875003536631811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16539691738500004715509081 12404768803875003536631811)
                  ·
                    refine ⟨18607153205812505304947717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12404768803875003536631811 18607153205812505304947717)
                    ·
                      refine ⟨3488841226089844744677697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18607153205812505304947717 3488841226089844744677697)
                      ·
                        rfl

theorem cell23_6794494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6794494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794494 prefixEnd_6794494 := by exact prefixLift 6794494
  have htrace : WordTrace (prefixWord ++ tailWord_6794494) baseStart_6794494 baseEnd_6794494 := by
    simpa [prefixWord, tailWord_6794494, baseEnd_6794494] using wordTrace_append hprefix tailTrace_6794494
  have hstable : (prefixWord ++ tailWord_6794494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794494).length < 2 ^ (prefixWord ++ tailWord_6794494).sum := by decide
  have hdescent : baseEnd_6794494 < baseStart_6794494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794497 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_6794497 : Nat := 118140960795 + 6794497 * 2 ^ 59
def prefixEnd_6794497 : Nat := 4983230072969 + 3 ^ 40 * 6794497 * 2
def baseEnd_6794497 : Nat := 3488842766531808232940183

theorem tailTrace_6794497 : CollatzResearch.WordTrace tailWord_6794497 prefixEnd_6794497 3488842766531808232940183 := by
  unfold tailWord_6794497
  simp only [CollatzResearch.WordTrace]
  refine ⟨247815664465705251547933745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165210442977136834365289163 247815664465705251547933745)
  ·
    refine ⟨185861748349278938660950309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247815664465705251547933745 185861748349278938660950309)
    ·
      refine ⟨34849077815489800998928183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185861748349278938660950309 34849077815489800998928183)
      ·
        refine ⟨52273616723234701498392275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34849077815489800998928183 52273616723234701498392275)
        ·
          refine ⟨78410425084852052247588413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52273616723234701498392275 78410425084852052247588413)
          ·
            refine ⟨29403909406819519592845655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78410425084852052247588413 29403909406819519592845655)
            ·
              refine ⟨44105864110229279389268483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29403909406819519592845655 44105864110229279389268483)
              ·
                refine ⟨66158796165343919083902725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44105864110229279389268483 66158796165343919083902725)
                ·
                  refine ⟨12404774281001984828231761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66158796165343919083902725 12404774281001984828231761)
                  ·
                    refine ⟨9303580710751488621173821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12404774281001984828231761 9303580710751488621173821)
                    ·
                      refine ⟨3488842766531808232940183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9303580710751488621173821 3488842766531808232940183)
                      ·
                        rfl

theorem cell23_6794497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_6794497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794497 prefixEnd_6794497 := by exact prefixLift 6794497
  have htrace : WordTrace (prefixWord ++ tailWord_6794497) baseStart_6794497 baseEnd_6794497 := by
    simpa [prefixWord, tailWord_6794497, baseEnd_6794497] using wordTrace_append hprefix tailTrace_6794497
  have hstable : (prefixWord ++ tailWord_6794497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794497).length < 2 ^ (prefixWord ++ tailWord_6794497).sum := by decide
  have hdescent : baseEnd_6794497 < baseStart_6794497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794554 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2]
def baseStart_6794554 : Nat := 118140960795 + 6794554 * 2 ^ 59
def prefixEnd_6794554 : Nat := 4983230072969 + 3 ^ 40 * 6794554 * 2
def baseEnd_6794554 : Nat := 3488872034929114509927421

theorem tailTrace_6794554 : CollatzResearch.WordTrace tailWord_6794554 prefixEnd_6794554 3488872034929114509927421 := by
  unfold tailWord_6794554
  simp only [CollatzResearch.WordTrace]
  refine ⟨61954435856624687570689679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165211828950999166855172477 61954435856624687570689679)
  ·
    refine ⟨92931653784937031356034519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61954435856624687570689679 92931653784937031356034519)
    ·
      refine ⟨139397480677405547034051779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92931653784937031356034519 139397480677405547034051779)
      ·
        refine ⟨209096221016108320551077669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139397480677405547034051779 209096221016108320551077669)
        ·
          refine ⟨39205541440520310103327063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209096221016108320551077669 39205541440520310103327063)
          ·
            refine ⟨58808312160780465154990595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39205541440520310103327063 58808312160780465154990595)
            ·
              refine ⟨88212468241170697732485893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58808312160780465154990595 88212468241170697732485893)
              ·
                refine ⟨16539837795219505824841105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88212468241170697732485893 16539837795219505824841105)
                ·
                  refine ⟨12404878346414629368630829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16539837795219505824841105 12404878346414629368630829)
                  ·
                    refine ⟨4651829379905486013236561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12404878346414629368630829 4651829379905486013236561)
                    ·
                      refine ⟨3488872034929114509927421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651829379905486013236561 3488872034929114509927421)
                      ·
                        rfl

theorem cell23_6794554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_6794554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794554 prefixEnd_6794554 := by exact prefixLift 6794554
  have htrace : WordTrace (prefixWord ++ tailWord_6794554) baseStart_6794554 baseEnd_6794554 := by
    simpa [prefixWord, tailWord_6794554, baseEnd_6794554] using wordTrace_append hprefix tailTrace_6794554
  have hstable : (prefixWord ++ tailWord_6794554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794554).length < 2 ^ (prefixWord ++ tailWord_6794554).sum := by decide
  have hdescent : baseEnd_6794554 < baseStart_6794554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794560 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 3, 6]
def baseStart_6794560 : Nat := 118140960795 + 6794560 * 2 ^ 59
def prefixEnd_6794560 : Nat := 4983230072969 + 3 ^ 40 * 6794560 * 2
def baseEnd_6794560 : Nat := 1162958371937680495484131

theorem tailTrace_6794560 : CollatzResearch.WordTrace tailWord_6794560 prefixEnd_6794560 1162958371937680495484131 := by
  unfold tailWord_6794560
  simp only [CollatzResearch.WordTrace]
  refine ⟨123908981132238506653738567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165211974842984675538318089 123908981132238506653738567)
  ·
    refine ⟨185863471698357759980607851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123908981132238506653738567 185863471698357759980607851)
    ·
      refine ⟨278795207547536639970911777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185863471698357759980607851 278795207547536639970911777)
      ·
        refine ⟨209096405660652479978183833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278795207547536639970911777 209096405660652479978183833)
        ·
          refine ⟨156822304245489359983637875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209096405660652479978183833 156822304245489359983637875)
          ·
            refine ⟨235233456368234039975456813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156822304245489359983637875 235233456368234039975456813)
            ·
              refine ⟨88212546138087764990796305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235233456368234039975456813 88212546138087764990796305)
              ·
                refine ⟨66159409603565823743097229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88212546138087764990796305 66159409603565823743097229)
                ·
                  refine ⟨24809778601337183903661461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66159409603565823743097229 24809778601337183903661461)
                  ·
                    refine ⟨1162958371937680495484131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24809778601337183903661461 1162958371937680495484131)
                    ·
                      rfl

theorem cell23_6794560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_6794560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794560 prefixEnd_6794560 := by exact prefixLift 6794560
  have htrace : WordTrace (prefixWord ++ tailWord_6794560) baseStart_6794560 baseEnd_6794560 := by
    simpa [prefixWord, tailWord_6794560, baseEnd_6794560] using wordTrace_append hprefix tailTrace_6794560
  have hstable : (prefixWord ++ tailWord_6794560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794560).length < 2 ^ (prefixWord ++ tailWord_6794560).sum := by decide
  have hdescent : baseEnd_6794560 < baseStart_6794560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794564 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6794564 : Nat := 118140960795 + 6794564 * 2 ^ 59
def prefixEnd_6794564 : Nat := 4983230072969 + 3 ^ 40 * 6794564 * 2
def baseEnd_6794564 : Nat := 1162959056578553156934125

theorem tailTrace_6794564 : CollatzResearch.WordTrace tailWord_6794564 prefixEnd_6794564 1162959056578553156934125 := by
  unfold tailWord_6794564
  simp only [CollatzResearch.WordTrace]
  refine ⟨123909054078231260995311373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165212072104308347993748497 123909054078231260995311373)
  ·
    refine ⟨46465895279336722873241765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123909054078231260995311373 46465895279336722873241765)
    ·
      refine ⟨8712355364875635538732831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46465895279336722873241765 8712355364875635538732831)
      ·
        refine ⟨13068533047313453308099247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712355364875635538732831 13068533047313453308099247)
        ·
          refine ⟨19602799570970179962148871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13068533047313453308099247 19602799570970179962148871)
          ·
            refine ⟨29404199356455269943223307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19602799570970179962148871 29404199356455269943223307)
            ·
              refine ⟨44106299034682904914834961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29404199356455269943223307 44106299034682904914834961)
              ·
                refine ⟨33079724276012178686126221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44106299034682904914834961 33079724276012178686126221)
                ·
                  refine ⟨12404896603504567007297333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33079724276012178686126221 12404896603504567007297333)
                  ·
                    refine ⟨1162959056578553156934125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12404896603504567007297333 1162959056578553156934125)
                    ·
                      rfl

theorem cell23_6794564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6794564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794564 prefixEnd_6794564 := by exact prefixLift 6794564
  have htrace : WordTrace (prefixWord ++ tailWord_6794564) baseStart_6794564 baseEnd_6794564 := by
    simpa [prefixWord, tailWord_6794564, baseEnd_6794564] using wordTrace_append hprefix tailTrace_6794564
  have hstable : (prefixWord ++ tailWord_6794564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794564).length < 2 ^ (prefixWord ++ tailWord_6794564).sum := by decide
  have hdescent : baseEnd_6794564 < baseStart_6794564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794567 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_6794567 : Nat := 118140960795 + 6794567 * 2 ^ 59
def prefixEnd_6794567 : Nat := 4983230072969 + 3 ^ 40 * 6794567 * 2
def baseEnd_6794567 : Nat := 3488878710177622959064861

theorem tailTrace_6794567 : CollatzResearch.WordTrace tailWord_6794567 prefixEnd_6794567 3488878710177622959064861 := by
  unfold tailWord_6794567
  simp only [CollatzResearch.WordTrace]
  refine ⟨247818217575451653502981955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165212145050301102335321303 247818217575451653502981955)
  ·
    refine ⟨371727326363177480254472933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247818217575451653502981955 371727326363177480254472933)
    ·
      refine ⟨69698873693095777547713675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371727326363177480254472933 69698873693095777547713675)
      ·
        refine ⟨104548310539643666321570513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69698873693095777547713675 104548310539643666321570513)
        ·
          refine ⟨78411232904732749741177885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104548310539643666321570513 78411232904732749741177885)
          ·
            refine ⟨29404212339274781152941707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78411232904732749741177885 29404212339274781152941707)
            ·
              refine ⟨44106318508912171729412561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29404212339274781152941707 44106318508912171729412561)
              ·
                refine ⟨33079738881684128797059421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44106318508912171729412561 33079738881684128797059421)
                ·
                  refine ⟨12404902080631548298897283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33079738881684128797059421 12404902080631548298897283)
                  ·
                    refine ⟨18607353120947322448345925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12404902080631548298897283 18607353120947322448345925)
                    ·
                      refine ⟨3488878710177622959064861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18607353120947322448345925 3488878710177622959064861)
                      ·
                        rfl

theorem cell23_6794567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_6794567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794567 prefixEnd_6794567 := by exact prefixLift 6794567
  have htrace : WordTrace (prefixWord ++ tailWord_6794567) baseStart_6794567 baseEnd_6794567 := by
    simpa [prefixWord, tailWord_6794567, baseEnd_6794567] using wordTrace_append hprefix tailTrace_6794567
  have hstable : (prefixWord ++ tailWord_6794567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794567).length < 2 ^ (prefixWord ++ tailWord_6794567).sum := by decide
  have hdescent : baseEnd_6794567 < baseStart_6794567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794577 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 1, 6]
def baseStart_6794577 : Nat := 118140960795 + 6794577 * 2 ^ 59
def prefixEnd_6794577 : Nat := 4983230072969 + 3 ^ 40 * 6794577 * 2
def baseEnd_6794577 : Nat := 1162961281661389306646605

theorem tailTrace_6794577 : CollatzResearch.WordTrace tailWord_6794577 prefixEnd_6794577 1162961281661389306646605 := by
  unfold tailWord_6794577
  simp only [CollatzResearch.WordTrace]
  refine ⟨247818582305415425210845985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165212388203610283473897323 247818582305415425210845985)
  ·
    refine ⟨185863936729061568908134489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247818582305415425210845985 185863936729061568908134489)
    ·
      refine ⟨139397952546796176681100867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185863936729061568908134489 139397952546796176681100867)
      ·
        refine ⟨209096928820194265021651301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139397952546796176681100867 209096928820194265021651301)
        ·
          refine ⟨39205674153786424691559619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209096928820194265021651301 39205674153786424691559619)
          ·
            refine ⟨58808511230679637037339429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39205674153786424691559619 58808511230679637037339429)
            ·
              refine ⟨11026595855752431944501143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58808511230679637037339429 11026595855752431944501143)
              ·
                refine ⟨16539893783628647916751715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026595855752431944501143 16539893783628647916751715)
                ·
                  refine ⟨24809840675442971875127573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16539893783628647916751715 24809840675442971875127573)
                  ·
                    refine ⟨1162961281661389306646605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24809840675442971875127573 1162961281661389306646605)
                    ·
                      rfl

theorem cell23_6794577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_6794577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794577 prefixEnd_6794577 := by exact prefixLift 6794577
  have htrace : WordTrace (prefixWord ++ tailWord_6794577) baseStart_6794577 baseEnd_6794577 := by
    simpa [prefixWord, tailWord_6794577, baseEnd_6794577] using wordTrace_append hprefix tailTrace_6794577
  have hstable : (prefixWord ++ tailWord_6794577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794577).length < 2 ^ (prefixWord ++ tailWord_6794577).sum := by decide
  have hdescent : baseEnd_6794577 < baseStart_6794577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794582 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6794582 : Nat := 118140960795 + 6794582 * 2 ^ 59
def prefixEnd_6794582 : Nat := 4983230072969 + 3 ^ 40 * 6794582 * 2
def baseEnd_6794582 : Nat := 3488886412387440400377293

theorem tailTrace_6794582 : CollatzResearch.WordTrace tailWord_6794582 prefixEnd_6794582 3488886412387440400377293 := by
  unfold tailWord_6794582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15488672791899831941548625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165212509780264874043185333 15488672791899831941548625)
  ·
    refine ⟨11616504593924873956161469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15488672791899831941548625 11616504593924873956161469)
    ·
      refine ⟨4356189222721827733560551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11616504593924873956161469 4356189222721827733560551)
      ·
        refine ⟨6534283834082741600340827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356189222721827733560551 6534283834082741600340827)
        ·
          refine ⟨9801425751124112400511241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534283834082741600340827 9801425751124112400511241)
          ·
            refine ⟨7351069313343084300383431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9801425751124112400511241 7351069313343084300383431)
            ·
              refine ⟨11026603970014626450575147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351069313343084300383431 11026603970014626450575147)
              ·
                refine ⟨16539905955021939675862721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11026603970014626450575147 16539905955021939675862721)
                ·
                  refine ⟨12404929466266454756897041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16539905955021939675862721 12404929466266454756897041)
                  ·
                    refine ⟨9303697099699841067672781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12404929466266454756897041 9303697099699841067672781)
                    ·
                      refine ⟨3488886412387440400377293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9303697099699841067672781 3488886412387440400377293)
                      ·
                        rfl

theorem cell23_6794582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6794582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794582 prefixEnd_6794582 := by exact prefixLift 6794582
  have htrace : WordTrace (prefixWord ++ tailWord_6794582) baseStart_6794582 baseEnd_6794582 := by
    simpa [prefixWord, tailWord_6794582, baseEnd_6794582] using wordTrace_append hprefix tailTrace_6794582
  have hstable : (prefixWord ++ tailWord_6794582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794582).length < 2 ^ (prefixWord ++ tailWord_6794582).sum := by decide
  have hdescent : baseEnd_6794582 < baseStart_6794582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794594 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6794594 : Nat := 118140960795 + 6794594 * 2 ^ 59
def prefixEnd_6794594 : Nat := 4983230072969 + 3 ^ 40 * 6794594 * 2
def baseEnd_6794594 : Nat := 1162964191385098117809079

theorem tailTrace_6794594 : CollatzResearch.WordTrace tailWord_6794594 prefixEnd_6794594 1162964191385098117809079 := by
  unfold tailWord_6794594
  simp only [CollatzResearch.WordTrace]
  refine ⟨61954800586588459278553709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165212801564235891409476557 61954800586588459278553709)
  ·
    refine ⟨23233050219970672229457641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61954800586588459278553709 23233050219970672229457641)
    ·
      refine ⟨17424787664978004172093231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23233050219970672229457641 17424787664978004172093231)
      ·
        refine ⟨26137181497467006258139847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17424787664978004172093231 26137181497467006258139847)
        ·
          refine ⟨39205772246200509387209771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26137181497467006258139847 39205772246200509387209771)
          ·
            refine ⟨58808658369300764080814657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39205772246200509387209771 58808658369300764080814657)
            ·
              refine ⟨44106493776975573060610993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58808658369300764080814657 44106493776975573060610993)
              ·
                refine ⟨33079870332731679795458245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44106493776975573060610993 33079870332731679795458245)
                ·
                  refine ⟨6202475687387189961648421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33079870332731679795458245 6202475687387189961648421)
                  ·
                    refine ⟨1162964191385098117809079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6202475687387189961648421 1162964191385098117809079)
                    ·
                      rfl

theorem cell23_6794594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6794594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794594 prefixEnd_6794594 := by exact prefixLift 6794594
  have htrace : WordTrace (prefixWord ++ tailWord_6794594) baseStart_6794594 baseEnd_6794594 := by
    simpa [prefixWord, tailWord_6794594, baseEnd_6794594] using wordTrace_append hprefix tailTrace_6794594
  have hstable : (prefixWord ++ tailWord_6794594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794594).length < 2 ^ (prefixWord ++ tailWord_6794594).sum := by decide
  have hdescent : baseEnd_6794594 < baseStart_6794594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794597 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_6794597 : Nat := 118140960795 + 6794597 * 2 ^ 59
def prefixEnd_6794597 : Nat := 4983230072969 + 3 ^ 40 * 6794597 * 2
def baseEnd_6794597 : Nat := 3488894114597257841689723

theorem tailTrace_6794597 : CollatzResearch.WordTrace tailWord_6794597 prefixEnd_6794597 3488894114597257841689723 := by
  unfold tailWord_6794597
  simp only [CollatzResearch.WordTrace]
  refine ⟨247819311765342968626574045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165212874510228645751049363 247819311765342968626574045)
  ·
    refine ⟨92932241912003613234965267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247819311765342968626574045 92932241912003613234965267)
    ·
      refine ⟨139398362868005419852447901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92932241912003613234965267 139398362868005419852447901)
      ·
        refine ⟨52274386075502032444667963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139398362868005419852447901 52274386075502032444667963)
        ·
          refine ⟨78411579113253048667001945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52274386075502032444667963 78411579113253048667001945)
          ·
            refine ⟨58808684334939786500251459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78411579113253048667001945 58808684334939786500251459)
            ·
              refine ⟨88213026502409679750377189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58808684334939786500251459 88213026502409679750377189)
              ·
                refine ⟨16539942469201814953195723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88213026502409679750377189 16539942469201814953195723)
                ·
                  refine ⟨24809913703802722429793585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16539942469201814953195723 24809913703802722429793585)
                  ·
                    refine ⟨18607435277852041822345189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24809913703802722429793585 18607435277852041822345189)
                    ·
                      refine ⟨3488894114597257841689723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18607435277852041822345189 3488894114597257841689723)
                      ·
                        rfl

theorem cell23_6794597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_6794597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794597 prefixEnd_6794597 := by exact prefixLift 6794597
  have htrace : WordTrace (prefixWord ++ tailWord_6794597) baseStart_6794597 baseEnd_6794597 := by
    simpa [prefixWord, tailWord_6794597, baseEnd_6794597] using wordTrace_append hprefix tailTrace_6794597
  have hstable : (prefixWord ++ tailWord_6794597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794597).length < 2 ^ (prefixWord ++ tailWord_6794597).sum := by decide
  have hdescent : baseEnd_6794597 < baseStart_6794597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794617 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 3]
def baseStart_6794617 : Nat := 118140960795 + 6794617 * 2 ^ 59
def prefixEnd_6794617 : Nat := 4983230072969 + 3 ^ 40 * 6794617 * 2
def baseEnd_6794617 : Nat := 3488904384210347763439631

theorem tailTrace_6794617 : CollatzResearch.WordTrace tailWord_6794617 prefixEnd_6794617 3488904384210347763439631 := by
  unfold tailWord_6794617
  simp only [CollatzResearch.WordTrace]
  refine ⟨247820041225270512042302105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165213360816847008028201403 247820041225270512042302105)
  ·
    refine ⟨185865030918952884031726579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247820041225270512042302105 185865030918952884031726579)
    ·
      refine ⟨278797546378429326047589869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185865030918952884031726579 278797546378429326047589869)
      ·
        refine ⟨104549079891910997267846201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278797546378429326047589869 104549079891910997267846201)
        ·
          refine ⟨78411809918933247950884651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104549079891910997267846201 78411809918933247950884651)
          ·
            refine ⟨117617714878399871926326977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78411809918933247950884651 117617714878399871926326977)
            ·
              refine ⟨88213286158799903944745233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117617714878399871926326977 88213286158799903944745233)
              ·
                refine ⟨66159964619099927958558925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88213286158799903944745233 66159964619099927958558925)
                ·
                  refine ⟨24809986732162472984459597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66159964619099927958558925 24809986732162472984459597)
                  ·
                    refine ⟨9303745024560927369172349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24809986732162472984459597 9303745024560927369172349)
                    ·
                      refine ⟨3488904384210347763439631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9303745024560927369172349 3488904384210347763439631)
                      ·
                        rfl

theorem cell23_6794617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_6794617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794617 prefixEnd_6794617 := by exact prefixLift 6794617
  have htrace : WordTrace (prefixWord ++ tailWord_6794617) baseStart_6794617 baseEnd_6794617 := by
    simpa [prefixWord, tailWord_6794617, baseEnd_6794617] using wordTrace_append hprefix tailTrace_6794617
  have hstable : (prefixWord ++ tailWord_6794617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794617).length < 2 ^ (prefixWord ++ tailWord_6794617).sum := by decide
  have hdescent : baseEnd_6794617 < baseStart_6794617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794638 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6794638 : Nat := 118140960795 + 6794638 * 2 ^ 59
def prefixEnd_6794638 : Nat := 4983230072969 + 3 ^ 40 * 6794638 * 2
def baseEnd_6794638 : Nat := 3488915167304092181277035

theorem tailTrace_6794638 : CollatzResearch.WordTrace tailWord_6794638 prefixEnd_6794638 3488915167304092181277035 := by
  unfold tailWord_6794638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30977600894774304078602071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165213871438796288419211045 30977600894774304078602071)
  ·
    refine ⟨46466401342161456117903107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30977600894774304078602071 46466401342161456117903107)
    ·
      refine ⟨69699602013242184176854661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46466401342161456117903107 69699602013242184176854661)
      ·
        refine ⟨13068675377482909533160249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69699602013242184176854661 13068675377482909533160249)
        ·
          refine ⟨9801506533112182149870187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13068675377482909533160249 9801506533112182149870187)
          ·
            refine ⟨14702259799668273224805281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9801506533112182149870187 14702259799668273224805281)
            ·
              refine ⟨11026694849751204918603961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14702259799668273224805281 11026694849751204918603961)
              ·
                refine ⟨8270021137313403688952971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11026694849751204918603961 8270021137313403688952971)
                ·
                  refine ⟨12405031705970105533429457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270021137313403688952971 12405031705970105533429457)
                  ·
                    refine ⟨9303773779477579150072093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12405031705970105533429457 9303773779477579150072093)
                    ·
                      refine ⟨3488915167304092181277035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9303773779477579150072093 3488915167304092181277035)
                      ·
                        rfl

theorem cell23_6794638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6794638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794638 prefixEnd_6794638 := by exact prefixLift 6794638
  have htrace : WordTrace (prefixWord ++ tailWord_6794638) baseStart_6794638 baseEnd_6794638 := by
    simpa [prefixWord, tailWord_6794638, baseEnd_6794638] using wordTrace_append hprefix tailTrace_6794638
  have hstable : (prefixWord ++ tailWord_6794638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794638).length < 2 ^ (prefixWord ++ tailWord_6794638).sum := by decide
  have hdescent : baseEnd_6794638 < baseStart_6794638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794674 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_6794674 : Nat := 118140960795 + 6794674 * 2 ^ 59
def prefixEnd_6794674 : Nat := 4983230072969 + 3 ^ 40 * 6794674 * 2
def baseEnd_6794674 : Nat := 3488933652607654040426869

theorem tailTrace_6794674 : CollatzResearch.WordTrace tailWord_6794674 prefixEnd_6794674 3488933652607654040426869 := by
  unfold tailWord_6794674
  simp only [CollatzResearch.WordTrace]
  refine ⟨61955530046516002694281769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165214746790709340518084717 61955530046516002694281769)
  ·
    refine ⟨46466647534887002020711327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61955530046516002694281769 46466647534887002020711327)
    ·
      refine ⟨69699971302330503031066991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46466647534887002020711327 69699971302330503031066991)
      ·
        refine ⟨104549956953495754546600487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69699971302330503031066991 104549956953495754546600487)
        ·
          refine ⟨156824935430243631819900731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104549956953495754546600487 156824935430243631819900731)
          ·
            refine ⟨235237403145365447729851097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156824935430243631819900731 235237403145365447729851097)
            ·
              refine ⟨176428052359024085797388323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235237403145365447729851097 176428052359024085797388323)
              ·
                refine ⟨264642078538536128696082485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176428052359024085797388323 264642078538536128696082485)
                ·
                  refine ⟨24810194862987762065257733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264642078538536128696082485 24810194862987762065257733)
                  ·
                    refine ⟨4651911536810205387235825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24810194862987762065257733 4651911536810205387235825)
                    ·
                      refine ⟨3488933652607654040426869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651911536810205387235825 3488933652607654040426869)
                      ·
                        rfl

theorem cell23_6794674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_6794674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794674 prefixEnd_6794674 := by exact prefixLift 6794674
  have htrace : WordTrace (prefixWord ++ tailWord_6794674) baseStart_6794674 baseEnd_6794674 := by
    simpa [prefixWord, tailWord_6794674, baseEnd_6794674] using wordTrace_append hprefix tailTrace_6794674
  have hstable : (prefixWord ++ tailWord_6794674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794674).length < 2 ^ (prefixWord ++ tailWord_6794674).sum := by decide
  have hdescent : baseEnd_6794674 < baseStart_6794674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794687 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_6794687 : Nat := 118140960795 + 6794687 * 2 ^ 59
def prefixEnd_6794687 : Nat := 4983230072969 + 3 ^ 40 * 6794687 * 2
def baseEnd_6794687 : Nat := 3488940327856162489564309

theorem tailTrace_6794687 : CollatzResearch.WordTrace tailWord_6794687 prefixEnd_6794687 3488940327856162489564309 := by
  unfold tailWord_6794687
  simp only [CollatzResearch.WordTrace]
  refine ⟨247822594335016913997350315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165215062890011275998233543 247822594335016913997350315)
  ·
    refine ⟨371733891502525370996025473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247822594335016913997350315 371733891502525370996025473)
    ·
      refine ⟨278800418626894028247019105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371733891502525370996025473 278800418626894028247019105)
      ·
        refine ⟨209100313970170521185264329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278800418626894028247019105 209100313970170521185264329)
        ·
          refine ⟨156825235477627890888948247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209100313970170521185264329 156825235477627890888948247)
          ·
            refine ⟨235237853216441836333422371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156825235477627890888948247 235237853216441836333422371)
            ·
              refine ⟨352856779824662754500133557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235237853216441836333422371 352856779824662754500133557)
              ·
                refine ⟨33080323108562133234387521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352856779824662754500133557 33080323108562133234387521)
                ·
                  refine ⟨24810242331421599925790641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33080323108562133234387521 24810242331421599925790641)
                  ·
                    refine ⟨18607681748566199944342981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24810242331421599925790641 18607681748566199944342981)
                    ·
                      refine ⟨3488940327856162489564309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18607681748566199944342981 3488940327856162489564309)
                      ·
                        rfl

theorem cell23_6794687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_6794687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794687 prefixEnd_6794687 := by exact prefixLift 6794687
  have htrace : WordTrace (prefixWord ++ tailWord_6794687) baseStart_6794687 baseEnd_6794687 := by
    simpa [prefixWord, tailWord_6794687, baseEnd_6794687] using wordTrace_append hprefix tailTrace_6794687
  have hstable : (prefixWord ++ tailWord_6794687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794687).length < 2 ^ (prefixWord ++ tailWord_6794687).sum := by decide
  have hdescent : baseEnd_6794687 < baseStart_6794687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794708 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_6794708 : Nat := 118140960795 + 6794708 * 2 ^ 59
def prefixEnd_6794708 : Nat := 4983230072969 + 3 ^ 40 * 6794708 * 2
def baseEnd_6794708 : Nat := 3488951110949906907401713

theorem tailTrace_6794708 : CollatzResearch.WordTrace tailWord_6794708 prefixEnd_6794708 3488951110949906907401713 := by
  unfold tailWord_6794708
  simp only [CollatzResearch.WordTrace]
  refine ⟨123911680133970417291932389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165215573511960556389243185 123911680133970417291932389)
  ·
    refine ⟨23233440025119453242237323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123911680133970417291932389 23233440025119453242237323)
    ·
      refine ⟨34850160037679179863355985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23233440025119453242237323 34850160037679179863355985)
      ·
        refine ⟨26137620028259384897516989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34850160037679179863355985 26137620028259384897516989)
        ·
          refine ⟨9801607510597269336568871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26137620028259384897516989 9801607510597269336568871)
          ·
            refine ⟨14702411265895904004853307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9801607510597269336568871 14702411265895904004853307)
            ·
              refine ⟨22053616898843856007279961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14702411265895904004853307 22053616898843856007279961)
              ·
                refine ⟨16540212674132892005459971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22053616898843856007279961 16540212674132892005459971)
                ·
                  refine ⟨24810319011199338008189957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16540212674132892005459971 24810319011199338008189957)
                  ·
                    refine ⟨4651934814599875876535617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24810319011199338008189957 4651934814599875876535617)
                    ·
                      refine ⟨3488951110949906907401713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651934814599875876535617 3488951110949906907401713)
                      ·
                        rfl

theorem cell23_6794708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_6794708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794708 prefixEnd_6794708 := by exact prefixLift 6794708
  have htrace : WordTrace (prefixWord ++ tailWord_6794708) baseStart_6794708 baseEnd_6794708 := by
    simpa [prefixWord, tailWord_6794708, baseEnd_6794708] using wordTrace_append hprefix tailTrace_6794708
  have hstable : (prefixWord ++ tailWord_6794708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794708).length < 2 ^ (prefixWord ++ tailWord_6794708).sum := by decide
  have hdescent : baseEnd_6794708 < baseStart_6794708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794725 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6794725 : Nat := 118140960795 + 6794725 * 2 ^ 59
def prefixEnd_6794725 : Nat := 4983230072969 + 3 ^ 40 * 6794725 * 2
def baseEnd_6794725 : Nat := 3488959840121033340889135

theorem tailTrace_6794725 : CollatzResearch.WordTrace tailWord_6794725 prefixEnd_6794725 3488959840121033340889135 := by
  unfold tailWord_6794725
  simp only [CollatzResearch.WordTrace]
  refine ⟨247823980308879246487233629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165215986872586164324822419 247823980308879246487233629)
  ·
    refine ⟨92933992615829717432712611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247823980308879246487233629 92933992615829717432712611)
    ·
      refine ⟨139400988923744576149068917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92933992615829717432712611 139400988923744576149068917)
      ·
        refine ⟨13068842711601054013975211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139400988923744576149068917 13068842711601054013975211)
        ·
          refine ⟨19603264067401581020962817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13068842711601054013975211 19603264067401581020962817)
          ·
            refine ⟨14702448050551185765722113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19603264067401581020962817 14702448050551185765722113)
            ·
              refine ⟨11026836037913389324291585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14702448050551185765722113 11026836037913389324291585)
              ·
                refine ⟨8270127028435041993218689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11026836037913389324291585 8270127028435041993218689)
                ·
                  refine ⟨6202595271326281494914017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8270127028435041993218689 6202595271326281494914017)
                  ·
                    refine ⟨4651946453494711121185513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6202595271326281494914017 4651946453494711121185513)
                    ·
                      refine ⟨3488959840121033340889135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651946453494711121185513 3488959840121033340889135)
                      ·
                        rfl

theorem cell23_6794725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6794725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794725 prefixEnd_6794725 := by exact prefixLift 6794725
  have htrace : WordTrace (prefixWord ++ tailWord_6794725) baseStart_6794725 baseEnd_6794725 := by
    simpa [prefixWord, tailWord_6794725, baseEnd_6794725] using wordTrace_append hprefix tailTrace_6794725
  have hstable : (prefixWord ++ tailWord_6794725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794725).length < 2 ^ (prefixWord ++ tailWord_6794725).sum := by decide
  have hdescent : baseEnd_6794725 < baseStart_6794725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794741 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6794741 : Nat := 118140960795 + 6794741 * 2 ^ 59
def prefixEnd_6794741 : Nat := 4983230072969 + 3 ^ 40 * 6794741 * 2
def baseEnd_6794741 : Nat := 3488968055811505278289061

theorem tailTrace_6794741 : CollatzResearch.WordTrace tailWord_6794741 prefixEnd_6794741 3488968055811505278289061 := by
  unfold tailWord_6794741
  simp only [CollatzResearch.WordTrace]
  refine ⟨247824563876821281219816077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165216375917880854146544051 247824563876821281219816077)
  ·
    refine ⟨92934211453807980457431029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247824563876821281219816077 92934211453807980457431029)
    ·
      refine ⟨8712582323794498167884159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92934211453807980457431029 8712582323794498167884159)
      ·
        refine ⟨13068873485691747251826239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712582323794498167884159 13068873485691747251826239)
        ·
          refine ⟨19603310228537620877739359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13068873485691747251826239 19603310228537620877739359)
          ·
            refine ⟨29404965342806431316609039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19603310228537620877739359 29404965342806431316609039)
            ·
              refine ⟨44107448014209646974913559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29404965342806431316609039 44107448014209646974913559)
              ·
                refine ⟨66161172021314470462370339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44107448014209646974913559 66161172021314470462370339)
                ·
                  refine ⟨99241758031971705693555509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66161172021314470462370339 99241758031971705693555509)
                  ·
                    refine ⟨9303914815497347408770829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99241758031971705693555509 9303914815497347408770829)
                    ·
                      refine ⟨3488968055811505278289061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9303914815497347408770829 3488968055811505278289061)
                      ·
                        rfl

theorem cell23_6794741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6794741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794741 prefixEnd_6794741 := by exact prefixLift 6794741
  have htrace : WordTrace (prefixWord ++ tailWord_6794741) baseStart_6794741 baseEnd_6794741 := by
    simpa [prefixWord, tailWord_6794741, baseEnd_6794741] using wordTrace_append hprefix tailTrace_6794741
  have hstable : (prefixWord ++ tailWord_6794741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794741).length < 2 ^ (prefixWord ++ tailWord_6794741).sum := by decide
  have hdescent : baseEnd_6794741 < baseStart_6794741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794747 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4]
def baseStart_6794747 : Nat := 118140960795 + 6794747 * 2 ^ 59
def prefixEnd_6794747 : Nat := 4983230072969 + 3 ^ 40 * 6794747 * 2
def baseEnd_6794747 : Nat := 3488971136695432254814033

theorem tailTrace_6794747 : CollatzResearch.WordTrace tailWord_6794747 prefixEnd_6794747 3488971136695432254814033 := by
  unfold tailWord_6794747
  simp only [CollatzResearch.WordTrace]
  refine ⟨247824782714799544244534495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165216521809866362829689663 247824782714799544244534495)
  ·
    refine ⟨371737174072199316366801743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247824782714799544244534495 371737174072199316366801743)
    ·
      refine ⟨557605761108298974550202615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371737174072199316366801743 557605761108298974550202615)
      ·
        refine ⟨836408641662448461825303923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557605761108298974550202615 836408641662448461825303923)
        ·
          refine ⟨1254612962493672692737955885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836408641662448461825303923 1254612962493672692737955885)
          ·
            refine ⟨470479860935127259776733457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1254612962493672692737955885 470479860935127259776733457)
            ·
              refine ⟨352859895701345444832550093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470479860935127259776733457 352859895701345444832550093)
              ·
                refine ⟨132322460888004541812206285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352859895701345444832550093 132322460888004541812206285)
                ·
                  refine ⟨49620922833001703179577357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132322460888004541812206285 49620922833001703179577357)
                  ·
                    refine ⟨18607846062375638692341509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49620922833001703179577357 18607846062375638692341509)
                    ·
                      refine ⟨3488971136695432254814033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18607846062375638692341509 3488971136695432254814033)
                      ·
                        rfl

theorem cell23_6794747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_6794747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794747 prefixEnd_6794747 := by exact prefixLift 6794747
  have htrace : WordTrace (prefixWord ++ tailWord_6794747) baseStart_6794747 baseEnd_6794747 := by
    simpa [prefixWord, tailWord_6794747, baseEnd_6794747] using wordTrace_append hprefix tailTrace_6794747
  have hstable : (prefixWord ++ tailWord_6794747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794747).length < 2 ^ (prefixWord ++ tailWord_6794747).sum := by decide
  have hdescent : baseEnd_6794747 < baseStart_6794747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794781 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_6794781 : Nat := 118140960795 + 6794781 * 2 ^ 59
def prefixEnd_6794781 : Nat := 4983230072969 + 3 ^ 40 * 6794781 * 2
def baseEnd_6794781 : Nat := 3488988595037685121788877

theorem tailTrace_6794781 : CollatzResearch.WordTrace tailWord_6794781 prefixEnd_6794781 3488988595037685121788877 := by
  unfold tailWord_6794781
  simp only [CollatzResearch.WordTrace]
  refine ⟨247826022796676368051272197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165217348531117578700848131 247826022796676368051272197)
  ·
    refine ⟨46467379274376819009613537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247826022796676368051272197 46467379274376819009613537)
    ·
      refine ⟨34850534455782614257210153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46467379274376819009613537 34850534455782614257210153)
      ·
        refine ⟨26137900841836960692907615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34850534455782614257210153 26137900841836960692907615)
        ·
          refine ⟨39206851262755441039361423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26137900841836960692907615 39206851262755441039361423)
          ·
            refine ⟨58810276894133161559042135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39206851262755441039361423 58810276894133161559042135)
            ·
              refine ⟨88215415341199742338563203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58810276894133161559042135 88215415341199742338563203)
              ·
                refine ⟨132323123011799613507844805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88215415341199742338563203 132323123011799613507844805)
                ·
                  refine ⟨24810585564712427532720901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132323123011799613507844805 24810585564712427532720901)
                  ·
                    refine ⟨4651984793383580162385169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24810585564712427532720901 4651984793383580162385169)
                    ·
                      refine ⟨3488988595037685121788877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651984793383580162385169 3488988595037685121788877)
                      ·
                        rfl

theorem cell23_6794781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_6794781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794781 prefixEnd_6794781 := by exact prefixLift 6794781
  have htrace : WordTrace (prefixWord ++ tailWord_6794781) baseStart_6794781 baseEnd_6794781 := by
    simpa [prefixWord, tailWord_6794781, baseEnd_6794781] using wordTrace_append hprefix tailTrace_6794781
  have hstable : (prefixWord ++ tailWord_6794781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794781).length < 2 ^ (prefixWord ++ tailWord_6794781).sum := by decide
  have hdescent : baseEnd_6794781 < baseStart_6794781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794794 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6794794 : Nat := 118140960795 + 6794794 * 2 ^ 59
def prefixEnd_6794794 : Nat := 4983230072969 + 3 ^ 40 * 6794794 * 2
def baseEnd_6794794 : Nat := 3488995270286193570926317

theorem tailTrace_6794794 : CollatzResearch.WordTrace tailWord_6794794 prefixEnd_6794794 3488995270286193570926317 := by
  unfold tailWord_6794794
  simp only [CollatzResearch.WordTrace]
  refine ⟨61956624236407317817873859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165217664630419514180996957 61956624236407317817873859)
  ·
    refine ⟨92934936354610976726810789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61956624236407317817873859 92934936354610976726810789)
    ·
      refine ⟨17425300566489558136277023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92934936354610976726810789 17425300566489558136277023)
      ·
        refine ⟨26137950849734337204415535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17425300566489558136277023 26137950849734337204415535)
        ·
          refine ⟨39206926274601505806623303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26137950849734337204415535 39206926274601505806623303)
          ·
            refine ⟨58810389411902258709934955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39206926274601505806623303 58810389411902258709934955)
            ·
              refine ⟨88215584117853388064902433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58810389411902258709934955 88215584117853388064902433)
              ·
                refine ⟨66161688088390041048676825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88215584117853388064902433 66161688088390041048676825)
                ·
                  refine ⟨49621266066292530786507619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66161688088390041048676825 49621266066292530786507619)
                  ·
                    refine ⟨74431899099438796179761429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49621266066292530786507619 74431899099438796179761429)
                    ·
                      refine ⟨3488995270286193570926317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74431899099438796179761429 3488995270286193570926317)
                      ·
                        rfl

theorem cell23_6794794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6794794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794794 prefixEnd_6794794 := by exact prefixLift 6794794
  have htrace : WordTrace (prefixWord ++ tailWord_6794794) baseStart_6794794 baseEnd_6794794 := by
    simpa [prefixWord, tailWord_6794794, baseEnd_6794794] using wordTrace_append hprefix tailTrace_6794794
  have hstable : (prefixWord ++ tailWord_6794794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794794).length < 2 ^ (prefixWord ++ tailWord_6794794).sum := by decide
  have hdescent : baseEnd_6794794 < baseStart_6794794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794798 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_6794798 : Nat := 118140960795 + 6794798 * 2 ^ 59
def prefixEnd_6794798 : Nat := 4983230072969 + 3 ^ 40 * 6794798 * 2
def baseEnd_6794798 : Nat := 3488997324208811555276299

theorem tailTrace_6794798 : CollatzResearch.WordTrace tailWord_6794798 prefixEnd_6794798 3488997324208811555276299 := by
  unfold tailWord_6794798
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978330354701847494330131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165217761891743186636427365 30978330354701847494330131)
  ·
    refine ⟨46467495532052771241495197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30978330354701847494330131 46467495532052771241495197)
    ·
      refine ⟨17425310824519789215560699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46467495532052771241495197 17425310824519789215560699)
      ·
        refine ⟨26137966236779683823341049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17425310824519789215560699 26137966236779683823341049)
        ·
          refine ⟨19603474677584762867505787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26137966236779683823341049 19603474677584762867505787)
          ·
            refine ⟨29405212016377144301258681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19603474677584762867505787 29405212016377144301258681)
            ·
              refine ⟨22053909012282858225944011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29405212016377144301258681 22053909012282858225944011)
              ·
                refine ⟨33080863518424287338916017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22053909012282858225944011 33080863518424287338916017)
                ·
                  refine ⟨24810647638818215504187013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33080863518424287338916017 24810647638818215504187013)
                  ·
                    refine ⟨4651996432278415407035065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24810647638818215504187013 4651996432278415407035065)
                    ·
                      refine ⟨3488997324208811555276299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4651996432278415407035065 3488997324208811555276299)
                      ·
                        rfl

theorem cell23_6794798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_6794798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794798 prefixEnd_6794798 := by exact prefixLift 6794798
  have htrace : WordTrace (prefixWord ++ tailWord_6794798) baseStart_6794798 baseEnd_6794798 := by
    simpa [prefixWord, tailWord_6794798, baseEnd_6794798] using wordTrace_append hprefix tailTrace_6794798
  have hstable : (prefixWord ++ tailWord_6794798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794798).length < 2 ^ (prefixWord ++ tailWord_6794798).sum := by decide
  have hdescent : baseEnd_6794798 < baseStart_6794798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794881 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 1, 6]
def baseStart_6794881 : Nat := 118140960795 + 6794881 * 2 ^ 59
def prefixEnd_6794881 : Nat := 4983230072969 + 3 ^ 40 * 6794881 * 2
def baseEnd_6794881 : Nat := 1163013314367711576846139

theorem tailTrace_6794881 : CollatzResearch.WordTrace tailWord_6794881 prefixEnd_6794881 1163013314367711576846139 := by
  unfold tailWord_6794881
  simp only [CollatzResearch.WordTrace]
  refine ⟨247829670096314085129912497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165219780064209390086608331 247829670096314085129912497)
  ·
    refine ⟨185872252572235563847434373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247829670096314085129912497 185872252572235563847434373)
    ·
      refine ⟨34851047357294168221393945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185872252572235563847434373 34851047357294168221393945)
      ·
        refine ⟨26138285517970626166045459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34851047357294168221393945 26138285517970626166045459)
        ·
          refine ⟨39207428276955939249068189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26138285517970626166045459 39207428276955939249068189)
          ·
            refine ⟨14702785603858477218400571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39207428276955939249068189 14702785603858477218400571)
            ·
              refine ⟨22054178405787715827600857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14702785603858477218400571 22054178405787715827600857)
              ·
                refine ⟨16540633804340786870700643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22054178405787715827600857 16540633804340786870700643)
                ·
                  refine ⟨24810950706511180306050965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16540633804340786870700643 24810950706511180306050965)
                  ·
                    refine ⟨1163013314367711576846139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24810950706511180306050965 1163013314367711576846139)
                    ·
                      rfl

theorem cell23_6794881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_6794881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794881 prefixEnd_6794881 := by exact prefixLift 6794881
  have htrace : WordTrace (prefixWord ++ tailWord_6794881) baseStart_6794881 baseEnd_6794881 := by
    simpa [prefixWord, tailWord_6794881, baseEnd_6794881] using wordTrace_append hprefix tailTrace_6794881
  have hstable : (prefixWord ++ tailWord_6794881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794881).length < 2 ^ (prefixWord ++ tailWord_6794881).sum := by decide
  have hdescent : baseEnd_6794881 < baseStart_6794881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794894 : List Nat := [4, 1, 1, 3, 1, 13]
def baseStart_6794894 : Nat := 118140960795 + 6794894 * 2 ^ 59
def prefixEnd_6794894 : Nat := 4983230072969 + 3 ^ 40 * 6794894 * 2
def baseEnd_6794894 : Nat := 14358216536426515142699

theorem tailTrace_6794894 : CollatzResearch.WordTrace tailWord_6794894 prefixEnd_6794894 14358216536426515142699 := by
  unfold tailWord_6794894
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978768030658373543766967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165220096163511325566757157 30978768030658373543766967)
  ·
    refine ⟨46468152045987560315650451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30978768030658373543766967 46468152045987560315650451)
    ·
      refine ⟨69702228068981340473475677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46468152045987560315650451 69702228068981340473475677)
      ·
        refine ⟨26138335525868002677553379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69702228068981340473475677 26138335525868002677553379)
        ·
          refine ⟨39207503288802004016330069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26138335525868002677553379 39207503288802004016330069)
          ·
            refine ⟨14358216536426515142699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 39207503288802004016330069 14358216536426515142699)
            ·
              rfl

theorem cell23_6794894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 13].length) (baseStart_6794894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794894 prefixEnd_6794894 := by exact prefixLift 6794894
  have htrace : WordTrace (prefixWord ++ tailWord_6794894) baseStart_6794894 baseEnd_6794894 := by
    simpa [prefixWord, tailWord_6794894, baseEnd_6794894] using wordTrace_append hprefix tailTrace_6794894
  have hstable : (prefixWord ++ tailWord_6794894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794894).length < 2 ^ (prefixWord ++ tailWord_6794894).sum := by decide
  have hdescent : baseEnd_6794894 < baseStart_6794894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794942 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_6794942 : Nat := 118140960795 + 6794942 * 2 ^ 59
def prefixEnd_6794942 : Nat := 4983230072969 + 3 ^ 40 * 6794942 * 2
def baseEnd_6794942 : Nat := 3489071265423058991875637

theorem tailTrace_6794942 : CollatzResearch.WordTrace tailWord_6794942 prefixEnd_6794942 3489071265423058991875637 := by
  unfold tailWord_6794942
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978986868636636568485385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165221263299395395031922053 30978986868636636568485385)
  ·
    refine ⟨23234240151477477426364039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30978986868636636568485385 23234240151477477426364039)
    ·
      refine ⟨34851360227216216139546059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23234240151477477426364039 34851360227216216139546059)
      ·
        refine ⟨52277040340824324209319089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34851360227216216139546059 52277040340824324209319089)
        ·
          refine ⟨39207780255618243156989317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52277040340824324209319089 39207780255618243156989317)
          ·
            refine ⟨7351458797928420591935497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39207780255618243156989317 7351458797928420591935497)
            ·
              refine ⟨5513594098446315443951623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7351458797928420591935497 5513594098446315443951623)
              ·
                refine ⟨8270391147669473165927435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513594098446315443951623 8270391147669473165927435)
                ·
                  refine ⟨12405586721504209748891153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270391147669473165927435 12405586721504209748891153)
                  ·
                    refine ⟨9304190041128157311668365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12405586721504209748891153 9304190041128157311668365)
                    ·
                      refine ⟨3489071265423058991875637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304190041128157311668365 3489071265423058991875637)
                      ·
                        rfl

theorem cell23_6794942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_6794942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794942 prefixEnd_6794942 := by exact prefixLift 6794942
  have htrace : WordTrace (prefixWord ++ tailWord_6794942) baseStart_6794942 baseEnd_6794942 := by
    simpa [prefixWord, tailWord_6794942, baseEnd_6794942] using wordTrace_append hprefix tailTrace_6794942
  have hstable : (prefixWord ++ tailWord_6794942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794942).length < 2 ^ (prefixWord ++ tailWord_6794942).sum := by decide
  have hdescent : baseEnd_6794942 < baseStart_6794942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794972 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6794972 : Nat := 118140960795 + 6794972 * 2 ^ 59
def prefixEnd_6794972 : Nat := 4983230072969 + 3 ^ 40 * 6794972 * 2
def baseEnd_6794972 : Nat := 3489086669842693874500499

theorem tailTrace_6794972 : CollatzResearch.WordTrace tailWord_6794972 prefixEnd_6794972 3489086669842693874500499 := by
  unfold tailWord_6794972
  simp only [CollatzResearch.WordTrace]
  refine ⟨123916494569492203835737585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165221992759322938447650113 123916494569492203835737585)
  ·
    refine ⟨92937370927119152876803189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123916494569492203835737585 92937370927119152876803189)
    ·
      refine ⟨8712878524417420582200299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92937370927119152876803189 8712878524417420582200299)
      ·
        refine ⟨13069317786626130873300449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8712878524417420582200299 13069317786626130873300449)
        ·
          refine ⟨9801988339969598154975337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13069317786626130873300449 9801988339969598154975337)
          ·
            refine ⟨7351491254977198616231503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9801988339969598154975337 7351491254977198616231503)
            ·
              refine ⟨11027236882465797924347255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351491254977198616231503 11027236882465797924347255)
              ·
                refine ⟨16540855323698696886520883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11027236882465797924347255 16540855323698696886520883)
                ·
                  refine ⟨24811282985548045329781325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16540855323698696886520883 24811282985548045329781325)
                  ·
                    refine ⟨9304231119580516998667997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24811282985548045329781325 9304231119580516998667997)
                    ·
                      refine ⟨3489086669842693874500499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304231119580516998667997 3489086669842693874500499)
                      ·
                        rfl

theorem cell23_6794972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6794972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794972 prefixEnd_6794972 := by exact prefixLift 6794972
  have htrace : WordTrace (prefixWord ++ tailWord_6794972) baseStart_6794972 baseEnd_6794972 := by
    simpa [prefixWord, tailWord_6794972, baseEnd_6794972] using wordTrace_append hprefix tailTrace_6794972
  have hstable : (prefixWord ++ tailWord_6794972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794972).length < 2 ^ (prefixWord ++ tailWord_6794972).sum := by decide
  have hdescent : baseEnd_6794972 < baseStart_6794972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794981 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6794981 : Nat := 118140960795 + 6794981 * 2 ^ 59
def prefixEnd_6794981 : Nat := 4983230072969 + 3 ^ 40 * 6794981 * 2
def baseEnd_6794981 : Nat := 3489091291168584339287957

theorem tailTrace_6794981 : CollatzResearch.WordTrace tailWord_6794981 prefixEnd_6794981 3489091291168584339287957 := by
  unfold tailWord_6794981
  simp only [CollatzResearch.WordTrace]
  refine ⟨247833317395951802208552797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165222211597301201472368531 247833317395951802208552797)
  ·
    refine ⟨92937494023481925828207299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247833317395951802208552797 92937494023481925828207299)
    ·
      refine ⟨139406241035222888742310949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92937494023481925828207299 139406241035222888742310949)
      ·
        refine ⟨26138670194104291639183303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139406241035222888742310949 26138670194104291639183303)
        ·
          refine ⟨39208005291156437458774955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26138670194104291639183303 39208005291156437458774955)
          ·
            refine ⟨58812007936734656188162433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39208005291156437458774955 58812007936734656188162433)
            ·
              refine ⟨44109005952550992141121825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58812007936734656188162433 44109005952550992141121825)
              ·
                refine ⟨33081754464413244105841369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44109005952550992141121825 33081754464413244105841369)
                ·
                  refine ⟨24811315848309933079381027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33081754464413244105841369 24811315848309933079381027)
                  ·
                    refine ⟨37216973772464899619071541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24811315848309933079381027 37216973772464899619071541)
                    ·
                      refine ⟨3489091291168584339287957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37216973772464899619071541 3489091291168584339287957)
                      ·
                        rfl

theorem cell23_6794981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6794981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794981 prefixEnd_6794981 := by exact prefixLift 6794981
  have htrace : WordTrace (prefixWord ++ tailWord_6794981) baseStart_6794981 baseEnd_6794981 := by
    simpa [prefixWord, tailWord_6794981, baseEnd_6794981] using wordTrace_append hprefix tailTrace_6794981
  have hstable : (prefixWord ++ tailWord_6794981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794981).length < 2 ^ (prefixWord ++ tailWord_6794981).sum := by decide
  have hdescent : baseEnd_6794981 < baseStart_6794981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6794998 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6794998 : Nat := 118140960795 + 6794998 * 2 ^ 59
def prefixEnd_6794998 : Nat := 4983230072969 + 3 ^ 40 * 6794998 * 2
def baseEnd_6794998 : Nat := 3489100020339710772775379

theorem tailTrace_6794998 : CollatzResearch.WordTrace tailWord_6794998 prefixEnd_6794998 3489100020339710772775379 := by
  unfold tailWord_6794998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15489621089805638381995103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165222624957926809407947765 15489621089805638381995103)
  ·
    refine ⟨23234431634708457572992655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15489621089805638381995103 23234431634708457572992655)
    ·
      refine ⟨34851647452062686359488983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23234431634708457572992655 34851647452062686359488983)
      ·
        refine ⟨52277471178094029539233475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34851647452062686359488983 52277471178094029539233475)
        ·
          refine ⟨78416206767141044308850213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52277471178094029539233475 78416206767141044308850213)
          ·
            refine ⟨14703038768838945807909415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78416206767141044308850213 14703038768838945807909415)
            ·
              refine ⟨22054558153258418711864123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14703038768838945807909415 22054558153258418711864123)
              ·
                refine ⟨33081837229887628067796185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22054558153258418711864123 33081837229887628067796185)
                ·
                  refine ⟨24811377922415721050847139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33081837229887628067796185 24811377922415721050847139)
                  ·
                    refine ⟨37217066883623581576270709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24811377922415721050847139 37217066883623581576270709)
                    ·
                      refine ⟨3489100020339710772775379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37217066883623581576270709 3489100020339710772775379)
                      ·
                        rfl

theorem cell23_6794998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6794998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6794998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6794998 prefixEnd_6794998 := by exact prefixLift 6794998
  have htrace : WordTrace (prefixWord ++ tailWord_6794998) baseStart_6794998 baseEnd_6794998 := by
    simpa [prefixWord, tailWord_6794998, baseEnd_6794998] using wordTrace_append hprefix tailTrace_6794998
  have hstable : (prefixWord ++ tailWord_6794998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6794998).length < 2 ^ (prefixWord ++ tailWord_6794998).sum := by decide
  have hdescent : baseEnd_6794998 < baseStart_6794998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6794998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795011 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 3]
def baseStart_6795011 : Nat := 118140960795 + 6795011 * 2 ^ 59
def prefixEnd_6795011 : Nat := 4983230072969 + 3 ^ 40 * 6795011 * 2
def baseEnd_6795011 : Nat := 3489106695588219221912819

theorem tailTrace_6795011 : CollatzResearch.WordTrace tailWord_6795011 prefixEnd_6795011 3489106695588219221912819 := by
  unfold tailWord_6795011
  simp only [CollatzResearch.WordTrace]
  refine ⟨247834411585843117332144887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165222941057228744888096591 247834411585843117332144887)
  ·
    refine ⟨371751617378764675998217331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247834411585843117332144887 371751617378764675998217331)
    ·
      refine ⟨557627426068147013997325997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371751617378764675998217331 557627426068147013997325997)
      ·
        refine ⟨209110284775555130248997249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557627426068147013997325997 209110284775555130248997249)
        ·
          refine ⟨156832713581666347686747937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209110284775555130248997249 156832713581666347686747937)
          ·
            refine ⟨117624535186249760765060953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156832713581666347686747937 117624535186249760765060953)
            ·
              refine ⟨88218401389687320573795715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117624535186249760765060953 88218401389687320573795715)
              ·
                refine ⟨132327602084530980860693573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88218401389687320573795715 132327602084530980860693573)
                ·
                  refine ⟨24811425390849558911380045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132327602084530980860693573 24811425390849558911380045)
                  ·
                    refine ⟨9304284521568584591767517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24811425390849558911380045 9304284521568584591767517)
                    ·
                      refine ⟨3489106695588219221912819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304284521568584591767517 3489106695588219221912819)
                      ·
                        rfl

theorem cell23_6795011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_6795011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795011 prefixEnd_6795011 := by exact prefixLift 6795011
  have htrace : WordTrace (prefixWord ++ tailWord_6795011) baseStart_6795011 baseEnd_6795011 := by
    simpa [prefixWord, tailWord_6795011, baseEnd_6795011] using wordTrace_append hprefix tailTrace_6795011
  have hstable : (prefixWord ++ tailWord_6795011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795011).length < 2 ^ (prefixWord ++ tailWord_6795011).sum := by decide
  have hdescent : baseEnd_6795011 < baseStart_6795011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795018 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 7]
def baseStart_6795018 : Nat := 118140960795 + 6795018 * 2 ^ 59
def prefixEnd_6795018 : Nat := 4983230072969 + 3 ^ 40 * 6795018 * 2
def baseEnd_6795018 : Nat := 387678921105866743836143

theorem tailTrace_6795018 : CollatzResearch.WordTrace tailWord_6795018 prefixEnd_6795018 387678921105866743836143 := by
  unfold tailWord_6795018
  simp only [CollatzResearch.WordTrace]
  refine ⟨61958666724204439381912427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165223111264545171685099805 61958666724204439381912427)
  ·
    refine ⟨92938000086306659072868641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61958666724204439381912427 92938000086306659072868641)
    ·
      refine ⟨69703500064729994304651481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92938000086306659072868641 69703500064729994304651481)
      ·
        refine ⟨52277625048547495728488611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69703500064729994304651481 52277625048547495728488611)
        ·
          refine ⟨78416437572821243592732917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52277625048547495728488611 78416437572821243592732917)
          ·
            refine ⟨7351541022451991586818711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78416437572821243592732917 7351541022451991586818711)
            ·
              refine ⟨11027311533677987380228067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351541022451991586818711 11027311533677987380228067)
              ·
                refine ⟨16540967300516981070342101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11027311533677987380228067 16540967300516981070342101)
                ·
                  refine ⟨387678921105866743836143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16540967300516981070342101 387678921105866743836143)
                  ·
                    rfl

theorem cell23_6795018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_6795018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795018 prefixEnd_6795018 := by exact prefixLift 6795018
  have htrace : WordTrace (prefixWord ++ tailWord_6795018) baseStart_6795018 baseEnd_6795018 := by
    simpa [prefixWord, tailWord_6795018, baseEnd_6795018] using wordTrace_append hprefix tailTrace_6795018
  have hstable : (prefixWord ++ tailWord_6795018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795018).length < 2 ^ (prefixWord ++ tailWord_6795018).sum := by decide
  have hdescent : baseEnd_6795018 < baseStart_6795018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795029 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_6795029 : Nat := 118140960795 + 6795029 * 2 ^ 59
def prefixEnd_6795029 : Nat := 4983230072969 + 3 ^ 40 * 6795029 * 2
def baseEnd_6795029 : Nat := 3489115938240000151487737

theorem tailTrace_6795029 : CollatzResearch.WordTrace tailWord_6795029 prefixEnd_6795029 3489115938240000151487737 := by
  unfold tailWord_6795029
  simp only [CollatzResearch.WordTrace]
  refine ⟨247835068099777906406300141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165223378733185270937533427 247835068099777906406300141)
  ·
    refine ⟨92938150537416714902362553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247835068099777906406300141 92938150537416714902362553)
    ·
      refine ⟨69703612903062536176771915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92938150537416714902362553 69703612903062536176771915)
      ·
        refine ⟨104555419354593804265157873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69703612903062536176771915 104555419354593804265157873)
        ·
          refine ⟨78416564515945353198868405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104555419354593804265157873 78416564515945353198868405)
          ·
            refine ⟨7351552923369876862393913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78416564515945353198868405 7351552923369876862393913)
            ·
              refine ⟨5513664692527407646795435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7351552923369876862393913 5513664692527407646795435)
              ·
                refine ⟨8270497038791111470193153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5513664692527407646795435 8270497038791111470193153)
                ·
                  refine ⟨6202872779093333602644865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8270497038791111470193153 6202872779093333602644865)
                  ·
                    refine ⟨4652154584320000201983649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6202872779093333602644865 4652154584320000201983649)
                    ·
                      refine ⟨3489115938240000151487737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652154584320000201983649 3489115938240000151487737)
                      ·
                        rfl

theorem cell23_6795029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_6795029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795029 prefixEnd_6795029 := by exact prefixLift 6795029
  have htrace : WordTrace (prefixWord ++ tailWord_6795029) baseStart_6795029 baseEnd_6795029 := by
    simpa [prefixWord, tailWord_6795029, baseEnd_6795029] using wordTrace_append hprefix tailTrace_6795029
  have hstable : (prefixWord ++ tailWord_6795029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795029).length < 2 ^ (prefixWord ++ tailWord_6795029).sum := by decide
  have hdescent : baseEnd_6795029 < baseStart_6795029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795048 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6795048 : Nat := 118140960795 + 6795048 * 2 ^ 59
def prefixEnd_6795048 : Nat := 4983230072969 + 3 ^ 40 * 6795048 * 2
def baseEnd_6795048 : Nat := 1163041898124145192383383

theorem tailTrace_6795048 : CollatzResearch.WordTrace tailWord_6795048 prefixEnd_6795048 1163041898124145192383383 := by
  unfold tailWord_6795048
  simp only [CollatzResearch.WordTrace]
  refine ⟨123917880543354536325620899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165223840724472715100827865 123917880543354536325620899)
  ·
    refine ⟨185876820815031804488431349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123917880543354536325620899 185876820815031804488431349)
    ·
      refine ⟨17425951951409231670790439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185876820815031804488431349 17425951951409231670790439)
      ·
        refine ⟨26138927927113847506185659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17425951951409231670790439 26138927927113847506185659)
        ·
          refine ⟨39208391890670771259278489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26138927927113847506185659 39208391890670771259278489)
          ·
            refine ⟨29406293918003078444458867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39208391890670771259278489 29406293918003078444458867)
            ·
              refine ⟨44109440877004617666688301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29406293918003078444458867 44109440877004617666688301)
              ·
                refine ⟨16541040328876731625008113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44109440877004617666688301 16541040328876731625008113)
                ·
                  refine ⟨12405780246657548718756085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16541040328876731625008113 12405780246657548718756085)
                  ·
                    refine ⟨1163041898124145192383383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12405780246657548718756085 1163041898124145192383383)
                    ·
                      rfl

theorem cell23_6795048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6795048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795048 prefixEnd_6795048 := by exact prefixLift 6795048
  have htrace : WordTrace (prefixWord ++ tailWord_6795048) baseStart_6795048 baseEnd_6795048 := by
    simpa [prefixWord, tailWord_6795048, baseEnd_6795048] using wordTrace_append hprefix tailTrace_6795048
  have hstable : (prefixWord ++ tailWord_6795048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795048).length < 2 ^ (prefixWord ++ tailWord_6795048).sum := by decide
  have hdescent : baseEnd_6795048 < baseStart_6795048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795068 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_6795068 : Nat := 118140960795 + 6795068 * 2 ^ 59
def prefixEnd_6795068 : Nat := 4983230072969 + 3 ^ 40 * 6795068 * 2
def baseEnd_6795068 : Nat := 3489135963985525498900057

theorem tailTrace_6795068 : CollatzResearch.WordTrace tailWord_6795068 prefixEnd_6795068 3489135963985525498900057 := by
  unfold tailWord_6795068
  simp only [CollatzResearch.WordTrace]
  refine ⟨123918245273318308033484929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165224327031091077377979905 123918245273318308033484929)
  ·
    refine ⟨92938683954988731025113697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123918245273318308033484929 92938683954988731025113697)
    ·
      refine ⟨69704012966241548268835273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92938683954988731025113697 69704012966241548268835273)
      ·
        refine ⟨52278009724681161201626455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69704012966241548268835273 52278009724681161201626455)
        ·
          refine ⟨78417014587021741802439683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52278009724681161201626455 78417014587021741802439683)
          ·
            refine ⟨117625521880532612703659525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78417014587021741802439683 117625521880532612703659525)
            ·
              refine ⟨22054785352599864881936161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117625521880532612703659525 22054785352599864881936161)
              ·
                refine ⟨16541089014449898661452121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22054785352599864881936161 16541089014449898661452121)
                ·
                  refine ⟨12405816760837423996089091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16541089014449898661452121 12405816760837423996089091)
                  ·
                    refine ⟨18608725141256135994133637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12405816760837423996089091 18608725141256135994133637)
                    ·
                      refine ⟨3489135963985525498900057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18608725141256135994133637 3489135963985525498900057)
                      ·
                        rfl

theorem cell23_6795068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_6795068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795068 prefixEnd_6795068 := by exact prefixLift 6795068
  have htrace : WordTrace (prefixWord ++ tailWord_6795068) baseStart_6795068 baseEnd_6795068 := by
    simpa [prefixWord, tailWord_6795068, baseEnd_6795068] using wordTrace_append hprefix tailTrace_6795068
  have hstable : (prefixWord ++ tailWord_6795068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795068).length < 2 ^ (prefixWord ++ tailWord_6795068).sum := by decide
  have hdescent : baseEnd_6795068 < baseStart_6795068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795095 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 3, 4]
def baseStart_6795095 : Nat := 118140960795 + 6795095 * 2 ^ 59
def prefixEnd_6795095 : Nat := 4983230072969 + 3 ^ 40 * 6795095 * 2
def baseEnd_6795095 : Nat := 1163049942654398964420811

theorem tailTrace_6795095 : CollatzResearch.WordTrace tailWord_6795095 prefixEnd_6795095 1163049942654398964420811 := by
  unfold tailWord_6795095
  simp only [CollatzResearch.WordTrace]
  refine ⟨247837475317538799678202739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165224983545025866452135159 247837475317538799678202739)
  ·
    refine ⟨371756212976308199517304109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247837475317538799678202739 371756212976308199517304109)
    ·
      refine ⟨139408579866115574818989041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371756212976308199517304109 139408579866115574818989041)
      ·
        refine ⟨104556434899586681114241781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139408579866115574818989041 104556434899586681114241781)
        ·
          refine ⟨9802165771836251354460167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104556434899586681114241781 9802165771836251354460167)
          ·
            refine ⟨14703248657754377031690251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9802165771836251354460167 14703248657754377031690251)
            ·
              refine ⟨22054872986631565547535377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14703248657754377031690251 22054872986631565547535377)
              ·
                refine ⟨16541154739973674160651533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22054872986631565547535377 16541154739973674160651533)
                ·
                  refine ⟨6202933027490127810244325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16541154739973674160651533 6202933027490127810244325)
                  ·
                    refine ⟨1163049942654398964420811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6202933027490127810244325 1163049942654398964420811)
                    ·
                      rfl

theorem cell23_6795095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_6795095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795095 prefixEnd_6795095 := by exact prefixLift 6795095
  have htrace : WordTrace (prefixWord ++ tailWord_6795095) baseStart_6795095 baseEnd_6795095 := by
    simpa [prefixWord, tailWord_6795095, baseEnd_6795095] using wordTrace_append hprefix tailTrace_6795095
  have hstable : (prefixWord ++ tailWord_6795095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795095).length < 2 ^ (prefixWord ++ tailWord_6795095).sum := by decide
  have hdescent : baseEnd_6795095 < baseStart_6795095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795112 : List Nat := [2, 1, 4, 2, 1, 1, 4, 3, 1, 4]
def baseStart_6795112 : Nat := 118140960795 + 6795112 * 2 ^ 59
def prefixEnd_6795112 : Nat := 4983230072969 + 3 ^ 40 * 6795112 * 2
def baseEnd_6795112 : Nat := 1163052852378107775583285

theorem tailTrace_6795112 : CollatzResearch.WordTrace tailWord_6795112 prefixEnd_6795112 1163052852378107775583285 := by
  unfold tailWord_6795112
  simp only [CollatzResearch.WordTrace]
  refine ⟨123919047679238605790785795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165225396905651474387714393 123919047679238605790785795)
  ·
    refine ⟨185878571518857908686178693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123919047679238605790785795 185878571518857908686178693)
    ·
      refine ⟨34852232159785857878658505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185878571518857908686178693 34852232159785857878658505)
      ·
        refine ⟨26139174119839393408993879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34852232159785857878658505 26139174119839393408993879)
        ·
          refine ⟨39208761179759090113490819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26139174119839393408993879 39208761179759090113490819)
          ·
            refine ⟨58813141769638635170236229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39208761179759090113490819 58813141769638635170236229)
            ·
              refine ⟨11027464081807244094419293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58813141769638635170236229 11027464081807244094419293)
              ·
                refine ⟨4135299030677716535407235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11027464081807244094419293 4135299030677716535407235)
                ·
                  refine ⟨6202948546016574803110853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135299030677716535407235 6202948546016574803110853)
                  ·
                    refine ⟨1163052852378107775583285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6202948546016574803110853 1163052852378107775583285)
                    ·
                      rfl

theorem cell23_6795112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_6795112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795112 prefixEnd_6795112 := by exact prefixLift 6795112
  have htrace : WordTrace (prefixWord ++ tailWord_6795112) baseStart_6795112 baseEnd_6795112 := by
    simpa [prefixWord, tailWord_6795112, baseEnd_6795112] using wordTrace_append hprefix tailTrace_6795112
  have hstable : (prefixWord ++ tailWord_6795112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795112).length < 2 ^ (prefixWord ++ tailWord_6795112).sum := by decide
  have hdescent : baseEnd_6795112 < baseStart_6795112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795185 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 4, 4]
def baseStart_6795185 : Nat := 118140960795 + 6795185 * 2 ^ 59
def prefixEnd_6795185 : Nat := 4983230072969 + 3 ^ 40 * 6795185 * 2
def baseEnd_6795185 : Nat := 1163065347074033847045673

theorem tailTrace_6795185 : CollatzResearch.WordTrace tailWord_6795185 prefixEnd_6795185 1163065347074033847045673 := by
  unfold tailWord_6795185
  simp only [CollatzResearch.WordTrace]
  refine ⟨247840757887212745048979009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165227171924808496699319339 247840757887212745048979009)
  ·
    refine ⟨185880568415409558786734257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247840757887212745048979009 185880568415409558786734257)
    ·
      refine ⟨139410426311557169090050693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185880568415409558786734257 139410426311557169090050693)
      ·
        refine ⟨26139454933416969204384505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139410426311557169090050693 26139454933416969204384505)
        ·
          refine ⟨19604591200062726903288379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26139454933416969204384505 19604591200062726903288379)
          ·
            refine ⟨29406886800094090354932569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19604591200062726903288379 29406886800094090354932569)
            ·
              refine ⟨22055165100070567766199427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29406886800094090354932569 22055165100070567766199427)
              ·
                refine ⟨33082747650105851649299141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22055165100070567766199427 33082747650105851649299141)
                ·
                  refine ⟨6203015184394847184243589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33082747650105851649299141 6203015184394847184243589)
                  ·
                    refine ⟨1163065347074033847045673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6203015184394847184243589 1163065347074033847045673)
                    ·
                      rfl

theorem cell23_6795185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_6795185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795185 prefixEnd_6795185 := by exact prefixLift 6795185
  have htrace : WordTrace (prefixWord ++ tailWord_6795185) baseStart_6795185 baseEnd_6795185 := by
    simpa [prefixWord, tailWord_6795185, baseEnd_6795185] using wordTrace_append hprefix tailTrace_6795185
  have hstable : (prefixWord ++ tailWord_6795185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795185).length < 2 ^ (prefixWord ++ tailWord_6795185).sum := by decide
  have hdescent : baseEnd_6795185 < baseStart_6795185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795198 : List Nat := [4, 2, 1, 1, 1, 3, 1, 10]
def baseStart_6795198 : Nat := 118140960795 + 6795198 * 2 ^ 59
def prefixEnd_6795198 : Nat := 4983230072969 + 3 ^ 40 * 6795198 * 2
def baseEnd_6795198 : Nat := 129229730239652221862017

theorem tailTrace_6795198 : CollatzResearch.WordTrace tailWord_6795198 prefixEnd_6795198 129229730239652221862017 := by
  unfold tailWord_6795198
  simp only [CollatzResearch.WordTrace]
  refine ⟨30980154004520706033650281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165227488024110432179468165 30980154004520706033650281)
  ·
    refine ⟨23235115503390529525237711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30980154004520706033650281 23235115503390529525237711)
    ·
      refine ⟨34852673255085794287856567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23235115503390529525237711 34852673255085794287856567)
      ·
        refine ⟨52279009882628691431784851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34852673255085794287856567 52279009882628691431784851)
        ·
          refine ⟨78418514823943037147677277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52279009882628691431784851 78418514823943037147677277)
          ·
            refine ⟨29406943058978638930378979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78418514823943037147677277 29406943058978638930378979)
            ·
              refine ⟨44110414588467958395568469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29406943058978638930378979 44110414588467958395568469)
              ·
                refine ⟨129229730239652221862017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44110414588467958395568469 129229730239652221862017)
                ·
                  rfl

theorem cell23_6795198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_6795198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795198 prefixEnd_6795198 := by exact prefixLift 6795198
  have htrace : WordTrace (prefixWord ++ tailWord_6795198) baseStart_6795198 baseEnd_6795198 := by
    simpa [prefixWord, tailWord_6795198, baseEnd_6795198] using wordTrace_append hprefix tailTrace_6795198
  have hstable : (prefixWord ++ tailWord_6795198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795198).length < 2 ^ (prefixWord ++ tailWord_6795198).sum := by decide
  have hdescent : baseEnd_6795198 < baseStart_6795198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795212 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_6795212 : Nat := 118140960795 + 6795212 * 2 ^ 59
def prefixEnd_6795212 : Nat := 4983230072969 + 3 ^ 40 * 6795212 * 2
def baseEnd_6795212 : Nat := 3489209905199772935499395

theorem tailTrace_6795212 : CollatzResearch.WordTrace tailWord_6795212 prefixEnd_6795212 3489209905199772935499395 := by
  unfold tailWord_6795212
  simp only [CollatzResearch.WordTrace]
  refine ⟨123920871329057464330105945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165227828438743285773474593 123920871329057464330105945)
  ·
    refine ⟨92940653496793098247579459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123920871329057464330105945 92940653496793098247579459)
    ·
      refine ⟨139410980245189647371369189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92940653496793098247579459 139410980245189647371369189)
      ·
        refine ⟨26139558795973058882131723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139410980245189647371369189 26139558795973058882131723)
        ·
          refine ⟨39209338193959588323197585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26139558795973058882131723 39209338193959588323197585)
          ·
            refine ⟨29407003645469691242398189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39209338193959588323197585 29407003645469691242398189)
            ·
              refine ⟨11027626367051134215899321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29407003645469691242398189 11027626367051134215899321)
              ·
                refine ⟨8270719775288350661924491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11027626367051134215899321 8270719775288350661924491)
                ·
                  refine ⟨12406079662932525992886737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270719775288350661924491 12406079662932525992886737)
                  ·
                    refine ⟨9304559747199394494665053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12406079662932525992886737 9304559747199394494665053)
                    ·
                      refine ⟨3489209905199772935499395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304559747199394494665053 3489209905199772935499395)
                      ·
                        rfl

theorem cell23_6795212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_6795212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795212 prefixEnd_6795212 := by exact prefixLift 6795212
  have htrace : WordTrace (prefixWord ++ tailWord_6795212) baseStart_6795212 baseEnd_6795212 := by
    simpa [prefixWord, tailWord_6795212, baseEnd_6795212] using wordTrace_append hprefix tailTrace_6795212
  have hstable : (prefixWord ++ tailWord_6795212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795212).length < 2 ^ (prefixWord ++ tailWord_6795212).sum := by decide
  have hdescent : baseEnd_6795212 < baseStart_6795212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795229 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6795229 : Nat := 118140960795 + 6795229 * 2 ^ 59
def prefixEnd_6795229 : Nat := 4983230072969 + 3 ^ 40 * 6795229 * 2
def baseEnd_6795229 : Nat := 3489218634370899368986817

theorem tailTrace_6795229 : CollatzResearch.WordTrace tailWord_6795229 prefixEnd_6795229 3489218634370899368986817 := by
  unfold tailWord_6795229
  simp only [CollatzResearch.WordTrace]
  refine ⟨247842362699053340563580741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165228241799368893709053827 247842362699053340563580741)
  ·
    refine ⟨46470443006072501355671389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247842362699053340563580741 46470443006072501355671389)
    ·
      refine ⟨17426416127277188008376771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46470443006072501355671389 17426416127277188008376771)
      ·
        refine ⟨26139624190915782012565157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17426416127277188008376771 26139624190915782012565157)
        ·
          refine ⟨4901179535796709127355967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26139624190915782012565157 4901179535796709127355967)
          ·
            refine ⟨7351769303695063691033951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901179535796709127355967 7351769303695063691033951)
            ·
              refine ⟨11027653955542595536550927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7351769303695063691033951 11027653955542595536550927)
              ·
                refine ⟨16541480933313893304826391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11027653955542595536550927 16541480933313893304826391)
                ·
                  refine ⟨24812221399970839957239587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16541480933313893304826391 24812221399970839957239587)
                  ·
                    refine ⟨37218332099956259935859381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24812221399970839957239587 37218332099956259935859381)
                    ·
                      refine ⟨3489218634370899368986817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37218332099956259935859381 3489218634370899368986817)
                      ·
                        rfl

theorem cell23_6795229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6795229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795229 prefixEnd_6795229 := by exact prefixLift 6795229
  have htrace : WordTrace (prefixWord ++ tailWord_6795229) baseStart_6795229 baseEnd_6795229 := by
    simpa [prefixWord, tailWord_6795229, baseEnd_6795229] using wordTrace_append hprefix tailTrace_6795229
  have hstable : (prefixWord ++ tailWord_6795229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795229).length < 2 ^ (prefixWord ++ tailWord_6795229).sum := by decide
  have hdescent : baseEnd_6795229 < baseStart_6795229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795248 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_6795248 : Nat := 118140960795 + 6795248 * 2 ^ 59
def prefixEnd_6795248 : Nat := 4983230072969 + 3 ^ 40 * 6795248 * 2
def baseEnd_6795248 : Nat := 3489228390503334794649229

theorem tailTrace_6795248 : CollatzResearch.WordTrace tailWord_6795248 prefixEnd_6795248 3489228390503334794649229 := by
  unfold tailWord_6795248
  simp only [CollatzResearch.WordTrace]
  refine ⟨123921527842992253404261199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165228703790656337872348265 123921527842992253404261199)
  ·
    refine ⟨185882291764488380106391799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123921527842992253404261199 185882291764488380106391799)
    ·
      refine ⟨278823437646732570159587699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185882291764488380106391799 278823437646732570159587699)
      ·
        refine ⟨418235156470098855239381549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278823437646732570159587699 418235156470098855239381549)
        ·
          refine ⟨156838183676287070714768081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418235156470098855239381549 156838183676287070714768081)
          ·
            refine ⟨117628637757215303036076061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156838183676287070714768081 117628637757215303036076061)
            ·
              refine ⟨44110739158955738638528523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117628637757215303036076061 44110739158955738638528523)
              ·
                refine ⟨66166108738433607957792785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44110739158955738638528523 66166108738433607957792785)
                ·
                  refine ⟨49624581553825205968344589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66166108738433607957792785 49624581553825205968344589)
                  ·
                    refine ⟨18609218082684452238129221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49624581553825205968344589 18609218082684452238129221)
                    ·
                      refine ⟨3489228390503334794649229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18609218082684452238129221 3489228390503334794649229)
                      ·
                        rfl

theorem cell23_6795248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_6795248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795248 prefixEnd_6795248 := by exact prefixLift 6795248
  have htrace : WordTrace (prefixWord ++ tailWord_6795248) baseStart_6795248 baseEnd_6795248 := by
    simpa [prefixWord, tailWord_6795248, baseEnd_6795248] using wordTrace_append hprefix tailTrace_6795248
  have hstable : (prefixWord ++ tailWord_6795248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795248).length < 2 ^ (prefixWord ++ tailWord_6795248).sum := by decide
  have hdescent : baseEnd_6795248 < baseStart_6795248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795277 : List Nat := [1, 7, 1, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6795277 : Nat := 118140960795 + 6795277 * 2 ^ 59
def prefixEnd_6795277 : Nat := 4983230072969 + 3 ^ 40 * 6795277 * 2
def baseEnd_6795277 : Nat := 3489243281442315181186597

theorem tailTrace_6795277 : CollatzResearch.WordTrace tailWord_6795277 prefixEnd_6795277 3489243281442315181186597 := by
  unfold tailWord_6795277
  simp only [CollatzResearch.WordTrace]
  refine ⟨247844113402879444761328085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165229408935252963174218723 247844113402879444761328085)
  ·
    refine ⟨5808846407879986986593627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 247844113402879444761328085 5808846407879986986593627)
    ·
      refine ⟨8713269611819980479890441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5808846407879986986593627 8713269611819980479890441)
      ·
        refine ⟨6534952208864985359917831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8713269611819980479890441 6534952208864985359917831)
        ·
          refine ⟨9802428313297478039876747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6534952208864985359917831 9802428313297478039876747)
          ·
            refine ⟨14703642469946217059815121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9802428313297478039876747 14703642469946217059815121)
            ·
              refine ⟨11027731852459662794861341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14703642469946217059815121 11027731852459662794861341)
              ·
                refine ⟨4135399444672373548073003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11027731852459662794861341 4135399444672373548073003)
                ·
                  refine ⟨6203099167008560322109505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135399444672373548073003 6203099167008560322109505)
                  ·
                    refine ⟨4652324375256420241582129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203099167008560322109505 4652324375256420241582129)
                    ·
                      refine ⟨3489243281442315181186597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652324375256420241582129 3489243281442315181186597)
                      ·
                        rfl

theorem cell23_6795277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6795277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795277 prefixEnd_6795277 := by exact prefixLift 6795277
  have htrace : WordTrace (prefixWord ++ tailWord_6795277) baseStart_6795277 baseEnd_6795277 := by
    simpa [prefixWord, tailWord_6795277, baseEnd_6795277] using wordTrace_append hprefix tailTrace_6795277
  have hstable : (prefixWord ++ tailWord_6795277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795277).length < 2 ^ (prefixWord ++ tailWord_6795277).sum := by decide
  have hdescent : baseEnd_6795277 < baseStart_6795277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795288 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 9]
def baseStart_6795288 : Nat := 118140960795 + 6795288 * 2 ^ 59
def prefixEnd_6795288 : Nat := 4983230072969 + 3 ^ 40 * 6795288 * 2
def baseEnd_6795288 : Nat := 387694325525501626461005

theorem tailTrace_6795288 : CollatzResearch.WordTrace tailWord_6795288 prefixEnd_6795288 387694325525501626461005 := by
  unfold tailWord_6795288
  simp only [CollatzResearch.WordTrace]
  refine ⟨123922257302919796819989259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165229676403893062426652345 123922257302919796819989259)
  ·
    refine ⟨185883385954379695229983889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123922257302919796819989259 185883385954379695229983889)
    ·
      refine ⟨139412539465784771422487917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185883385954379695229983889 139412539465784771422487917)
      ·
        refine ⟨52279702299669289283432969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139412539465784771422487917 52279702299669289283432969)
        ·
          refine ⟨39209776724751966962574727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52279702299669289283432969 39209776724751966962574727)
          ·
            refine ⟨58814665087127950443862091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39209776724751966962574727 58814665087127950443862091)
            ·
              refine ⟨88221997630691925665793137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58814665087127950443862091 88221997630691925665793137)
              ·
                refine ⟨66166498223018944249344853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88221997630691925665793137 66166498223018944249344853)
                ·
                  refine ⟨387694325525501626461005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66166498223018944249344853 387694325525501626461005)
                  ·
                    rfl

theorem cell23_6795288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 9].length) (baseStart_6795288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795288 prefixEnd_6795288 := by exact prefixLift 6795288
  have htrace : WordTrace (prefixWord ++ tailWord_6795288) baseStart_6795288 baseEnd_6795288 := by
    simpa [prefixWord, tailWord_6795288, baseEnd_6795288] using wordTrace_append hprefix tailTrace_6795288
  have hstable : (prefixWord ++ tailWord_6795288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795288).length < 2 ^ (prefixWord ++ tailWord_6795288).sum := by decide
  have hdescent : baseEnd_6795288 < baseStart_6795288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795315 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 3]
def baseStart_6795315 : Nat := 118140960795 + 6795315 * 2 ^ 59
def prefixEnd_6795315 : Nat := 4983230072969 + 3 ^ 40 * 6795315 * 2
def baseEnd_6795315 : Nat := 3489262793707186032511421

theorem tailTrace_6795315 : CollatzResearch.WordTrace tailWord_6795315 prefixEnd_6795315 3489262793707186032511421 := by
  unfold tailWord_6795315
  simp only [CollatzResearch.WordTrace]
  refine ⟨247845499376741777251211399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165230332917827851500807599 247845499376741777251211399)
  ·
    refine ⟨371768249065112665876817099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247845499376741777251211399 371768249065112665876817099)
    ·
      refine ⟨557652373597668998815225649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371768249065112665876817099 557652373597668998815225649)
      ·
        refine ⟨418239280198251749111419237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557652373597668998815225649 418239280198251749111419237)
        ·
          refine ⟨78419865037172202958391107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418239280198251749111419237 78419865037172202958391107)
          ·
            refine ⟨117629797555758304437586661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78419865037172202958391107 117629797555758304437586661)
            ·
              refine ⟨22055587041704682082047499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117629797555758304437586661 22055587041704682082047499)
              ·
                refine ⟨33083380562557023123071249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22055587041704682082047499 33083380562557023123071249)
                ·
                  refine ⟨24812535421917767342303437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33083380562557023123071249 24812535421917767342303437)
                  ·
                    refine ⟨9304700783219162753363789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24812535421917767342303437 9304700783219162753363789)
                    ·
                      refine ⟨3489262793707186032511421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304700783219162753363789 3489262793707186032511421)
                      ·
                        rfl

theorem cell23_6795315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_6795315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795315 prefixEnd_6795315 := by exact prefixLift 6795315
  have htrace : WordTrace (prefixWord ++ tailWord_6795315) baseStart_6795315 baseEnd_6795315 := by
    simpa [prefixWord, tailWord_6795315, baseEnd_6795315] using wordTrace_append hprefix tailTrace_6795315
  have hstable : (prefixWord ++ tailWord_6795315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795315).length < 2 ^ (prefixWord ++ tailWord_6795315).sum := by decide
  have hdescent : baseEnd_6795315 < baseStart_6795315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795335 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 2, 5]
def baseStart_6795335 : Nat := 118140960795 + 6795335 * 2 ^ 59
def prefixEnd_6795335 : Nat := 4983230072969 + 3 ^ 40 * 6795335 * 2
def baseEnd_6795335 : Nat := 1163091021106758651420443

theorem tailTrace_6795335 : CollatzResearch.WordTrace tailWord_6795335 prefixEnd_6795335 1163091021106758651420443 := by
  unfold tailWord_6795335
  simp only [CollatzResearch.WordTrace]
  refine ⟨247846228836669320666939459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165230819224446213777959639 247846228836669320666939459)
  ·
    refine ⟨371769343255003981000409189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247846228836669320666939459 371769343255003981000409189)
    ·
      refine ⟨69706751860313246437576723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371769343255003981000409189 69706751860313246437576723)
      ·
        refine ⟨104560127790469869656365085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69706751860313246437576723 104560127790469869656365085)
        ·
          refine ⟨39210047921426201121136907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104560127790469869656365085 39210047921426201121136907)
          ·
            refine ⟨58815071882139301681705361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39210047921426201121136907 58815071882139301681705361)
            ·
              refine ⟨44111303911604476261279021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58815071882139301681705361 44111303911604476261279021)
              ·
                refine ⟨16541738966851678597979633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44111303911604476261279021 16541738966851678597979633)
                ·
                  refine ⟨12406304225138758948484725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16541738966851678597979633 12406304225138758948484725)
                  ·
                    refine ⟨1163091021106758651420443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12406304225138758948484725 1163091021106758651420443)
                    ·
                      rfl

theorem cell23_6795335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_6795335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795335 prefixEnd_6795335 := by exact prefixLift 6795335
  have htrace : WordTrace (prefixWord ++ tailWord_6795335) baseStart_6795335 baseEnd_6795335 := by
    simpa [prefixWord, tailWord_6795335, baseEnd_6795335] using wordTrace_append hprefix tailTrace_6795335
  have hstable : (prefixWord ++ tailWord_6795335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795335).length < 2 ^ (prefixWord ++ tailWord_6795335).sum := by decide
  have hdescent : baseEnd_6795335 < baseStart_6795335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795416 : List Nat := [2, 1, 2, 4, 3, 1, 1, 4, 1, 4]
def baseStart_6795416 : Nat := 118140960795 + 6795416 * 2 ^ 59
def prefixEnd_6795416 : Nat := 4983230072969 + 3 ^ 40 * 6795416 * 2
def baseEnd_6795416 : Nat := 1163104885084430045782819

theorem tailTrace_6795416 : CollatzResearch.WordTrace tailWord_6795416 prefixEnd_6795416 1163104885084430045782819 := by
  unfold tailWord_6795416
  simp only [CollatzResearch.WordTrace]
  refine ⟨123924591574687935750319051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165232788766250581000425401 123924591574687935750319051)
  ·
    refine ⟨185886887362031903625478577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123924591574687935750319051 185886887362031903625478577)
    ·
      refine ⟨139415165521523927719108933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185886887362031903625478577 139415165521523927719108933)
      ·
        refine ⟨26140343535285736447332925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139415165521523927719108933 26140343535285736447332925)
        ·
          refine ⟨9802628825732151167749847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26140343535285736447332925 9802628825732151167749847)
          ·
            refine ⟨14703943238598226751624771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9802628825732151167749847 14703943238598226751624771)
            ·
              refine ⟨22055914857897340127437157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14703943238598226751624771 22055914857897340127437157)
              ·
                refine ⟨4135484035855751273894467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22055914857897340127437157 4135484035855751273894467)
                ·
                  refine ⟨6203226053783626910841701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135484035855751273894467 6203226053783626910841701)
                  ·
                    refine ⟨1163104885084430045782819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6203226053783626910841701 1163104885084430045782819)
                    ·
                      rfl

theorem cell23_6795416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_6795416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795416 prefixEnd_6795416 := by exact prefixLift 6795416
  have htrace : WordTrace (prefixWord ++ tailWord_6795416) baseStart_6795416 baseEnd_6795416 := by
    simpa [prefixWord, tailWord_6795416, baseEnd_6795416] using wordTrace_append hprefix tailTrace_6795416
  have hstable : (prefixWord ++ tailWord_6795416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795416).length < 2 ^ (prefixWord ++ tailWord_6795416).sum := by decide
  have hdescent : baseEnd_6795416 < baseStart_6795416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795442 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_6795442 : Nat := 118140960795 + 6795442 * 2 ^ 59
def prefixEnd_6795442 : Nat := 4983230072969 + 3 ^ 40 * 6795442 * 2
def baseEnd_6795442 : Nat := 1163109335250102345207779

theorem tailTrace_6795442 : CollatzResearch.WordTrace tailWord_6795442 prefixEnd_6795442 1163109335250102345207779 := by
  unfold tailWord_6795442
  simp only [CollatzResearch.WordTrace]
  refine ⟨61962532861820419485271145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165233420964854451960723053 61962532861820419485271145)
  ·
    refine ⟨46471899646365314613953359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61962532861820419485271145 46471899646365314613953359)
    ·
      refine ⟨69707849469547971920930039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46471899646365314613953359 69707849469547971920930039)
      ·
        refine ⟨104561774204321957881395059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69707849469547971920930039 104561774204321957881395059)
        ·
          refine ⟨156842661306482936822092589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104561774204321957881395059 156842661306482936822092589)
          ·
            refine ⟨58815997989931101308284721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156842661306482936822092589 58815997989931101308284721)
            ·
              refine ⟨44111998492448325981213541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58815997989931101308284721 44111998492448325981213541)
              ·
                refine ⟨8270999717334061121477539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44111998492448325981213541 8270999717334061121477539)
                ·
                  refine ⟨12406499576001091682216309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8270999717334061121477539 12406499576001091682216309)
                  ·
                    refine ⟨1163109335250102345207779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12406499576001091682216309 1163109335250102345207779)
                    ·
                      rfl

theorem cell23_6795442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_6795442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795442 prefixEnd_6795442 := by exact prefixLift 6795442
  have htrace : WordTrace (prefixWord ++ tailWord_6795442) baseStart_6795442 baseEnd_6795442 := by
    simpa [prefixWord, tailWord_6795442, baseEnd_6795442] using wordTrace_append hprefix tailTrace_6795442
  have hstable : (prefixWord ++ tailWord_6795442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795442).length < 2 ^ (prefixWord ++ tailWord_6795442).sum := by decide
  have hdescent : baseEnd_6795442 < baseStart_6795442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795456 : List Nat := [2, 1, 1, 2, 5, 1, 1, 5, 1, 1, 3]
def baseStart_6795456 : Nat := 118140960795 + 6795456 * 2 ^ 59
def prefixEnd_6795456 : Nat := 4983230072969 + 3 ^ 40 * 6795456 * 2
def baseEnd_6795456 : Nat := 3489335194479469980848273

theorem tailTrace_6795456 : CollatzResearch.WordTrace tailWord_6795456 prefixEnd_6795456 3489335194479469980848273 := by
  unfold tailWord_6795456
  simp only [CollatzResearch.WordTrace]
  refine ⟨123925321034615479166047111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165233761379487305554729481 123925321034615479166047111)
  ·
    refine ⟨185887981551923218749070667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123925321034615479166047111 185887981551923218749070667)
    ·
      refine ⟨278831972327884828123606001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185887981551923218749070667 278831972327884828123606001)
      ·
        refine ⟨209123979245913621092704501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278831972327884828123606001 209123979245913621092704501)
        ·
          refine ⟨19605373054304401977441047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209123979245913621092704501 19605373054304401977441047)
          ·
            refine ⟨29408059581456602966161571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19605373054304401977441047 29408059581456602966161571)
            ·
              refine ⟨44112089372184904449242357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29408059581456602966161571 44112089372184904449242357)
              ·
                refine ⟨4135508378642334792116471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44112089372184904449242357 4135508378642334792116471)
                ·
                  refine ⟨6203262567963502188174707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135508378642334792116471 6203262567963502188174707)
                  ·
                    refine ⟨9304893851945253282262061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6203262567963502188174707 9304893851945253282262061)
                    ·
                      refine ⟨3489335194479469980848273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304893851945253282262061 3489335194479469980848273)
                      ·
                        rfl

theorem cell23_6795456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_6795456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795456 prefixEnd_6795456 := by exact prefixLift 6795456
  have htrace : WordTrace (prefixWord ++ tailWord_6795456) baseStart_6795456 baseEnd_6795456 := by
    simpa [prefixWord, tailWord_6795456, baseEnd_6795456] using wordTrace_append hprefix tailTrace_6795456
  have hstable : (prefixWord ++ tailWord_6795456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795456).length < 2 ^ (prefixWord ++ tailWord_6795456).sum := by decide
  have hdescent : baseEnd_6795456 < baseStart_6795456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795482 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_6795482 : Nat := 118140960795 + 6795482 * 2 ^ 59
def prefixEnd_6795482 : Nat := 4983230072969 + 3 ^ 40 * 6795482 * 2
def baseEnd_6795482 : Nat := 3489348544976486879123153

theorem tailTrace_6795482 : CollatzResearch.WordTrace tailWord_6795482 prefixEnd_6795482 3489348544976486879123153 := by
  unfold tailWord_6795482
  simp only [CollatzResearch.WordTrace]
  refine ⟨61962897591784191193135175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165234393578091176515027133 61962897591784191193135175)
  ·
    refine ⟨92944346387676286789702763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61962897591784191193135175 92944346387676286789702763)
    ·
      refine ⟨139416519581514430184554145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92944346387676286789702763 139416519581514430184554145)
      ·
        refine ⟨104562389686135822638415609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139416519581514430184554145 104562389686135822638415609)
        ·
          refine ⟨78421792264601866978811707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104562389686135822638415609 78421792264601866978811707)
          ·
            refine ⟨117632688396902800468217561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78421792264601866978811707 117632688396902800468217561)
            ·
              refine ⟨88224516297677100351163171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117632688396902800468217561 88224516297677100351163171)
              ·
                refine ⟨132336774446515650526744757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88224516297677100351163171 132336774446515650526744757)
                ·
                  refine ⟨12406572604360842236882321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132336774446515650526744757 12406572604360842236882321)
                  ·
                    refine ⟨9304929453270631677661741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12406572604360842236882321 9304929453270631677661741)
                    ·
                      refine ⟨3489348544976486879123153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304929453270631677661741 3489348544976486879123153)
                      ·
                        rfl

theorem cell23_6795482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_6795482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795482 prefixEnd_6795482 := by exact prefixLift 6795482
  have htrace : WordTrace (prefixWord ++ tailWord_6795482) baseStart_6795482 baseEnd_6795482 := by
    simpa [prefixWord, tailWord_6795482, baseEnd_6795482] using wordTrace_append hprefix tailTrace_6795482
  have hstable : (prefixWord ++ tailWord_6795482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795482).length < 2 ^ (prefixWord ++ tailWord_6795482).sum := by decide
  have hdescent : baseEnd_6795482 < baseStart_6795482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795496 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_6795496 : Nat := 118140960795 + 6795496 * 2 ^ 59
def prefixEnd_6795496 : Nat := 4983230072969 + 3 ^ 40 * 6795496 * 2
def baseEnd_6795496 : Nat := 3489355733705649824348089

theorem tailTrace_6795496 : CollatzResearch.WordTrace tailWord_6795496 prefixEnd_6795496 3489355733705649824348089 := by
  unfold tailWord_6795496
  simp only [CollatzResearch.WordTrace]
  refine ⟨123926050494543022581775171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165234733992724030109033561 123926050494543022581775171)
  ·
    refine ⟨185889075741814533872662757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123926050494543022581775171 185889075741814533872662757)
    ·
      refine ⟨34854201701590225101124267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185889075741814533872662757 34854201701590225101124267)
      ·
        refine ⟨52281302552385337651686401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34854201701590225101124267 52281302552385337651686401)
        ·
          refine ⟨39210976914289003238764801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52281302552385337651686401 39210976914289003238764801)
          ·
            refine ⟨29408232685716752429073601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39210976914289003238764801 29408232685716752429073601)
            ·
              refine ⟨22056174514287564321805201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29408232685716752429073601 22056174514287564321805201)
              ·
                refine ⟨16542130885715673241353901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22056174514287564321805201 16542130885715673241353901)
                ·
                  refine ⟨6203299082143377465507713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16542130885715673241353901 6203299082143377465507713)
                  ·
                    refine ⟨4652474311607533099130785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203299082143377465507713 4652474311607533099130785)
                    ·
                      refine ⟨3489355733705649824348089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652474311607533099130785 3489355733705649824348089)
                      ·
                        rfl

theorem cell23_6795496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_6795496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795496 prefixEnd_6795496 := by exact prefixLift 6795496
  have htrace : WordTrace (prefixWord ++ tailWord_6795496) baseStart_6795496 baseEnd_6795496 := by
    simpa [prefixWord, tailWord_6795496, baseEnd_6795496] using wordTrace_append hprefix tailTrace_6795496
  have hstable : (prefixWord ++ tailWord_6795496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795496).length < 2 ^ (prefixWord ++ tailWord_6795496).sum := by decide
  have hdescent : baseEnd_6795496 < baseStart_6795496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795499 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 3]
def baseStart_6795499 : Nat := 118140960795 + 6795499 * 2 ^ 59
def prefixEnd_6795499 : Nat := 4983230072969 + 3 ^ 40 * 6795499 * 2
def baseEnd_6795499 : Nat := 3489357274147613312610575

theorem tailTrace_6795499 : CollatzResearch.WordTrace tailWord_6795499 prefixEnd_6795499 3489357274147613312610575 := by
  unfold tailWord_6795499
  simp only [CollatzResearch.WordTrace]
  refine ⟨247852210408075176675909551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165234806938716784450606367 247852210408075176675909551)
  ·
    refine ⟨371778315612112765013864327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247852210408075176675909551 371778315612112765013864327)
    ·
      refine ⟨557667473418169147520796491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371778315612112765013864327 557667473418169147520796491)
      ·
        refine ⟨836501210127253721281194737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557667473418169147520796491 836501210127253721281194737)
        ·
          refine ⟨627375907595440290960896053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836501210127253721281194737 627375907595440290960896053)
          ·
            refine ⟨58816491337072527277584005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 627375907595440290960896053 58816491337072527277584005)
            ·
              refine ⟨11028092125701098864547001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58816491337072527277584005 11028092125701098864547001)
              ·
                refine ⟨8271069094275824148410251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028092125701098864547001 8271069094275824148410251)
                ·
                  refine ⟨12406603641413736222615377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271069094275824148410251 12406603641413736222615377)
                  ·
                    refine ⟨9304952731060302166961533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12406603641413736222615377 9304952731060302166961533)
                    ·
                      refine ⟨3489357274147613312610575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304952731060302166961533 3489357274147613312610575)
                      ·
                        rfl

theorem cell23_6795499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 3].length) (baseStart_6795499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795499 prefixEnd_6795499 := by exact prefixLift 6795499
  have htrace : WordTrace (prefixWord ++ tailWord_6795499) baseStart_6795499 baseEnd_6795499 := by
    simpa [prefixWord, tailWord_6795499, baseEnd_6795499] using wordTrace_append hprefix tailTrace_6795499
  have hstable : (prefixWord ++ tailWord_6795499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795499).length < 2 ^ (prefixWord ++ tailWord_6795499).sum := by decide
  have hdescent : baseEnd_6795499 < baseStart_6795499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795512 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_6795512 : Nat := 118140960795 + 6795512 * 2 ^ 59
def prefixEnd_6795512 : Nat := 4983230072969 + 3 ^ 40 * 6795512 * 2
def baseEnd_6795512 : Nat := 3489363949396121761748015

theorem tailTrace_6795512 : CollatzResearch.WordTrace tailWord_6795512 prefixEnd_6795512 3489363949396121761748015 := by
  unfold tailWord_6795512
  simp only [CollatzResearch.WordTrace]
  refine ⟨123926342278514039948066395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165235123038018719930755193 123926342278514039948066395)
  ·
    refine ⟨185889513417771059922099593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123926342278514039948066395 185889513417771059922099593)
    ·
      refine ⟨139417135063328294941574695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185889513417771059922099593 139417135063328294941574695)
      ·
        refine ⟨209125702594992442412362043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139417135063328294941574695 209125702594992442412362043)
        ·
          refine ⟨313688553892488663618543065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209125702594992442412362043 313688553892488663618543065)
          ·
            refine ⟨235266415419366497713907299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313688553892488663618543065 235266415419366497713907299)
            ·
              refine ⟨352899623129049746570860949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235266415419366497713907299 352899623129049746570860949)
              ·
                refine ⟨16542169834174206870509107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 352899623129049746570860949 16542169834174206870509107)
                ·
                  refine ⟨24813254751261310305763661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16542169834174206870509107 24813254751261310305763661)
                  ·
                    refine ⟨9304970531722991364661373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24813254751261310305763661 9304970531722991364661373)
                    ·
                      refine ⟨3489363949396121761748015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304970531722991364661373 3489363949396121761748015)
                      ·
                        rfl

theorem cell23_6795512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_6795512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795512 prefixEnd_6795512 := by exact prefixLift 6795512
  have htrace : WordTrace (prefixWord ++ tailWord_6795512) baseStart_6795512 baseEnd_6795512 := by
    simpa [prefixWord, tailWord_6795512, baseEnd_6795512] using wordTrace_append hprefix tailTrace_6795512
  have hstable : (prefixWord ++ tailWord_6795512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795512).length < 2 ^ (prefixWord ++ tailWord_6795512).sum := by decide
  have hdescent : baseEnd_6795512 < baseStart_6795512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795529 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 3]
def baseStart_6795529 : Nat := 118140960795 + 6795529 * 2 ^ 59
def prefixEnd_6795529 : Nat := 4983230072969 + 3 ^ 40 * 6795529 * 2
def baseEnd_6795529 : Nat := 3489372678567248195235437

theorem tailTrace_6795529 : CollatzResearch.WordTrace tailWord_6795529 prefixEnd_6795529 3489372678567248195235437 := by
  unfold tailWord_6795529
  simp only [CollatzResearch.WordTrace]
  refine ⟨247853304597966491799501641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165235536398644327866334427 247853304597966491799501641)
  ·
    refine ⟨185889978448474868849626231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247853304597966491799501641 185889978448474868849626231)
    ·
      refine ⟨278834967672712303274439347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185889978448474868849626231 278834967672712303274439347)
      ·
        refine ⟨418252451509068454911659021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278834967672712303274439347 418252451509068454911659021)
        ·
          refine ⟨156844669315900670591872133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418252451509068454911659021 156844669315900670591872133)
          ·
            refine ⟨29408375496731375735976025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156844669315900670591872133 29408375496731375735976025)
            ·
              refine ⟨22056281622548531801982019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29408375496731375735976025 22056281622548531801982019)
              ·
                refine ⟨33084422433822797702973029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22056281622548531801982019 33084422433822797702973029)
                ·
                  refine ⟨6203329206341774569307443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33084422433822797702973029 6203329206341774569307443)
                  ·
                    refine ⟨9304993809512661853961165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6203329206341774569307443 9304993809512661853961165)
                    ·
                      refine ⟨3489372678567248195235437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9304993809512661853961165 3489372678567248195235437)
                      ·
                        rfl

theorem cell23_6795529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 1, 3].length) (baseStart_6795529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795529 prefixEnd_6795529 := by exact prefixLift 6795529
  have htrace : WordTrace (prefixWord ++ tailWord_6795529) baseStart_6795529 baseEnd_6795529 := by
    simpa [prefixWord, tailWord_6795529, baseEnd_6795529] using wordTrace_append hprefix tailTrace_6795529
  have hstable : (prefixWord ++ tailWord_6795529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795529).length < 2 ^ (prefixWord ++ tailWord_6795529).sum := by decide
  have hdescent : baseEnd_6795529 < baseStart_6795529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795550 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6795550 : Nat := 118140960795 + 6795550 * 2 ^ 59
def prefixEnd_6795550 : Nat := 4983230072969 + 3 ^ 40 * 6795550 * 2
def baseEnd_6795550 : Nat := 3489383461660992613072841

theorem tailTrace_6795550 : CollatzResearch.WordTrace tailWord_6795550 prefixEnd_6795550 3489383461660992613072841 := by
  unfold tailWord_6795550
  simp only [CollatzResearch.WordTrace]
  refine ⟨30981758816361301548252013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165236047020593608257344069 30981758816361301548252013)
  ·
    refine ⟨11618159556135488080594505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30981758816361301548252013 11618159556135488080594505)
    ·
      refine ⟨8713619667101616060445879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11618159556135488080594505 8713619667101616060445879)
      ·
        refine ⟨13070429500652424090668819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8713619667101616060445879 13070429500652424090668819)
        ·
          refine ⟨19605644250978636136003229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13070429500652424090668819 19605644250978636136003229)
          ·
            refine ⟨7352116594116988551001211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19605644250978636136003229 7352116594116988551001211)
            ·
              refine ⟨11028174891175482826501817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352116594116988551001211 11028174891175482826501817)
              ·
                refine ⟨8271131168381612119876363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028174891175482826501817 8271131168381612119876363)
                ·
                  refine ⟨12406696752572418179814545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271131168381612119876363 12406696752572418179814545)
                  ·
                    refine ⟨9305022564429313634860909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12406696752572418179814545 9305022564429313634860909)
                    ·
                      refine ⟨3489383461660992613072841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305022564429313634860909 3489383461660992613072841)
                      ·
                        rfl

theorem cell23_6795550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6795550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795550 prefixEnd_6795550 := by exact prefixLift 6795550
  have htrace : WordTrace (prefixWord ++ tailWord_6795550) baseStart_6795550 baseEnd_6795550 := by
    simpa [prefixWord, tailWord_6795550, baseEnd_6795550] using wordTrace_append hprefix tailTrace_6795550
  have hstable : (prefixWord ++ tailWord_6795550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795550).length < 2 ^ (prefixWord ++ tailWord_6795550).sum := by decide
  have hdescent : baseEnd_6795550 < baseStart_6795550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795556 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_6795556 : Nat := 118140960795 + 6795556 * 2 ^ 59
def prefixEnd_6795556 : Nat := 4983230072969 + 3 ^ 40 * 6795556 * 2
def baseEnd_6795556 : Nat := 3489386542544919589597813

theorem tailTrace_6795556 : CollatzResearch.WordTrace tailWord_6795556 prefixEnd_6795556 3489386542544919589597813 := by
  unfold tailWord_6795556
  simp only [CollatzResearch.WordTrace]
  refine ⟨123927144684434337705367261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165236192912579116940489681 123927144684434337705367261)
  ·
    refine ⟨46472679256662876639512723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123927144684434337705367261 46472679256662876639512723)
    ·
      refine ⟨69709018884994314959269085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46472679256662876639512723 69709018884994314959269085)
      ·
        refine ⟨26140882081872868109725907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69709018884994314959269085 26140882081872868109725907)
        ·
          refine ⟨39211323122809302164588861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26140882081872868109725907 39211323122809302164588861)
          ·
            refine ⟨14704246171053488311720823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39211323122809302164588861 14704246171053488311720823)
            ·
              refine ⟨22056369256580232467581235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14704246171053488311720823 22056369256580232467581235)
              ·
                refine ⟨33084553884870348701371853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22056369256580232467581235 33084553884870348701371853)
                ·
                  refine ⟨12406707706826380763014445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33084553884870348701371853 12406707706826380763014445)
                  ·
                    refine ⟨4652515390059892786130417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12406707706826380763014445 4652515390059892786130417)
                    ·
                      refine ⟨3489386542544919589597813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652515390059892786130417 3489386542544919589597813)
                      ·
                        rfl

theorem cell23_6795556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_6795556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795556 prefixEnd_6795556 := by exact prefixLift 6795556
  have htrace : WordTrace (prefixWord ++ tailWord_6795556) baseStart_6795556 baseEnd_6795556 := by
    simpa [prefixWord, tailWord_6795556, baseEnd_6795556] using wordTrace_append hprefix tailTrace_6795556
  have hstable : (prefixWord ++ tailWord_6795556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795556).length < 2 ^ (prefixWord ++ tailWord_6795556).sum := by decide
  have hdescent : baseEnd_6795556 < baseStart_6795556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795573 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_6795573 : Nat := 118140960795 + 6795573 * 2 ^ 59
def prefixEnd_6795573 : Nat := 4983230072969 + 3 ^ 40 * 6795573 * 2
def baseEnd_6795573 : Nat := 3489395271716046023085235

theorem tailTrace_6795573 : CollatzResearch.WordTrace tailWord_6795573 prefixEnd_6795573 3489395271716046023085235 := by
  unfold tailWord_6795573
  simp only [CollatzResearch.WordTrace]
  refine ⟨247854909409807087314103373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165236606273204724876068915 247854909409807087314103373)
  ·
    refine ⟨92945591028677657742788765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247854909409807087314103373 92945591028677657742788765)
    ·
      refine ⟨34854596635754121653545787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92945591028677657742788765 34854596635754121653545787)
      ·
        refine ⟨52281894953631182480318681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34854596635754121653545787 52281894953631182480318681)
        ·
          refine ⟨39211421215223386860239011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52281894953631182480318681 39211421215223386860239011)
          ·
            refine ⟨58817131822835080290358517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39211421215223386860239011 58817131822835080290358517)
            ·
              refine ⟨5514106108390788777221111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58817131822835080290358517 5514106108390788777221111)
              ·
                refine ⟨8271159162586183165831667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5514106108390788777221111 8271159162586183165831667)
                ·
                  refine ⟨12406738743879274748747501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271159162586183165831667 12406738743879274748747501)
                  ·
                    refine ⟨4652527028954728030780313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12406738743879274748747501 4652527028954728030780313)
                    ·
                      refine ⟨3489395271716046023085235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652527028954728030780313 3489395271716046023085235)
                      ·
                        rfl

theorem cell23_6795573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_6795573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795573 prefixEnd_6795573 := by exact prefixLift 6795573
  have htrace : WordTrace (prefixWord ++ tailWord_6795573) baseStart_6795573 baseEnd_6795573 := by
    simpa [prefixWord, tailWord_6795573, baseEnd_6795573] using wordTrace_append hprefix tailTrace_6795573
  have hstable : (prefixWord ++ tailWord_6795573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795573).length < 2 ^ (prefixWord ++ tailWord_6795573).sum := by decide
  have hdescent : baseEnd_6795573 < baseStart_6795573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795626 : List Nat := [3, 1, 3, 3, 1, 1, 1, 5, 5]
def baseStart_6795626 : Nat := 118140960795 + 6795626 * 2 ^ 59
def prefixEnd_6795626 : Nat := 4983230072969 + 3 ^ 40 * 6795626 * 2
def baseEnd_6795626 : Nat := 387713609576748257302499

theorem tailTrace_6795626 : CollatzResearch.WordTrace tailWord_6795626 prefixEnd_6795626 387713609576748257302499 := by
  unfold tailWord_6795626
  simp only [CollatzResearch.WordTrace]
  refine ⟨61964210619653769341445683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165237894985743384910521821 61964210619653769341445683)
  ·
    refine ⟨92946315929480654012168525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61964210619653769341445683 92946315929480654012168525)
    ·
      refine ⟨34854868473555245254563197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92946315929480654012168525 34854868473555245254563197)
      ·
        refine ⟨13070575677583216970461199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34854868473555245254563197 13070575677583216970461199)
        ·
          refine ⟨19605863516374825455691799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13070575677583216970461199 19605863516374825455691799)
          ·
            refine ⟨29408795274562238183537699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19605863516374825455691799 29408795274562238183537699)
            ·
              refine ⟨44113192911843357275306549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29408795274562238183537699 44113192911843357275306549)
              ·
                refine ⟨4135611835485314744559989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44113192911843357275306549 4135611835485314744559989)
                ·
                  refine ⟨387713609576748257302499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4135611835485314744559989 387713609576748257302499)
                  ·
                    rfl

theorem cell23_6795626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_6795626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795626 prefixEnd_6795626 := by exact prefixLift 6795626
  have htrace : WordTrace (prefixWord ++ tailWord_6795626) baseStart_6795626 baseEnd_6795626 := by
    simpa [prefixWord, tailWord_6795626, baseEnd_6795626] using wordTrace_append hprefix tailTrace_6795626
  have hstable : (prefixWord ++ tailWord_6795626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795626).length < 2 ^ (prefixWord ++ tailWord_6795626).sum := by decide
  have hdescent : baseEnd_6795626 < baseStart_6795626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795642 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_6795642 : Nat := 118140960795 + 6795642 * 2 ^ 59
def prefixEnd_6795642 : Nat := 4983230072969 + 3 ^ 40 * 6795642 * 2
def baseEnd_6795642 : Nat := 3489430701881206253122417

theorem tailTrace_6795642 : CollatzResearch.WordTrace tailWord_6795642 prefixEnd_6795642 3489430701881206253122417 := by
  unfold tailWord_6795642
  simp only [CollatzResearch.WordTrace]
  refine ⟨61964356511639278024591295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165238284031038074732243453 61964356511639278024591295)
  ·
    refine ⟨92946534767458917036886943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61964356511639278024591295 92946534767458917036886943)
    ·
      refine ⟨139419802151188375555330415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92946534767458917036886943 139419802151188375555330415)
      ·
        refine ⟨209129703226782563332995623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139419802151188375555330415 209129703226782563332995623)
        ·
          refine ⟨313694554840173844999493435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209129703226782563332995623 313694554840173844999493435)
          ·
            refine ⟨470541832260260767499240153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313694554840173844999493435 470541832260260767499240153)
            ·
              refine ⟨352906374195195575624430115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470541832260260767499240153 352906374195195575624430115)
              ·
                refine ⟨529359561292793363436645173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352906374195195575624430115 529359561292793363436645173)
                ·
                  refine ⟨49627458871199377822185485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 529359561292793363436645173 49627458871199377822185485)
                  ·
                    refine ⟨18610297076699766683319557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49627458871199377822185485 18610297076699766683319557)
                    ·
                      refine ⟨3489430701881206253122417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18610297076699766683319557 3489430701881206253122417)
                      ·
                        rfl

theorem cell23_6795642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_6795642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795642 prefixEnd_6795642 := by exact prefixLift 6795642
  have htrace : WordTrace (prefixWord ++ tailWord_6795642) baseStart_6795642 baseEnd_6795642 := by
    simpa [prefixWord, tailWord_6795642, baseEnd_6795642] using wordTrace_append hprefix tailTrace_6795642
  have hstable : (prefixWord ++ tailWord_6795642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795642).length < 2 ^ (prefixWord ++ tailWord_6795642).sum := by decide
  have hdescent : baseEnd_6795642 < baseStart_6795642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795679 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 3]
def baseStart_6795679 : Nat := 118140960795 + 6795679 * 2 ^ 59
def prefixEnd_6795679 : Nat := 4983230072969 + 3 ^ 40 * 6795679 * 2
def baseEnd_6795679 : Nat := 3489449700665422608359747

theorem tailTrace_6795679 : CollatzResearch.WordTrace tailWord_6795679 prefixEnd_6795679 3489449700665422608359747 := by
  unfold tailWord_6795679
  simp only [CollatzResearch.WordTrace]
  refine ⟨247858775547423067417462091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165239183698282044944974727 247858775547423067417462091)
  ·
    refine ⟨371788163321134601126193137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247858775547423067417462091 371788163321134601126193137)
    ·
      refine ⟨278841122490850950844644853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371788163321134601126193137 278841122490850950844644853)
      ·
        refine ⟨26141355233517276641685455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278841122490850950844644853 26141355233517276641685455)
        ·
          refine ⟨39212032850275914962528183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26141355233517276641685455 39212032850275914962528183)
          ·
            refine ⟨58818049275413872443792275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39212032850275914962528183 58818049275413872443792275)
            ·
              refine ⟨88227073913120808665688413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58818049275413872443792275 88227073913120808665688413)
              ·
                refine ⟨33085152717420303249633155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88227073913120808665688413 33085152717420303249633155)
                ·
                  refine ⟨49627729076130454874449733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33085152717420303249633155 49627729076130454874449733)
                  ·
                    refine ⟨9305199201774460288959325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49627729076130454874449733 9305199201774460288959325)
                    ·
                      refine ⟨3489449700665422608359747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305199201774460288959325 3489449700665422608359747)
                      ·
                        rfl

theorem cell23_6795679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_6795679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795679 prefixEnd_6795679 := by exact prefixLift 6795679
  have htrace : WordTrace (prefixWord ++ tailWord_6795679) baseStart_6795679 baseEnd_6795679 := by
    simpa [prefixWord, tailWord_6795679, baseEnd_6795679] using wordTrace_append hprefix tailTrace_6795679
  have hstable : (prefixWord ++ tailWord_6795679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795679).length < 2 ^ (prefixWord ++ tailWord_6795679).sum := by decide
  have hdescent : baseEnd_6795679 < baseStart_6795679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795690 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6795690 : Nat := 118140960795 + 6795690 * 2 ^ 59
def prefixEnd_6795690 : Nat := 4983230072969 + 3 ^ 40 * 6795690 * 2
def baseEnd_6795690 : Nat := 1163151782984207355107399

theorem tailTrace_6795690 : CollatzResearch.WordTrace tailWord_6795690 prefixEnd_6795690 1163151782984207355107399 := by
  unfold tailWord_6795690
  simp only [CollatzResearch.WordTrace]
  refine ⟨61964794187595804074028131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165239451166922144197408349 61964794187595804074028131)
  ·
    refine ⟨92947191281393706111042197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61964794187595804074028131 92947191281393706111042197)
    ·
      refine ⟨4356899591315329973955103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92947191281393706111042197 4356899591315329973955103)
      ·
        refine ⟨6535349386972994960932655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356899591315329973955103 6535349386972994960932655)
        ·
          refine ⟨9803024080459492441398983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535349386972994960932655 9803024080459492441398983)
          ·
            refine ⟨14704536120689238662098475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9803024080459492441398983 14704536120689238662098475)
            ·
              refine ⟨22056804181033857993147713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14704536120689238662098475 22056804181033857993147713)
              ·
                refine ⟨16542603135775393494860785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22056804181033857993147713 16542603135775393494860785)
                ·
                  refine ⟨12406952351831545121145589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16542603135775393494860785 12406952351831545121145589)
                  ·
                    refine ⟨1163151782984207355107399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12406952351831545121145589 1163151782984207355107399)
                    ·
                      rfl

theorem cell23_6795690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6795690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795690 prefixEnd_6795690 := by exact prefixLift 6795690
  have htrace : WordTrace (prefixWord ++ tailWord_6795690) baseStart_6795690 baseEnd_6795690 := by
    simpa [prefixWord, tailWord_6795690, baseEnd_6795690] using wordTrace_append hprefix tailTrace_6795690
  have hstable : (prefixWord ++ tailWord_6795690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795690).length < 2 ^ (prefixWord ++ tailWord_6795690).sum := by decide
  have hdescent : baseEnd_6795690 < baseStart_6795690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795693 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_6795693 : Nat := 118140960795 + 6795693 * 2 ^ 59
def prefixEnd_6795693 : Nat := 4983230072969 + 3 ^ 40 * 6795693 * 2
def baseEnd_6795693 : Nat := 3489456889394585553584683

theorem tailTrace_6795693 : CollatzResearch.WordTrace tailWord_6795693 prefixEnd_6795693 3489456889394585553584683 := by
  unfold tailWord_6795693
  simp only [CollatzResearch.WordTrace]
  refine ⟨247859286169372347808471733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165239524112914898538981155 247859286169372347808471733)
  ·
    refine ⟨23236808078378657607044225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247859286169372347808471733 23236808078378657607044225)
    ·
      refine ⟨17427606058783993205283169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23236808078378657607044225 17427606058783993205283169)
      ·
        refine ⟨13070704544087994903962377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17427606058783993205283169 13070704544087994903962377)
        ·
          refine ⟨9803028408065996177971783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13070704544087994903962377 9803028408065996177971783)
          ·
            refine ⟨14704542612098994266957675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9803028408065996177971783 14704542612098994266957675)
            ·
              refine ⟨22056813918148491400436513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14704542612098994266957675 22056813918148491400436513)
              ·
                refine ⟨16542610438611368550327385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22056813918148491400436513 16542610438611368550327385)
                ·
                  refine ⟨12406957828958526412745539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16542610438611368550327385 12406957828958526412745539)
                  ·
                    refine ⟨18610436743437789619118309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12406957828958526412745539 18610436743437789619118309)
                    ·
                      refine ⟨3489456889394585553584683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18610436743437789619118309 3489456889394585553584683)
                      ·
                        rfl

theorem cell23_6795693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_6795693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795693 prefixEnd_6795693 := by exact prefixLift 6795693
  have htrace : WordTrace (prefixWord ++ tailWord_6795693) baseStart_6795693 baseEnd_6795693 := by
    simpa [prefixWord, tailWord_6795693, baseEnd_6795693] using wordTrace_append hprefix tailTrace_6795693
  have hstable : (prefixWord ++ tailWord_6795693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795693).length < 2 ^ (prefixWord ++ tailWord_6795693).sum := by decide
  have hdescent : baseEnd_6795693 < baseStart_6795693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795712 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 9]
def baseStart_6795712 : Nat := 118140960795 + 6795712 * 2 ^ 59
def prefixEnd_6795712 : Nat := 4983230072969 + 3 ^ 40 * 6795712 * 2
def baseEnd_6795712 : Nat := 1163155548509006993082365

theorem tailTrace_6795712 : CollatzResearch.WordTrace tailWord_6795712 prefixEnd_6795712 1163155548509006993082365 := by
  unfold tailWord_6795712
  simp only [CollatzResearch.WordTrace]
  refine ⟨123929989578151757026706695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165239986104202342702275593 123929989578151757026706695)
  ·
    refine ⟨185894984367227635540060043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123929989578151757026706695 185894984367227635540060043)
    ·
      refine ⟨278842476550841453310090065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185894984367227635540060043 278842476550841453310090065)
      ·
        refine ⟨209131857413131089982567549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278842476550841453310090065 209131857413131089982567549)
        ·
          refine ⟨78424446529924158743462831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209131857413131089982567549 78424446529924158743462831)
          ·
            refine ⟨117636669794886238115194247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78424446529924158743462831 117636669794886238115194247)
            ·
              refine ⟨176455004692329357172791371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117636669794886238115194247 176455004692329357172791371)
              ·
                refine ⟨264682507038494035759187057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176455004692329357172791371 264682507038494035759187057)
                ·
                  refine ⟨198511880278870526819390293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264682507038494035759187057 198511880278870526819390293)
                  ·
                    refine ⟨1163155548509006993082365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198511880278870526819390293 1163155548509006993082365)
                    ·
                      rfl

theorem cell23_6795712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_6795712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795712 prefixEnd_6795712 := by exact prefixLift 6795712
  have htrace : WordTrace (prefixWord ++ tailWord_6795712) baseStart_6795712 baseEnd_6795712 := by
    simpa [prefixWord, tailWord_6795712, baseEnd_6795712] using wordTrace_append hprefix tailTrace_6795712
  have hstable : (prefixWord ++ tailWord_6795712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795712).length < 2 ^ (prefixWord ++ tailWord_6795712).sum := by decide
  have hdescent : baseEnd_6795712 < baseStart_6795712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795726 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_6795726 : Nat := 118140960795 + 6795726 * 2 ^ 59
def prefixEnd_6795726 : Nat := 4983230072969 + 3 ^ 40 * 6795726 * 2
def baseEnd_6795726 : Nat := 3489473834256183924472031

theorem tailTrace_6795726 : CollatzResearch.WordTrace tailWord_6795726 prefixEnd_6795726 3489473834256183924472031 := by
  unfold tailWord_6795726
  simp only [CollatzResearch.WordTrace]
  refine ⟨30982561222281599305552879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165240326518835196296282021 30982561222281599305552879)
  ·
    refine ⟨46473841833422398958329319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30982561222281599305552879 46473841833422398958329319)
    ·
      refine ⟨69710762750133598437493979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46473841833422398958329319 69710762750133598437493979)
      ·
        refine ⟨104566144125200397656240969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69710762750133598437493979 104566144125200397656240969)
        ·
          refine ⟨78424608093900298242180727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104566144125200397656240969 78424608093900298242180727)
          ·
            refine ⟨117636912140850447363271091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78424608093900298242180727 117636912140850447363271091)
            ·
              refine ⟨176455368211275671044906637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117636912140850447363271091 176455368211275671044906637)
              ·
                refine ⟨66170763079228376641839989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176455368211275671044906637 66170763079228376641839989)
                ·
                  refine ⟨6203509038677660310172499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66170763079228376641839989 6203509038677660310172499)
                  ·
                    refine ⟨9305263558016490465258749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6203509038677660310172499 9305263558016490465258749)
                    ·
                      refine ⟨3489473834256183924472031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305263558016490465258749 3489473834256183924472031)
                      ·
                        rfl

theorem cell23_6795726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_6795726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795726 prefixEnd_6795726 := by exact prefixLift 6795726
  have htrace : WordTrace (prefixWord ++ tailWord_6795726) baseStart_6795726 baseEnd_6795726 := by
    simpa [prefixWord, tailWord_6795726, baseEnd_6795726] using wordTrace_append hprefix tailTrace_6795726
  have hstable : (prefixWord ++ tailWord_6795726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795726).length < 2 ^ (prefixWord ++ tailWord_6795726).sum := by decide
  have hdescent : baseEnd_6795726 < baseStart_6795726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795730 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6795730 : Nat := 118140960795 + 6795730 * 2 ^ 59
def prefixEnd_6795730 : Nat := 4983230072969 + 3 ^ 40 * 6795730 * 2
def baseEnd_6795730 : Nat := 3489475888178801908822013

theorem tailTrace_6795730 : CollatzResearch.WordTrace tailWord_6795730 prefixEnd_6795730 3489475888178801908822013 := by
  unfold tailWord_6795730
  simp only [CollatzResearch.WordTrace]
  refine ⟨61965158917559575781892161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165240423780158868751712429 61965158917559575781892161)
  ·
    refine ⟨46473869188169681836419121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61965158917559575781892161 46473869188169681836419121)
    ·
      refine ⟨34855401891127261377314341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46473869188169681836419121 34855401891127261377314341)
      ·
        refine ⟨6535387854586361508246439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34855401891127261377314341 6535387854586361508246439)
        ·
          refine ⟨9803081781879542262369659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535387854586361508246439 9803081781879542262369659)
          ·
            refine ⟨14704622672819313393554489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9803081781879542262369659 14704622672819313393554489)
            ·
              refine ⟨11028467004614485045165867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14704622672819313393554489 11028467004614485045165867)
              ·
                refine ⟨16542700506921727567748801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11028467004614485045165867 16542700506921727567748801)
                ·
                  refine ⟨12407025380191295675811601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16542700506921727567748801 12407025380191295675811601)
                  ·
                    refine ⟨9305269035143471756858701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12407025380191295675811601 9305269035143471756858701)
                    ·
                      refine ⟨3489475888178801908822013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305269035143471756858701 3489475888178801908822013)
                      ·
                        rfl

theorem cell23_6795730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6795730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795730 prefixEnd_6795730 := by exact prefixLift 6795730
  have htrace : WordTrace (prefixWord ++ tailWord_6795730) baseStart_6795730 baseEnd_6795730 := by
    simpa [prefixWord, tailWord_6795730, baseEnd_6795730] using wordTrace_append hprefix tailTrace_6795730
  have hstable : (prefixWord ++ tailWord_6795730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795730).length < 2 ^ (prefixWord ++ tailWord_6795730).sum := by decide
  have hdescent : baseEnd_6795730 < baseStart_6795730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795766 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6795766 : Nat := 118140960795 + 6795766 * 2 ^ 59
def prefixEnd_6795766 : Nat := 4983230072969 + 3 ^ 40 * 6795766 * 2
def baseEnd_6795766 : Nat := 3489494373482363767971847

theorem tailTrace_6795766 : CollatzResearch.WordTrace tailWord_6795766 prefixEnd_6795766 3489494373482363767971847 := by
  unfold tailWord_6795766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15491371793631742579742447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165241299132071920850586101 15491371793631742579742447)
  ·
    refine ⟨23237057690447613869613671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15491371793631742579742447 23237057690447613869613671)
    ·
      refine ⟨34855586535671420804420507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23237057690447613869613671 34855586535671420804420507)
      ·
        refine ⟨52283379803507131206630761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34855586535671420804420507 52283379803507131206630761)
        ·
          refine ⟨39212534852630348404973071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52283379803507131206630761 39212534852630348404973071)
          ·
            refine ⟨58818802278945522607459607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39212534852630348404973071 58818802278945522607459607)
            ·
              refine ⟨88228203418418283911189411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58818802278945522607459607 88228203418418283911189411)
              ·
                refine ⟨132342305127627425866784117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88228203418418283911189411 132342305127627425866784117)
                ·
                  refine ⟨12407091105715071175011011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132342305127627425866784117 12407091105715071175011011)
                  ·
                    refine ⟨18610636658572606762516517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12407091105715071175011011 18610636658572606762516517)
                    ·
                      refine ⟨3489494373482363767971847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18610636658572606762516517 3489494373482363767971847)
                      ·
                        rfl

theorem cell23_6795766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6795766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795766 prefixEnd_6795766 := by exact prefixLift 6795766
  have htrace : WordTrace (prefixWord ++ tailWord_6795766) baseStart_6795766 baseEnd_6795766 := by
    simpa [prefixWord, tailWord_6795766, baseEnd_6795766] using wordTrace_append hprefix tailTrace_6795766
  have hstable : (prefixWord ++ tailWord_6795766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795766).length < 2 ^ (prefixWord ++ tailWord_6795766).sum := by decide
  have hdescent : baseEnd_6795766 < baseStart_6795766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795769 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_6795769 : Nat := 118140960795 + 6795769 * 2 ^ 59
def prefixEnd_6795769 : Nat := 4983230072969 + 3 ^ 40 * 6795769 * 2
def baseEnd_6795769 : Nat := 3489495913924327256234333

theorem tailTrace_6795769 : CollatzResearch.WordTrace tailWord_6795769 prefixEnd_6795769 3489495913924327256234333 := by
  unfold tailWord_6795769
  simp only [CollatzResearch.WordTrace]
  refine ⟨247862058117097012788238361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165241372078064675192158907 247862058117097012788238361)
  ·
    refine ⟨185896543587822759591178771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247862058117097012788238361 185896543587822759591178771)
    ·
      refine ⟨278844815381734139386768157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185896543587822759591178771 278844815381734139386768157)
      ·
        refine ⟨104566805768150302270038059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278844815381734139386768157 104566805768150302270038059)
        ·
          refine ⟨156850208652225453405057089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104566805768150302270038059 156850208652225453405057089)
          ·
            refine ⟨117637656489169090053792817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156850208652225453405057089 117637656489169090053792817)
            ·
              refine ⟨88228242366876817540344613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117637656489169090053792817 88228242366876817540344613)
              ·
                refine ⟨16542795443789403288814615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88228242366876817540344613 16542795443789403288814615)
                ·
                  refine ⟨24814193165684104933221923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16542795443789403288814615 24814193165684104933221923)
                  ·
                    refine ⟨37221289748526157399832885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24814193165684104933221923 37221289748526157399832885)
                    ·
                      refine ⟨3489495913924327256234333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37221289748526157399832885 3489495913924327256234333)
                      ·
                        rfl

theorem cell23_6795769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_6795769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795769 prefixEnd_6795769 := by exact prefixLift 6795769
  have htrace : WordTrace (prefixWord ++ tailWord_6795769) baseStart_6795769 baseEnd_6795769 := by
    simpa [prefixWord, tailWord_6795769, baseEnd_6795769] using wordTrace_append hprefix tailTrace_6795769
  have hstable : (prefixWord ++ tailWord_6795769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795769).length < 2 ^ (prefixWord ++ tailWord_6795769).sum := by decide
  have hdescent : baseEnd_6795769 < baseStart_6795769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795786 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_6795786 : Nat := 118140960795 + 6795786 * 2 ^ 59
def prefixEnd_6795786 : Nat := 4983230072969 + 3 ^ 40 * 6795786 * 2
def baseEnd_6795786 : Nat := 3489504643095453689721755

theorem tailTrace_6795786 : CollatzResearch.WordTrace tailWord_6795786 prefixEnd_6795786 3489504643095453689721755 := by
  unfold tailWord_6795786
  simp only [CollatzResearch.WordTrace]
  refine ⟨61965669539508856172901803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165241785438690283127738141 61965669539508856172901803)
  ·
    refine ⟨92948504309263284259352705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61965669539508856172901803 92948504309263284259352705)
    ·
      refine ⟨69711378231947463194514529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92948504309263284259352705 69711378231947463194514529)
      ·
        refine ⟨52283533673960597395885897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69711378231947463194514529 52283533673960597395885897)
        ·
          refine ⟨39212650255470448046914423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52283533673960597395885897 39212650255470448046914423)
          ·
            refine ⟨58818975383205672070371635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39212650255470448046914423 58818975383205672070371635)
            ·
              refine ⟨88228463074808508105557453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58818975383205672070371635 88228463074808508105557453)
              ·
                refine ⟨33085673653053190539584045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88228463074808508105557453 33085673653053190539584045)
                ·
                  refine ⟨12407127619894946452344017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33085673653053190539584045 12407127619894946452344017)
                  ·
                    refine ⟨9305345714921209839258013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12407127619894946452344017 9305345714921209839258013)
                    ·
                      refine ⟨3489504643095453689721755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305345714921209839258013 3489504643095453689721755)
                      ·
                        rfl

theorem cell23_6795786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_6795786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795786 prefixEnd_6795786 := by exact prefixLift 6795786
  have htrace : WordTrace (prefixWord ++ tailWord_6795786) baseStart_6795786 baseEnd_6795786 := by
    simpa [prefixWord, tailWord_6795786, baseEnd_6795786] using wordTrace_append hprefix tailTrace_6795786
  have hstable : (prefixWord ++ tailWord_6795786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795786).length < 2 ^ (prefixWord ++ tailWord_6795786).sum := by decide
  have hdescent : baseEnd_6795786 < baseStart_6795786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795800 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 1, 1, 4]
def baseStart_6795800 : Nat := 118140960795 + 6795800 * 2 ^ 59
def prefixEnd_6795800 : Nat := 4983230072969 + 3 ^ 40 * 6795800 * 2
def baseEnd_6795800 : Nat := 3489511831824616634946691

theorem tailTrace_6795800 : CollatzResearch.WordTrace tailWord_6795800 prefixEnd_6795800 3489511831824616634946691 := by
  unfold tailWord_6795800
  simp only [CollatzResearch.WordTrace]
  refine ⟨123931594389992352541308427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165242125853323136721744569 123931594389992352541308427)
  ·
    refine ⟨185897391584988528811962641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123931594389992352541308427 185897391584988528811962641)
    ·
      refine ⟨139423043688741396608971981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185897391584988528811962641 139423043688741396608971981)
      ·
        refine ⟨52283641383278023728364493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139423043688741396608971981 52283641383278023728364493)
        ·
          refine ⟨19606365518729258898136685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52283641383278023728364493 19606365518729258898136685)
          ·
            refine ⟨7352387069523472086801257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19606365518729258898136685 7352387069523472086801257)
            ·
              refine ⟨5514290302142604065100943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7352387069523472086801257 5514290302142604065100943)
              ·
                refine ⟨8271435453213906097651415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5514290302142604065100943 8271435453213906097651415)
                ·
                  refine ⟨12407153179820859146477123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271435453213906097651415 12407153179820859146477123)
                  ·
                    refine ⟨18610729769731288719715685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12407153179820859146477123 18610729769731288719715685)
                    ·
                      refine ⟨3489511831824616634946691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18610729769731288719715685 3489511831824616634946691)
                      ·
                        rfl

theorem cell23_6795800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_6795800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795800 prefixEnd_6795800 := by exact prefixLift 6795800
  have htrace : WordTrace (prefixWord ++ tailWord_6795800) baseStart_6795800 baseEnd_6795800 := by
    simpa [prefixWord, tailWord_6795800, baseEnd_6795800] using wordTrace_append hprefix tailTrace_6795800
  have hstable : (prefixWord ++ tailWord_6795800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795800).length < 2 ^ (prefixWord ++ tailWord_6795800).sum := by decide
  have hdescent : baseEnd_6795800 < baseStart_6795800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795830 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_6795830 : Nat := 118140960795 + 6795830 * 2 ^ 59
def prefixEnd_6795830 : Nat := 4983230072969 + 3 ^ 40 * 6795830 * 2
def baseEnd_6795830 : Nat := 3489527236244251517571553

theorem tailTrace_6795830 : CollatzResearch.WordTrace tailWord_6795830 prefixEnd_6795830 3489527236244251517571553 := by
  unfold tailWord_6795830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15491517685617251262888059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165242855313250680137472629 15491517685617251262888059)
  ·
    refine ⟨23237276528425876894332089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15491517685617251262888059 23237276528425876894332089)
    ·
      refine ⟨17427957396319407670749067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23237276528425876894332089 17427957396319407670749067)
      ·
        refine ⟨26141936094479111506123601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17427957396319407670749067 26141936094479111506123601)
        ·
          refine ⟨19606452070859333629592701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26141936094479111506123601 19606452070859333629592701)
          ·
            refine ⟨7352419526572250111097263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19606452070859333629592701 7352419526572250111097263)
            ·
              refine ⟨11028629289858375166645895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352419526572250111097263 11028629289858375166645895)
              ·
                refine ⟨16542943934787562749968843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11028629289858375166645895 16542943934787562749968843)
                ·
                  refine ⟨24814415902181344124953265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16542943934787562749968843 24814415902181344124953265)
                  ·
                    refine ⟨18610811926636008093714949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24814415902181344124953265 18610811926636008093714949)
                    ·
                      refine ⟨3489527236244251517571553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18610811926636008093714949 3489527236244251517571553)
                      ·
                        rfl

theorem cell23_6795830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_6795830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795830 prefixEnd_6795830 := by exact prefixLift 6795830
  have htrace : WordTrace (prefixWord ++ tailWord_6795830) baseStart_6795830 baseEnd_6795830 := by
    simpa [prefixWord, tailWord_6795830, baseEnd_6795830] using wordTrace_append hprefix tailTrace_6795830
  have hstable : (prefixWord ++ tailWord_6795830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795830).length < 2 ^ (prefixWord ++ tailWord_6795830).sum := by decide
  have hdescent : baseEnd_6795830 < baseStart_6795830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795860 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_6795860 : Nat := 118140960795 + 6795860 * 2 ^ 59
def prefixEnd_6795860 : Nat := 4983230072969 + 3 ^ 40 * 6795860 * 2
def baseEnd_6795860 : Nat := 3489542640663886400196415

theorem tailTrace_6795860 : CollatzResearch.WordTrace tailWord_6795860 prefixEnd_6795860 3489542640663886400196415 := by
  unfold tailWord_6795860
  simp only [CollatzResearch.WordTrace]
  refine ⟨123932688579883667664900517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165243584773178223553200689 123932688579883667664900517)
  ·
    refine ⟨23237379108728187687168847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123932688579883667664900517 23237379108728187687168847)
    ·
      refine ⟨34856068663092281530753271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23237379108728187687168847 34856068663092281530753271)
      ·
        refine ⟨52284102994638422296129907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34856068663092281530753271 52284102994638422296129907)
        ·
          refine ⟨78426154491957633444194861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52284102994638422296129907 78426154491957633444194861)
          ·
            refine ⟨29409807934484112541573073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78426154491957633444194861 29409807934484112541573073)
            ·
              refine ⟨22057355950863084406179805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29409807934484112541573073 22057355950863084406179805)
              ·
                refine ⟨8271508481573656652317427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22057355950863084406179805 8271508481573656652317427)
                ·
                  refine ⟨12407262722360484978476141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271508481573656652317427 12407262722360484978476141)
                  ·
                    refine ⟨4652723520885181866928553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12407262722360484978476141 4652723520885181866928553)
                    ·
                      refine ⟨3489542640663886400196415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652723520885181866928553 3489542640663886400196415)
                      ·
                        rfl

theorem cell23_6795860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_6795860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795860 prefixEnd_6795860 := by exact prefixLift 6795860
  have htrace : WordTrace (prefixWord ++ tailWord_6795860) baseStart_6795860 baseEnd_6795860 := by
    simpa [prefixWord, tailWord_6795860, baseEnd_6795860] using wordTrace_append hprefix tailTrace_6795860
  have hstable : (prefixWord ++ tailWord_6795860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795860).length < 2 ^ (prefixWord ++ tailWord_6795860).sum := by decide
  have hdescent : baseEnd_6795860 < baseStart_6795860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795876 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_6795876 : Nat := 118140960795 + 6795876 * 2 ^ 59
def prefixEnd_6795876 : Nat := 4983230072969 + 3 ^ 40 * 6795876 * 2
def baseEnd_6795876 : Nat := 3489550856354358337596341

theorem tailTrace_6795876 : CollatzResearch.WordTrace tailWord_6795876 prefixEnd_6795876 3489550856354358337596341 := by
  unfold tailWord_6795876
  simp only [CollatzResearch.WordTrace]
  refine ⟨123932980363854685031191741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165243973818472913374922321 123932980363854685031191741)
  ·
    refine ⟨46474867636445506886696903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123932980363854685031191741 46474867636445506886696903)
    ·
      refine ⟨69712301454668260330045355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46474867636445506886696903 69712301454668260330045355)
      ·
        refine ⟨104568452182002390495068033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69712301454668260330045355 104568452182002390495068033)
        ·
          refine ⟨78426339136501792871301025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104568452182002390495068033 78426339136501792871301025)
          ·
            refine ⟨58819754352376344653475769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78426339136501792871301025 58819754352376344653475769)
            ·
              refine ⟨44114815764282258490106827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58819754352376344653475769 44114815764282258490106827)
              ·
                refine ⟨66172223646423387735160241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44114815764282258490106827 66172223646423387735160241)
                ·
                  refine ⟨49629167734817540801370181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66172223646423387735160241 49629167734817540801370181)
                  ·
                    refine ⟨9305468950278288900256909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49629167734817540801370181 9305468950278288900256909)
                    ·
                      refine ⟨3489550856354358337596341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305468950278288900256909 3489550856354358337596341)
                      ·
                        rfl

theorem cell23_6795876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_6795876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795876 prefixEnd_6795876 := by exact prefixLift 6795876
  have htrace : WordTrace (prefixWord ++ tailWord_6795876) baseStart_6795876 baseEnd_6795876 := by
    simpa [prefixWord, tailWord_6795876, baseEnd_6795876] using wordTrace_append hprefix tailTrace_6795876
  have hstable : (prefixWord ++ tailWord_6795876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795876).length < 2 ^ (prefixWord ++ tailWord_6795876).sum := by decide
  have hdescent : baseEnd_6795876 < baseStart_6795876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795894 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6795894 : Nat := 118140960795 + 6795894 * 2 ^ 59
def prefixEnd_6795894 : Nat := 4983230072969 + 3 ^ 40 * 6795894 * 2
def baseEnd_6795894 : Nat := 3489560099006139267171259

theorem tailTrace_6795894 : CollatzResearch.WordTrace tailWord_6795894 prefixEnd_6795894 3489560099006139267171259 := by
  unfold tailWord_6795894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15491663577602759946033671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165244411494429439424359157 15491663577602759946033671)
  ·
    refine ⟨23237495366404139919050507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15491663577602759946033671 23237495366404139919050507)
    ·
      refine ⟨34856243049606209878575761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23237495366404139919050507 34856243049606209878575761)
      ·
        refine ⟨26142182287204657408931821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34856243049606209878575761 26142182287204657408931821)
        ·
          refine ⟨9803318357701746528349433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26142182287204657408931821 9803318357701746528349433)
          ·
            refine ⟨7352488768276309896262075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9803318357701746528349433 7352488768276309896262075)
            ·
              refine ⟨11028733152414464844393113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352488768276309896262075 11028733152414464844393113)
              ·
                refine ⟨8271549864310848633294835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028733152414464844393113 8271549864310848633294835)
                ·
                  refine ⟨12407324796466272949942253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271549864310848633294835 12407324796466272949942253)
                  ·
                    refine ⟨4652746798674852356228345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12407324796466272949942253 4652746798674852356228345)
                    ·
                      refine ⟨3489560099006139267171259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652746798674852356228345 3489560099006139267171259)
                      ·
                        rfl

theorem cell23_6795894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6795894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795894 prefixEnd_6795894 := by exact prefixLift 6795894
  have htrace : WordTrace (prefixWord ++ tailWord_6795894) baseStart_6795894 baseEnd_6795894 := by
    simpa [prefixWord, tailWord_6795894, baseEnd_6795894] using wordTrace_append hprefix tailTrace_6795894
  have hstable : (prefixWord ++ tailWord_6795894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795894).length < 2 ^ (prefixWord ++ tailWord_6795894).sum := by decide
  have hdescent : baseEnd_6795894 < baseStart_6795894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795919 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_6795919 : Nat := 118140960795 + 6795919 * 2 ^ 59
def prefixEnd_6795919 : Nat := 4983230072969 + 3 ^ 40 * 6795919 * 2
def baseEnd_6795919 : Nat := 3489572936022501669358643

theorem tailTrace_6795919 : CollatzResearch.WordTrace tailWord_6795919 prefixEnd_6795919 3489572936022501669358643 := by
  unfold tailWord_6795919
  simp only [CollatzResearch.WordTrace]
  refine ⟨247867529066553588406198811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165245019377702392270799207 247867529066553588406198811)
  ·
    refine ⟨371801293599830382609298217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247867529066553588406198811 371801293599830382609298217)
    ·
      refine ⟨278850970199872786956973663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371801293599830382609298217 278850970199872786956973663)
      ·
        refine ⟨418276455299809180435460495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278850970199872786956973663 418276455299809180435460495)
        ·
          refine ⟨627414682949713770653190743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418276455299809180435460495 627414682949713770653190743)
          ·
            refine ⟨941122024424570655979786115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627414682949713770653190743 941122024424570655979786115)
            ·
              refine ⟨1411683036636855983969679173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941122024424570655979786115 1411683036636855983969679173)
              ·
                refine ⟨264690569369410496994314845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1411683036636855983969679173 264690569369410496994314845)
                ·
                  refine ⟨99258963513528936372868067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264690569369410496994314845 99258963513528936372868067)
                  ·
                    refine ⟨148888445270293404559302101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99258963513528936372868067 148888445270293404559302101)
                    ·
                      refine ⟨3489572936022501669358643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148888445270293404559302101 3489572936022501669358643)
                      ·
                        rfl

theorem cell23_6795919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_6795919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795919 prefixEnd_6795919 := by exact prefixLift 6795919
  have htrace : WordTrace (prefixWord ++ tailWord_6795919) baseStart_6795919 baseEnd_6795919 := by
    simpa [prefixWord, tailWord_6795919, baseEnd_6795919] using wordTrace_append hprefix tailTrace_6795919
  have hstable : (prefixWord ++ tailWord_6795919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795919).length < 2 ^ (prefixWord ++ tailWord_6795919).sum := by decide
  have hdescent : baseEnd_6795919 < baseStart_6795919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795924 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6795924 : Nat := 118140960795 + 6795924 * 2 ^ 59
def prefixEnd_6795924 : Nat := 4983230072969 + 3 ^ 40 * 6795924 * 2
def baseEnd_6795924 : Nat := 3489575503425774149796121

theorem tailTrace_6795924 : CollatzResearch.WordTrace tailWord_6795924 prefixEnd_6795924 3489575503425774149796121 := by
  unfold tailWord_6795924
  simp only [CollatzResearch.WordTrace]
  refine ⟨123933855715767737130065413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165245140954356982840087217 123933855715767737130065413)
  ·
    refine ⟨23237597946706450711887265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123933855715767737130065413 23237597946706450711887265)
    ·
      refine ⟨17428198460029838033915449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23237597946706450711887265 17428198460029838033915449)
      ·
        refine ⟨13071148845022378525436587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17428198460029838033915449 13071148845022378525436587)
        ·
          refine ⟨19606723267533567788154881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071148845022378525436587 19606723267533567788154881)
          ·
            refine ⟨14705042450650175841116161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19606723267533567788154881 14705042450650175841116161)
            ·
              refine ⟨11028781837987631880837121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14705042450650175841116161 11028781837987631880837121)
              ·
                refine ⟨8271586378490723910627841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11028781837987631880837121 8271586378490723910627841)
                ·
                  refine ⟨6203689783868042932970881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8271586378490723910627841 6203689783868042932970881)
                  ·
                    refine ⟨4652767337901032199728161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203689783868042932970881 4652767337901032199728161)
                    ·
                      refine ⟨3489575503425774149796121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652767337901032199728161 3489575503425774149796121)
                      ·
                        rfl

theorem cell23_6795924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6795924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795924 prefixEnd_6795924 := by exact prefixLift 6795924
  have htrace : WordTrace (prefixWord ++ tailWord_6795924) baseStart_6795924 baseEnd_6795924 := by
    simpa [prefixWord, tailWord_6795924, baseEnd_6795924] using wordTrace_append hprefix tailTrace_6795924
  have hstable : (prefixWord ++ tailWord_6795924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795924).length < 2 ^ (prefixWord ++ tailWord_6795924).sum := by decide
  have hdescent : baseEnd_6795924 < baseStart_6795924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795933 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_6795933 : Nat := 118140960795 + 6795933 * 2 ^ 59
def prefixEnd_6795933 : Nat := 4983230072969 + 3 ^ 40 * 6795933 * 2
def baseEnd_6795933 : Nat := 3489580124751664614583579

theorem tailTrace_6795933 : CollatzResearch.WordTrace tailWord_6795933 prefixEnd_6795933 3489580124751664614583579 := by
  unfold tailWord_6795933
  simp only [CollatzResearch.WordTrace]
  refine ⟨247868039688502868797208453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165245359792335245864805635 247868039688502868797208453)
  ·
    refine ⟨46475257441594287899476585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247868039688502868797208453 46475257441594287899476585)
    ·
      refine ⟨34856443081195715924607439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46475257441594287899476585 34856443081195715924607439)
      ·
        refine ⟨52284664621793573886911159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34856443081195715924607439 52284664621793573886911159)
        ·
          refine ⟨78426996932690360830366739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52284664621793573886911159 78426996932690360830366739)
          ·
            refine ⟨117640495399035541245550109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78426996932690360830366739 117640495399035541245550109)
            ·
              refine ⟨44115185774638327967081291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117640495399035541245550109 44115185774638327967081291)
              ·
                refine ⟨66172778661957491950621937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44115185774638327967081291 66172778661957491950621937)
                ·
                  refine ⟨49629583996468118962966453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66172778661957491950621937 49629583996468118962966453)
                  ·
                    refine ⟨4652773499668886152778105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49629583996468118962966453 4652773499668886152778105)
                    ·
                      refine ⟨3489580124751664614583579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652773499668886152778105 3489580124751664614583579)
                      ·
                        rfl

theorem cell23_6795933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_6795933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795933 prefixEnd_6795933 := by exact prefixLift 6795933
  have htrace : WordTrace (prefixWord ++ tailWord_6795933) baseStart_6795933 baseEnd_6795933 := by
    simpa [prefixWord, tailWord_6795933, baseEnd_6795933] using wordTrace_append hprefix tailTrace_6795933
  have hstable : (prefixWord ++ tailWord_6795933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795933).length < 2 ^ (prefixWord ++ tailWord_6795933).sum := by decide
  have hdescent : baseEnd_6795933 < baseStart_6795933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795976 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_6795976 : Nat := 118140960795 + 6795976 * 2 ^ 59
def prefixEnd_6795976 : Nat := 4983230072969 + 3 ^ 40 * 6795976 * 2
def baseEnd_6795976 : Nat := 3489602204419807946345881

theorem tailTrace_6795976 : CollatzResearch.WordTrace tailWord_6795976 prefixEnd_6795976 3489602204419807946345881 := by
  unfold tailWord_6795976
  simp only [CollatzResearch.WordTrace]
  refine ⟨123934804013673543570511891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165246405351564724760682521 123934804013673543570511891)
  ·
    refine ⟨185902206020510315355767837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123934804013673543570511891 185902206020510315355767837)
    ·
      refine ⟨69713327257691368258412939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185902206020510315355767837 69713327257691368258412939)
      ·
        refine ⟨104569990886537052387619409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69713327257691368258412939 104569990886537052387619409)
        ·
          refine ⟨78427493164902789290714557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104569990886537052387619409 78427493164902789290714557)
          ·
            refine ⟨29410309936838545984017959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78427493164902789290714557 29410309936838545984017959)
            ·
              refine ⟨44115464905257818976026939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29410309936838545984017959 44115464905257818976026939)
              ·
                refine ⟨66173197357886728464040409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44115464905257818976026939 66173197357886728464040409)
                ·
                  refine ⟨49629898018415046348030307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66173197357886728464040409 49629898018415046348030307)
                  ·
                    refine ⟨74444847027622569522045461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49629898018415046348030307 74444847027622569522045461)
                    ·
                      refine ⟨3489602204419807946345881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74444847027622569522045461 3489602204419807946345881)
                      ·
                        rfl

theorem cell23_6795976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_6795976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795976 prefixEnd_6795976 := by exact prefixLift 6795976
  have htrace : WordTrace (prefixWord ++ tailWord_6795976) baseStart_6795976 baseEnd_6795976 := by
    simpa [prefixWord, tailWord_6795976, baseEnd_6795976] using wordTrace_append hprefix tailTrace_6795976
  have hstable : (prefixWord ++ tailWord_6795976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795976).length < 2 ^ (prefixWord ++ tailWord_6795976).sum := by decide
  have hdescent : baseEnd_6795976 < baseStart_6795976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6795980 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6795980 : Nat := 118140960795 + 6795980 * 2 ^ 59
def prefixEnd_6795980 : Nat := 4983230072969 + 3 ^ 40 * 6795980 * 2
def baseEnd_6795980 : Nat := 3489604258342425930695863

theorem tailTrace_6795980 : CollatzResearch.WordTrace tailWord_6795980 prefixEnd_6795980 3489604258342425930695863 := by
  unfold tailWord_6795980
  simp only [CollatzResearch.WordTrace]
  refine ⟨123934876959666297912084697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165246502612888397216112929 123934876959666297912084697)
  ·
    refine ⟨92951157719749723434063523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123934876959666297912084697 92951157719749723434063523)
    ·
      refine ⟨139426736579624585151095285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92951157719749723434063523 139426736579624585151095285)
      ·
        refine ⟨13071256554339804857915183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139426736579624585151095285 13071256554339804857915183)
        ·
          refine ⟨19606884831509707286872775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071256554339804857915183 19606884831509707286872775)
          ·
            refine ⟨29410327247264560930309163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19606884831509707286872775 29410327247264560930309163)
            ·
              refine ⟨44115490870896841395463745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29410327247264560930309163 44115490870896841395463745)
              ·
                refine ⟨33086618153172631046597809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44115490870896841395463745 33086618153172631046597809)
                ·
                  refine ⟨24814963614879473284948357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33086618153172631046597809 24814963614879473284948357)
                  ·
                    refine ⟨4652805677789901240927817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24814963614879473284948357 4652805677789901240927817)
                    ·
                      refine ⟨3489604258342425930695863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652805677789901240927817 3489604258342425930695863)
                      ·
                        rfl

theorem cell23_6795980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6795980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6795980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6795980 prefixEnd_6795980 := by exact prefixLift 6795980
  have htrace : WordTrace (prefixWord ++ tailWord_6795980) baseStart_6795980 baseEnd_6795980 := by
    simpa [prefixWord, tailWord_6795980, baseEnd_6795980] using wordTrace_append hprefix tailTrace_6795980
  have hstable : (prefixWord ++ tailWord_6795980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6795980).length < 2 ^ (prefixWord ++ tailWord_6795980).sum := by decide
  have hdescent : baseEnd_6795980 < baseStart_6795980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6795980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796013 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_6796013 : Nat := 118140960795 + 6796013 * 2 ^ 59
def prefixEnd_6796013 : Nat := 4983230072969 + 3 ^ 40 * 6796013 * 2
def baseEnd_6796013 : Nat := 3489621203204024301583211

theorem tailTrace_6796013 : CollatzResearch.WordTrace tailWord_6796013 prefixEnd_6796013 3489621203204024301583211 := by
  unfold tailWord_6796013
  simp only [CollatzResearch.WordTrace]
  refine ⟨247870957528213042460120693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165247305018808694973413795 247870957528213042460120693)
  ·
    refine ⟨23237902268269972730636315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247870957528213042460120693 23237902268269972730636315)
    ·
      refine ⟨34856853402404959095954473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23237902268269972730636315 34856853402404959095954473)
      ·
        refine ⟨26142640051803719321965855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34856853402404959095954473 26142640051803719321965855)
        ·
          refine ⟨39213960077705578982948783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26142640051803719321965855 39213960077705578982948783)
          ·
            refine ⟨58820940116558368474423175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39213960077705578982948783 58820940116558368474423175)
            ·
              refine ⟨88231410174837552711634763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58820940116558368474423175 88231410174837552711634763)
              ·
                refine ⟨132347115262256329067452145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88231410174837552711634763 132347115262256329067452145)
                ·
                  refine ⟨99260336446692246800589109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132347115262256329067452145 99260336446692246800589109)
                  ·
                    refine ⟨9305656541877398137555229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99260336446692246800589109 9305656541877398137555229)
                    ·
                      refine ⟨3489621203204024301583211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305656541877398137555229 3489621203204024301583211)
                      ·
                        rfl

theorem cell23_6796013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_6796013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796013 prefixEnd_6796013 := by exact prefixLift 6796013
  have htrace : WordTrace (prefixWord ++ tailWord_6796013) baseStart_6796013 baseEnd_6796013 := by
    simpa [prefixWord, tailWord_6796013, baseEnd_6796013] using wordTrace_append hprefix tailTrace_6796013
  have hstable : (prefixWord ++ tailWord_6796013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796013).length < 2 ^ (prefixWord ++ tailWord_6796013).sum := by decide
  have hdescent : baseEnd_6796013 < baseStart_6796013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796040 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_6796040 : Nat := 118140960795 + 6796040 * 2 ^ 59
def prefixEnd_6796040 : Nat := 4983230072969 + 3 ^ 40 * 6796040 * 2
def baseEnd_6796040 : Nat := 3489635067181695695945587

theorem tailTrace_6796040 : CollatzResearch.WordTrace tailWord_6796040 prefixEnd_6796040 3489635067181695695945587 := by
  unfold tailWord_6796040
  simp only [CollatzResearch.WordTrace]
  refine ⟨123935971149557613035676787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165247961532743484047569049 123935971149557613035676787)
  ·
    refine ⟨185903956724336419553515181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123935971149557613035676787 185903956724336419553515181)
    ·
      refine ⟨69713983771626157332568193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185903956724336419553515181 69713983771626157332568193)
      ·
        refine ⟨52285487828719617999426145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69713983771626157332568193 52285487828719617999426145)
        ·
          refine ⟨39214115871539713499569609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52285487828719617999426145 39214115871539713499569609)
          ·
            refine ⟨29410586903654785124677207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39214115871539713499569609 29410586903654785124677207)
            ·
              refine ⟨44115880355482177687015811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29410586903654785124677207 44115880355482177687015811)
              ·
                refine ⟨66173820533223266530523717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44115880355482177687015811 66173820533223266530523717)
                ·
                  refine ⟨12407591349979362474473197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66173820533223266530523717 12407591349979362474473197)
                  ·
                    refine ⟨4652846756242260927927449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12407591349979362474473197 4652846756242260927927449)
                    ·
                      refine ⟨3489635067181695695945587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652846756242260927927449 3489635067181695695945587)
                      ·
                        rfl

theorem cell23_6796040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_6796040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796040 prefixEnd_6796040 := by exact prefixLift 6796040
  have htrace : WordTrace (prefixWord ++ tailWord_6796040) baseStart_6796040 baseEnd_6796040 := by
    simpa [prefixWord, tailWord_6796040, baseEnd_6796040] using wordTrace_append hprefix tailTrace_6796040
  have hstable : (prefixWord ++ tailWord_6796040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796040).length < 2 ^ (prefixWord ++ tailWord_6796040).sum := by decide
  have hdescent : baseEnd_6796040 < baseStart_6796040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796053 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_6796053 : Nat := 118140960795 + 6796053 * 2 ^ 59
def prefixEnd_6796053 : Nat := 4983230072969 + 3 ^ 40 * 6796053 * 2
def baseEnd_6796053 : Nat := 3489641742430204145083027

theorem tailTrace_6796053 : CollatzResearch.WordTrace tailWord_6796053 prefixEnd_6796053 3489641742430204145083027 := by
  unfold tailWord_6796053
  simp only [CollatzResearch.WordTrace]
  refine ⟨247872416448068129291576813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165248277632045419527717875 247872416448068129291576813)
  ·
    refine ⟨92952156168025548484341305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247872416448068129291576813 92952156168025548484341305)
    ·
      refine ⟨69714117126019161363255979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92952156168025548484341305 69714117126019161363255979)
      ·
        refine ⟨104571175689028742044883969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69714117126019161363255979 104571175689028742044883969)
        ·
          refine ⟨78428381766771556533662977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104571175689028742044883969 78428381766771556533662977)
          ·
            refine ⟨58821286325078667400247233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78428381766771556533662977 58821286325078667400247233)
            ·
              refine ⟨44115964743809000550185425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58821286325078667400247233 44115964743809000550185425)
              ·
                refine ⟨33086973557856750412639069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44115964743809000550185425 33086973557856750412639069)
                ·
                  refine ⟨12407615084196281404739651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33086973557856750412639069 12407615084196281404739651)
                  ·
                    refine ⟨18611422626294422107109477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12407615084196281404739651 18611422626294422107109477)
                    ·
                      refine ⟨3489641742430204145083027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18611422626294422107109477 3489641742430204145083027)
                      ·
                        rfl

theorem cell23_6796053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_6796053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796053 prefixEnd_6796053 := by exact prefixLift 6796053
  have htrace : WordTrace (prefixWord ++ tailWord_6796053) baseStart_6796053 baseEnd_6796053 := by
    simpa [prefixWord, tailWord_6796053, baseEnd_6796053] using wordTrace_append hprefix tailTrace_6796053
  have hstable : (prefixWord ++ tailWord_6796053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796053).length < 2 ^ (prefixWord ++ tailWord_6796053).sum := by decide
  have hdescent : baseEnd_6796053 < baseStart_6796053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796073 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 3]
def baseStart_6796073 : Nat := 118140960795 + 6796073 * 2 ^ 59
def prefixEnd_6796073 : Nat := 4983230072969 + 3 ^ 40 * 6796073 * 2
def baseEnd_6796073 : Nat := 3489652012043294066832935

theorem tailTrace_6796073 : CollatzResearch.WordTrace tailWord_6796073 prefixEnd_6796073 3489652012043294066832935 := by
  unfold tailWord_6796073
  simp only [CollatzResearch.WordTrace]
  refine ⟨247873145907995672707304873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165248763938663781804869915 247873145907995672707304873)
  ·
    refine ⟨185904859430996754530478655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247873145907995672707304873 185904859430996754530478655)
    ·
      refine ⟨278857289146495131795717983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185904859430996754530478655 278857289146495131795717983)
      ·
        refine ⟨418285933719742697693576975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278857289146495131795717983 418285933719742697693576975)
        ·
          refine ⟨627428900579614046540365463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418285933719742697693576975 627428900579614046540365463)
          ·
            refine ⟨941143350869421069810548195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627428900579614046540365463 941143350869421069810548195)
            ·
              refine ⟨1411715026304131604715822293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941143350869421069810548195 1411715026304131604715822293)
              ·
                refine ⟨33087070929003084485527085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1411715026304131604715822293 33087070929003084485527085)
                ·
                  refine ⟨12407651598376156682072657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33087070929003084485527085 12407651598376156682072657)
                  ·
                    refine ⟨9305738698782117511554493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12407651598376156682072657 9305738698782117511554493)
                    ·
                      refine ⟨3489652012043294066832935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305738698782117511554493 3489652012043294066832935)
                      ·
                        rfl

theorem cell23_6796073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_6796073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796073 prefixEnd_6796073 := by exact prefixLift 6796073
  have htrace : WordTrace (prefixWord ++ tailWord_6796073) baseStart_6796073 baseEnd_6796073 := by
    simpa [prefixWord, tailWord_6796073, baseEnd_6796073] using wordTrace_append hprefix tailTrace_6796073
  have hstable : (prefixWord ++ tailWord_6796073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796073).length < 2 ^ (prefixWord ++ tailWord_6796073).sum := by decide
  have hdescent : baseEnd_6796073 < baseStart_6796073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796076 : List Nat := [2, 2, 1, 1, 1, 4, 1, 11]
def baseStart_6796076 : Nat := 118140960795 + 6796076 * 2 ^ 59
def prefixEnd_6796076 : Nat := 4983230072969 + 3 ^ 40 * 6796076 * 2
def baseEnd_6796076 : Nat := 129246427869824353892423

theorem tailTrace_6796076 : CollatzResearch.WordTrace tailWord_6796076 prefixEnd_6796076 129246427869824353892423 := by
  unfold tailWord_6796076
  simp only [CollatzResearch.WordTrace]
  refine ⟨123936627663492402109832041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165248836884656536146442721 123936627663492402109832041)
  ·
    refine ⟨92952470747619301582374031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123936627663492402109832041 92952470747619301582374031)
    ·
      refine ⟨139428706121428952373561047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92952470747619301582374031 139428706121428952373561047)
      ·
        refine ⟨209143059182143428560341571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139428706121428952373561047 209143059182143428560341571)
        ·
          refine ⟨313714588773215142840512357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209143059182143428560341571 313714588773215142840512357)
          ·
            refine ⟨58821485394977839282596067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313714588773215142840512357 58821485394977839282596067)
            ·
              refine ⟨88232228092466758923894101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58821485394977839282596067 88232228092466758923894101)
              ·
                refine ⟨129246427869824353892423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 88232228092466758923894101 129246427869824353892423)
                ·
                  rfl

theorem cell23_6796076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 11].length) (baseStart_6796076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796076 prefixEnd_6796076 := by exact prefixLift 6796076
  have htrace : WordTrace (prefixWord ++ tailWord_6796076) baseStart_6796076 baseEnd_6796076 := by
    simpa [prefixWord, tailWord_6796076, baseEnd_6796076] using wordTrace_append hprefix tailTrace_6796076
  have hstable : (prefixWord ++ tailWord_6796076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796076).length < 2 ^ (prefixWord ++ tailWord_6796076).sum := by decide
  have hdescent : baseEnd_6796076 < baseStart_6796076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796083 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4]
def baseStart_6796083 : Nat := 118140960795 + 6796083 * 2 ^ 59
def prefixEnd_6796083 : Nat := 4983230072969 + 3 ^ 40 * 6796083 * 2
def baseEnd_6796083 : Nat := 3489657146849839027707889

theorem tailTrace_6796083 : CollatzResearch.WordTrace tailWord_6796083 prefixEnd_6796083 3489657146849839027707889 := by
  unfold tailWord_6796083
  simp only [CollatzResearch.WordTrace]
  refine ⟨247873510637959444415168903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165249007091972962943445935 247873510637959444415168903)
  ·
    refine ⟨371810265956939166622753355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247873510637959444415168903 371810265956939166622753355)
    ·
      refine ⟨557715398935408749934130033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371810265956939166622753355 557715398935408749934130033)
      ·
        refine ⟨418286549201556562450597525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557715398935408749934130033 418286549201556562450597525)
        ·
          refine ⟨19607181993822963864871759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 418286549201556562450597525 19607181993822963864871759)
          ·
            refine ⟨29410772990734445797307639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19607181993822963864871759 29410772990734445797307639)
            ·
              refine ⟨44116159486101668695961459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29410772990734445797307639 44116159486101668695961459)
              ·
                refine ⟨66174239229152503043942189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44116159486101668695961459 66174239229152503043942189)
                ·
                  refine ⟨24815339710932188641478321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66174239229152503043942189 24815339710932188641478321)
                  ·
                    refine ⟨18611504783199141481108741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24815339710932188641478321 18611504783199141481108741)
                    ·
                      refine ⟨3489657146849839027707889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18611504783199141481108741 3489657146849839027707889)
                      ·
                        rfl

theorem cell23_6796083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_6796083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796083 prefixEnd_6796083 := by exact prefixLift 6796083
  have htrace : WordTrace (prefixWord ++ tailWord_6796083) baseStart_6796083 baseEnd_6796083 := by
    simpa [prefixWord, tailWord_6796083, baseEnd_6796083] using wordTrace_append hprefix tailTrace_6796083
  have hstable : (prefixWord ++ tailWord_6796083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796083).length < 2 ^ (prefixWord ++ tailWord_6796083).sum := by decide
  have hdescent : baseEnd_6796083 < baseStart_6796083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796084 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_6796084 : Nat := 118140960795 + 6796084 * 2 ^ 59
def prefixEnd_6796084 : Nat := 4983230072969 + 3 ^ 40 * 6796084 * 2
def baseEnd_6796084 : Nat := 1163219220110164507931795

theorem tailTrace_6796084 : CollatzResearch.WordTrace tailWord_6796084 prefixEnd_6796084 1163219220110164507931795 := by
  unfold tailWord_6796084
  simp only [CollatzResearch.WordTrace]
  refine ⟨123936773555477910792977653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165249031407303881057303537 123936773555477910792977653)
  ·
    refine ⟨11619072520826054136841655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123936773555477910792977653 11619072520826054136841655)
    ·
      refine ⟨17428608781239081205262483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11619072520826054136841655 17428608781239081205262483)
      ·
        refine ⟨26142913171858621807893725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17428608781239081205262483 26142913171858621807893725)
        ·
          refine ⟨9803592439446983177960147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26142913171858621807893725 9803592439446983177960147)
          ·
            refine ⟨14705388659170474766940221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9803592439446983177960147 14705388659170474766940221)
            ·
              refine ⟨5514520747188928037602583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14705388659170474766940221 5514520747188928037602583)
              ·
                refine ⟨8271781120783392056403875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5514520747188928037602583 8271781120783392056403875)
                ·
                  refine ⟨12407671681175088084605813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8271781120783392056403875 12407671681175088084605813)
                  ·
                    refine ⟨1163219220110164507931795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12407671681175088084605813 1163219220110164507931795)
                    ·
                      rfl

theorem cell23_6796084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_6796084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796084 prefixEnd_6796084 := by exact prefixLift 6796084
  have htrace : WordTrace (prefixWord ++ tailWord_6796084) baseStart_6796084 baseEnd_6796084 := by
    simpa [prefixWord, tailWord_6796084, baseEnd_6796084] using wordTrace_append hprefix tailTrace_6796084
  have hstable : (prefixWord ++ tailWord_6796084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796084).length < 2 ^ (prefixWord ++ tailWord_6796084).sum := by decide
  have hdescent : baseEnd_6796084 < baseStart_6796084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796093 : List Nat := [1, 4, 1, 4, 2, 11]
def baseStart_6796093 : Nat := 118140960795 + 6796093 * 2 ^ 59
def prefixEnd_6796093 : Nat := 4983230072969 + 3 ^ 40 * 6796093 * 2
def baseEnd_6796093 : Nat := 14360750130273185138201

theorem tailTrace_6796093 : CollatzResearch.WordTrace tailWord_6796093 prefixEnd_6796093 14360750130273185138201 := by
  unfold tailWord_6796093
  simp only [CollatzResearch.WordTrace]
  refine ⟨247873875367923216123032933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165249250245282144082021955 247873875367923216123032933)
  ·
    refine ⟨46476351631485603023068675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247873875367923216123032933 46476351631485603023068675)
    ·
      refine ⟨69714527447228404534603013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46476351631485603023068675 69714527447228404534603013)
      ·
        refine ⟨13071473896355325850238065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69714527447228404534603013 13071473896355325850238065)
        ·
          refine ⟨9803605422266494387678549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13071473896355325850238065 9803605422266494387678549)
          ·
            refine ⟨14360750130273185138201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9803605422266494387678549 14360750130273185138201)
            ·
              rfl

theorem cell23_6796093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 11].length) (baseStart_6796093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796093 prefixEnd_6796093 := by exact prefixLift 6796093
  have htrace : WordTrace (prefixWord ++ tailWord_6796093) baseStart_6796093 baseEnd_6796093 := by
    simpa [prefixWord, tailWord_6796093, baseEnd_6796093] using wordTrace_append hprefix tailTrace_6796093
  have hstable : (prefixWord ++ tailWord_6796093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796093).length < 2 ^ (prefixWord ++ tailWord_6796093).sum := by decide
  have hdescent : baseEnd_6796093 < baseStart_6796093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796103 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_6796103 : Nat := 118140960795 + 6796103 * 2 ^ 59
def prefixEnd_6796103 : Nat := 4983230072969 + 3 ^ 40 * 6796103 * 2
def baseEnd_6796103 : Nat := 3489667416462928949457797

theorem tailTrace_6796103 : CollatzResearch.WordTrace tailWord_6796103 prefixEnd_6796103 3489667416462928949457797 := by
  unfold tailWord_6796103
  simp only [CollatzResearch.WordTrace]
  refine ⟨247874240097886987830896963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165249493398591325220597975 247874240097886987830896963)
  ·
    refine ⟨371811360146830481746345445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247874240097886987830896963 371811360146830481746345445)
    ·
      refine ⟨69714630027530715327439771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371811360146830481746345445 69714630027530715327439771)
      ·
        refine ⟨104571945041296072991159657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69714630027530715327439771 104571945041296072991159657)
        ·
          refine ⟨78428958780972054743369743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104571945041296072991159657 78428958780972054743369743)
          ·
            refine ⟨117643438171458082115054615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78428958780972054743369743 117643438171458082115054615)
            ·
              refine ⟨176465157257187123172581923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117643438171458082115054615 176465157257187123172581923)
              ·
                refine ⟨264697735885780684758872885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176465157257187123172581923 264697735885780684758872885)
                ·
                  refine ⟨24815412739291939196144333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264697735885780684758872885 24815412739291939196144333)
                  ·
                    refine ⟨9305779777234477198554125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24815412739291939196144333 9305779777234477198554125)
                    ·
                      refine ⟨3489667416462928949457797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9305779777234477198554125 3489667416462928949457797)
                      ·
                        rfl

theorem cell23_6796103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_6796103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796103 prefixEnd_6796103 := by exact prefixLift 6796103
  have htrace : WordTrace (prefixWord ++ tailWord_6796103) baseStart_6796103 baseEnd_6796103 := by
    simpa [prefixWord, tailWord_6796103, baseEnd_6796103] using wordTrace_append hprefix tailTrace_6796103
  have hstable : (prefixWord ++ tailWord_6796103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796103).length < 2 ^ (prefixWord ++ tailWord_6796103).sum := by decide
  have hdescent : baseEnd_6796103 < baseStart_6796103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796104 : List Nat := [2, 1, 3, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_6796104 : Nat := 118140960795 + 6796104 * 2 ^ 59
def prefixEnd_6796104 : Nat := 4983230072969 + 3 ^ 40 * 6796104 * 2
def baseEnd_6796104 : Nat := 3489667929943583445545293

theorem tailTrace_6796104 : CollatzResearch.WordTrace tailWord_6796104 prefixEnd_6796104 3489667929943583445545293 := by
  unfold tailWord_6796104
  simp only [CollatzResearch.WordTrace]
  refine ⟨123937138285441682500841683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165249517713922243334455577 123937138285441682500841683)
  ·
    refine ⟨185905707428162523751262525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123937138285441682500841683 185905707428162523751262525)
    ·
      refine ⟨69714640285560946406723447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185905707428162523751262525 69714640285560946406723447)
      ·
        refine ⟨104571960428341419610085171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69714640285560946406723447 104571960428341419610085171)
        ·
          refine ⟨156857940642512129415127757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104571960428341419610085171 156857940642512129415127757)
          ·
            refine ⟨58821727740942048530672909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156857940642512129415127757 58821727740942048530672909)
            ·
              refine ⟨22058147902853268199002341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58821727740942048530672909 22058147902853268199002341)
              ·
                refine ⟨4135902731784987787312939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22058147902853268199002341 4135902731784987787312939)
                ·
                  refine ⟨6203854097677481680969409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4135902731784987787312939 6203854097677481680969409)
                  ·
                    refine ⟨4652890573258111260727057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203854097677481680969409 4652890573258111260727057)
                    ·
                      refine ⟨3489667929943583445545293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652890573258111260727057 3489667929943583445545293)
                      ·
                        rfl

theorem cell23_6796104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_6796104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796104 prefixEnd_6796104 := by exact prefixLift 6796104
  have htrace : WordTrace (prefixWord ++ tailWord_6796104) baseStart_6796104 baseEnd_6796104 := by
    simpa [prefixWord, tailWord_6796104, baseEnd_6796104] using wordTrace_append hprefix tailTrace_6796104
  have hstable : (prefixWord ++ tailWord_6796104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796104).length < 2 ^ (prefixWord ++ tailWord_6796104).sum := by decide
  have hdescent : baseEnd_6796104 < baseStart_6796104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796153 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 2, 6]
def baseStart_6796153 : Nat := 118140960795 + 6796153 * 2 ^ 59
def prefixEnd_6796153 : Nat := 4983230072969 + 3 ^ 40 * 6796153 * 2
def baseEnd_6796153 : Nat := 1163231030165217917944189

theorem tailTrace_6796153 : CollatzResearch.WordTrace tailWord_6796153 prefixEnd_6796153 1163231030165217917944189 := by
  unfold tailWord_6796153
  simp only [CollatzResearch.WordTrace]
  refine ⟨247876063747705846370217113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165250709165137230913478075 247876063747705846370217113)
  ·
    refine ⟨185907047810779384777662835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247876063747705846370217113 185907047810779384777662835)
    ·
      refine ⟨278860571716169077166494253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185907047810779384777662835 278860571716169077166494253)
      ·
        refine ⟨104572714393563403937435345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278860571716169077166494253 104572714393563403937435345)
        ·
          refine ⟨78429535795172552953076509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104572714393563403937435345 78429535795172552953076509)
          ·
            refine ⟨29411075923189707357403691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78429535795172552953076509 29411075923189707357403691)
            ·
              refine ⟨44116613884784561036105537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29411075923189707357403691 44116613884784561036105537)
              ·
                refine ⟨33087460413588420777079153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44116613884784561036105537 33087460413588420777079153)
                ·
                  refine ⟨24815595310191315582809365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33087460413588420777079153 24815595310191315582809365)
                  ·
                    refine ⟨1163231030165217917944189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24815595310191315582809365 1163231030165217917944189)
                    ·
                      rfl

theorem cell23_6796153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_6796153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796153 prefixEnd_6796153 := by exact prefixLift 6796153
  have htrace : WordTrace (prefixWord ++ tailWord_6796153) baseStart_6796153 baseEnd_6796153 := by
    simpa [prefixWord, tailWord_6796153, baseEnd_6796153] using wordTrace_append hprefix tailTrace_6796153
  have hstable : (prefixWord ++ tailWord_6796153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796153).length < 2 ^ (prefixWord ++ tailWord_6796153).sum := by decide
  have hdescent : baseEnd_6796153 < baseStart_6796153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796170 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_6796170 : Nat := 118140960795 + 6796170 * 2 ^ 59
def prefixEnd_6796170 : Nat := 4983230072969 + 3 ^ 40 * 6796170 * 2
def baseEnd_6796170 : Nat := 1163233939888926729106663

theorem tailTrace_6796170 : CollatzResearch.WordTrace tailWord_6796170 prefixEnd_6796170 1163233939888926729106663 := by
  unfold tailWord_6796170
  simp only [CollatzResearch.WordTrace]
  refine ⟨61969170947161064568396491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165251122525762838849057309 61969170947161064568396491)
  ·
    refine ⟨92953756420741596852594737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61969170947161064568396491 92953756420741596852594737)
    ·
      refine ⟨69715317315556197639446053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92953756420741596852594737 69715317315556197639446053)
      ·
        refine ⟨13071621996666787057396135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69715317315556197639446053 13071621996666787057396135)
        ·
          refine ⟨19607432995000180586094203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071621996666787057396135 19607432995000180586094203)
          ·
            refine ⟨29411149492500270879141305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19607432995000180586094203 29411149492500270879141305)
            ·
              refine ⟨22058362119375203159355979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29411149492500270879141305 22058362119375203159355979)
              ·
                refine ⟨33087543179062804739033969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22058362119375203159355979 33087543179062804739033969)
                ·
                  refine ⟨24815657384297103554275477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33087543179062804739033969 24815657384297103554275477)
                  ·
                    refine ⟨1163233939888926729106663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24815657384297103554275477 1163233939888926729106663)
                    ·
                      rfl

theorem cell23_6796170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_6796170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796170 prefixEnd_6796170 := by exact prefixLift 6796170
  have htrace : WordTrace (prefixWord ++ tailWord_6796170) baseStart_6796170 baseEnd_6796170 := by
    simpa [prefixWord, tailWord_6796170, baseEnd_6796170] using wordTrace_append hprefix tailTrace_6796170
  have hstable : (prefixWord ++ tailWord_6796170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796170).length < 2 ^ (prefixWord ++ tailWord_6796170).sum := by decide
  have hdescent : baseEnd_6796170 < baseStart_6796170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796180 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6796180 : Nat := 118140960795 + 6796180 * 2 ^ 59
def prefixEnd_6796180 : Nat := 4983230072969 + 3 ^ 40 * 6796180 * 2
def baseEnd_6796180 : Nat := 3489706954473325148194943

theorem tailTrace_6796180 : CollatzResearch.WordTrace tailWord_6796180 prefixEnd_6796180 3489706954473325148194943 := by
  unfold tailWord_6796180
  simp only [CollatzResearch.WordTrace]
  refine ⟨123938524259304014990724997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165251365679072019987633329 123938524259304014990724997)
  ·
    refine ⟨23238473298619502810760937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123938524259304014990724997 23238473298619502810760937)
    ·
      refine ⟨17428854973964627108070703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23238473298619502810760937 17428854973964627108070703)
      ·
        refine ⟨26143282460946940662106055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17428854973964627108070703 26143282460946940662106055)
        ·
          refine ⟨39214923691420410993159083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26143282460946940662106055 39214923691420410993159083)
          ·
            refine ⟨58822385537130616489738625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39214923691420410993159083 58822385537130616489738625)
            ·
              refine ⟨44116789152847962367303969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58822385537130616489738625 44116789152847962367303969)
              ·
                refine ⟨33087591864635971775477977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44116789152847962367303969 33087591864635971775477977)
                ·
                  refine ⟨24815693898476978831608483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33087591864635971775477977 24815693898476978831608483)
                  ·
                    refine ⟨37223540847715468247412725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24815693898476978831608483 37223540847715468247412725)
                    ·
                      refine ⟨3489706954473325148194943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37223540847715468247412725 3489706954473325148194943)
                      ·
                        rfl

theorem cell23_6796180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6796180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796180 prefixEnd_6796180 := by exact prefixLift 6796180
  have htrace : WordTrace (prefixWord ++ tailWord_6796180) baseStart_6796180 baseEnd_6796180 := by
    simpa [prefixWord, tailWord_6796180, baseEnd_6796180] using wordTrace_append hprefix tailTrace_6796180
  have hstable : (prefixWord ++ tailWord_6796180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796180).length < 2 ^ (prefixWord ++ tailWord_6796180).sum := by decide
  have hdescent : baseEnd_6796180 < baseStart_6796180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796183 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 7]
def baseStart_6796183 : Nat := 118140960795 + 6796183 * 2 ^ 59
def prefixEnd_6796183 : Nat := 4983230072969 + 3 ^ 40 * 6796183 * 2
def baseEnd_6796183 : Nat := 387745388323920959606381

theorem tailTrace_6796183 : CollatzResearch.WordTrace tailWord_6796183 prefixEnd_6796183 387745388323920959606381 := by
  unfold tailWord_6796183
  simp only [CollatzResearch.WordTrace]
  refine ⟨247877157937597161493809203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165251438625064774329206135 247877157937597161493809203)
  ·
    refine ⟨371815736906395742240713805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247877157937597161493809203 371815736906395742240713805)
    ·
      refine ⟨139430901339898403340267677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371815736906395742240713805 139430901339898403340267677)
      ·
        refine ⟨52286588002461901252600379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139430901339898403340267677 52286588002461901252600379)
        ·
          refine ⟨78429882003692851878900569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52286588002461901252600379 78429882003692851878900569)
          ·
            refine ⟨58822411502769638909175427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78429882003692851878900569 58822411502769638909175427)
            ·
              refine ⟨88233617254154458363763141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58822411502769638909175427 88233617254154458363763141)
              ·
                refine ⟨16543803235153960943205589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88233617254154458363763141 16543803235153960943205589)
                ·
                  refine ⟨387745388323920959606381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16543803235153960943205589 387745388323920959606381)
                  ·
                    rfl

theorem cell23_6796183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 7].length) (baseStart_6796183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796183 prefixEnd_6796183 := by exact prefixLift 6796183
  have htrace : WordTrace (prefixWord ++ tailWord_6796183) baseStart_6796183 baseEnd_6796183 := by
    simpa [prefixWord, tailWord_6796183, baseEnd_6796183] using wordTrace_append hprefix tailTrace_6796183
  have hstable : (prefixWord ++ tailWord_6796183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796183).length < 2 ^ (prefixWord ++ tailWord_6796183).sum := by decide
  have hdescent : baseEnd_6796183 < baseStart_6796183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796194 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_6796194 : Nat := 118140960795 + 6796194 * 2 ^ 59
def prefixEnd_6796194 : Nat := 4983230072969 + 3 ^ 40 * 6796194 * 2
def baseEnd_6796194 : Nat := 3489714143202488093419879

theorem tailTrace_6796194 : CollatzResearch.WordTrace tailWord_6796194 prefixEnd_6796194 3489714143202488093419879 := by
  unfold tailWord_6796194
  simp only [CollatzResearch.WordTrace]
  refine ⟨61969389785139327593114909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165251706093704873581639757 61969389785139327593114909)
  ·
    refine ⟨23238521169427247847418091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61969389785139327593114909 23238521169427247847418091)
    ·
      refine ⟨34857781754140871771127137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23238521169427247847418091 34857781754140871771127137)
      ·
        refine ⟨26143336315605653828345353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34857781754140871771127137 26143336315605653828345353)
        ·
          refine ⟨19607502236704240371259015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26143336315605653828345353 19607502236704240371259015)
          ·
            refine ⟨29411253355056360556888523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19607502236704240371259015 29411253355056360556888523)
            ·
              refine ⟨44116880032584540835332785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29411253355056360556888523 44116880032584540835332785)
              ·
                refine ⟨33087660024438405626499589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44116880032584540835332785 33087660024438405626499589)
                ·
                  refine ⟨6203936254582201054968673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33087660024438405626499589 6203936254582201054968673)
                  ·
                    refine ⟨4652952190936650791226505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203936254582201054968673 4652952190936650791226505)
                    ·
                      refine ⟨3489714143202488093419879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652952190936650791226505 3489714143202488093419879)
                      ·
                        rfl

theorem cell23_6796194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_6796194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796194 prefixEnd_6796194 := by exact prefixLift 6796194
  have htrace : WordTrace (prefixWord ++ tailWord_6796194) baseStart_6796194 baseEnd_6796194 := by
    simpa [prefixWord, tailWord_6796194, baseEnd_6796194] using wordTrace_append hprefix tailTrace_6796194
  have hstable : (prefixWord ++ tailWord_6796194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796194).length < 2 ^ (prefixWord ++ tailWord_6796194).sum := by decide
  have hdescent : baseEnd_6796194 < baseStart_6796194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796228 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6796228 : Nat := 118140960795 + 6796228 * 2 ^ 59
def prefixEnd_6796228 : Nat := 4983230072969 + 3 ^ 40 * 6796228 * 2
def baseEnd_6796228 : Nat := 3489731601544740960394723

theorem tailTrace_6796228 : CollatzResearch.WordTrace tailWord_6796228 prefixEnd_6796228 3489731601544740960394723 := by
  unfold tailWord_6796228
  simp only [CollatzResearch.WordTrace]
  refine ⟨123939399611217067089598669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165252532814956089452798225 123939399611217067089598669)
  ·
    refine ⟨46477274854206400158599501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123939399611217067089598669 46477274854206400158599501)
    ·
      refine ⟨17428978070327400059474813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46477274854206400158599501 17428978070327400059474813)
      ·
        refine ⟨6535866776372775022303055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17428978070327400059474813 6535866776372775022303055)
        ·
          refine ⟨9803800164559162533454583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6535866776372775022303055 9803800164559162533454583)
          ·
            refine ⟨14705700246838743800181875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9803800164559162533454583 14705700246838743800181875)
            ·
              refine ⟨22058550370258115700272813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14705700246838743800181875 22058550370258115700272813)
              ·
                refine ⟨8271956388846793387602305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22058550370258115700272813 8271956388846793387602305)
                ·
                  refine ⟨6203967291635095040701729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8271956388846793387602305 6203967291635095040701729)
                  ·
                    refine ⟨4652975468726321280526297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6203967291635095040701729 4652975468726321280526297)
                    ·
                      refine ⟨3489731601544740960394723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4652975468726321280526297 3489731601544740960394723)
                      ·
                        rfl

theorem cell23_6796228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6796228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796228 prefixEnd_6796228 := by exact prefixLift 6796228
  have htrace : WordTrace (prefixWord ++ tailWord_6796228) baseStart_6796228 baseEnd_6796228 := by
    simpa [prefixWord, tailWord_6796228, baseEnd_6796228] using wordTrace_append hprefix tailTrace_6796228
  have hstable : (prefixWord ++ tailWord_6796228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796228).length < 2 ^ (prefixWord ++ tailWord_6796228).sum := by decide
  have hdescent : baseEnd_6796228 < baseStart_6796228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796260 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_6796260 : Nat := 118140960795 + 6796260 * 2 ^ 59
def prefixEnd_6796260 : Nat := 4983230072969 + 3 ^ 40 * 6796260 * 2
def baseEnd_6796260 : Nat := 1163249344308561611731525

theorem tailTrace_6796260 : CollatzResearch.WordTrace tailWord_6796260 prefixEnd_6796260 1163249344308561611731525 := by
  unfold tailWord_6796260
  simp only [CollatzResearch.WordTrace]
  refine ⟨123939983179159101822181117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165253310905545469096241489 123939983179159101822181117)
  ·
    refine ⟨46477493692184663183317919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123939983179159101822181117 46477493692184663183317919)
    ·
      refine ⟨69716240538276994774976879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46477493692184663183317919 69716240538276994774976879)
      ·
        refine ⟨104574360807415492162465319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69716240538276994774976879 104574360807415492162465319)
        ·
          refine ⟨156861541211123238243697979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104574360807415492162465319 156861541211123238243697979)
          ·
            refine ⟨235292311816684857365546969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156861541211123238243697979 235292311816684857365546969)
            ·
              refine ⟨176469233862513643024160227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235292311816684857365546969 176469233862513643024160227)
              ·
                refine ⟨264703850793770464536240341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176469233862513643024160227 264703850793770464536240341)
                ·
                  refine ⟨6203996502978995262568133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 264703850793770464536240341 6203996502978995262568133)
                  ·
                    refine ⟨1163249344308561611731525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6203996502978995262568133 1163249344308561611731525)
                    ·
                      rfl

theorem cell23_6796260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_6796260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796260 prefixEnd_6796260 := by exact prefixLift 6796260
  have htrace : WordTrace (prefixWord ++ tailWord_6796260) baseStart_6796260 baseEnd_6796260 := by
    simpa [prefixWord, tailWord_6796260, baseEnd_6796260] using wordTrace_append hprefix tailTrace_6796260
  have hstable : (prefixWord ++ tailWord_6796260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796260).length < 2 ^ (prefixWord ++ tailWord_6796260).sum := by decide
  have hdescent : baseEnd_6796260 < baseStart_6796260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796303 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 9]
def baseStart_6796303 : Nat := 118140960795 + 6796303 * 2 ^ 59
def prefixEnd_6796303 : Nat := 4983230072969 + 3 ^ 40 * 6796303 * 2
def baseEnd_6796303 : Nat := 1163256704197942722318959

theorem tailTrace_6796303 : CollatzResearch.WordTrace tailWord_6796303 prefixEnd_6796303 1163256704197942722318959 := by
  unfold tailWord_6796303
  simp only [CollatzResearch.WordTrace]
  refine ⟨247881534697162421988177563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165254356464774947992118375 247881534697162421988177563)
  ·
    refine ⟨371822302045743632982266345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247881534697162421988177563 371822302045743632982266345)
    ·
      refine ⟨278866726534307724736699759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371822302045743632982266345 278866726534307724736699759)
      ·
        refine ⟨418300089801461587105049639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278866726534307724736699759 418300089801461587105049639)
        ·
          refine ⟨627450134702192380657574459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418300089801461587105049639 627450134702192380657574459)
          ·
            refine ⟨941175202053288570986361689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627450134702192380657574459 941175202053288570986361689)
            ·
              refine ⟨705881401539966428239771267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941175202053288570986361689 705881401539966428239771267)
              ·
                refine ⟨1058822102309949642359656901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705881401539966428239771267 1058822102309949642359656901)
                ·
                  refine ⟨198529144183115557942435669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058822102309949642359656901 198529144183115557942435669)
                  ·
                    refine ⟨1163256704197942722318959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 198529144183115557942435669 1163256704197942722318959)
                    ·
                      rfl

theorem cell23_6796303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_6796303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796303 prefixEnd_6796303 := by exact prefixLift 6796303
  have htrace : WordTrace (prefixWord ++ tailWord_6796303) baseStart_6796303 baseEnd_6796303 := by
    simpa [prefixWord, tailWord_6796303, baseEnd_6796303] using wordTrace_append hprefix tailTrace_6796303
  have hstable : (prefixWord ++ tailWord_6796303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796303).length < 2 ^ (prefixWord ++ tailWord_6796303).sum := by decide
  have hdescent : baseEnd_6796303 < baseStart_6796303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796311 : List Nat := [1, 1, 3, 5, 1, 2, 2, 3, 1, 4]
def baseStart_6796311 : Nat := 118140960795 + 6796311 * 2 ^ 59
def prefixEnd_6796311 : Nat := 4983230072969 + 3 ^ 40 * 6796311 * 2
def baseEnd_6796311 : Nat := 1163258073479688045218947

theorem tailTrace_6796311 : CollatzResearch.WordTrace tailWord_6796311 prefixEnd_6796311 1163258073479688045218947 := by
  unfold tailWord_6796311
  simp only [CollatzResearch.WordTrace]
  refine ⟨247881826481133439354468787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165254550987422292902979191 247881826481133439354468787)
  ·
    refine ⟨371822739721700159031703181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247881826481133439354468787 371822739721700159031703181)
    ·
      refine ⟨139433527395637559636888693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371822739721700159031703181 139433527395637559636888693)
      ·
        refine ⟨13071893193341021215958315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139433527395637559636888693 13071893193341021215958315)
        ·
          refine ⟨19607839790011531823937473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071893193341021215958315 19607839790011531823937473)
          ·
            refine ⟨14705879842508648867953105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19607839790011531823937473 14705879842508648867953105)
            ·
              refine ⟨11029409881881486650964829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14705879842508648867953105 11029409881881486650964829)
              ·
                refine ⟨4136028705705557494111811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11029409881881486650964829 4136028705705557494111811)
                ·
                  refine ⟨6204043058558336241167717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136028705705557494111811 6204043058558336241167717)
                  ·
                    refine ⟨1163258073479688045218947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6204043058558336241167717 1163258073479688045218947)
                    ·
                      rfl

theorem cell23_6796311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_6796311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796311 prefixEnd_6796311 := by exact prefixLift 6796311
  have htrace : WordTrace (prefixWord ++ tailWord_6796311) baseStart_6796311 baseEnd_6796311 := by
    simpa [prefixWord, tailWord_6796311, baseEnd_6796311] using wordTrace_append hprefix tailTrace_6796311
  have hstable : (prefixWord ++ tailWord_6796311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796311).length < 2 ^ (prefixWord ++ tailWord_6796311).sum := by decide
  have hdescent : baseEnd_6796311 < baseStart_6796311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796324 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 6]
def baseStart_6796324 : Nat := 118140960795 + 6796324 * 2 ^ 59
def prefixEnd_6796324 : Nat := 4983230072969 + 3 ^ 40 * 6796324 * 2
def baseEnd_6796324 : Nat := 387753432854174731643809

theorem tailTrace_6796324 : CollatzResearch.WordTrace tailWord_6796324 prefixEnd_6796324 387753432854174731643809 := by
  unfold tailWord_6796324
  simp only [CollatzResearch.WordTrace]
  refine ⟨123941150315043171287346013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165254867086724228383128017 123941150315043171287346013)
  ·
    refine ⟨46477931368141189232754755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123941150315043171287346013 46477931368141189232754755)
    ·
      refine ⟨69716897052211783849132133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46477931368141189232754755 69716897052211783849132133)
      ·
        refine ⟨13071918197289709471712275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69716897052211783849132133 13071918197289709471712275)
        ·
          refine ⟨19607877295934564207568413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071918197289709471712275 19607877295934564207568413)
          ·
            refine ⟨7352953985975461577838155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19607877295934564207568413 7352953985975461577838155)
            ·
              refine ⟨11029430978963192366757233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352953985975461577838155 11029430978963192366757233)
              ·
                refine ⟨8272073234222394275067925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11029430978963192366757233 8272073234222394275067925)
                ·
                  refine ⟨387753432854174731643809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8272073234222394275067925 387753432854174731643809)
                  ·
                    rfl

theorem cell23_6796324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_6796324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796324 prefixEnd_6796324 := by exact prefixLift 6796324
  have htrace : WordTrace (prefixWord ++ tailWord_6796324) baseStart_6796324 baseEnd_6796324 := by
    simpa [prefixWord, tailWord_6796324, baseEnd_6796324] using wordTrace_append hprefix tailTrace_6796324
  have hstable : (prefixWord ++ tailWord_6796324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796324).length < 2 ^ (prefixWord ++ tailWord_6796324).sum := by decide
  have hdescent : baseEnd_6796324 < baseStart_6796324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796327 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6796327 : Nat := 118140960795 + 6796327 * 2 ^ 59
def prefixEnd_6796327 : Nat := 4983230072969 + 3 ^ 40 * 6796327 * 2
def baseEnd_6796327 : Nat := 3489782436129536073056767

theorem tailTrace_6796327 : CollatzResearch.WordTrace tailWord_6796327 prefixEnd_6796327 3489782436129536073056767 := by
  unfold tailWord_6796327
  simp only [CollatzResearch.WordTrace]
  refine ⟨247882410049075474087051235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165254940032716982724700823 247882410049075474087051235)
  ·
    refine ⟨371823615073613211130576853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247882410049075474087051235 371823615073613211130576853)
    ·
      refine ⟨8714615978287809635872895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 371823615073613211130576853 8714615978287809635872895)
      ·
        refine ⟨13071923967431714453809343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714615978287809635872895 13071923967431714453809343)
        ·
          refine ⟨19607885951147571680714015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13071923967431714453809343 19607885951147571680714015)
          ·
            refine ⟨29411828926721357521071023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19607885951147571680714015 29411828926721357521071023)
            ·
              refine ⟨44117743390082036281606535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29411828926721357521071023 44117743390082036281606535)
              ·
                refine ⟨66176615085123054422409803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44117743390082036281606535 66176615085123054422409803)
                ·
                  refine ⟨99264922627684581633614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66176615085123054422409803 99264922627684581633614705)
                  ·
                    refine ⟨74448691970763436225211029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99264922627684581633614705 74448691970763436225211029)
                    ·
                      refine ⟨3489782436129536073056767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74448691970763436225211029 3489782436129536073056767)
                      ·
                        rfl

theorem cell23_6796327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6796327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796327 prefixEnd_6796327 := by exact prefixLift 6796327
  have htrace : WordTrace (prefixWord ++ tailWord_6796327) baseStart_6796327 baseEnd_6796327 := by
    simpa [prefixWord, tailWord_6796327, baseEnd_6796327] using wordTrace_append hprefix tailTrace_6796327
  have hstable : (prefixWord ++ tailWord_6796327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796327).length < 2 ^ (prefixWord ++ tailWord_6796327).sum := by decide
  have hdescent : baseEnd_6796327 < baseStart_6796327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796357 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_6796357 : Nat := 118140960795 + 6796357 * 2 ^ 59
def prefixEnd_6796357 : Nat := 4983230072969 + 3 ^ 40 * 6796357 * 2
def baseEnd_6796357 : Nat := 3489797840549170955681629

theorem tailTrace_6796357 : CollatzResearch.WordTrace tailWord_6796357 prefixEnd_6796357 3489797840549170955681629 := by
  unfold tailWord_6796357
  simp only [CollatzResearch.WordTrace]
  refine ⟨247883504238966789210643325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165255669492644526140428883 247883504238966789210643325)
  ·
    refine ⟨92956314089612545953991247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247883504238966789210643325 92956314089612545953991247)
    ·
      refine ⟨139434471134418818930986871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92956314089612545953991247 139434471134418818930986871)
      ·
        refine ⟨209151706701628228396480307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139434471134418818930986871 209151706701628228396480307)
        ·
          refine ⟨313727560052442342594720461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209151706701628228396480307 313727560052442342594720461)
          ·
            refine ⟨117647835019665878473020173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313727560052442342594720461 117647835019665878473020173)
            ·
              refine ⟨44117938132374704427382565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117647835019665878473020173 44117938132374704427382565)
              ·
                refine ⟨8272113399820257080134231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44117938132374704427382565 8272113399820257080134231)
                ·
                  refine ⟨12408170099730385620201347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8272113399820257080134231 12408170099730385620201347)
                  ·
                    refine ⟨18612255149595578430302021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12408170099730385620201347 18612255149595578430302021)
                    ·
                      refine ⟨3489797840549170955681629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18612255149595578430302021 3489797840549170955681629)
                      ·
                        rfl

theorem cell23_6796357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_6796357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796357 prefixEnd_6796357 := by exact prefixLift 6796357
  have htrace : WordTrace (prefixWord ++ tailWord_6796357) baseStart_6796357 baseEnd_6796357 := by
    simpa [prefixWord, tailWord_6796357, baseEnd_6796357] using wordTrace_append hprefix tailTrace_6796357
  have hstable : (prefixWord ++ tailWord_6796357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796357).length < 2 ^ (prefixWord ++ tailWord_6796357).sum := by decide
  have hdescent : baseEnd_6796357 < baseStart_6796357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796360 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_6796360 : Nat := 118140960795 + 6796360 * 2 ^ 59
def prefixEnd_6796360 : Nat := 4983230072969 + 3 ^ 40 * 6796360 * 2
def baseEnd_6796360 : Nat := 3489799380991134443944115

theorem tailTrace_6796360 : CollatzResearch.WordTrace tailWord_6796360 prefixEnd_6796360 3489799380991134443944115 := by
  unfold tailWord_6796360
  simp only [CollatzResearch.WordTrace]
  refine ⟨123941806828977960361501267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165255742438637280482001689 123941806828977960361501267)
  ·
    refine ⟨185912710243466940542251901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123941806828977960361501267 185912710243466940542251901)
    ·
      refine ⟨69717266341300102703344463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185912710243466940542251901 69717266341300102703344463)
      ·
        refine ⟨104575899511950154055016695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69717266341300102703344463 104575899511950154055016695)
        ·
          refine ⟨156863849267925231082525043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104575899511950154055016695 156863849267925231082525043)
          ·
            refine ⟨235295773901887846623787565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156863849267925231082525043 235295773901887846623787565)
            ·
              refine ⟨88235915213207942483920337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235295773901887846623787565 88235915213207942483920337)
              ·
                refine ⟨66176936409905956862940253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88235915213207942483920337 66176936409905956862940253)
                ·
                  refine ⟨24816351153714733823602595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66176936409905956862940253 24816351153714733823602595)
                  ·
                    refine ⟨37224526730572100735403893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24816351153714733823602595 37224526730572100735403893)
                    ·
                      refine ⟨3489799380991134443944115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37224526730572100735403893 3489799380991134443944115)
                      ·
                        rfl

theorem cell23_6796360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_6796360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796360 prefixEnd_6796360 := by exact prefixLift 6796360
  have htrace : WordTrace (prefixWord ++ tailWord_6796360) baseStart_6796360 baseEnd_6796360 := by
    simpa [prefixWord, tailWord_6796360, baseEnd_6796360] using wordTrace_append hprefix tailTrace_6796360
  have hstable : (prefixWord ++ tailWord_6796360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796360).length < 2 ^ (prefixWord ++ tailWord_6796360).sum := by decide
  have hdescent : baseEnd_6796360 < baseStart_6796360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796391 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_6796391 : Nat := 118140960795 + 6796391 * 2 ^ 59
def prefixEnd_6796391 : Nat := 4983230072969 + 3 ^ 40 * 6796391 * 2
def baseEnd_6796391 : Nat := 3489815298891423822656473

theorem tailTrace_6796391 : CollatzResearch.WordTrace tailWord_6796391 prefixEnd_6796391 3489815298891423822656473 := by
  unfold tailWord_6796391
  simp only [CollatzResearch.WordTrace]
  refine ⟨247884744320843613017381027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165256496213895742011587351 247884744320843613017381027)
  ·
    refine ⟨371827116481265419526071541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247884744320843613017381027 371827116481265419526071541)
    ·
      refine ⟨34858792170118633080569207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371827116481265419526071541 34858792170118633080569207)
      ·
        refine ⟨52288188255177949620853811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34858792170118633080569207 52288188255177949620853811)
        ·
          refine ⟨78432282382766924431280717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52288188255177949620853811 78432282382766924431280717)
          ·
            refine ⟨29412105893537596661730269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78432282382766924431280717 29412105893537596661730269)
            ·
              refine ⟨11029539710076598748148851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29412105893537596661730269 11029539710076598748148851)
              ·
                refine ⟨16544309565114898122223277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11029539710076598748148851 16544309565114898122223277)
                ·
                  refine ⟨6204116086918086795833729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16544309565114898122223277 6204116086918086795833729)
                  ·
                    refine ⟨4653087065188565096875297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204116086918086795833729 4653087065188565096875297)
                    ·
                      refine ⟨3489815298891423822656473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653087065188565096875297 3489815298891423822656473)
                      ·
                        rfl

theorem cell23_6796391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_6796391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796391 prefixEnd_6796391 := by exact prefixLift 6796391
  have htrace : WordTrace (prefixWord ++ tailWord_6796391) baseStart_6796391 baseEnd_6796391 := by
    simpa [prefixWord, tailWord_6796391, baseEnd_6796391] using wordTrace_append hprefix tailTrace_6796391
  have hstable : (prefixWord ++ tailWord_6796391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796391).length < 2 ^ (prefixWord ++ tailWord_6796391).sum := by decide
  have hdescent : baseEnd_6796391 < baseStart_6796391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796397 : List Nat := [1, 5, 1, 1, 2, 3, 2, 8]
def baseStart_6796397 : Nat := 118140960795 + 6796397 * 2 ^ 59
def prefixEnd_6796397 : Nat := 4983230072969 + 3 ^ 40 * 6796397 * 2
def baseEnd_6796397 : Nat := 129252532584272251821535

theorem tailTrace_6796397 : CollatzResearch.WordTrace tailWord_6796397 prefixEnd_6796397 129252532584272251821535 := by
  unfold tailWord_6796397
  simp only [CollatzResearch.WordTrace]
  refine ⟨247884963158821876042099445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165256642105881250694732963 247884963158821876042099445)
  ·
    refine ⟨23239215296139550878946823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247884963158821876042099445 23239215296139550878946823)
    ·
      refine ⟨34858822944209326318420235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23239215296139550878946823 34858822944209326318420235)
      ·
        refine ⟨52288234416313989477630353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34858822944209326318420235 52288234416313989477630353)
        ·
          refine ⟨39216175812235492108222765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52288234416313989477630353 39216175812235492108222765)
          ·
            refine ⟨14706065929588309540583537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39216175812235492108222765 14706065929588309540583537)
            ·
              refine ⟨11029549447191232155437653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14706065929588309540583537 11029549447191232155437653)
              ·
                refine ⟨129252532584272251821535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11029549447191232155437653 129252532584272251821535)
                ·
                  rfl

theorem cell23_6796397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 8].length) (baseStart_6796397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796397 prefixEnd_6796397 := by exact prefixLift 6796397
  have htrace : WordTrace (prefixWord ++ tailWord_6796397) baseStart_6796397 baseEnd_6796397 := by
    simpa [prefixWord, tailWord_6796397, baseEnd_6796397] using wordTrace_append hprefix tailTrace_6796397
  have hstable : (prefixWord ++ tailWord_6796397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796397).length < 2 ^ (prefixWord ++ tailWord_6796397).sum := by decide
  have hdescent : baseEnd_6796397 < baseStart_6796397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796400 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_6796400 : Nat := 118140960795 + 6796400 * 2 ^ 59
def prefixEnd_6796400 : Nat := 4983230072969 + 3 ^ 40 * 6796400 * 2
def baseEnd_6796400 : Nat := 3489819920217314287443931

theorem tailTrace_6796400 : CollatzResearch.WordTrace tailWord_6796400 prefixEnd_6796400 3489819920217314287443931 := by
  unfold tailWord_6796400
  simp only [CollatzResearch.WordTrace]
  refine ⟨123942536288905503777229327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165256715051874005036305769 123942536288905503777229327)
  ·
    refine ⟨185913804433358255665843991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123942536288905503777229327 185913804433358255665843991)
    ·
      refine ⟨278870706650037383498765987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185913804433358255665843991 278870706650037383498765987)
      ·
        refine ⟨418306059975056075248148981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278870706650037383498765987 418306059975056075248148981)
        ·
          refine ⟨39216193122661507054513967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 418306059975056075248148981 39216193122661507054513967)
          ·
            refine ⟨58824289683992260581770951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39216193122661507054513967 58824289683992260581770951)
            ·
              refine ⟨88236434525988390872656427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58824289683992260581770951 88236434525988390872656427)
              ·
                refine ⟨132354651788982586308984641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88236434525988390872656427 132354651788982586308984641)
                ·
                  refine ⟨99265988841736939731738481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132354651788982586308984641 99265988841736939731738481)
                  ·
                    refine ⟨74449491631302704798803861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99265988841736939731738481 74449491631302704798803861)
                    ·
                      refine ⟨3489819920217314287443931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74449491631302704798803861 3489819920217314287443931)
                      ·
                        rfl

theorem cell23_6796400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_6796400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796400 prefixEnd_6796400 := by exact prefixLift 6796400
  have htrace : WordTrace (prefixWord ++ tailWord_6796400) baseStart_6796400 baseEnd_6796400 := by
    simpa [prefixWord, tailWord_6796400, baseEnd_6796400] using wordTrace_append hprefix tailTrace_6796400
  have hstable : (prefixWord ++ tailWord_6796400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796400).length < 2 ^ (prefixWord ++ tailWord_6796400).sum := by decide
  have hdescent : baseEnd_6796400 < baseStart_6796400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796407 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_6796407 : Nat := 118140960795 + 6796407 * 2 ^ 59
def prefixEnd_6796407 : Nat := 4983230072969 + 3 ^ 40 * 6796407 * 2
def baseEnd_6796407 : Nat := 3489823514581895760056399

theorem tailTrace_6796407 : CollatzResearch.WordTrace tailWord_6796407 prefixEnd_6796407 3489823514581895760056399 := by
  unfold tailWord_6796407
  simp only [CollatzResearch.WordTrace]
  refine ⟨247885327888785647749963475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165256885259190431833308983 247885327888785647749963475)
  ·
    refine ⟨371827991833178471624945213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247885327888785647749963475 371827991833178471624945213)
    ·
      refine ⟨139435496937441926859354455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371827991833178471624945213 139435496937441926859354455)
      ·
        refine ⟨209153245406162890289031683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139435496937441926859354455 209153245406162890289031683)
        ·
          refine ⟨313729868109244335433547525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209153245406162890289031683 313729868109244335433547525)
          ·
            refine ⟨58824350270483312893790161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313729868109244335433547525 58824350270483312893790161)
            ·
              refine ⟨44118262702862484670342621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58824350270483312893790161 44118262702862484670342621)
              ·
                refine ⟨16544348513573431751378483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44118262702862484670342621 16544348513573431751378483)
                ·
                  refine ⟨24816522770360147627067725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16544348513573431751378483 24816522770360147627067725)
                  ·
                    refine ⟨9306196038885055360150397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24816522770360147627067725 9306196038885055360150397)
                    ·
                      refine ⟨3489823514581895760056399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9306196038885055360150397 3489823514581895760056399)
                      ·
                        rfl

theorem cell23_6796407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_6796407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796407 prefixEnd_6796407 := by exact prefixLift 6796407
  have htrace : WordTrace (prefixWord ++ tailWord_6796407) baseStart_6796407 baseEnd_6796407 := by
    simpa [prefixWord, tailWord_6796407, baseEnd_6796407] using wordTrace_append hprefix tailTrace_6796407
  have hstable : (prefixWord ++ tailWord_6796407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796407).length < 2 ^ (prefixWord ++ tailWord_6796407).sum := by decide
  have hdescent : baseEnd_6796407 < baseStart_6796407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796442 : List Nat := [3, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6796442 : Nat := 118140960795 + 6796442 * 2 ^ 59
def prefixEnd_6796442 : Nat := 4983230072969 + 3 ^ 40 * 6796442 * 2
def baseEnd_6796442 : Nat := 3489841486404803123118739

theorem tailTrace_6796442 : CollatzResearch.WordTrace tailWord_6796442 prefixEnd_6796442 3489841486404803123118739 := by
  unfold tailWord_6796442
  simp only [CollatzResearch.WordTrace]
  refine ⟨61971651110914712181871895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165257736295772565818325053 61971651110914712181871895)
  ·
    refine ⟨92957476666372068272807843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61971651110914712181871895 92957476666372068272807843)
    ·
      refine ⟨139436214999558102409211765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92957476666372068272807843 139436214999558102409211765)
      ·
        refine ⟨13072145156208572100863603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139436214999558102409211765 13072145156208572100863603)
        ·
          refine ⟨19608217734312858151295405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072145156208572100863603 19608217734312858151295405)
          ·
            refine ⟨7353081650367321806735777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19608217734312858151295405 7353081650367321806735777)
            ·
              refine ⟨5514811237775491355051833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7353081650367321806735777 5514811237775491355051833)
              ·
                refine ⟨4136108428331618516288875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5514811237775491355051833 4136108428331618516288875)
                ·
                  refine ⟨6204162642497427774433313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136108428331618516288875 6204162642497427774433313)
                  ·
                    refine ⟨4653121981873070830824985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204162642497427774433313 4653121981873070830824985)
                    ·
                      refine ⟨3489841486404803123118739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653121981873070830824985 3489841486404803123118739)
                      ·
                        rfl

theorem cell23_6796442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6796442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796442 prefixEnd_6796442 := by exact prefixLift 6796442
  have htrace : WordTrace (prefixWord ++ tailWord_6796442) baseStart_6796442 baseEnd_6796442 := by
    simpa [prefixWord, tailWord_6796442, baseEnd_6796442] using wordTrace_append hprefix tailTrace_6796442
  have hstable : (prefixWord ++ tailWord_6796442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796442).length < 2 ^ (prefixWord ++ tailWord_6796442).sum := by decide
  have hdescent : baseEnd_6796442 < baseStart_6796442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796458 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6796458 : Nat := 118140960795 + 6796458 * 2 ^ 59
def prefixEnd_6796458 : Nat := 4983230072969 + 3 ^ 40 * 6796458 * 2
def baseEnd_6796458 : Nat := 3489849702095275060518665

theorem tailTrace_6796458 : CollatzResearch.WordTrace tailWord_6796458 prefixEnd_6796458 3489849702095275060518665 := by
  unfold tailWord_6796458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61971797002900220865017507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165258125341067255640046685 61971797002900220865017507)
  ·
    refine ⟨92957695504350331297526261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61971797002900220865017507 92957695504350331297526261)
    ·
      refine ⟨8714783953532843559143087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92957695504350331297526261 8714783953532843559143087)
      ·
        refine ⟨13072175930299265338714631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8714783953532843559143087 13072175930299265338714631)
        ·
          refine ⟨19608263895448898008071947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072175930299265338714631 19608263895448898008071947)
          ·
            refine ⟨29412395843173347012107921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19608263895448898008071947 29412395843173347012107921)
            ·
              refine ⟨22059296882380010259080941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29412395843173347012107921 22059296882380010259080941)
              ·
                refine ⟨8272236330892503847155353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22059296882380010259080941 8272236330892503847155353)
                ·
                  refine ⟨6204177248169377885366515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8272236330892503847155353 6204177248169377885366515)
                  ·
                    refine ⟨9306265872254066828049773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6204177248169377885366515 9306265872254066828049773)
                    ·
                      refine ⟨3489849702095275060518665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9306265872254066828049773 3489849702095275060518665)
                      ·
                        rfl

theorem cell23_6796458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6796458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796458 prefixEnd_6796458 := by exact prefixLift 6796458
  have htrace : WordTrace (prefixWord ++ tailWord_6796458) baseStart_6796458 baseEnd_6796458 := by
    simpa [prefixWord, tailWord_6796458, baseEnd_6796458] using wordTrace_append hprefix tailTrace_6796458
  have hstable : (prefixWord ++ tailWord_6796458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796458).length < 2 ^ (prefixWord ++ tailWord_6796458).sum := by decide
  have hdescent : baseEnd_6796458 < baseStart_6796458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796504 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 7]
def baseStart_6796504 : Nat := 118140960795 + 6796504 * 2 ^ 59
def prefixEnd_6796504 : Nat := 4983230072969 + 3 ^ 40 * 6796504 * 2
def baseEnd_6796504 : Nat := 387763702467264653393717

theorem tailTrace_6796504 : CollatzResearch.WordTrace tailWord_6796504 prefixEnd_6796504 387763702467264653393717 := by
  unfold tailWord_6796504
  simp only [CollatzResearch.WordTrace]
  refine ⟨123944432884717116658122283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165259243846289488877496377 123944432884717116658122283)
  ·
    refine ⟨185916649327075674987183425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123944432884717116658122283 185916649327075674987183425)
    ·
      refine ⟨139437486995306756240387569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185916649327075674987183425 139437486995306756240387569)
      ·
        refine ⟨104578115246480067180290677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139437486995306756240387569 104578115246480067180290677)
        ·
          refine ⟨9804198304357506298152251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104578115246480067180290677 9804198304357506298152251)
          ·
            refine ⟨14706297456536259447228377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9804198304357506298152251 14706297456536259447228377)
            ·
              refine ⟨11029723092402194585421283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14706297456536259447228377 11029723092402194585421283)
              ·
                refine ⟨16544584638603291878131925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11029723092402194585421283 16544584638603291878131925)
                ·
                  refine ⟨387763702467264653393717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16544584638603291878131925 387763702467264653393717)
                  ·
                    rfl

theorem cell23_6796504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 7].length) (baseStart_6796504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796504 prefixEnd_6796504 := by exact prefixLift 6796504
  have htrace : WordTrace (prefixWord ++ tailWord_6796504) baseStart_6796504 baseEnd_6796504 := by
    simpa [prefixWord, tailWord_6796504, baseEnd_6796504] using wordTrace_append hprefix tailTrace_6796504
  have hstable : (prefixWord ++ tailWord_6796504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796504).length < 2 ^ (prefixWord ++ tailWord_6796504).sum := by decide
  have hdescent : baseEnd_6796504 < baseStart_6796504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796534 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_6796534 : Nat := 118140960795 + 6796534 * 2 ^ 59
def prefixEnd_6796534 : Nat := 4983230072969 + 3 ^ 40 * 6796534 * 2
def baseEnd_6796534 : Nat := 1163296242208338921056105

theorem tailTrace_6796534 : CollatzResearch.WordTrace tailWord_6796534 prefixEnd_6796534 1163296242208338921056105 := by
  unfold tailWord_6796534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15493122497457846777489791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165259973306217032293224437 15493122497457846777489791)
  ·
    refine ⟨23239683746186770166234687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15493122497457846777489791 23239683746186770166234687)
    ·
      refine ⟨34859525619280155249352031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23239683746186770166234687 34859525619280155249352031)
      ·
        refine ⟨52289288428920232874028047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34859525619280155249352031 52289288428920232874028047)
        ·
          refine ⟨78433932643380349311042071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52289288428920232874028047 78433932643380349311042071)
          ·
            refine ⟨117650898965070523966563107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78433932643380349311042071 117650898965070523966563107)
            ·
              refine ⟨176476348447605785949844661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117650898965070523966563107 176476348447605785949844661)
              ·
                refine ⟨16544657666963042432797937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176476348447605785949844661 16544657666963042432797937)
                ·
                  refine ⟨12408493250222281824598453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16544657666963042432797937 12408493250222281824598453)
                  ·
                    refine ⟨1163296242208338921056105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12408493250222281824598453 1163296242208338921056105)
                    ·
                      rfl

theorem cell23_6796534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_6796534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796534 prefixEnd_6796534 := by exact prefixLift 6796534
  have htrace : WordTrace (prefixWord ++ tailWord_6796534) baseStart_6796534 baseEnd_6796534 := by
    simpa [prefixWord, tailWord_6796534, baseEnd_6796534] using wordTrace_append hprefix tailTrace_6796534
  have hstable : (prefixWord ++ tailWord_6796534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796534).length < 2 ^ (prefixWord ++ tailWord_6796534).sum := by decide
  have hdescent : baseEnd_6796534 < baseStart_6796534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796537 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_6796537 : Nat := 118140960795 + 6796537 * 2 ^ 59
def prefixEnd_6796537 : Nat := 4983230072969 + 3 ^ 40 * 6796537 * 2
def baseEnd_6796537 : Nat := 3489890267066980251430801

theorem tailTrace_6796537 : CollatzResearch.WordTrace tailWord_6796537 prefixEnd_6796537 3489890267066980251430801 := by
  unfold tailWord_6796537
  simp only [CollatzResearch.WordTrace]
  refine ⟨247890069378314679952195865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165260046252209786634797243 247890069378314679952195865)
  ·
    refine ⟨185917552033736009964146899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247890069378314679952195865 185917552033736009964146899)
    ·
      refine ⟨278876328050604014946220349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185917552033736009964146899 278876328050604014946220349)
      ·
        refine ⟨104578623018976505604832631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278876328050604014946220349 104578623018976505604832631)
        ·
          refine ⟨156867934528464758407248947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104578623018976505604832631 156867934528464758407248947)
          ·
            refine ⟨235301901792697137610873421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156867934528464758407248947 235301901792697137610873421)
            ·
              refine ⟨88238213172261426604077533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235301901792697137610873421 88238213172261426604077533)
              ·
                refine ⟨33089329939598034976529075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88238213172261426604077533 33089329939598034976529075)
                ·
                  refine ⟨49633994909397052464793613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33089329939598034976529075 49633994909397052464793613)
                  ·
                    refine ⟨18612748091023894674297605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49633994909397052464793613 18612748091023894674297605)
                    ·
                      refine ⟨3489890267066980251430801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18612748091023894674297605 3489890267066980251430801)
                      ·
                        rfl

theorem cell23_6796537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_6796537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796537 prefixEnd_6796537 := by exact prefixLift 6796537
  have htrace : WordTrace (prefixWord ++ tailWord_6796537) baseStart_6796537 baseEnd_6796537 := by
    simpa [prefixWord, tailWord_6796537, baseEnd_6796537] using wordTrace_append hprefix tailTrace_6796537
  have hstable : (prefixWord ++ tailWord_6796537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796537).length < 2 ^ (prefixWord ++ tailWord_6796537).sum := by decide
  have hdescent : baseEnd_6796537 < baseStart_6796537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796615 : List Nat := [1, 1, 4, 1, 2, 5, 2, 2, 1, 4]
def baseStart_6796615 : Nat := 118140960795 + 6796615 * 2 ^ 59
def prefixEnd_6796615 : Nat := 4983230072969 + 3 ^ 40 * 6796615 * 2
def baseEnd_6796615 : Nat := 1163310106186010315418481

theorem tailTrace_6796615 : CollatzResearch.WordTrace tailWord_6796615 prefixEnd_6796615 1163310106186010315418481 := by
  unfold tailWord_6796615
  simp only [CollatzResearch.WordTrace]
  refine ⟨247892914272032099273535299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165261942848021399515690199 247892914272032099273535299)
  ·
    refine ⟨371839371408048148910302949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247892914272032099273535299 371839371408048148910302949)
    ·
      refine ⟨69719882139009027920681803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371839371408048148910302949 69719882139009027920681803)
      ·
        refine ⟨104579823208513541881022705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69719882139009027920681803 104579823208513541881022705)
        ·
          refine ⟨78434867406385156410767029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104579823208513541881022705 78434867406385156410767029)
          ·
            refine ⟨7353268819348608413509409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78434867406385156410767029 7353268819348608413509409)
            ·
              refine ⟨5514951614511456310132057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7353268819348608413509409 5514951614511456310132057)
              ·
                refine ⟨4136213710883592232599043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5514951614511456310132057 4136213710883592232599043)
                ·
                  refine ⟨6204320566325388348898565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136213710883592232599043 6204320566325388348898565)
                  ·
                    refine ⟨1163310106186010315418481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6204320566325388348898565 1163310106186010315418481)
                    ·
                      rfl

theorem cell23_6796615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_6796615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796615 prefixEnd_6796615 := by exact prefixLift 6796615
  have htrace : WordTrace (prefixWord ++ tailWord_6796615) baseStart_6796615 baseEnd_6796615 := by
    simpa [prefixWord, tailWord_6796615, baseEnd_6796615] using wordTrace_append hprefix tailTrace_6796615
  have hstable : (prefixWord ++ tailWord_6796615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796615).length < 2 ^ (prefixWord ++ tailWord_6796615).sum := by decide
  have hdescent : baseEnd_6796615 < baseStart_6796615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796648 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6796648 : Nat := 118140960795 + 6796648 * 2 ^ 59
def prefixEnd_6796648 : Nat := 4983230072969 + 3 ^ 40 * 6796648 * 2
def baseEnd_6796648 : Nat := 3489947263419629317142791

theorem tailTrace_6796648 : CollatzResearch.WordTrace tailWord_6796648 prefixEnd_6796648 3489947263419629317142791 := by
  unfold tailWord_6796648
  simp only [CollatzResearch.WordTrace]
  refine ⟨123947058940456272954743299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165262745253941697272991065 123947058940456272954743299)
  ·
    refine ⟨185920588410684409432114949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123947058940456272954743299 185920588410684409432114949)
    ·
      refine ⟨34860110327003326768521553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185920588410684409432114949 34860110327003326768521553)
      ·
        refine ⟨26145082745252495076391165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34860110327003326768521553 26145082745252495076391165)
        ·
          refine ⟨9804406029469685653646687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26145082745252495076391165 9804406029469685653646687)
          ·
            refine ⟨14706609044204528480470031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9804406029469685653646687 14706609044204528480470031)
            ·
              refine ⟨22059913566306792720705047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14706609044204528480470031 22059913566306792720705047)
              ·
                refine ⟨33089870349460189081057571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22059913566306792720705047 33089870349460189081057571)
                ·
                  refine ⟨49634805524190283621586357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33089870349460189081057571 49634805524190283621586357)
                  ·
                    refine ⟨4653263017892839089523721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49634805524190283621586357 4653263017892839089523721)
                    ·
                      refine ⟨3489947263419629317142791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653263017892839089523721 3489947263419629317142791)
                      ·
                        rfl

theorem cell23_6796648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6796648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796648 prefixEnd_6796648 := by exact prefixLift 6796648
  have htrace : WordTrace (prefixWord ++ tailWord_6796648) baseStart_6796648 baseEnd_6796648 := by
    simpa [prefixWord, tailWord_6796648, baseEnd_6796648] using wordTrace_append hprefix tailTrace_6796648
  have hstable : (prefixWord ++ tailWord_6796648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796648).length < 2 ^ (prefixWord ++ tailWord_6796648).sum := by decide
  have hdescent : baseEnd_6796648 < baseStart_6796648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796667 : List Nat := [1, 1, 1, 1, 1, 6, 12]
def baseStart_6796667 : Nat := 118140960795 + 6796667 * 2 ^ 59
def prefixEnd_6796667 : Nat := 4983230072969 + 3 ^ 40 * 6796667 * 2
def baseEnd_6796667 : Nat := 43085889130272404232163

theorem tailTrace_6796667 : CollatzResearch.WordTrace tailWord_6796667 prefixEnd_6796667 43085889130272404232163 := by
  unfold tailWord_6796667
  simp only [CollatzResearch.WordTrace]
  refine ⟨247894810867843712154428255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165263207245229141436285503 247894810867843712154428255)
  ·
    refine ⟨371842216301765568231642383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247894810867843712154428255 371842216301765568231642383)
    ·
      refine ⟨557763324452648352347463575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371842216301765568231642383 557763324452648352347463575)
      ·
        refine ⟨836644986678972528521195363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557763324452648352347463575 836644986678972528521195363)
        ·
          refine ⟨1254967480018458792781793045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836644986678972528521195363 1254967480018458792781793045)
          ·
            refine ⟨58826600625865255911646549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1254967480018458792781793045 58826600625865255911646549)
            ·
              refine ⟨43085889130272404232163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 58826600625865255911646549 43085889130272404232163)
              ·
                rfl

theorem cell23_6796667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 12].length) (baseStart_6796667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796667 prefixEnd_6796667 := by exact prefixLift 6796667
  have htrace : WordTrace (prefixWord ++ tailWord_6796667) baseStart_6796667 baseEnd_6796667 := by
    simpa [prefixWord, tailWord_6796667, baseEnd_6796667] using wordTrace_append hprefix tailTrace_6796667
  have hstable : (prefixWord ++ tailWord_6796667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796667).length < 2 ^ (prefixWord ++ tailWord_6796667).sum := by decide
  have hdescent : baseEnd_6796667 < baseStart_6796667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796681 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 5]
def baseStart_6796681 : Nat := 118140960795 + 6796681 * 2 ^ 59
def prefixEnd_6796681 : Nat := 4983230072969 + 3 ^ 40 * 6796681 * 2
def baseEnd_6796681 : Nat := 3489964208281227688030139

theorem tailTrace_6796681 : CollatzResearch.WordTrace tailWord_6796681 prefixEnd_6796681 3489964208281227688030139 := by
  unfold tailWord_6796681
  simp only [CollatzResearch.WordTrace]
  refine ⟨247895321489792992545437897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165263547659861995030291931 247895321489792992545437897)
  ·
    refine ⟨185921491117344744409078423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247895321489792992545437897 185921491117344744409078423)
    ·
      refine ⟨278882236676017116613617635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185921491117344744409078423 278882236676017116613617635)
      ·
        refine ⟨418323355014025674920426453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278882236676017116613617635 418323355014025674920426453)
        ·
          refine ⟨9804453633141226755947495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 418323355014025674920426453 9804453633141226755947495)
          ·
            refine ⟨14706680449711840133921243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9804453633141226755947495 14706680449711840133921243)
            ·
              refine ⟨22060020674567760200881865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14706680449711840133921243 22060020674567760200881865)
              ·
                refine ⟨16545015505925820150661399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22060020674567760200881865 16545015505925820150661399)
                ·
                  refine ⟨24817523258888730225992099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16545015505925820150661399 24817523258888730225992099)
                  ·
                    refine ⟨37226284888333095338988149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24817523258888730225992099 37226284888333095338988149)
                    ·
                      refine ⟨3489964208281227688030139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37226284888333095338988149 3489964208281227688030139)
                      ·
                        rfl

theorem cell23_6796681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_6796681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796681 prefixEnd_6796681 := by exact prefixLift 6796681
  have htrace : WordTrace (prefixWord ++ tailWord_6796681) baseStart_6796681 baseEnd_6796681 := by
    simpa [prefixWord, tailWord_6796681, baseEnd_6796681] using wordTrace_append hprefix tailTrace_6796681
  have hstable : (prefixWord ++ tailWord_6796681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796681).length < 2 ^ (prefixWord ++ tailWord_6796681).sum := by decide
  have hdescent : baseEnd_6796681 < baseStart_6796681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796698 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_6796698 : Nat := 118140960795 + 6796698 * 2 ^ 59
def prefixEnd_6796698 : Nat := 4983230072969 + 3 ^ 40 * 6796698 * 2
def baseEnd_6796698 : Nat := 3489972937452354121517561

theorem tailTrace_6796698 : CollatzResearch.WordTrace tailWord_6796698 prefixEnd_6796698 3489972937452354121517561 := by
  unfold tailWord_6796698
  simp only [CollatzResearch.WordTrace]
  refine ⟨61973985382682851112201687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165263961020487602965871165 61973985382682851112201687)
  ·
    refine ⟨92960978074024276668302531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61973985382682851112201687 92960978074024276668302531)
    ·
      refine ⟨139441467111036415002453797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92960978074024276668302531 139441467111036415002453797)
      ·
        refine ⟨26145275083319327812960087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139441467111036415002453797 26145275083319327812960087)
        ·
          refine ⟨39217912624978991719440131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26145275083319327812960087 39217912624978991719440131)
          ·
            refine ⟨58826868937468487579160197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39217912624978991719440131 58826868937468487579160197)
            ·
              refine ⟨11030037925775341421092537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58826868937468487579160197 11030037925775341421092537)
              ·
                refine ⟨8272528444331506065819403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11030037925775341421092537 8272528444331506065819403)
                ·
                  refine ⟨12408792666497259098729105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8272528444331506065819403 12408792666497259098729105)
                  ·
                    refine ⟨9306594499872944324046829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12408792666497259098729105 9306594499872944324046829)
                    ·
                      refine ⟨3489972937452354121517561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9306594499872944324046829 3489972937452354121517561)
                      ·
                        rfl

theorem cell23_6796698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_6796698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796698 prefixEnd_6796698 := by exact prefixLift 6796698
  have htrace : WordTrace (prefixWord ++ tailWord_6796698) baseStart_6796698 baseEnd_6796698 := by
    simpa [prefixWord, tailWord_6796698, baseEnd_6796698] using wordTrace_append hprefix tailTrace_6796698
  have hstable : (prefixWord ++ tailWord_6796698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796698).length < 2 ^ (prefixWord ++ tailWord_6796698).sum := by decide
  have hdescent : baseEnd_6796698 < baseStart_6796698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796701 : List Nat := [1, 4, 2, 1, 3, 1, 4, 7]
def baseStart_6796701 : Nat := 118140960795 + 6796701 * 2 ^ 59
def prefixEnd_6796701 : Nat := 4983230072969 + 3 ^ 40 * 6796701 * 2
def baseEnd_6796701 : Nat := 129258313996085837399261

theorem tailTrace_6796701 : CollatzResearch.WordTrace tailWord_6796701 prefixEnd_6796701 129258313996085837399261 := by
  unfold tailWord_6796701
  simp only [CollatzResearch.WordTrace]
  refine ⟨247896050949720535961165957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165264033966480357307443971 247896050949720535961165957)
  ·
    refine ⟨46480509553072600492718617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247896050949720535961165957 46480509553072600492718617)
    ·
      refine ⟨34860382164804450369538963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46480509553072600492718617 34860382164804450369538963)
      ·
        refine ⟨52290573247206675554308445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34860382164804450369538963 52290573247206675554308445)
        ·
          refine ⟨19608964967702503332865667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52290573247206675554308445 19608964967702503332865667)
          ·
            refine ⟨29413447451553754999298501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19608964967702503332865667 29413447451553754999298501)
            ·
              refine ⟨5515021397166329062368469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29413447451553754999298501 5515021397166329062368469)
              ·
                refine ⟨129258313996085837399261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5515021397166329062368469 129258313996085837399261)
                ·
                  rfl

theorem cell23_6796701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 7].length) (baseStart_6796701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796701 prefixEnd_6796701 := by exact prefixLift 6796701
  have htrace : WordTrace (prefixWord ++ tailWord_6796701) baseStart_6796701 baseEnd_6796701 := by
    simpa [prefixWord, tailWord_6796701, baseEnd_6796701] using wordTrace_append hprefix tailTrace_6796701
  have hstable : (prefixWord ++ tailWord_6796701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796701).length < 2 ^ (prefixWord ++ tailWord_6796701).sum := by decide
  have hdescent : baseEnd_6796701 < baseStart_6796701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796711 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_6796711 : Nat := 118140960795 + 6796711 * 2 ^ 59
def prefixEnd_6796711 : Nat := 4983230072969 + 3 ^ 40 * 6796711 * 2
def baseEnd_6796711 : Nat := 3489979612700862570655001

theorem tailTrace_6796711 : CollatzResearch.WordTrace tailWord_6796711 prefixEnd_6796711 3489979612700862570655001 := by
  unfold tailWord_6796711
  simp only [CollatzResearch.WordTrace]
  refine ⟨247896415679684307669029987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165264277119789538446019991 247896415679684307669029987)
  ·
    refine ⟨371844623519526461503544981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247896415679684307669029987 371844623519526461503544981)
    ·
      refine ⟨17430216727477802882978671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 371844623519526461503544981 17430216727477802882978671)
      ·
        refine ⟨26145325091216704324468007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17430216727477802882978671 26145325091216704324468007)
        ·
          refine ⟨39217987636825056486702011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26145325091216704324468007 39217987636825056486702011)
          ·
            refine ⟨58826981455237584730053017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39217987636825056486702011 58826981455237584730053017)
            ·
              refine ⟨44120236091428188547539763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58826981455237584730053017 44120236091428188547539763)
              ·
                refine ⟨66180354137142282821309645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44120236091428188547539763 66180354137142282821309645)
                ·
                  refine ⟨24817632801428356057991117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66180354137142282821309645 24817632801428356057991117)
                  ·
                    refine ⟨9306612300535633521746669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24817632801428356057991117 9306612300535633521746669)
                    ·
                      refine ⟨3489979612700862570655001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9306612300535633521746669 3489979612700862570655001)
                      ·
                        rfl

theorem cell23_6796711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_6796711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796711 prefixEnd_6796711 := by exact prefixLift 6796711
  have htrace : WordTrace (prefixWord ++ tailWord_6796711) baseStart_6796711 baseEnd_6796711 := by
    simpa [prefixWord, tailWord_6796711, baseEnd_6796711] using wordTrace_append hprefix tailTrace_6796711
  have hstable : (prefixWord ++ tailWord_6796711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796711).length < 2 ^ (prefixWord ++ tailWord_6796711).sum := by decide
  have hdescent : baseEnd_6796711 < baseStart_6796711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796729 : List Nat := [1, 2, 1, 4, 4, 1, 3, 2, 1, 2, 2]
def baseStart_6796729 : Nat := 118140960795 + 6796729 * 2 ^ 59
def prefixEnd_6796729 : Nat := 4983230072969 + 3 ^ 40 * 6796729 * 2
def baseEnd_6796729 : Nat := 3489988855352643500229919

theorem tailTrace_6796729 : CollatzResearch.WordTrace tailWord_6796729 prefixEnd_6796729 3489988855352643500229919 := by
  unfold tailWord_6796729
  simp only [CollatzResearch.WordTrace]
  refine ⟨247897072193619096743185241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165264714795746064495456827 247897072193619096743185241)
  ·
    refine ⟨185922804145214322557388931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247897072193619096743185241 185922804145214322557388931)
    ·
      refine ⟨278884206217821483836083397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185922804145214322557388931 278884206217821483836083397)
      ·
        refine ⟨52290788665841528219265637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278884206217821483836083397 52290788665841528219265637)
        ·
          refine ⟨9804522874845286541112307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52290788665841528219265637 9804522874845286541112307)
          ·
            refine ⟨14706784312267929811668461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9804522874845286541112307 14706784312267929811668461)
            ·
              refine ⟨5515044117100473679375673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14706784312267929811668461 5515044117100473679375673)
              ·
                refine ⟨4136283087825355259531755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5515044117100473679375673 4136283087825355259531755)
                ·
                  refine ⟨6204424631738032889297633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136283087825355259531755 6204424631738032889297633)
                  ·
                    refine ⟨4653318473803524666973225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204424631738032889297633 4653318473803524666973225)
                    ·
                      refine ⟨3489988855352643500229919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653318473803524666973225 3489988855352643500229919)
                      ·
                        rfl

theorem cell23_6796729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_6796729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796729 prefixEnd_6796729 := by exact prefixLift 6796729
  have htrace : WordTrace (prefixWord ++ tailWord_6796729) baseStart_6796729 baseEnd_6796729 := by
    simpa [prefixWord, tailWord_6796729, baseEnd_6796729] using wordTrace_append hprefix tailTrace_6796729
  have hstable : (prefixWord ++ tailWord_6796729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796729).length < 2 ^ (prefixWord ++ tailWord_6796729).sum := by decide
  have hdescent : baseEnd_6796729 < baseStart_6796729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796744 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 1, 8]
def baseStart_6796744 : Nat := 118140960795 + 6796744 * 2 ^ 59
def prefixEnd_6796744 : Nat := 4983230072969 + 3 ^ 40 * 6796744 * 2
def baseEnd_6796744 : Nat := 1163332185854153647180783

theorem tailTrace_6796744 : CollatzResearch.WordTrace tailWord_6796744 prefixEnd_6796744 1163332185854153647180783 := by
  unfold tailWord_6796744
  simp only [CollatzResearch.WordTrace]
  refine ⟨123948809644282377152490643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165265079525709836203320857 123948809644282377152490643)
  ·
    refine ⟨185923214466423565728735965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123948809644282377152490643 185923214466423565728735965)
    ·
      refine ⟨69721205424908837148275987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185923214466423565728735965 69721205424908837148275987)
      ·
        refine ⟨104581808137363255722413981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69721205424908837148275987 104581808137363255722413981)
        ·
          refine ⟨39218178051511220895905243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104581808137363255722413981 39218178051511220895905243)
          ·
            refine ⟨58827267077266831343857865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39218178051511220895905243 58827267077266831343857865)
            ·
              refine ⟨44120450307950123507893399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58827267077266831343857865 44120450307950123507893399)
              ·
                refine ⟨66180675461925185261840099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44120450307950123507893399 66180675461925185261840099)
                ·
                  refine ⟨99271013192887777892760149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66180675461925185261840099 99271013192887777892760149)
                  ·
                    refine ⟨1163332185854153647180783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99271013192887777892760149 1163332185854153647180783)
                    ·
                      rfl

theorem cell23_6796744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_6796744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796744 prefixEnd_6796744 := by exact prefixLift 6796744
  have htrace : WordTrace (prefixWord ++ tailWord_6796744) baseStart_6796744 baseEnd_6796744 := by
    simpa [prefixWord, tailWord_6796744, baseEnd_6796744] using wordTrace_append hprefix tailTrace_6796744
  have hstable : (prefixWord ++ tailWord_6796744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796744).length < 2 ^ (prefixWord ++ tailWord_6796744).sum := by decide
  have hdescent : baseEnd_6796744 < baseStart_6796744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796768 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 4, 2, 2]
def baseStart_6796768 : Nat := 118140960795 + 6796768 * 2 ^ 59
def prefixEnd_6796768 : Nat := 4983230072969 + 3 ^ 40 * 6796768 * 2
def baseEnd_6796768 : Nat := 3490008881098168847642239

theorem tailTrace_6796768 : CollatzResearch.WordTrace tailWord_6796768 prefixEnd_6796768 3490008881098168847642239 := by
  unfold tailWord_6796768
  simp only [CollatzResearch.WordTrace]
  refine ⟨123949247320238903201927479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165265663093651870935903305 123949247320238903201927479)
  ·
    refine ⟨185923870980358354802891219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123949247320238903201927479 185923870980358354802891219)
    ·
      refine ⟨278885806470537532204336829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185923870980358354802891219 278885806470537532204336829)
      ·
        refine ⟨104582177426451574576626311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278885806470537532204336829 104582177426451574576626311)
        ·
          refine ⟨156873266139677361864939467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104582177426451574576626311 156873266139677361864939467)
          ·
            refine ⟨235309899209516042797409201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156873266139677361864939467 235309899209516042797409201)
            ·
              refine ⟨176482424407137032098056901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235309899209516042797409201 176482424407137032098056901)
              ·
                refine ⟨33090454576338193518385669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176482424407137032098056901 33090454576338193518385669)
                ·
                  refine ⟨6204460233063411284697313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33090454576338193518385669 6204460233063411284697313)
                  ·
                    refine ⟨4653345174797558463522985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204460233063411284697313 4653345174797558463522985)
                    ·
                      refine ⟨3490008881098168847642239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653345174797558463522985 3490008881098168847642239)
                      ·
                        rfl

theorem cell23_6796768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_6796768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796768 prefixEnd_6796768 := by exact prefixLift 6796768
  have htrace : WordTrace (prefixWord ++ tailWord_6796768) baseStart_6796768 baseEnd_6796768 := by
    simpa [prefixWord, tailWord_6796768, baseEnd_6796768] using wordTrace_append hprefix tailTrace_6796768
  have hstable : (prefixWord ++ tailWord_6796768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796768).length < 2 ^ (prefixWord ++ tailWord_6796768).sum := by decide
  have hdescent : baseEnd_6796768 < baseStart_6796768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796771 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6796771 : Nat := 118140960795 + 6796771 * 2 ^ 59
def prefixEnd_6796771 : Nat := 4983230072969 + 3 ^ 40 * 6796771 * 2
def baseEnd_6796771 : Nat := 3490010421540132335904725

theorem tailTrace_6796771 : CollatzResearch.WordTrace tailWord_6796771 prefixEnd_6796771 3490010421540132335904725 := by
  unfold tailWord_6796771
  simp only [CollatzResearch.WordTrace]
  refine ⟨247898604059466937916214167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165265736039644625277476111 247898604059466937916214167)
  ·
    refine ⟨371847906089200406874321251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247898604059466937916214167 371847906089200406874321251)
    ·
      refine ⟨557771859133800610311481877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371847906089200406874321251 557771859133800610311481877)
      ·
        refine ⟨26145555896896903608350713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 557771859133800610311481877 26145555896896903608350713)
        ·
          refine ⟨19609166922672677706263035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26145555896896903608350713 19609166922672677706263035)
          ·
            refine ⟨29413750384009016559394553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19609166922672677706263035 29413750384009016559394553)
            ·
              refine ⟨22060312788006762419545915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29413750384009016559394553 22060312788006762419545915)
              ·
                refine ⟨33090469182010143629318873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22060312788006762419545915 33090469182010143629318873)
                ·
                  refine ⟨24817851886507607721989155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33090469182010143629318873 24817851886507607721989155)
                  ·
                    refine ⟨37226777829761411582983733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24817851886507607721989155 37226777829761411582983733)
                    ·
                      refine ⟨3490010421540132335904725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37226777829761411582983733 3490010421540132335904725)
                      ·
                        rfl

theorem cell23_6796771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6796771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796771 prefixEnd_6796771 := by exact prefixLift 6796771
  have htrace : WordTrace (prefixWord ++ tailWord_6796771) baseStart_6796771 baseEnd_6796771 := by
    simpa [prefixWord, tailWord_6796771, baseEnd_6796771] using wordTrace_append hprefix tailTrace_6796771
  have hstable : (prefixWord ++ tailWord_6796771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796771).length < 2 ^ (prefixWord ++ tailWord_6796771).sum := by decide
  have hdescent : baseEnd_6796771 < baseStart_6796771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796785 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 2, 2, 2]
def baseStart_6796785 : Nat := 118140960795 + 6796785 * 2 ^ 59
def prefixEnd_6796785 : Nat := 4983230072969 + 3 ^ 40 * 6796785 * 2
def baseEnd_6796785 : Nat := 3490017610269295281129661

theorem tailTrace_6796785 : CollatzResearch.WordTrace tailWord_6796785 prefixEnd_6796785 3490017610269295281129661 := by
  unfold tailWord_6796785
  simp only [CollatzResearch.WordTrace]
  refine ⟨247899114681416218307223809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165266076454277478871482539 247899114681416218307223809)
  ·
    refine ⟨185924336011062163730417857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247899114681416218307223809 185924336011062163730417857)
    ·
      refine ⟨139443252008296622797813393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185924336011062163730417857 139443252008296622797813393)
      ·
        refine ⟨104582439006222467098360045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139443252008296622797813393 104582439006222467098360045)
        ·
          refine ⟨39218414627333425161885017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104582439006222467098360045 39218414627333425161885017)
          ·
            refine ⟨29413810970500068871413763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39218414627333425161885017 29413810970500068871413763)
            ·
              refine ⟨44120716455750103307120645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29413810970500068871413763 44120716455750103307120645)
              ·
                refine ⟨8272634335453144370085121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44120716455750103307120645 8272634335453144370085121)
                ·
                  refine ⟨6204475751589858277563841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8272634335453144370085121 6204475751589858277563841)
                  ·
                    refine ⟨4653356813692393708172881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204475751589858277563841 4653356813692393708172881)
                    ·
                      refine ⟨3490017610269295281129661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653356813692393708172881 3490017610269295281129661)
                      ·
                        rfl

theorem cell23_6796785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_6796785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796785 prefixEnd_6796785 := by exact prefixLift 6796785
  have htrace : WordTrace (prefixWord ++ tailWord_6796785) baseStart_6796785 baseEnd_6796785 := by
    simpa [prefixWord, tailWord_6796785, baseEnd_6796785] using wordTrace_append hprefix tailTrace_6796785
  have hstable : (prefixWord ++ tailWord_6796785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796785).length < 2 ^ (prefixWord ++ tailWord_6796785).sum := by decide
  have hdescent : baseEnd_6796785 < baseStart_6796785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796802 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_6796802 : Nat := 118140960795 + 6796802 * 2 ^ 59
def prefixEnd_6796802 : Nat := 4983230072969 + 3 ^ 40 * 6796802 * 2
def baseEnd_6796802 : Nat := 3490026339440421714617083

theorem tailTrace_6796802 : CollatzResearch.WordTrace tailWord_6796802 prefixEnd_6796802 3490026339440421714617083 := by
  unfold tailWord_6796802
  simp only [CollatzResearch.WordTrace]
  refine ⟨61974933680588657552648165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165266489814903086807061773 61974933680588657552648165)
  ·
    refine ⟨11620300065110373291121531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61974933680588657552648165 11620300065110373291121531)
    ·
      refine ⟨17430450097665559936682297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11620300065110373291121531 17430450097665559936682297)
      ·
        refine ⟨13072837573249169952511723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17430450097665559936682297 13072837573249169952511723)
        ·
          refine ⟨19609256359873754928767585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13072837573249169952511723 19609256359873754928767585)
          ·
            refine ⟨14706942269905316196575689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19609256359873754928767585 14706942269905316196575689)
            ·
              refine ⟨11030206702428987147431767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14706942269905316196575689 11030206702428987147431767)
              ·
                refine ⟨16545310053643480721147651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11030206702428987147431767 16545310053643480721147651)
                ·
                  refine ⟨24817965080465221081721477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16545310053643480721147651 24817965080465221081721477)
                  ·
                    refine ⟨4653368452587228952822777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24817965080465221081721477 4653368452587228952822777)
                    ·
                      refine ⟨3490026339440421714617083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653368452587228952822777 3490026339440421714617083)
                      ·
                        rfl

theorem cell23_6796802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_6796802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796802 prefixEnd_6796802 := by exact prefixLift 6796802
  have htrace : WordTrace (prefixWord ++ tailWord_6796802) baseStart_6796802 baseEnd_6796802 := by
    simpa [prefixWord, tailWord_6796802, baseEnd_6796802] using wordTrace_append hprefix tailTrace_6796802
  have hstable : (prefixWord ++ tailWord_6796802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796802).length < 2 ^ (prefixWord ++ tailWord_6796802).sum := by decide
  have hdescent : baseEnd_6796802 < baseStart_6796802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796821 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_6796821 : Nat := 118140960795 + 6796821 * 2 ^ 59
def prefixEnd_6796821 : Nat := 4983230072969 + 3 ^ 40 * 6796821 * 2
def baseEnd_6796821 : Nat := 1163345365190952380093165

theorem tailTrace_6796821 : CollatzResearch.WordTrace tailWord_6796821 prefixEnd_6796821 1163345365190952380093165 := by
  unfold tailWord_6796821
  simp only [CollatzResearch.WordTrace]
  refine ⟨247900427709285796455534317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165266951806190530970356211 247900427709285796455534317)
  ·
    refine ⟨92962660390982173670825369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247900427709285796455534317 92962660390982173670825369)
    ·
      refine ⟨69721995293236630253119027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92962660390982173670825369 69721995293236630253119027)
      ·
        refine ⟨104582992939854945379678541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69721995293236630253119027 104582992939854945379678541)
        ·
          refine ⟨39218622352445604517379453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104582992939854945379678541 39218622352445604517379453)
          ·
            refine ⟨14706983382167101694017295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39218622352445604517379453 14706983382167101694017295)
            ·
              refine ⟨22060475073250652541025943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14706983382167101694017295 22060475073250652541025943)
              ·
                refine ⟨33090712609875978811538915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22060475073250652541025943 33090712609875978811538915)
                ·
                  refine ⟨49636068914813968217308373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33090712609875978811538915 49636068914813968217308373)
                  ·
                    refine ⟨1163345365190952380093165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49636068914813968217308373 1163345365190952380093165)
                    ·
                      rfl

theorem cell23_6796821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_6796821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796821 prefixEnd_6796821 := by exact prefixLift 6796821
  have htrace : WordTrace (prefixWord ++ tailWord_6796821) baseStart_6796821 baseEnd_6796821 := by
    simpa [prefixWord, tailWord_6796821, baseEnd_6796821] using wordTrace_append hprefix tailTrace_6796821
  have hstable : (prefixWord ++ tailWord_6796821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796821).length < 2 ^ (prefixWord ++ tailWord_6796821).sum := by decide
  have hdescent : baseEnd_6796821 < baseStart_6796821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796858 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2]
def baseStart_6796858 : Nat := 118140960795 + 6796858 * 2 ^ 59
def prefixEnd_6796858 : Nat := 4983230072969 + 3 ^ 40 * 6796858 * 2
def baseEnd_6796858 : Nat := 3490055094357073495516825

theorem tailTrace_6796858 : CollatzResearch.WordTrace tailWord_6796858 prefixEnd_6796858 3490055094357073495516825 := by
  unfold tailWord_6796858
  simp only [CollatzResearch.WordTrace]
  refine ⟨61975444302537937943657807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165267851473434501183087485 61975444302537937943657807)
  ·
    refine ⟨92963166453806906915486711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61975444302537937943657807 92963166453806906915486711)
    ·
      refine ⟨139444749680710360373230067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92963166453806906915486711 139444749680710360373230067)
      ·
        refine ⟨209167124521065540559845101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139444749680710360373230067 209167124521065540559845101)
        ·
          refine ⟨78437671695399577709941913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209167124521065540559845101 78437671695399577709941913)
          ·
            refine ⟨58828253771549683282456435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78437671695399577709941913 58828253771549683282456435)
            ·
              refine ⟨88242380657324524923684653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58828253771549683282456435 88242380657324524923684653)
              ·
                refine ⟨33090892746496696846381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88242380657324524923684653 33090892746496696846381745)
                ·
                  refine ⟨24818169559872522634786309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33090892746496696846381745 24818169559872522634786309)
                  ·
                    refine ⟨4653406792476097994022433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24818169559872522634786309 4653406792476097994022433)
                    ·
                      refine ⟨3490055094357073495516825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653406792476097994022433 3490055094357073495516825)
                      ·
                        rfl

theorem cell23_6796858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_6796858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796858 prefixEnd_6796858 := by exact prefixLift 6796858
  have htrace : WordTrace (prefixWord ++ tailWord_6796858) baseStart_6796858 baseEnd_6796858 := by
    simpa [prefixWord, tailWord_6796858, baseEnd_6796858] using wordTrace_append hprefix tailTrace_6796858
  have hstable : (prefixWord ++ tailWord_6796858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796858).length < 2 ^ (prefixWord ++ tailWord_6796858).sum := by decide
  have hdescent : baseEnd_6796858 < baseStart_6796858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796878 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_6796878 : Nat := 118140960795 + 6796878 * 2 ^ 59
def prefixEnd_6796878 : Nat := 4983230072969 + 3 ^ 40 * 6796878 * 2
def baseEnd_6796878 : Nat := 3490065363970163417266733

theorem tailTrace_6796878 : CollatzResearch.WordTrace tailWord_6796878 prefixEnd_6796878 3490065363970163417266733 := by
  unfold tailWord_6796878
  simp only [CollatzResearch.WordTrace]
  refine ⟨30987813333759911898794911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165268337780052863460239525 30987813333759911898794911)
  ·
    refine ⟨46481720000639867848192367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30987813333759911898794911 46481720000639867848192367)
    ·
      refine ⟨69722580000959801772288551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46481720000639867848192367 69722580000959801772288551)
      ·
        refine ⟨104583870001439702658432827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69722580000959801772288551 104583870001439702658432827)
        ·
          refine ⟨156875805002159553987649241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104583870001439702658432827 156875805002159553987649241)
          ·
            refine ⟨117656853751619665490736931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156875805002159553987649241 117656853751619665490736931)
            ·
              refine ⟨176485280627429498236105397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117656853751619665490736931 176485280627429498236105397)
              ·
                refine ⟨16545495058821515459634881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176485280627429498236105397 16545495058821515459634881)
                ·
                  refine ⟨12409121294116136594726161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16545495058821515459634881 12409121294116136594726161)
                  ·
                    refine ⟨9306840970587102446044621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12409121294116136594726161 9306840970587102446044621)
                    ·
                      refine ⟨3490065363970163417266733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9306840970587102446044621 3490065363970163417266733)
                      ·
                        rfl

theorem cell23_6796878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_6796878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796878 prefixEnd_6796878 := by exact prefixLift 6796878
  have htrace : WordTrace (prefixWord ++ tailWord_6796878) baseStart_6796878 baseEnd_6796878 := by
    simpa [prefixWord, tailWord_6796878, baseEnd_6796878] using wordTrace_append hprefix tailTrace_6796878
  have hstable : (prefixWord ++ tailWord_6796878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796878).length < 2 ^ (prefixWord ++ tailWord_6796878).sum := by decide
  have hdescent : baseEnd_6796878 < baseStart_6796878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796911 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 3, 5]
def baseStart_6796911 : Nat := 118140960795 + 6796911 * 2 ^ 59
def prefixEnd_6796911 : Nat := 4983230072969 + 3 ^ 40 * 6796911 * 2
def baseEnd_6796911 : Nat := 1163360769610587262718027

theorem tailTrace_6796911 : CollatzResearch.WordTrace tailWord_6796911 prefixEnd_6796911 1163360769610587262718027 := by
  unfold tailWord_6796911
  simp only [CollatzResearch.WordTrace]
  refine ⟨247903710278959741826310587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165269140185973161217540391 247903710278959741826310587)
  ·
    refine ⟨371855565418439612739465881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247903710278959741826310587 371855565418439612739465881)
    ·
      refine ⟨278891674063829709554599411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371855565418439612739465881 278891674063829709554599411)
      ·
        refine ⟨418337511095744564331899117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278891674063829709554599411 418337511095744564331899117)
        ·
          refine ⟨156876566660904211624462169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418337511095744564331899117 156876566660904211624462169)
          ·
            refine ⟨117657424995678158718346627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156876566660904211624462169 117657424995678158718346627)
            ·
              refine ⟨176486137493517238077519941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117657424995678158718346627 176486137493517238077519941)
              ·
                refine ⟨33091150780034482139534989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176486137493517238077519941 33091150780034482139534989)
                ·
                  refine ⟨12409181542512930802325621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33091150780034482139534989 12409181542512930802325621)
                  ·
                    refine ⟨1163360769610587262718027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12409181542512930802325621 1163360769610587262718027)
                    ·
                      rfl

theorem cell23_6796911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_6796911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796911 prefixEnd_6796911 := by exact prefixLift 6796911
  have htrace : WordTrace (prefixWord ++ tailWord_6796911) baseStart_6796911 baseEnd_6796911 := by
    simpa [prefixWord, tailWord_6796911, baseEnd_6796911] using wordTrace_append hprefix tailTrace_6796911
  have hstable : (prefixWord ++ tailWord_6796911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796911).length < 2 ^ (prefixWord ++ tailWord_6796911).sum := by decide
  have hdescent : baseEnd_6796911 < baseStart_6796911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796935 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_6796935 : Nat := 118140960795 + 6796935 * 2 ^ 59
def prefixEnd_6796935 : Nat := 4983230072969 + 3 ^ 40 * 6796935 * 2
def baseEnd_6796935 : Nat := 3490094632367469694253971

theorem tailTrace_6796935 : CollatzResearch.WordTrace tailWord_6796935 prefixEnd_6796935 3490094632367469694253971 := by
  unfold tailWord_6796935
  simp only [CollatzResearch.WordTrace]
  refine ⟨247904585630872793925184259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165269723753915195950122839 247904585630872793925184259)
  ·
    refine ⟨371856878446309190887776389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247904585630872793925184259 371856878446309190887776389)
    ·
      refine ⟨69723164708682973291458073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371856878446309190887776389 69723164708682973291458073)
      ·
        refine ⟨52292373531512229968593555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69723164708682973291458073 52292373531512229968593555)
        ·
          refine ⟨78438560297268344952890333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52292373531512229968593555 78438560297268344952890333)
          ·
            refine ⟨29414460111475629357333875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78438560297268344952890333 29414460111475629357333875)
            ·
              refine ⟨44121690167213444036000813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29414460111475629357333875 44121690167213444036000813)
              ·
                refine ⟨16545633812705041513500305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44121690167213444036000813 16545633812705041513500305)
                ·
                  refine ⟨12409225359528781135125229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16545633812705041513500305 12409225359528781135125229)
                  ·
                    refine ⟨4653459509823292925671961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12409225359528781135125229 4653459509823292925671961)
                    ·
                      refine ⟨3490094632367469694253971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653459509823292925671961 3490094632367469694253971)
                      ·
                        rfl

theorem cell23_6796935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_6796935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796935 prefixEnd_6796935 := by exact prefixLift 6796935
  have htrace : WordTrace (prefixWord ++ tailWord_6796935) baseStart_6796935 baseEnd_6796935 := by
    simpa [prefixWord, tailWord_6796935, baseEnd_6796935] using wordTrace_append hprefix tailTrace_6796935
  have hstable : (prefixWord ++ tailWord_6796935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796935).length < 2 ^ (prefixWord ++ tailWord_6796935).sum := by decide
  have hdescent : baseEnd_6796935 < baseStart_6796935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796978 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_6796978 : Nat := 118140960795 + 6796978 * 2 ^ 59
def prefixEnd_6796978 : Nat := 4983230072969 + 3 ^ 40 * 6796978 * 2
def baseEnd_6796978 : Nat := 3490116712035613026016273

theorem tailTrace_6796978 : CollatzResearch.WordTrace tailWord_6796978 prefixEnd_6796978 3490116712035613026016273 := by
  unfold tailWord_6796978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61976538492429253067249897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165270769313144674845999725 61976538492429253067249897)
  ·
    refine ⟨46482403869321939800437423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61976538492429253067249897 46482403869321939800437423)
    ·
      refine ⟨69723605803982909700656135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46482403869321939800437423 69723605803982909700656135)
      ·
        refine ⟨104585408705974364550984203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69723605803982909700656135 104585408705974364550984203)
        ·
          refine ⟨156878113058961546826476305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104585408705974364550984203 156878113058961546826476305)
          ·
            refine ⟨117658584794221160119857229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156878113058961546826476305 117658584794221160119857229)
            ·
              refine ⟨44121969297832935044946461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117658584794221160119857229 44121969297832935044946461)
              ·
                refine ⟨16545738486687350641854923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44121969297832935044946461 16545738486687350641854923)
                ·
                  refine ⟨24818607730031025962782385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16545738486687350641854923 24818607730031025962782385)
                  ·
                    refine ⟨18613955797523269472086789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24818607730031025962782385 18613955797523269472086789)
                    ·
                      refine ⟨3490116712035613026016273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18613955797523269472086789 3490116712035613026016273)
                      ·
                        rfl

theorem cell23_6796978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_6796978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796978 prefixEnd_6796978 := by exact prefixLift 6796978
  have htrace : WordTrace (prefixWord ++ tailWord_6796978) baseStart_6796978 baseEnd_6796978 := by
    simpa [prefixWord, tailWord_6796978, baseEnd_6796978] using wordTrace_append hprefix tailTrace_6796978
  have hstable : (prefixWord ++ tailWord_6796978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796978).length < 2 ^ (prefixWord ++ tailWord_6796978).sum := by decide
  have hdescent : baseEnd_6796978 < baseStart_6796978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796982 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6796982 : Nat := 118140960795 + 6796982 * 2 ^ 59
def prefixEnd_6796982 : Nat := 4983230072969 + 3 ^ 40 * 6796982 * 2
def baseEnd_6796982 : Nat := 3490118765958231010366255

theorem tailTrace_6796982 : CollatzResearch.WordTrace tailWord_6796982 prefixEnd_6796982 3490118765958231010366255 := by
  unfold tailWord_6796982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15494143741356407559509075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165270866574468347301430133 15494143741356407559509075)
  ·
    refine ⟨23241215612034611339263613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15494143741356407559509075 23241215612034611339263613)
    ·
      refine ⟨8715455854512979252223855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23241215612034611339263613 8715455854512979252223855)
      ·
        refine ⟨13073183781769468878335783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715455854512979252223855 13073183781769468878335783)
        ·
          refine ⟨19609775672654203317503675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13073183781769468878335783 19609775672654203317503675)
          ·
            refine ⟨29414663508981304976255513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19609775672654203317503675 29414663508981304976255513)
            ·
              refine ⟨22060997631735978732191635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29414663508981304976255513 22060997631735978732191635)
              ·
                refine ⟨33091496447603968098287453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22060997631735978732191635 33091496447603968098287453)
                ·
                  refine ⟨12409311167851488036857795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33091496447603968098287453 12409311167851488036857795)
                  ·
                    refine ⟨18613966751777232055286693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12409311167851488036857795 18613966751777232055286693)
                    ·
                      refine ⟨3490118765958231010366255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18613966751777232055286693 3490118765958231010366255)
                      ·
                        rfl

theorem cell23_6796982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6796982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796982 prefixEnd_6796982 := by exact prefixLift 6796982
  have htrace : WordTrace (prefixWord ++ tailWord_6796982) baseStart_6796982 baseEnd_6796982 := by
    simpa [prefixWord, tailWord_6796982, baseEnd_6796982] using wordTrace_append hprefix tailTrace_6796982
  have hstable : (prefixWord ++ tailWord_6796982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796982).length < 2 ^ (prefixWord ++ tailWord_6796982).sum := by decide
  have hdescent : baseEnd_6796982 < baseStart_6796982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6796999 : List Nat := [1, 1, 4, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_6796999 : Nat := 118140960795 + 6796999 * 2 ^ 59
def prefixEnd_6796999 : Nat := 4983230072969 + 3 ^ 40 * 6796999 * 2
def baseEnd_6796999 : Nat := 3490127495129357443853677

theorem tailTrace_6796999 : CollatzResearch.WordTrace tailWord_6796999 prefixEnd_6796999 3490127495129357443853677 := by
  unfold tailWord_6796999
  simp only [CollatzResearch.WordTrace]
  refine ⟨247906919902640932855514051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165271279935093955237009367 247906919902640932855514051)
  ·
    refine ⟨371860379853961399283271077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247906919902640932855514051 371860379853961399283271077)
    ·
      refine ⟨69723821222617762365613327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371860379853961399283271077 69723821222617762365613327)
      ·
        refine ⟨104585731833926643548419991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69723821222617762365613327 104585731833926643548419991)
        ·
          refine ⟨156878597750889965322629987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104585731833926643548419991 156878597750889965322629987)
          ·
            refine ⟨235317896626334947983944981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156878597750889965322629987 235317896626334947983944981)
            ·
              refine ⟨11030526404359450686747421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 235317896626334947983944981 11030526404359450686747421)
              ·
                refine ⟨4136447401634794007530283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11030526404359450686747421 4136447401634794007530283)
                ·
                  refine ⟨6204671102452191011295425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4136447401634794007530283 6204671102452191011295425)
                  ·
                    refine ⟨4653503326839143258471569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204671102452191011295425 4653503326839143258471569)
                    ·
                      refine ⟨3490127495129357443853677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653503326839143258471569 3490127495129357443853677)
                      ·
                        rfl

theorem cell23_6796999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_6796999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6796999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6796999 prefixEnd_6796999 := by exact prefixLift 6796999
  have htrace : WordTrace (prefixWord ++ tailWord_6796999) baseStart_6796999 baseEnd_6796999 := by
    simpa [prefixWord, tailWord_6796999, baseEnd_6796999] using wordTrace_append hprefix tailTrace_6796999
  have hstable : (prefixWord ++ tailWord_6796999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6796999).length < 2 ^ (prefixWord ++ tailWord_6796999).sum := by decide
  have hdescent : baseEnd_6796999 < baseStart_6796999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6796999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797002 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_6797002 : Nat := 118140960795 + 6797002 * 2 ^ 59
def prefixEnd_6797002 : Nat := 4983230072969 + 3 ^ 40 * 6797002 * 2
def baseEnd_6797002 : Nat := 3490129035571320932116163

theorem tailTrace_6797002 : CollatzResearch.WordTrace tailWord_6797002 prefixEnd_6797002 3490129035571320932116163 := by
  unfold tailWord_6797002
  simp only [CollatzResearch.WordTrace]
  refine ⟨61976757330407516091968315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165271352881086709578582173 61976757330407516091968315)
  ·
    refine ⟨92965135995611274137952473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61976757330407516091968315 92965135995611274137952473)
    ·
      refine ⟨69723851996708455603464355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92965135995611274137952473 69723851996708455603464355)
      ·
        refine ⟨104585777995062683405196533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69723851996708455603464355 104585777995062683405196533)
        ·
          refine ⟨9804916687037126569237175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104585777995062683405196533 9804916687037126569237175)
          ·
            refine ⟨14707375030555689853855763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9804916687037126569237175 14707375030555689853855763)
            ·
              refine ⟨22061062545833534780783645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14707375030555689853855763 22061062545833534780783645)
              ·
                refine ⟨8272898454687575542793867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22061062545833534780783645 8272898454687575542793867)
                ·
                  refine ⟨12409347682031363314190801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8272898454687575542793867 12409347682031363314190801)
                  ·
                    refine ⟨9307010761523522485643101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12409347682031363314190801 9307010761523522485643101)
                    ·
                      refine ⟨3490129035571320932116163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9307010761523522485643101 3490129035571320932116163)
                      ·
                        rfl

theorem cell23_6797002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_6797002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797002 prefixEnd_6797002 := by exact prefixLift 6797002
  have htrace : WordTrace (prefixWord ++ tailWord_6797002) baseStart_6797002 baseEnd_6797002 := by
    simpa [prefixWord, tailWord_6797002, baseEnd_6797002] using wordTrace_append hprefix tailTrace_6797002
  have hstable : (prefixWord ++ tailWord_6797002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797002).length < 2 ^ (prefixWord ++ tailWord_6797002).sum := by decide
  have hdescent : baseEnd_6797002 < baseStart_6797002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797005 : List Nat := [1, 6, 2, 1, 1, 2, 10]
def baseStart_6797005 : Nat := 118140960795 + 6797005 * 2 ^ 59
def prefixEnd_6797005 : Nat := 4983230072969 + 3 ^ 40 * 6797005 * 2
def baseEnd_6797005 : Nat := 43088031802633140992329

theorem tailTrace_6797005 : CollatzResearch.WordTrace tailWord_6797005 prefixEnd_6797005 43088031802633140992329 := by
  unfold tailWord_6797005
  simp only [CollatzResearch.WordTrace]
  refine ⟨247907138740619195880232469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165271425827079463920154979 247907138740619195880232469)
  ·
    refine ⟨11620647128466524806885897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247907138740619195880232469 11620647128466524806885897)
    ·
      refine ⟨8715485346349893605164423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11620647128466524806885897 8715485346349893605164423)
      ·
        refine ⟨13073228019524840407746635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8715485346349893605164423 13073228019524840407746635)
        ·
          refine ⟨19609842029287260611619953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13073228019524840407746635 19609842029287260611619953)
          ·
            refine ⟨14707381521965445458714965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19609842029287260611619953 14707381521965445458714965)
            ·
              refine ⟨43088031802633140992329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14707381521965445458714965 43088031802633140992329)
              ·
                rfl

theorem cell23_6797005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 10].length) (baseStart_6797005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797005 prefixEnd_6797005 := by exact prefixLift 6797005
  have htrace : WordTrace (prefixWord ++ tailWord_6797005) baseStart_6797005 baseEnd_6797005 := by
    simpa [prefixWord, tailWord_6797005, baseEnd_6797005] using wordTrace_append hprefix tailTrace_6797005
  have hstable : (prefixWord ++ tailWord_6797005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797005).length < 2 ^ (prefixWord ++ tailWord_6797005).sum := by decide
  have hdescent : baseEnd_6797005 < baseStart_6797005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797015 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_6797015 : Nat := 118140960795 + 6797015 * 2 ^ 59
def prefixEnd_6797015 : Nat := 4983230072969 + 3 ^ 40 * 6797015 * 2
def baseEnd_6797015 : Nat := 3490135710819829381253603

theorem tailTrace_6797015 : CollatzResearch.WordTrace tailWord_6797015 prefixEnd_6797015 3490135710819829381253603 := by
  unfold tailWord_6797015
  simp only [CollatzResearch.WordTrace]
  refine ⟨247907503470582967588096499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165271668980388645058730999 247907503470582967588096499)
  ·
    refine ⟨371861255205874451382144749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247907503470582967588096499 371861255205874451382144749)
    ·
      refine ⟨139447970702202919268304281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371861255205874451382144749 139447970702202919268304281)
      ·
        refine ⟨104585978026652189451228211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139447970702202919268304281 104585978026652189451228211)
        ·
          refine ⟨156878967039978284176842317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104585978026652189451228211 156878967039978284176842317)
          ·
            refine ⟨58829612639991856566315869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156878967039978284176842317 58829612639991856566315869)
            ·
              refine ⟨22061104739996946212368451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58829612639991856566315869 22061104739996946212368451)
              ·
                refine ⟨33091657109995419318552677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22061104739996946212368451 33091657109995419318552677)
                ·
                  refine ⟨6204685708124141122228627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33091657109995419318552677 6204685708124141122228627)
                  ·
                    refine ⟨9307028562186211683342941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6204685708124141122228627 9307028562186211683342941)
                    ·
                      refine ⟨3490135710819829381253603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9307028562186211683342941 3490135710819829381253603)
                      ·
                        rfl

theorem cell23_6797015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_6797015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797015 prefixEnd_6797015 := by exact prefixLift 6797015
  have htrace : WordTrace (prefixWord ++ tailWord_6797015) baseStart_6797015 baseEnd_6797015 := by
    simpa [prefixWord, tailWord_6797015, baseEnd_6797015] using wordTrace_append hprefix tailTrace_6797015
  have hstable : (prefixWord ++ tailWord_6797015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797015).length < 2 ^ (prefixWord ++ tailWord_6797015).sum := by decide
  have hdescent : baseEnd_6797015 < baseStart_6797015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797032 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_6797032 : Nat := 118140960795 + 6797032 * 2 ^ 59
def prefixEnd_6797032 : Nat := 4983230072969 + 3 ^ 40 * 6797032 * 2
def baseEnd_6797032 : Nat := 3490144439990955814741025

theorem tailTrace_6797032 : CollatzResearch.WordTrace tailWord_6797032 prefixEnd_6797032 3490144439990955814741025 := by
  unfold tailWord_6797032
  simp only [CollatzResearch.WordTrace]
  refine ⟨123954061755760689745732675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165272082341014252994310233 123954061755760689745732675)
  ·
    refine ⟨185931092633641034618599013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123954061755760689745732675 185931092633641034618599013)
    ·
      refine ⟨34862079868807693990987315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185931092633641034618599013 34862079868807693990987315)
      ·
        refine ⟨52293119803211540986480973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34862079868807693990987315 52293119803211540986480973)
        ·
          refine ⟨19609919926204327869930365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52293119803211540986480973 19609919926204327869930365)
          ·
            refine ⟨7353719972326622951223887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19609919926204327869930365 7353719972326622951223887)
            ·
              refine ⟨11030579958489934426835831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353719972326622951223887 11030579958489934426835831)
              ·
                refine ⟨16545869937734901640253747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11030579958489934426835831 16545869937734901640253747)
                ·
                  refine ⟨24818804906602352460380621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16545869937734901640253747 24818804906602352460380621)
                  ·
                    refine ⟨9307051839975882172642733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24818804906602352460380621 9307051839975882172642733)
                    ·
                      refine ⟨3490144439990955814741025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9307051839975882172642733 3490144439990955814741025)
                      ·
                        rfl

theorem cell23_6797032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_6797032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797032 prefixEnd_6797032 := by exact prefixLift 6797032
  have htrace : WordTrace (prefixWord ++ tailWord_6797032) baseStart_6797032 baseEnd_6797032 := by
    simpa [prefixWord, tailWord_6797032, baseEnd_6797032] using wordTrace_append hprefix tailTrace_6797032
  have hstable : (prefixWord ++ tailWord_6797032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797032).length < 2 ^ (prefixWord ++ tailWord_6797032).sum := by decide
  have hdescent : baseEnd_6797032 < baseStart_6797032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797055 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 1, 4, 2]
def baseStart_6797055 : Nat := 118140960795 + 6797055 * 2 ^ 59
def prefixEnd_6797055 : Nat := 4983230072969 + 3 ^ 40 * 6797055 * 2
def baseEnd_6797055 : Nat := 3490156250046009224753419

theorem tailTrace_6797055 : CollatzResearch.WordTrace tailWord_6797055 prefixEnd_6797055 3490156250046009224753419 := by
  unfold tailWord_6797055
  simp only [CollatzResearch.WordTrace]
  refine ⟨247908962390438054419552619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165272641593625369613035079 247908962390438054419552619)
  ·
    refine ⟨371863443585657081629328929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247908962390438054419552619 371863443585657081629328929)
    ·
      refine ⟨278897582689242811221996697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371863443585657081629328929 278897582689242811221996697)
      ·
        refine ⟨209173187016932108416497523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278897582689242811221996697 209173187016932108416497523)
        ·
          refine ⟨313759780525398162624746285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209173187016932108416497523 313759780525398162624746285)
          ·
            refine ⟨117659917697024310984279857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313759780525398162624746285 117659917697024310984279857)
            ·
              refine ⟨88244938272768233238209893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117659917697024310984279857 88244938272768233238209893)
              ·
                refine ⟨16545925926144043732164355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88244938272768233238209893 16545925926144043732164355)
                ·
                  refine ⟨24818888889216065598246533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16545925926144043732164355 24818888889216065598246533)
                  ·
                    refine ⟨4653541666728012299671225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24818888889216065598246533 4653541666728012299671225)
                    ·
                      refine ⟨3490156250046009224753419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653541666728012299671225 3490156250046009224753419)
                      ·
                        rfl

theorem cell23_6797055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_6797055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797055 prefixEnd_6797055 := by exact prefixLift 6797055
  have htrace : WordTrace (prefixWord ++ tailWord_6797055) baseStart_6797055 baseEnd_6797055 := by
    simpa [prefixWord, tailWord_6797055, baseEnd_6797055] using wordTrace_append hprefix tailTrace_6797055
  have hstable : (prefixWord ++ tailWord_6797055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797055).length < 2 ^ (prefixWord ++ tailWord_6797055).sum := by decide
  have hdescent : baseEnd_6797055 < baseStart_6797055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797068 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6797068 : Nat := 118140960795 + 6797068 * 2 ^ 59
def prefixEnd_6797068 : Nat := 4983230072969 + 3 ^ 40 * 6797068 * 2
def baseEnd_6797068 : Nat := 3490162925294517673890859

theorem tailTrace_6797068 : CollatzResearch.WordTrace tailWord_6797068 prefixEnd_6797068 3490162925294517673890859 := by
  unfold tailWord_6797068
  simp only [CollatzResearch.WordTrace]
  refine ⟨123954718269695478819887929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165272957692927305093183905 123954718269695478819887929)
  ·
    refine ⟨92966038702271609114915947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123954718269695478819887929 92966038702271609114915947)
    ·
      refine ⟨139449058053407413672373921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92966038702271609114915947 139449058053407413672373921)
      ·
        refine ⟨104586793540055560254280441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139449058053407413672373921 104586793540055560254280441)
        ·
          refine ⟨78440095155041670190710331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104586793540055560254280441 78440095155041670190710331)
          ·
            refine ⟨117660142732562505286065497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78440095155041670190710331 117660142732562505286065497)
            ·
              refine ⟨88245107049421878964549123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117660142732562505286065497 88245107049421878964549123)
              ·
                refine ⟨132367660574132818446823685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88245107049421878964549123 132367660574132818446823685)
                ·
                  refine ⟨24818936357649903458779441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132367660574132818446823685 24818936357649903458779441)
                  ·
                    refine ⟨18614202268237427594084581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24818936357649903458779441 18614202268237427594084581)
                    ·
                      refine ⟨3490162925294517673890859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18614202268237427594084581 3490162925294517673890859)
                      ·
                        rfl

theorem cell23_6797068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6797068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797068 prefixEnd_6797068 := by exact prefixLift 6797068
  have htrace : WordTrace (prefixWord ++ tailWord_6797068) baseStart_6797068 baseEnd_6797068 := by
    simpa [prefixWord, tailWord_6797068, baseEnd_6797068] using wordTrace_append hprefix tailTrace_6797068
  have hstable : (prefixWord ++ tailWord_6797068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797068).length < 2 ^ (prefixWord ++ tailWord_6797068).sum := by decide
  have hdescent : baseEnd_6797068 < baseStart_6797068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797089 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_6797089 : Nat := 118140960795 + 6797089 * 2 ^ 59
def prefixEnd_6797089 : Nat := 4983230072969 + 3 ^ 40 * 6797089 * 2
def baseEnd_6797089 : Nat := 3490173708388262091728263

theorem tailTrace_6797089 : CollatzResearch.WordTrace tailWord_6797089 prefixEnd_6797089 3490173708388262091728263 := by
  unfold tailWord_6797089
  simp only [CollatzResearch.WordTrace]
  refine ⟨247910202472314878226290321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165273468314876585484193547 247910202472314878226290321)
  ·
    refine ⟨185932651854236158669717741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247910202472314878226290321 185932651854236158669717741)
    ·
      refine ⟨69724744445338559501144153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185932651854236158669717741 69724744445338559501144153)
      ·
        refine ⟨52293558334003919625858115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69724744445338559501144153 52293558334003919625858115)
        ·
          refine ⟨78440337501005879438787173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52293558334003919625858115 78440337501005879438787173)
          ·
            refine ⟨14707563281438602394772595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78440337501005879438787173 14707563281438602394772595)
            ·
              refine ⟨22061344922157903592158893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14707563281438602394772595 22061344922157903592158893)
              ·
                refine ⟨8273004345809213847059585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22061344922157903592158893 8273004345809213847059585)
                ·
                  refine ⟨6204753259356910385294689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8273004345809213847059585 6204753259356910385294689)
                  ·
                    refine ⟨4653564944517682788971017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6204753259356910385294689 4653564944517682788971017)
                    ·
                      refine ⟨3490173708388262091728263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653564944517682788971017 3490173708388262091728263)
                      ·
                        rfl

theorem cell23_6797089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_6797089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797089 prefixEnd_6797089 := by exact prefixLift 6797089
  have htrace : WordTrace (prefixWord ++ tailWord_6797089) baseStart_6797089 baseEnd_6797089 := by
    simpa [prefixWord, tailWord_6797089, baseEnd_6797089] using wordTrace_append hprefix tailTrace_6797089
  have hstable : (prefixWord ++ tailWord_6797089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797089).length < 2 ^ (prefixWord ++ tailWord_6797089).sum := by decide
  have hdescent : baseEnd_6797089 < baseStart_6797089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797168 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 8]
def baseStart_6797168 : Nat := 118140960795 + 6797168 * 2 ^ 59
def prefixEnd_6797168 : Nat := 4983230072969 + 3 ^ 40 * 6797168 * 2
def baseEnd_6797168 : Nat := 387801585928885253626711

theorem tailTrace_6797168 : CollatzResearch.WordTrace tailWord_6797168 prefixEnd_6797168 387801585928885253626711 := by
  unfold tailWord_6797168
  simp only [CollatzResearch.WordTrace]
  refine ⟨123956541919514337359208079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165275389226019116478944105 123956541919514337359208079)
  ·
    refine ⟨185934812879271506038812119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123956541919514337359208079 185934812879271506038812119)
    ·
      refine ⟨278902219318907259058218179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185934812879271506038812119 278902219318907259058218179)
      ·
        refine ⟨418353328978360888587327269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278902219318907259058218179 418353328978360888587327269)
        ·
          refine ⟨78441249183442666610123863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418353328978360888587327269 78441249183442666610123863)
          ·
            refine ⟨117661873775163999915185795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78441249183442666610123863 117661873775163999915185795)
            ·
              refine ⟨176492810662745999872778693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117661873775163999915185795 176492810662745999872778693)
              ·
                refine ⟨33092401999264874976146005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176492810662745999872778693 33092401999264874976146005)
                ·
                  refine ⟨387801585928885253626711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33092401999264874976146005 387801585928885253626711)
                  ·
                    rfl

theorem cell23_6797168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_6797168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797168 prefixEnd_6797168 := by exact prefixLift 6797168
  have htrace : WordTrace (prefixWord ++ tailWord_6797168) baseStart_6797168 baseEnd_6797168 := by
    simpa [prefixWord, tailWord_6797168, baseEnd_6797168] using wordTrace_append hprefix tailTrace_6797168
  have hstable : (prefixWord ++ tailWord_6797168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797168).length < 2 ^ (prefixWord ++ tailWord_6797168).sum := by decide
  have hdescent : baseEnd_6797168 < baseStart_6797168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797246 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_6797246 : Nat := 118140960795 + 6797246 * 2 ^ 59
def prefixEnd_6797246 : Nat := 4983230072969 + 3 ^ 40 * 6797246 * 2
def baseEnd_6797246 : Nat := 3490254324851017977465041

theorem tailTrace_6797246 : CollatzResearch.WordTrace tailWord_6797246 prefixEnd_6797246 3490254324851017977465041 := by
  unfold tailWord_6797246
  simp only [CollatzResearch.WordTrace]
  refine ⟨30989491091593261754969449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165277285821830729359837061 30989491091593261754969449)
  ·
    refine ⟨23242118318694946316227087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30989491091593261754969449 23242118318694946316227087)
    ·
      refine ⟨34863177478042419474340631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23242118318694946316227087 34863177478042419474340631)
      ·
        refine ⟨52294766217063629211510947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34863177478042419474340631 52294766217063629211510947)
        ·
          refine ⟨78442149325595443817266421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52294766217063629211510947 78442149325595443817266421)
          ·
            refine ⟨7353951499274572857868727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78442149325595443817266421 7353951499274572857868727)
            ·
              refine ⟨11030927248911859286803091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353951499274572857868727 11030927248911859286803091)
              ·
                refine ⟨16546390873367788930204637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11030927248911859286803091 16546390873367788930204637)
                ·
                  refine ⟨6204896577512920848826739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16546390873367788930204637 6204896577512920848826739)
                  ·
                    refine ⟨9307344866269381273240109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6204896577512920848826739 9307344866269381273240109)
                    ·
                      refine ⟨3490254324851017977465041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9307344866269381273240109 3490254324851017977465041)
                      ·
                        rfl

theorem cell23_6797246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_6797246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797246 prefixEnd_6797246 := by exact prefixLift 6797246
  have htrace : WordTrace (prefixWord ++ tailWord_6797246) baseStart_6797246 baseEnd_6797246 := by
    simpa [prefixWord, tailWord_6797246, baseEnd_6797246] using wordTrace_append hprefix tailTrace_6797246
  have hstable : (prefixWord ++ tailWord_6797246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797246).length < 2 ^ (prefixWord ++ tailWord_6797246).sum := by decide
  have hdescent : baseEnd_6797246 < baseStart_6797246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797255 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_6797255 : Nat := 118140960795 + 6797255 * 2 ^ 59
def prefixEnd_6797255 : Nat := 4983230072969 + 3 ^ 40 * 6797255 * 2
def baseEnd_6797255 : Nat := 3490258946176908442252499

theorem tailTrace_6797255 : CollatzResearch.WordTrace tailWord_6797255 prefixEnd_6797255 3490258946176908442252499 := by
  unfold tailWord_6797255
  simp only [CollatzResearch.WordTrace]
  refine ⟨247916256989713488576833219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165277504659808992384555479 247916256989713488576833219)
  ·
    refine ⟨371874385484570232865249829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247916256989713488576833219 371874385484570232865249829)
    ·
      refine ⟨69726447278356918662234343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371874385484570232865249829 69726447278356918662234343)
      ·
        refine ⟨104589670917535377993351515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69726447278356918662234343 104589670917535377993351515)
        ·
          refine ⟨156884506376303066990027273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104589670917535377993351515 156884506376303066990027273)
          ·
            refine ⟨117663379782227300242520455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156884506376303066990027273 117663379782227300242520455)
            ·
              refine ⟨176495069673340950363780683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117663379782227300242520455 176495069673340950363780683)
              ·
                refine ⟨264742604510011425545671025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176495069673340950363780683 264742604510011425545671025)
                ·
                  refine ⟨198556953382508569159253269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264742604510011425545671025 198556953382508569159253269)
                  ·
                    refine ⟨9307357189805089179339997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 198556953382508569159253269 9307357189805089179339997)
                    ·
                      refine ⟨3490258946176908442252499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9307357189805089179339997 3490258946176908442252499)
                      ·
                        rfl

theorem cell23_6797255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_6797255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797255 prefixEnd_6797255 := by exact prefixLift 6797255
  have htrace : WordTrace (prefixWord ++ tailWord_6797255) baseStart_6797255 baseEnd_6797255 := by
    simpa [prefixWord, tailWord_6797255, baseEnd_6797255] using wordTrace_append hprefix tailTrace_6797255
  have hstable : (prefixWord ++ tailWord_6797255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797255).length < 2 ^ (prefixWord ++ tailWord_6797255).sum := by decide
  have hdescent : baseEnd_6797255 < baseStart_6797255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797266 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_6797266 : Nat := 118140960795 + 6797266 * 2 ^ 59
def prefixEnd_6797266 : Nat := 4983230072969 + 3 ^ 40 * 6797266 * 2
def baseEnd_6797266 : Nat := 1163421531488035966404983

theorem tailTrace_6797266 : CollatzResearch.WordTrace tailWord_6797266 prefixEnd_6797266 1163421531488035966404983 := by
  unfold tailWord_6797266
  simp only [CollatzResearch.WordTrace]
  refine ⟨61979164548168409363870913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165277772128449091636989101 61979164548168409363870913)
  ·
    refine ⟨46484373411126307022903185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61979164548168409363870913 46484373411126307022903185)
    ·
      refine ⟨34863280058344730267177389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46484373411126307022903185 34863280058344730267177389)
      ·
        refine ⟨13073730021879273850191521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34863280058344730267177389 13073730021879273850191521)
        ·
          refine ⟨9805297516409455387643641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13073730021879273850191521 9805297516409455387643641)
          ·
            refine ⟨7353973137307091540732731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9805297516409455387643641 7353973137307091540732731)
            ·
              refine ⟨11030959705960637311099097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353973137307091540732731 11030959705960637311099097)
              ·
                refine ⟨8273219779470477983324323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11030959705960637311099097 8273219779470477983324323)
                ·
                  refine ⟨12409829669205716974986485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8273219779470477983324323 12409829669205716974986485)
                  ·
                    refine ⟨1163421531488035966404983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12409829669205716974986485 1163421531488035966404983)
                    ·
                      rfl

theorem cell23_6797266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_6797266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797266 prefixEnd_6797266 := by exact prefixLift 6797266
  have htrace : WordTrace (prefixWord ++ tailWord_6797266) baseStart_6797266 baseEnd_6797266 := by
    simpa [prefixWord, tailWord_6797266, baseEnd_6797266] using wordTrace_append hprefix tailTrace_6797266
  have hstable : (prefixWord ++ tailWord_6797266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797266).length < 2 ^ (prefixWord ++ tailWord_6797266).sum := by decide
  have hdescent : baseEnd_6797266 < baseStart_6797266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797269 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6797269 : Nat := 118140960795 + 6797269 * 2 ^ 59
def prefixEnd_6797269 : Nat := 4983230072969 + 3 ^ 40 * 6797269 * 2
def baseEnd_6797269 : Nat := 3490266134906071387477435

theorem tailTrace_6797269 : CollatzResearch.WordTrace tailWord_6797269 prefixEnd_6797269 3490266134906071387477435 := by
  unfold tailWord_6797269
  simp only [CollatzResearch.WordTrace]
  refine ⟨247916767611662768967842861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165277845074441845978561907 247916767611662768967842861)
  ·
    refine ⟨92968787854373538362941073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247916767611662768967842861 92968787854373538362941073)
    ·
      refine ⟨69726590890780153772205805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92968787854373538362941073 69726590890780153772205805)
      ·
        refine ⟨26147471584042557664577177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69726590890780153772205805 26147471584042557664577177)
        ·
          refine ⟨19610603688031918248432883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26147471584042557664577177 19610603688031918248432883)
          ·
            refine ⟨29415905532047877372649325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19610603688031918248432883 29415905532047877372649325)
            ·
              refine ⟨11030964574517954014743497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29415905532047877372649325 11030964574517954014743497)
              ·
                refine ⟨8273223430888465511057623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11030964574517954014743497 8273223430888465511057623)
                ·
                  refine ⟨12409835146332698266586435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8273223430888465511057623 12409835146332698266586435)
                  ·
                    refine ⟨18614752719499047399879653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12409835146332698266586435 18614752719499047399879653)
                    ·
                      refine ⟨3490266134906071387477435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18614752719499047399879653 3490266134906071387477435)
                      ·
                        rfl

theorem cell23_6797269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6797269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797269 prefixEnd_6797269 := by exact prefixLift 6797269
  have htrace : WordTrace (prefixWord ++ tailWord_6797269) baseStart_6797269 baseEnd_6797269 := by
    simpa [prefixWord, tailWord_6797269, baseEnd_6797269] using wordTrace_append hprefix tailTrace_6797269
  have hstable : (prefixWord ++ tailWord_6797269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797269).length < 2 ^ (prefixWord ++ tailWord_6797269).sum := by decide
  have hdescent : baseEnd_6797269 < baseStart_6797269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797272 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_6797272 : Nat := 118140960795 + 6797272 * 2 ^ 59
def prefixEnd_6797272 : Nat := 4983230072969 + 3 ^ 40 * 6797272 * 2
def baseEnd_6797272 : Nat := 3490267675348034875739921

theorem tailTrace_6797272 : CollatzResearch.WordTrace tailWord_6797272 prefixEnd_6797272 3490267675348034875739921 := by
  unfold tailWord_6797272
  simp only [CollatzResearch.WordTrace]
  refine ⟨123958438515325950240101035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165277918020434600320134713 123958438515325950240101035)
  ·
    refine ⟨185937657772988925360151553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123958438515325950240101035 185937657772988925360151553)
    ·
      refine ⟨139453243329741694020113665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185937657772988925360151553 139453243329741694020113665)
      ·
        refine ⟨104589932497306270515085249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139453243329741694020113665 104589932497306270515085249)
        ·
          refine ⟨78442449372979702886313937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104589932497306270515085249 78442449372979702886313937)
          ·
            refine ⟨58831837029734777164735453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78442449372979702886313937 58831837029734777164735453)
            ·
              refine ⟨22061938886150541436775795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58831837029734777164735453 22061938886150541436775795)
              ·
                refine ⟨33092908329225812155163693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22061938886150541436775795 33092908329225812155163693)
                ·
                  refine ⟨12409840623459679558186385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33092908329225812155163693 12409840623459679558186385)
                  ·
                    refine ⟨9307380467594759668639789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12409840623459679558186385 9307380467594759668639789)
                    ·
                      refine ⟨3490267675348034875739921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9307380467594759668639789 3490267675348034875739921)
                      ·
                        rfl

theorem cell23_6797272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_6797272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797272 prefixEnd_6797272 := by exact prefixLift 6797272
  have htrace : WordTrace (prefixWord ++ tailWord_6797272) baseStart_6797272 baseEnd_6797272 := by
    simpa [prefixWord, tailWord_6797272, baseEnd_6797272] using wordTrace_append hprefix tailTrace_6797272
  have hstable : (prefixWord ++ tailWord_6797272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797272).length < 2 ^ (prefixWord ++ tailWord_6797272).sum := by decide
  have hdescent : baseEnd_6797272 < baseStart_6797272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797305 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 2, 7]
def baseStart_6797305 : Nat := 118140960795 + 6797305 * 2 ^ 59
def prefixEnd_6797305 : Nat := 4983230072969 + 3 ^ 40 * 6797305 * 2
def baseEnd_6797305 : Nat := 1163428206736544415542423

theorem tailTrace_6797305 : CollatzResearch.WordTrace tailWord_6797305 prefixEnd_6797305 1163428206736544415542423 := by
  unfold tailWord_6797305
  simp only [CollatzResearch.WordTrace]
  refine ⟨247918080639532347116153369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165278720426354898077435579 247918080639532347116153369)
  ·
    refine ⟨185938560479649260337115027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247918080639532347116153369 185938560479649260337115027)
    ·
      refine ⟨278907840719473890505672541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185938560479649260337115027 278907840719473890505672541)
      ·
        refine ⟨104590440269802708939627203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278907840719473890505672541 104590440269802708939627203)
        ·
          refine ⟨156885660404704063409440805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104590440269802708939627203 156885660404704063409440805)
          ·
            refine ⟨29416061325882011889270151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156885660404704063409440805 29416061325882011889270151)
            ·
              refine ⟨44124091988823017833905227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29416061325882011889270151 44124091988823017833905227)
              ·
                refine ⟨66186137983234526750857841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44124091988823017833905227 66186137983234526750857841)
                ·
                  refine ⟨49639603487425895063143381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66186137983234526750857841 49639603487425895063143381)
                  ·
                    refine ⟨1163428206736544415542423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49639603487425895063143381 1163428206736544415542423)
                    ·
                      rfl

theorem cell23_6797305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_6797305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797305 prefixEnd_6797305 := by exact prefixLift 6797305
  have htrace : WordTrace (prefixWord ++ tailWord_6797305) baseStart_6797305 baseEnd_6797305 := by
    simpa [prefixWord, tailWord_6797305, baseEnd_6797305] using wordTrace_append hprefix tailTrace_6797305
  have hstable : (prefixWord ++ tailWord_6797305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797305).length < 2 ^ (prefixWord ++ tailWord_6797305).sum := by decide
  have hdescent : baseEnd_6797305 < baseStart_6797305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797316 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6797316 : Nat := 118140960795 + 6797316 * 2 ^ 59
def prefixEnd_6797316 : Nat := 4983230072969 + 3 ^ 40 * 6797316 * 2
def baseEnd_6797316 : Nat := 3490290268496832703589719

theorem tailTrace_6797316 : CollatzResearch.WordTrace tailWord_6797316 prefixEnd_6797316 3490290268496832703589719 := by
  unfold tailWord_6797316
  simp only [CollatzResearch.WordTrace]
  refine ⟨123959240921246247997401901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165278987894994997329869201 123959240921246247997401901)
  ·
    refine ⟨46484715345467342999025713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123959240921246247997401901 46484715345467342999025713)
    ·
      refine ⟨34863536509100507249269285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46484715345467342999025713 34863536509100507249269285)
      ·
        refine ⟨6536913095456345109237991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34863536509100507249269285 6536913095456345109237991)
        ·
          refine ⟨9805369643184517663856987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6536913095456345109237991 9805369643184517663856987)
          ·
            refine ⟨14708054464776776495785481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9805369643184517663856987 14708054464776776495785481)
            ·
              refine ⟨11031040848582582371839111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14708054464776776495785481 11031040848582582371839111)
              ·
                refine ⟨16546561272873873557758667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031040848582582371839111 16546561272873873557758667)
                ·
                  refine ⟨24819841909310810336638001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16546561272873873557758667 24819841909310810336638001)
                  ·
                    refine ⟨18614881431983107752478501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24819841909310810336638001 18614881431983107752478501)
                    ·
                      refine ⟨3490290268496832703589719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18614881431983107752478501 3490290268496832703589719)
                      ·
                        rfl

theorem cell23_6797316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6797316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797316 prefixEnd_6797316 := by exact prefixLift 6797316
  have htrace : WordTrace (prefixWord ++ tailWord_6797316) baseStart_6797316 baseEnd_6797316 := by
    simpa [prefixWord, tailWord_6797316, baseEnd_6797316] using wordTrace_append hprefix tailTrace_6797316
  have hstable : (prefixWord ++ tailWord_6797316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797316).length < 2 ^ (prefixWord ++ tailWord_6797316).sum := by decide
  have hdescent : baseEnd_6797316 < baseStart_6797316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797319 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_6797319 : Nat := 118140960795 + 6797319 * 2 ^ 59
def prefixEnd_6797319 : Nat := 4983230072969 + 3 ^ 40 * 6797319 * 2
def baseEnd_6797319 : Nat := 3490291808938796191852205

theorem tailTrace_6797319 : CollatzResearch.WordTrace tailWord_6797319 prefixEnd_6797319 3490291808938796191852205 := by
  unfold tailWord_6797319
  simp only [CollatzResearch.WordTrace]
  refine ⟨247918591261481627507163011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165279060840987751671442007 247918591261481627507163011)
  ·
    refine ⟨371877886892222441260744517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247918591261481627507163011 371877886892222441260744517)
    ·
      refine ⟨69727103792291707736389597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371877886892222441260744517 69727103792291707736389597)
      ·
        refine ⟨26147663922109390401146099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69727103792291707736389597 26147663922109390401146099)
        ·
          refine ⟨39221495883164085601719149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26147663922109390401146099 39221495883164085601719149)
          ·
            refine ⟨14708060956186532100644681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39221495883164085601719149 14708060956186532100644681)
            ·
              refine ⟨11031045717139899075483511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14708060956186532100644681 11031045717139899075483511)
              ·
                refine ⟨16546568575709848613225267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031045717139899075483511 16546568575709848613225267)
                ·
                  refine ⟨24819852863564772919837901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16546568575709848613225267 24819852863564772919837901)
                  ·
                    refine ⟨9307444823836789844939213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24819852863564772919837901 9307444823836789844939213)
                    ·
                      refine ⟨3490291808938796191852205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9307444823836789844939213 3490291808938796191852205)
                      ·
                        rfl

theorem cell23_6797319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_6797319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797319 prefixEnd_6797319 := by exact prefixLift 6797319
  have htrace : WordTrace (prefixWord ++ tailWord_6797319) baseStart_6797319 baseEnd_6797319 := by
    simpa [prefixWord, tailWord_6797319, baseEnd_6797319] using wordTrace_append hprefix tailTrace_6797319
  have hstable : (prefixWord ++ tailWord_6797319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797319).length < 2 ^ (prefixWord ++ tailWord_6797319).sum := by decide
  have hdescent : baseEnd_6797319 < baseStart_6797319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797346 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_6797346 : Nat := 118140960795 + 6797346 * 2 ^ 59
def prefixEnd_6797346 : Nat := 4983230072969 + 3 ^ 40 * 6797346 * 2
def baseEnd_6797346 : Nat := 3490305672916467586214581

theorem tailTrace_6797346 : CollatzResearch.WordTrace tailWord_6797346 prefixEnd_6797346 3490305672916467586214581 := by
  unfold tailWord_6797346
  simp only [CollatzResearch.WordTrace]
  refine ⟨61979894008095952779598973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165279717354922540745597261 61979894008095952779598973)
  ·
    refine ⟨23242460253035982292349615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61979894008095952779598973 23242460253035982292349615)
    ·
      refine ⟨34863690379553973438524423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23242460253035982292349615 34863690379553973438524423)
      ·
        refine ⟨52295535569330960157786635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34863690379553973438524423 52295535569330960157786635)
        ·
          refine ⟨78443303353996440236679953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52295535569330960157786635 78443303353996440236679953)
          ·
            refine ⟨58832477515497330177509965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78443303353996440236679953 58832477515497330177509965)
            ·
              refine ⟨22062179068311498816566237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58832477515497330177509965 22062179068311498816566237)
              ·
                refine ⟨8273317150616812056212339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22062179068311498816566237 8273317150616812056212339)
                ·
                  refine ⟨12409975725925218084318509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8273317150616812056212339 12409975725925218084318509)
                  ·
                    refine ⟨4653740897221956781619441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12409975725925218084318509 4653740897221956781619441)
                    ·
                      refine ⟨3490305672916467586214581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653740897221956781619441 3490305672916467586214581)
                      ·
                        rfl

theorem cell23_6797346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_6797346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797346 prefixEnd_6797346 := by exact prefixLift 6797346
  have htrace : WordTrace (prefixWord ++ tailWord_6797346) baseStart_6797346 baseEnd_6797346 := by
    simpa [prefixWord, tailWord_6797346, baseEnd_6797346] using wordTrace_append hprefix tailTrace_6797346
  have hstable : (prefixWord ++ tailWord_6797346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797346).length < 2 ^ (prefixWord ++ tailWord_6797346).sum := by decide
  have hdescent : baseEnd_6797346 < baseStart_6797346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797372 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_6797372 : Nat := 118140960795 + 6797372 * 2 ^ 59
def prefixEnd_6797372 : Nat := 4983230072969 + 3 ^ 40 * 6797372 * 2
def baseEnd_6797372 : Nat := 3490319023413484484489461

theorem tailTrace_6797372 : CollatzResearch.WordTrace tailWord_6797372 prefixEnd_6797372 3490319023413484484489461 := by
  unfold tailWord_6797372
  simp only [CollatzResearch.WordTrace]
  refine ⟨123960262165144808779421185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165280349553526411705894913 123960262165144808779421185)
  ·
    refine ⟨92970196623858606584565889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123960262165144808779421185 92970196623858606584565889)
    ·
      refine ⟨69727647467893954938424417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92970196623858606584565889 69727647467893954938424417)
      ·
        refine ⟨52295735600920466203818313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69727647467893954938424417 52295735600920466203818313)
        ·
          refine ⟨39221801700690349652863735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52295735600920466203818313 39221801700690349652863735)
          ·
            refine ⟨58832702551035524479295603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39221801700690349652863735 58832702551035524479295603)
            ·
              refine ⟨88249053826553286718943405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58832702551035524479295603 88249053826553286718943405)
              ·
                refine ⟨33093395184957482519603777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88249053826553286718943405 33093395184957482519603777)
                ·
                  refine ⟨24820046388718111889702833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33093395184957482519603777 24820046388718111889702833)
                  ·
                    refine ⟨18615034791538583917277125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24820046388718111889702833 18615034791538583917277125)
                    ·
                      refine ⟨3490319023413484484489461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18615034791538583917277125 3490319023413484484489461)
                      ·
                        rfl

theorem cell23_6797372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_6797372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797372 prefixEnd_6797372 := by exact prefixLift 6797372
  have htrace : WordTrace (prefixWord ++ tailWord_6797372) baseStart_6797372 baseEnd_6797372 := by
    simpa [prefixWord, tailWord_6797372, baseEnd_6797372] using wordTrace_append hprefix tailTrace_6797372
  have hstable : (prefixWord ++ tailWord_6797372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797372).length < 2 ^ (prefixWord ++ tailWord_6797372).sum := by decide
  have hdescent : baseEnd_6797372 < baseStart_6797372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797376 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 1, 4, 2]
def baseStart_6797376 : Nat := 118140960795 + 6797376 * 2 ^ 59
def prefixEnd_6797376 : Nat := 4983230072969 + 3 ^ 40 * 6797376 * 2
def baseEnd_6797376 : Nat := 3490321077336102468839443

theorem tailTrace_6797376 : CollatzResearch.WordTrace tailWord_6797376 prefixEnd_6797376 3490321077336102468839443 := by
  unfold tailWord_6797376
  simp only [CollatzResearch.WordTrace]
  refine ⟨123960335111137563120993991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165280446814850084161325321 123960335111137563120993991)
  ·
    refine ⟨185940502666706344681490987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123960335111137563120993991 185940502666706344681490987)
    ·
      refine ⟨278910754000059517022236481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185940502666706344681490987 278910754000059517022236481)
      ·
        refine ⟨209183065500044637766677361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278910754000059517022236481 209183065500044637766677361)
        ·
          refine ⟨156887299125033478325008021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209183065500044637766677361 156887299125033478325008021)
          ·
            refine ⟨7354092146485944296484751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156887299125033478325008021 7354092146485944296484751)
            ·
              refine ⟨11031138219728916444727127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7354092146485944296484751 11031138219728916444727127)
              ·
                refine ⟨16546707329593374667090691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031138219728916444727127 16546707329593374667090691)
                ·
                  refine ⟨24820060994390062000636037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16546707329593374667090691 24820060994390062000636037)
                  ·
                    refine ⟨4653761436448136625119257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24820060994390062000636037 4653761436448136625119257)
                    ·
                      refine ⟨3490321077336102468839443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653761436448136625119257 3490321077336102468839443)
                      ·
                        rfl

theorem cell23_6797376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_6797376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797376 prefixEnd_6797376 := by exact prefixLift 6797376
  have htrace : WordTrace (prefixWord ++ tailWord_6797376) baseStart_6797376 baseEnd_6797376 := by
    simpa [prefixWord, tailWord_6797376, baseEnd_6797376] using wordTrace_append hprefix tailTrace_6797376
  have hstable : (prefixWord ++ tailWord_6797376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797376).length < 2 ^ (prefixWord ++ tailWord_6797376).sum := by decide
  have hdescent : baseEnd_6797376 < baseStart_6797376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797395 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 5, 7]
def baseStart_6797395 : Nat := 118140960795 + 6797395 * 2 ^ 59
def prefixEnd_6797395 : Nat := 4983230072969 + 3 ^ 40 * 6797395 * 2
def baseEnd_6797395 : Nat := 1163443611156179298167285

theorem tailTrace_6797395 : CollatzResearch.WordTrace tailWord_6797395 prefixEnd_6797395 1163443611156179298167285 := by
  unfold tailWord_6797395
  simp only [CollatzResearch.WordTrace]
  refine ⟨247921363209206292486929639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165280908806137528324619759 247921363209206292486929639)
  ·
    refine ⟨371882044813809438730394459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247921363209206292486929639 371882044813809438730394459)
    ·
      refine ⟨557823067220714158095591689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371882044813809438730394459 557823067220714158095591689)
      ·
        refine ⟨418367300415535618571693767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557823067220714158095591689 418367300415535618571693767)
        ·
          refine ⟨627550950623303427857540651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418367300415535618571693767 627550950623303427857540651)
          ·
            refine ⟨941326425934955141786310977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627550950623303427857540651 941326425934955141786310977)
            ·
              refine ⟨705994819451216356339733233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941326425934955141786310977 705994819451216356339733233)
              ·
                refine ⟨529496114588412267254799925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705994819451216356339733233 529496114588412267254799925)
                ·
                  refine ⟨49640260742663650055137493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 529496114588412267254799925 49640260742663650055137493)
                  ·
                    refine ⟨1163443611156179298167285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49640260742663650055137493 1163443611156179298167285)
                    ·
                      rfl

theorem cell23_6797395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 7].length) (baseStart_6797395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797395 prefixEnd_6797395 := by exact prefixLift 6797395
  have htrace : WordTrace (prefixWord ++ tailWord_6797395) baseStart_6797395 baseEnd_6797395 := by
    simpa [prefixWord, tailWord_6797395, baseEnd_6797395] using wordTrace_append hprefix tailTrace_6797395
  have hstable : (prefixWord ++ tailWord_6797395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797395).length < 2 ^ (prefixWord ++ tailWord_6797395).sum := by decide
  have hdescent : baseEnd_6797395 < baseStart_6797395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797399 : List Nat := [1, 1, 3, 2, 2, 1, 5, 3, 5]
def baseStart_6797399 : Nat := 118140960795 + 6797399 * 2 ^ 59
def prefixEnd_6797399 : Nat := 4983230072969 + 3 ^ 40 * 6797399 * 2
def baseEnd_6797399 : Nat := 387814765265683986539093

theorem tailTrace_6797399 : CollatzResearch.WordTrace tailWord_6797399 prefixEnd_6797399 387814765265683986539093 := by
  unfold tailWord_6797399
  simp only [CollatzResearch.WordTrace]
  refine ⟨247921509101191801170075251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165281006067461200780050167 247921509101191801170075251)
  ·
    refine ⟨371882263651787701755112877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247921509101191801170075251 371882263651787701755112877)
    ·
      refine ⟨139455848869420388158167329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371882263651787701755112877 139455848869420388158167329)
      ·
        refine ⟨104591886652065291118625497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139455848869420388158167329 104591886652065291118625497)
        ·
          refine ⟨78443914989048968338969123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104591886652065291118625497 78443914989048968338969123)
          ·
            refine ⟨117665872483573452508453685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78443914989048968338969123 117665872483573452508453685)
            ·
              refine ⟨11031175545335011172667533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117665872483573452508453685 11031175545335011172667533)
              ·
                refine ⟨4136690829500629189750325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11031175545335011172667533 4136690829500629189750325)
                ·
                  refine ⟨387814765265683986539093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4136690829500629189750325 387814765265683986539093)
                  ·
                    rfl

theorem cell23_6797399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 5].length) (baseStart_6797399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797399 prefixEnd_6797399 := by exact prefixLift 6797399
  have htrace : WordTrace (prefixWord ++ tailWord_6797399) baseStart_6797399 baseEnd_6797399 := by
    simpa [prefixWord, tailWord_6797399, baseEnd_6797399] using wordTrace_append hprefix tailTrace_6797399
  have hstable : (prefixWord ++ tailWord_6797399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797399).length < 2 ^ (prefixWord ++ tailWord_6797399).sum := by decide
  have hdescent : baseEnd_6797399 < baseStart_6797399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797412 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_6797412 : Nat := 118140960795 + 6797412 * 2 ^ 59
def prefixEnd_6797412 : Nat := 4983230072969 + 3 ^ 40 * 6797412 * 2
def baseEnd_6797412 : Nat := 1163446520879888109329759

theorem tailTrace_6797412 : CollatzResearch.WordTrace tailWord_6797412 prefixEnd_6797412 1163446520879888109329759 := by
  unfold tailWord_6797412
  simp only [CollatzResearch.WordTrace]
  refine ⟨123960991625072352195149245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165281322166763136260198993 123960991625072352195149245)
  ·
    refine ⟨46485371859402132073180967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123960991625072352195149245 46485371859402132073180967)
    ·
      refine ⟨69728057789103198109771451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46485371859402132073180967 69728057789103198109771451)
      ·
        refine ⟨104592086683654797164657177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69728057789103198109771451 104592086683654797164657177)
        ·
          refine ⟨78444065012741097873492883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104592086683654797164657177 78444065012741097873492883)
          ·
            refine ⟨117666097519111646810239325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78444065012741097873492883 117666097519111646810239325)
            ·
              refine ⟨44124786569666867553839747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117666097519111646810239325 44124786569666867553839747)
              ·
                refine ⟨66187179854500301330759621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44124786569666867553839747 66187179854500301330759621)
                ·
                  refine ⟨12410096222718806499517429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66187179854500301330759621 12410096222718806499517429)
                  ·
                    refine ⟨1163446520879888109329759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12410096222718806499517429 1163446520879888109329759)
                    ·
                      rfl

theorem cell23_6797412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_6797412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797412 prefixEnd_6797412 := by exact prefixLift 6797412
  have htrace : WordTrace (prefixWord ++ tailWord_6797412) baseStart_6797412 baseEnd_6797412 := by
    simpa [prefixWord, tailWord_6797412, baseEnd_6797412] using wordTrace_append hprefix tailTrace_6797412
  have hstable : (prefixWord ++ tailWord_6797412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797412).length < 2 ^ (prefixWord ++ tailWord_6797412).sum := by decide
  have hdescent : baseEnd_6797412 < baseStart_6797412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797432 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_6797432 : Nat := 118140960795 + 6797432 * 2 ^ 59
def prefixEnd_6797432 : Nat := 4983230072969 + 3 ^ 40 * 6797432 * 2
def baseEnd_6797432 : Nat := 3490349832252754249739185

theorem tailTrace_6797432 : CollatzResearch.WordTrace tailWord_6797432 prefixEnd_6797432 3490349832252754249739185 := by
  unfold tailWord_6797432
  simp only [CollatzResearch.WordTrace]
  refine ⟨123961356355036123903013275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165281808473381498537351033 123961356355036123903013275)
  ·
    refine ⟨185942034532554185854519913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123961356355036123903013275 185942034532554185854519913)
    ·
      refine ⟨139456525899415639390889935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185942034532554185854519913 139456525899415639390889935)
      ·
        refine ⟨209184788849123459086334903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139456525899415639390889935 209184788849123459086334903)
        ·
          refine ⟨313777183273685188629502355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209184788849123459086334903 313777183273685188629502355)
          ·
            refine ⟨470665774910527782944253533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313777183273685188629502355 470665774910527782944253533)
            ·
              refine ⟨176499665591447918604095075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470665774910527782944253533 176499665591447918604095075)
              ·
                refine ⟨264749498387171877906142613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176499665591447918604095075 264749498387171877906142613)
                ·
                  refine ⟨12410132736898681776850435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 264749498387171877906142613 12410132736898681776850435)
                  ·
                    refine ⟨18615199105348022665275653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12410132736898681776850435 18615199105348022665275653)
                    ·
                      refine ⟨3490349832252754249739185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18615199105348022665275653 3490349832252754249739185)
                      ·
                        rfl

theorem cell23_6797432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_6797432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797432 prefixEnd_6797432 := by exact prefixLift 6797432
  have htrace : WordTrace (prefixWord ++ tailWord_6797432) baseStart_6797432 baseEnd_6797432 := by
    simpa [prefixWord, tailWord_6797432, baseEnd_6797432] using wordTrace_append hprefix tailTrace_6797432
  have hstable : (prefixWord ++ tailWord_6797432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797432).length < 2 ^ (prefixWord ++ tailWord_6797432).sum := by decide
  have hdescent : baseEnd_6797432 < baseStart_6797432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797449 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 4]
def baseStart_6797449 : Nat := 118140960795 + 6797449 * 2 ^ 59
def prefixEnd_6797449 : Nat := 4983230072969 + 3 ^ 40 * 6797449 * 2
def baseEnd_6797449 : Nat := 3490358561423880683226607

theorem tailTrace_6797449 : CollatzResearch.WordTrace tailWord_6797449 prefixEnd_6797449 3490358561423880683226607 := by
  unfold tailWord_6797449
  simp only [CollatzResearch.WordTrace]
  refine ⟨247923332751010659709395401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165282221834007106472930267 247923332751010659709395401)
  ·
    refine ⟨185942499563257994782046551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247923332751010659709395401 185942499563257994782046551)
    ·
      refine ⟨278913749344886992173069827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185942499563257994782046551 278913749344886992173069827)
      ·
        refine ⟨418370624017330488259604741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278913749344886992173069827 418370624017330488259604741)
        ·
          refine ⟨78444492003249466548675889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418370624017330488259604741 78444492003249466548675889)
          ·
            refine ⟨58833369002437099911506917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78444492003249466548675889 58833369002437099911506917)
            ·
              refine ⟨11031256687956956233407547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58833369002437099911506917 11031256687956956233407547)
              ·
                refine ⟨16546885031935434350111321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031256687956956233407547 16546885031935434350111321)
                ·
                  refine ⟨12410163773951575762583491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16546885031935434350111321 12410163773951575762583491)
                  ·
                    refine ⟨18615245660927363643875237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12410163773951575762583491 18615245660927363643875237)
                    ·
                      refine ⟨3490358561423880683226607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18615245660927363643875237 3490358561423880683226607)
                      ·
                        rfl

theorem cell23_6797449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 1, 4].length) (baseStart_6797449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797449 prefixEnd_6797449 := by exact prefixLift 6797449
  have htrace : WordTrace (prefixWord ++ tailWord_6797449) baseStart_6797449 baseEnd_6797449 := by
    simpa [prefixWord, tailWord_6797449, baseEnd_6797449] using wordTrace_append hprefix tailTrace_6797449
  have hstable : (prefixWord ++ tailWord_6797449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797449).length < 2 ^ (prefixWord ++ tailWord_6797449).sum := by decide
  have hdescent : baseEnd_6797449 < baseStart_6797449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797493 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_6797493 : Nat := 118140960795 + 6797493 * 2 ^ 59
def prefixEnd_6797493 : Nat := 4983230072969 + 3 ^ 40 * 6797493 * 2
def baseEnd_6797493 : Nat := 1163460384857559503692135

theorem tailTrace_6797493 : CollatzResearch.WordTrace tailWord_6797493 prefixEnd_6797493 1163460384857559503692135 := by
  unfold tailWord_6797493
  simp only [CollatzResearch.WordTrace]
  refine ⟨247924937562851255223997133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165283291708567503482664755 247924937562851255223997133)
  ·
    refine ⟨92971851586069220708998925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247924937562851255223997133 92971851586069220708998925)
    ·
      refine ⟨34864444344775957765874597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92971851586069220708998925 34864444344775957765874597)
      ·
        refine ⟨6537083314645492081101487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34864444344775957765874597 6537083314645492081101487)
        ·
          refine ⟨9805624971968238121652231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537083314645492081101487 9805624971968238121652231)
          ·
            refine ⟨14708437457952357182478347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9805624971968238121652231 14708437457952357182478347)
            ·
              refine ⟨22062656186928535773717521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14708437457952357182478347 22062656186928535773717521)
              ·
                refine ⟨16546992140196401830288141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22062656186928535773717521 16546992140196401830288141)
                ·
                  refine ⟨6205122052573650686358053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16546992140196401830288141 6205122052573650686358053)
                  ·
                    refine ⟨1163460384857559503692135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205122052573650686358053 1163460384857559503692135)
                    ·
                      rfl

theorem cell23_6797493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_6797493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797493 prefixEnd_6797493 := by exact prefixLift 6797493
  have htrace : WordTrace (prefixWord ++ tailWord_6797493) baseStart_6797493 baseEnd_6797493 := by
    simpa [prefixWord, tailWord_6797493, baseEnd_6797493] using wordTrace_append hprefix tailTrace_6797493
  have hstable : (prefixWord ++ tailWord_6797493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797493).length < 2 ^ (prefixWord ++ tailWord_6797493).sum := by decide
  have hdescent : baseEnd_6797493 < baseStart_6797493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797512 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_6797512 : Nat := 118140960795 + 6797512 * 2 ^ 59
def prefixEnd_6797512 : Nat := 4983230072969 + 3 ^ 40 * 6797512 * 2
def baseEnd_6797512 : Nat := 3490390910705113936738817

theorem tailTrace_6797512 : CollatzResearch.WordTrace tailWord_6797512 prefixEnd_6797512 3490390910705113936738817 := by
  unfold tailWord_6797512
  simp only [CollatzResearch.WordTrace]
  refine ⟨123962815274891210734469395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165283753699854947645959193 123962815274891210734469395)
  ·
    refine ⟨185944222912336816101704093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123962815274891210734469395 185944222912336816101704093)
    ·
      refine ⟨69729083592126306038139035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185944222912336816101704093 69729083592126306038139035)
      ·
        refine ⟨104593625388189459057208553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69729083592126306038139035 104593625388189459057208553)
        ·
          refine ⟨78445219041142094292906415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104593625388189459057208553 78445219041142094292906415)
          ·
            refine ⟨117667828561713141439359623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78445219041142094292906415 117667828561713141439359623)
            ·
              refine ⟨176501742842569712159039435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117667828561713141439359623 176501742842569712159039435)
              ·
                refine ⟨264752614263854568238559153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176501742842569712159039435 264752614263854568238559153)
                ·
                  refine ⟨198564460697890926178919365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264752614263854568238559153 198564460697890926178919365)
                  ·
                    refine ⟨37230836380854548658547381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198564460697890926178919365 37230836380854548658547381)
                    ·
                      refine ⟨3490390910705113936738817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37230836380854548658547381 3490390910705113936738817)
                      ·
                        rfl

theorem cell23_6797512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_6797512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797512 prefixEnd_6797512 := by exact prefixLift 6797512
  have htrace : WordTrace (prefixWord ++ tailWord_6797512) baseStart_6797512 baseEnd_6797512 := by
    simpa [prefixWord, tailWord_6797512, baseEnd_6797512] using wordTrace_append hprefix tailTrace_6797512
  have hstable : (prefixWord ++ tailWord_6797512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797512).length < 2 ^ (prefixWord ++ tailWord_6797512).sum := by decide
  have hdescent : baseEnd_6797512 < baseStart_6797512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797519 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 1, 5]
def baseStart_6797519 : Nat := 118140960795 + 6797519 * 2 ^ 59
def prefixEnd_6797519 : Nat := 4983230072969 + 3 ^ 40 * 6797519 * 2
def baseEnd_6797519 : Nat := 1163464835023231803117095

theorem tailTrace_6797519 : CollatzResearch.WordTrace tailWord_6797519 prefixEnd_6797519 1163464835023231803117095 := by
  unfold tailWord_6797519
  simp only [CollatzResearch.WordTrace]
  refine ⟨247925885860757061664443611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165283923907171374442962407 247925885860757061664443611)
  ·
    refine ⟨371888828791135592496665417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247925885860757061664443611 371888828791135592496665417)
    ·
      refine ⟨278916621593351694372499063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371888828791135592496665417 278916621593351694372499063)
      ·
        refine ⟨418374932390027541558748595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278916621593351694372499063 418374932390027541558748595)
        ·
          refine ⟨627562398585041312338122893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418374932390027541558748595 627562398585041312338122893)
          ·
            refine ⟨235335899469390492126796085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 627562398585041312338122893 235335899469390492126796085)
            ·
              refine ⟨22062740575255358636887133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235335899469390492126796085 22062740575255358636887133)
              ·
                refine ⟨8273527715720759488832675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22062740575255358636887133 8273527715720759488832675)
                ·
                  refine ⟨12410291573581139233249013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8273527715720759488832675 12410291573581139233249013)
                  ·
                    refine ⟨1163464835023231803117095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12410291573581139233249013 1163464835023231803117095)
                    ·
                      rfl

theorem cell23_6797519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_6797519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797519 prefixEnd_6797519 := by exact prefixLift 6797519
  have htrace : WordTrace (prefixWord ++ tailWord_6797519) baseStart_6797519 baseEnd_6797519 := by
    simpa [prefixWord, tailWord_6797519, baseEnd_6797519] using wordTrace_append hprefix tailTrace_6797519
  have hstable : (prefixWord ++ tailWord_6797519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797519).length < 2 ^ (prefixWord ++ tailWord_6797519).sum := by decide
  have hdescent : baseEnd_6797519 < baseStart_6797519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797526 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6797526 : Nat := 118140960795 + 6797526 * 2 ^ 59
def prefixEnd_6797526 : Nat := 4983230072969 + 3 ^ 40 * 6797526 * 2
def baseEnd_6797526 : Nat := 3490398099434276881963753

theorem tailTrace_6797526 : CollatzResearch.WordTrace tailWord_6797526 prefixEnd_6797526 3490398099434276881963753 := by
  unfold tailWord_6797526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15495383823233231366246777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165284094114487801239965621 15495383823233231366246777)
  ·
    refine ⟨11621537867424923524685083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15495383823233231366246777 11621537867424923524685083)
    ·
      refine ⟨17432306801137385287027625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11621537867424923524685083 17432306801137385287027625)
      ·
        refine ⟨13074230100853038965270719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17432306801137385287027625 13074230100853038965270719)
        ·
          refine ⟨19611345151279558447906079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13074230100853038965270719 19611345151279558447906079)
          ·
            refine ⟨29417017726919337671859119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19611345151279558447906079 29417017726919337671859119)
            ·
              refine ⟨44125526590379006507788679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29417017726919337671859119 44125526590379006507788679)
              ·
                refine ⟨66188289885568509761683019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44125526590379006507788679 66188289885568509761683019)
                ·
                  refine ⟨99282434828352764642524529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66188289885568509761683019 99282434828352764642524529)
                  ·
                    refine ⟨74461826121264573481893397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99282434828352764642524529 74461826121264573481893397)
                    ·
                      refine ⟨3490398099434276881963753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74461826121264573481893397 3490398099434276881963753)
                      ·
                        rfl

theorem cell23_6797526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6797526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797526 prefixEnd_6797526 := by exact prefixLift 6797526
  have htrace : WordTrace (prefixWord ++ tailWord_6797526) baseStart_6797526 baseEnd_6797526 := by
    simpa [prefixWord, tailWord_6797526, baseEnd_6797526] using wordTrace_append hprefix tailTrace_6797526
  have hstable : (prefixWord ++ tailWord_6797526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797526).length < 2 ^ (prefixWord ++ tailWord_6797526).sum := by decide
  have hdescent : baseEnd_6797526 < baseStart_6797526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797533 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6797533 : Nat := 118140960795 + 6797533 * 2 ^ 59
def prefixEnd_6797533 : Nat := 4983230072969 + 3 ^ 40 * 6797533 * 2
def baseEnd_6797533 : Nat := 3490401693798858354576221

theorem tailTrace_6797533 : CollatzResearch.WordTrace tailWord_6797533 prefixEnd_6797533 3490401693798858354576221 := by
  unfold tailWord_6797533
  simp only [CollatzResearch.WordTrace]
  refine ⟨247926396482706342055453253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165284264321804228036968835 247926396482706342055453253)
  ·
    refine ⟨46486199340507439135397485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247926396482706342055453253 46486199340507439135397485)
    ·
      refine ⟨17432324752690289675774057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46486199340507439135397485 17432324752690289675774057)
      ·
        refine ⟨13074243564517717256830543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17432324752690289675774057 13074243564517717256830543)
        ·
          refine ⟨19611365346776575885245815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13074243564517717256830543 19611365346776575885245815)
          ·
            refine ⟨29417048020164863827868723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19611365346776575885245815 29417048020164863827868723)
            ·
              refine ⟨44125572030247295741803085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29417048020164863827868723 44125572030247295741803085)
              ·
                refine ⟨16547089511342735903176157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44125572030247295741803085 16547089511342735903176157)
                ·
                  refine ⟨6205158566753525963691059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16547089511342735903176157 6205158566753525963691059)
                  ·
                    refine ⟨9307737850130288945536589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6205158566753525963691059 9307737850130288945536589)
                    ·
                      refine ⟨3490401693798858354576221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9307737850130288945536589 3490401693798858354576221)
                      ·
                        rfl

theorem cell23_6797533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6797533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797533 prefixEnd_6797533 := by exact prefixLift 6797533
  have htrace : WordTrace (prefixWord ++ tailWord_6797533) baseStart_6797533 baseEnd_6797533 := by
    simpa [prefixWord, tailWord_6797533, baseEnd_6797533] using wordTrace_append hprefix tailTrace_6797533
  have hstable : (prefixWord ++ tailWord_6797533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797533).length < 2 ^ (prefixWord ++ tailWord_6797533).sum := by decide
  have hdescent : baseEnd_6797533 < baseStart_6797533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797566 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6797566 : Nat := 118140960795 + 6797566 * 2 ^ 59
def prefixEnd_6797566 : Nat := 4983230072969 + 3 ^ 40 * 6797566 * 2
def baseEnd_6797566 : Nat := 1163472879553485575154523

theorem tailTrace_6797566 : CollatzResearch.WordTrace tailWord_6797566 prefixEnd_6797566 1163472879553485575154523 := by
  unfold tailWord_6797566
  simp only [CollatzResearch.WordTrace]
  refine ⟨30990950011448348586425569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165285066727724525794269701 30990950011448348586425569)
  ·
    refine ⟨23243212508586261439819177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30990950011448348586425569 23243212508586261439819177)
    ·
      refine ⟨17432409381439696079864383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23243212508586261439819177 17432409381439696079864383)
      ·
        refine ⟨26148614072159544119796575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17432409381439696079864383 26148614072159544119796575)
        ·
          refine ⟨39222921108239316179694863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26148614072159544119796575 39222921108239316179694863)
          ·
            refine ⟨58834381662358974269542295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39222921108239316179694863 58834381662358974269542295)
            ·
              refine ⟨88251572493538461404313443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58834381662358974269542295 88251572493538461404313443)
              ·
                refine ⟨132377358740307692106470165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88251572493538461404313443 132377358740307692106470165)
                ·
                  refine ⟨6205188690951923067490789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132377358740307692106470165 6205188690951923067490789)
                  ·
                    refine ⟨1163472879553485575154523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205188690951923067490789 1163472879553485575154523)
                    ·
                      rfl

theorem cell23_6797566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6797566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797566 prefixEnd_6797566 := by exact prefixLift 6797566
  have htrace : WordTrace (prefixWord ++ tailWord_6797566) baseStart_6797566 baseEnd_6797566 := by
    simpa [prefixWord, tailWord_6797566, baseEnd_6797566] using wordTrace_append hprefix tailTrace_6797566
  have hstable : (prefixWord ++ tailWord_6797566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797566).length < 2 ^ (prefixWord ++ tailWord_6797566).sum := by decide
  have hdescent : baseEnd_6797566 < baseStart_6797566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797569 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_6797569 : Nat := 118140960795 + 6797569 * 2 ^ 59
def prefixEnd_6797569 : Nat := 4983230072969 + 3 ^ 40 * 6797569 * 2
def baseEnd_6797569 : Nat := 3490420179102420213726055

theorem tailTrace_6797569 : CollatzResearch.WordTrace tailWord_6797569 prefixEnd_6797569 3490420179102420213726055 := by
  unfold tailWord_6797569
  simp only [CollatzResearch.WordTrace]
  refine ⟨247927709510575920203763761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165285139673717280135842507 247927709510575920203763761)
  ·
    refine ⟨185945782132931940152822821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247927709510575920203763761 185945782132931940152822821)
    ·
      refine ⟨34864834149924738778654279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185945782132931940152822821 34864834149924738778654279)
      ·
        refine ⟨52297251224887108167981419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34864834149924738778654279 52297251224887108167981419)
        ·
          refine ⟨78445876837330662251972129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52297251224887108167981419 78445876837330662251972129)
          ·
            refine ⟨58834407627997996688979097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78445876837330662251972129 58834407627997996688979097)
            ·
              refine ⟨44125805720998497516734323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58834407627997996688979097 44125805720998497516734323)
              ·
                refine ⟨66188708581497746275101485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44125805720998497516734323 66188708581497746275101485)
                ·
                  refine ⟨24820765718061654853163057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66188708581497746275101485 24820765718061654853163057)
                  ·
                    refine ⟨18615574288546241139872293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24820765718061654853163057 18615574288546241139872293)
                    ·
                      refine ⟨3490420179102420213726055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18615574288546241139872293 3490420179102420213726055)
                      ·
                        rfl

theorem cell23_6797569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_6797569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797569 prefixEnd_6797569 := by exact prefixLift 6797569
  have htrace : WordTrace (prefixWord ++ tailWord_6797569) baseStart_6797569 baseEnd_6797569 := by
    simpa [prefixWord, tailWord_6797569, baseEnd_6797569] using wordTrace_append hprefix tailTrace_6797569
  have hstable : (prefixWord ++ tailWord_6797569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797569).length < 2 ^ (prefixWord ++ tailWord_6797569).sum := by decide
  have hdescent : baseEnd_6797569 < baseStart_6797569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797576 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_6797576 : Nat := 118140960795 + 6797576 * 2 ^ 59
def prefixEnd_6797576 : Nat := 4983230072969 + 3 ^ 40 * 6797576 * 2
def baseEnd_6797576 : Nat := 3490423773467001686338523

theorem tailTrace_6797576 : CollatzResearch.WordTrace tailWord_6797576 prefixEnd_6797576 3490423773467001686338523 := by
  unfold tailWord_6797576
  simp only [CollatzResearch.WordTrace]
  refine ⟨123963982410775280199634291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165285309881033706932845721 123963982410775280199634291)
  ·
    refine ⟨185945973616162920299451437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123963982410775280199634291 185945973616162920299451437)
    ·
      refine ⟨69729740106061095112294289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185945973616162920299451437 69729740106061095112294289)
      ·
        refine ⟨52297305079545821334220717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69729740106061095112294289 52297305079545821334220717)
        ·
          refine ⟨19611489404829683000332769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52297305079545821334220717 19611489404829683000332769)
          ·
            refine ⟨14708617053622262250249577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19611489404829683000332769 14708617053622262250249577)
            ·
              refine ⟨11031462790216696687687183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14708617053622262250249577 11031462790216696687687183)
              ·
                refine ⟨16547194185325045031530775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031462790216696687687183 16547194185325045031530775)
                ·
                  refine ⟨24820791277987567547296163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16547194185325045031530775 24820791277987567547296163)
                  ·
                    refine ⟨37231186916981351320944245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24820791277987567547296163 37231186916981351320944245)
                    ·
                      refine ⟨3490423773467001686338523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37231186916981351320944245 3490423773467001686338523)
                      ·
                        rfl

theorem cell23_6797576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_6797576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797576 prefixEnd_6797576 := by exact prefixLift 6797576
  have htrace : WordTrace (prefixWord ++ tailWord_6797576) baseStart_6797576 baseEnd_6797576 := by
    simpa [prefixWord, tailWord_6797576, baseEnd_6797576] using wordTrace_append hprefix tailTrace_6797576
  have hstable : (prefixWord ++ tailWord_6797576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797576).length < 2 ^ (prefixWord ++ tailWord_6797576).sum := by decide
  have hdescent : baseEnd_6797576 < baseStart_6797576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797600 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 2, 4]
def baseStart_6797600 : Nat := 118140960795 + 6797600 * 2 ^ 59
def prefixEnd_6797600 : Nat := 4983230072969 + 3 ^ 40 * 6797600 * 2
def baseEnd_6797600 : Nat := 1163478699000903197479471

theorem tailTrace_6797600 : CollatzResearch.WordTrace tailWord_6797600 prefixEnd_6797600 1163478699000903197479471 := by
  unfold tailWord_6797600
  simp only [CollatzResearch.WordTrace]
  refine ⟨123964420086731806249071127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165285893448975741665428169 123964420086731806249071127)
  ·
    refine ⟨185946630130097709373606691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123964420086731806249071127 185946630130097709373606691)
    ·
      refine ⟨278919945195146564060410037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185946630130097709373606691 278919945195146564060410037)
      ·
        refine ⟨26148744862044990380663441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278919945195146564060410037 26148744862044990380663441)
        ·
          refine ⟨19611558646533742785497581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26148744862044990380663441 19611558646533742785497581)
          ·
            refine ⟨7354334492450153544561593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19611558646533742785497581 7354334492450153544561593)
            ·
              refine ⟨5515750869337615158421195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7354334492450153544561593 5515750869337615158421195)
              ·
                refine ⟨8273626304006422737631793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5515750869337615158421195 8273626304006422737631793)
                ·
                  refine ⟨6205219728004817053223845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8273626304006422737631793 6205219728004817053223845)
                  ·
                    refine ⟨1163478699000903197479471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205219728004817053223845 1163478699000903197479471)
                    ·
                      rfl

theorem cell23_6797600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 4].length) (baseStart_6797600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797600 prefixEnd_6797600 := by exact prefixLift 6797600
  have htrace : WordTrace (prefixWord ++ tailWord_6797600) baseStart_6797600 baseEnd_6797600 := by
    simpa [prefixWord, tailWord_6797600, baseEnd_6797600] using wordTrace_append hprefix tailTrace_6797600
  have hstable : (prefixWord ++ tailWord_6797600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797600).length < 2 ^ (prefixWord ++ tailWord_6797600).sum := by decide
  have hdescent : baseEnd_6797600 < baseStart_6797600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797639 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 2, 6]
def baseStart_6797639 : Nat := 118140960795 + 6797639 * 2 ^ 59
def prefixEnd_6797639 : Nat := 4983230072969 + 3 ^ 40 * 6797639 * 2
def baseEnd_6797639 : Nat := 1163485374249411646616911

theorem tailTrace_6797639 : CollatzResearch.WordTrace tailWord_6797639 prefixEnd_6797639 1163485374249411646616911 := by
  unfold tailWord_6797639
  simp only [CollatzResearch.WordTrace]
  refine ⟨247930262620322322158811971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165286841746881548105874647 247930262620322322158811971)
  ·
    refine ⟨371895393930483483238217957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247930262620322322158811971 371895393930483483238217957)
    ·
      refine ⟨69730386361965653107165867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371895393930483483238217957 69730386361965653107165867)
      ·
        refine ⟨104595579542948479660748801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69730386361965653107165867 104595579542948479660748801)
        ·
          refine ⟨78446684657211359745561601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104595579542948479660748801 78446684657211359745561601)
          ·
            refine ⟨58835013492908519809171201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78446684657211359745561601 58835013492908519809171201)
            ·
              refine ⟨44126260119681389856878401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58835013492908519809171201 44126260119681389856878401)
              ·
                refine ⟨33094695089761042392658801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44126260119681389856878401 33094695089761042392658801)
                ·
                  refine ⟨24821021317320781794494101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33094695089761042392658801 24821021317320781794494101)
                  ·
                    refine ⟨1163485374249411646616911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24821021317320781794494101 1163485374249411646616911)
                    ·
                      rfl

theorem cell23_6797639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_6797639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797639 prefixEnd_6797639 := by exact prefixLift 6797639
  have htrace : WordTrace (prefixWord ++ tailWord_6797639) baseStart_6797639 baseEnd_6797639 := by
    simpa [prefixWord, tailWord_6797639, baseEnd_6797639] using wordTrace_append hprefix tailTrace_6797639
  have hstable : (prefixWord ++ tailWord_6797639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797639).length < 2 ^ (prefixWord ++ tailWord_6797639).sum := by decide
  have hdescent : baseEnd_6797639 < baseStart_6797639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797669 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 9]
def baseStart_6797669 : Nat := 118140960795 + 6797669 * 2 ^ 59
def prefixEnd_6797669 : Nat := 4983230072969 + 3 ^ 40 * 6797669 * 2
def baseEnd_6797669 : Nat := 387830169685318869163955

theorem tailTrace_6797669 : CollatzResearch.WordTrace tailWord_6797669 prefixEnd_6797669 387830169685318869163955 := by
  unfold tailWord_6797669
  simp only [CollatzResearch.WordTrace]
  refine ⟨247931356810213637282404061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165287571206809091521602707 247931356810213637282404061)
  ·
    refine ⟨92974258803830113980901523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247931356810213637282404061 92974258803830113980901523)
    ·
      refine ⟨139461388205745170971352285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92974258803830113980901523 139461388205745170971352285)
      ·
        refine ⟨52298020577154439114257107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139461388205745170971352285 52298020577154439114257107)
        ·
          refine ⟨78447030865731658671385661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52298020577154439114257107 78447030865731658671385661)
          ·
            refine ⟨29417636574649372001769623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78447030865731658671385661 29417636574649372001769623)
            ·
              refine ⟨44126454861974058002654435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29417636574649372001769623 44126454861974058002654435)
              ·
                refine ⟨66189682292961087003981653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44126454861974058002654435 66189682292961087003981653)
                ·
                  refine ⟨387830169685318869163955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66189682292961087003981653 387830169685318869163955)
                  ·
                    rfl

theorem cell23_6797669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_6797669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797669 prefixEnd_6797669 := by exact prefixLift 6797669
  have htrace : WordTrace (prefixWord ++ tailWord_6797669) baseStart_6797669 baseEnd_6797669 := by
    simpa [prefixWord, tailWord_6797669, baseEnd_6797669] using wordTrace_append hprefix tailTrace_6797669
  have hstable : (prefixWord ++ tailWord_6797669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797669).length < 2 ^ (prefixWord ++ tailWord_6797669).sum := by decide
  have hdescent : baseEnd_6797669 < baseStart_6797669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797697 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_6797697 : Nat := 118140960795 + 6797697 * 2 ^ 59
def prefixEnd_6797697 : Nat := 4983230072969 + 3 ^ 40 * 6797697 * 2
def baseEnd_6797697 : Nat := 3490485904626195712925467

theorem tailTrace_6797697 : CollatzResearch.WordTrace tailWord_6797697 prefixEnd_6797697 3490485904626195712925467 := by
  unfold tailWord_6797697
  simp only [CollatzResearch.WordTrace]
  refine ⟨247932378054112198064423345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165288252036074798709615563 247932378054112198064423345)
  ·
    refine ⟨185949283540584148548317509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247932378054112198064423345 185949283540584148548317509)
    ·
      refine ⟨34865490663859527852809533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185949283540584148548317509 34865490663859527852809533)
      ·
        refine ⟨13074558998947322944803575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34865490663859527852809533 13074558998947322944803575)
        ·
          refine ⟨19611838498420984417205363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13074558998947322944803575 19611838498420984417205363)
          ·
            refine ⟨29417757747631476625808045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19611838498420984417205363 29417757747631476625808045)
            ·
              refine ⟨11031659155361803734678017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29417757747631476625808045 11031659155361803734678017)
              ·
                refine ⟨8273744366521352801008513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11031659155361803734678017 8273744366521352801008513)
                ·
                  refine ⟨6205308274891014600756385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8273744366521352801008513 6205308274891014600756385)
                  ·
                    refine ⟨4653981206168260950567289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6205308274891014600756385 4653981206168260950567289)
                    ·
                      refine ⟨3490485904626195712925467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4653981206168260950567289 3490485904626195712925467)
                      ·
                        rfl

theorem cell23_6797697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_6797697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797697 prefixEnd_6797697 := by exact prefixLift 6797697
  have htrace : WordTrace (prefixWord ++ tailWord_6797697) baseStart_6797697 baseEnd_6797697 := by
    simpa [prefixWord, tailWord_6797697, baseEnd_6797697] using wordTrace_append hprefix tailTrace_6797697
  have hstable : (prefixWord ++ tailWord_6797697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797697).length < 2 ^ (prefixWord ++ tailWord_6797697).sum := by decide
  have hdescent : baseEnd_6797697 < baseStart_6797697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797753 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6797753 : Nat := 118140960795 + 6797753 * 2 ^ 59
def prefixEnd_6797753 : Nat := 4983230072969 + 3 ^ 40 * 6797753 * 2
def baseEnd_6797753 : Nat := 3490514659542847493825209

theorem tailTrace_6797753 : CollatzResearch.WordTrace tailWord_6797753 prefixEnd_6797753 3490514659542847493825209 := by
  unfold tailWord_6797753
  simp only [CollatzResearch.WordTrace]
  refine ⟨247934420541909319628461913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165289613694606213085641275 247934420541909319628461913)
  ·
    refine ⟨185950815406431989721346435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247934420541909319628461913 185950815406431989721346435)
    ·
      refine ⟨278926223109647984582019653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185950815406431989721346435 278926223109647984582019653)
      ·
        refine ⟨52298666833058997109128685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278926223109647984582019653 52298666833058997109128685)
        ·
          refine ⟨19612000062397123915923257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52298666833058997109128685 19612000062397123915923257)
          ·
            refine ⟨14709000046797842936942443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19612000062397123915923257 14709000046797842936942443)
            ·
              refine ⟨22063500070196764405413665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14709000046797842936942443 22063500070196764405413665)
              ·
                refine ⟨16547625052647573304060249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22063500070196764405413665 16547625052647573304060249)
                ·
                  refine ⟨12410718789485679978045187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16547625052647573304060249 12410718789485679978045187)
                  ·
                    refine ⟨18616078184228519967067781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12410718789485679978045187 18616078184228519967067781)
                    ·
                      refine ⟨3490514659542847493825209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18616078184228519967067781 3490514659542847493825209)
                      ·
                        rfl

theorem cell23_6797753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6797753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797753 prefixEnd_6797753 := by exact prefixLift 6797753
  have htrace : WordTrace (prefixWord ++ tailWord_6797753) baseStart_6797753 baseEnd_6797753 := by
    simpa [prefixWord, tailWord_6797753, baseEnd_6797753] using wordTrace_append hprefix tailTrace_6797753
  have hstable : (prefixWord ++ tailWord_6797753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797753).length < 2 ^ (prefixWord ++ tailWord_6797753).sum := by decide
  have hdescent : baseEnd_6797753 < baseStart_6797753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797779 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8]
def baseStart_6797779 : Nat := 118140960795 + 6797779 * 2 ^ 59
def prefixEnd_6797779 : Nat := 4983230072969 + 3 ^ 40 * 6797779 * 2
def baseEnd_6797779 : Nat := 3490528010039864392100089

theorem tailTrace_6797779 : CollatzResearch.WordTrace tailWord_6797779 prefixEnd_6797779 3490528010039864392100089 := by
  unfold tailWord_6797779
  simp only [CollatzResearch.WordTrace]
  refine ⟨247935368839815126068908391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165290245893210084045938927 247935368839815126068908391)
  ·
    refine ⟨371903053259722689103362587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247935368839815126068908391 371903053259722689103362587)
    ·
      refine ⟨557854579889584033655043881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371903053259722689103362587 557854579889584033655043881)
      ·
        refine ⟨418390934917188025241282911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557854579889584033655043881 418390934917188025241282911)
        ·
          refine ⟨627586402375782037861924367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418390934917188025241282911 627586402375782037861924367)
          ·
            refine ⟨941379603563673056792886551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627586402375782037861924367 941379603563673056792886551)
            ·
              refine ⟨1412069405345509585189329827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941379603563673056792886551 1412069405345509585189329827)
              ·
                refine ⟨2118104108018264377783994741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412069405345509585189329827 2118104108018264377783994741)
                ·
                  refine ⟨198572260126712285417249507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2118104108018264377783994741 198572260126712285417249507)
                  ·
                    refine ⟨297858390190068428125874261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198572260126712285417249507 297858390190068428125874261)
                    ·
                      refine ⟨3490528010039864392100089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 297858390190068428125874261 3490528010039864392100089)
                      ·
                        rfl

theorem cell23_6797779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_6797779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797779 prefixEnd_6797779 := by exact prefixLift 6797779
  have htrace : WordTrace (prefixWord ++ tailWord_6797779) baseStart_6797779 baseEnd_6797779 := by
    simpa [prefixWord, tailWord_6797779, baseEnd_6797779] using wordTrace_append hprefix tailTrace_6797779
  have hstable : (prefixWord ++ tailWord_6797779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797779).length < 2 ^ (prefixWord ++ tailWord_6797779).sum := by decide
  have hdescent : baseEnd_6797779 < baseStart_6797779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797810 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 6]
def baseStart_6797810 : Nat := 118140960795 + 6797810 * 2 ^ 59
def prefixEnd_6797810 : Nat := 4983230072969 + 3 ^ 40 * 6797810 * 2
def baseEnd_6797810 : Nat := 387838214215572641201383

theorem tailTrace_6797810 : CollatzResearch.WordTrace tailWord_6797810 prefixEnd_6797810 387838214215572641201383 := by
  unfold tailWord_6797810
  simp only [CollatzResearch.WordTrace]
  refine ⟨61984124875675704590821721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165290999668468545575524589 61984124875675704590821721)
  ·
    refine ⟨46488093656756778443116291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61984124875675704590821721 46488093656756778443116291)
    ·
      refine ⟨69732140485135167664674437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46488093656756778443116291 69732140485135167664674437)
      ·
        refine ⟨13074776340962843937126457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69732140485135167664674437 13074776340962843937126457)
        ·
          refine ⟨9806082255722132952844843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13074776340962843937126457 9806082255722132952844843)
          ·
            refine ⟨14709123383583199429267265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806082255722132952844843 14709123383583199429267265)
            ·
              refine ⟨11031842537687399571950449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14709123383583199429267265 11031842537687399571950449)
              ·
                refine ⟨8273881903265549678962837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11031842537687399571950449 8273881903265549678962837)
                ·
                  refine ⟨387838214215572641201383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8273881903265549678962837 387838214215572641201383)
                  ·
                    rfl

theorem cell23_6797810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_6797810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797810 prefixEnd_6797810 := by exact prefixLift 6797810
  have htrace : WordTrace (prefixWord ++ tailWord_6797810) baseStart_6797810 baseEnd_6797810 := by
    simpa [prefixWord, tailWord_6797810, baseEnd_6797810] using wordTrace_append hprefix tailTrace_6797810
  have hstable : (prefixWord ++ tailWord_6797810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797810).length < 2 ^ (prefixWord ++ tailWord_6797810).sum := by decide
  have hdescent : baseEnd_6797810 < baseStart_6797810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797843 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 4]
def baseStart_6797843 : Nat := 118140960795 + 6797843 * 2 ^ 59
def prefixEnd_6797843 : Nat := 4983230072969 + 3 ^ 40 * 6797843 * 2
def baseEnd_6797843 : Nat := 3490560872801752141699795

theorem tailTrace_6797843 : CollatzResearch.WordTrace tailWord_6797843 prefixEnd_6797843 3490560872801752141699795 := by
  unfold tailWord_6797843
  simp only [CollatzResearch.WordTrace]
  refine ⟨247937703111583264999238183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165291802074388843332825455 247937703111583264999238183)
  ·
    refine ⟨371906554667374897498857275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247937703111583264999238183 371906554667374897498857275)
    ·
      refine ⟨557859832001062346248285913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371906554667374897498857275 557859832001062346248285913)
      ·
        refine ⟨418394874000796759686214435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557859832001062346248285913 418394874000796759686214435)
        ·
          refine ⟨627592311001195139529321653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418394874000796759686214435 627592311001195139529321653)
          ·
            refine ⟨58836779156362044330873905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 627592311001195139529321653 58836779156362044330873905)
            ·
              refine ⟨44127584367271533248155429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58836779156362044330873905 44127584367271533248155429)
              ·
                refine ⟨8273922068863412484029143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44127584367271533248155429 8273922068863412484029143)
                ·
                  refine ⟨12410883103295118726043715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8273922068863412484029143 12410883103295118726043715)
                  ·
                    refine ⟨18616324654942678089065573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12410883103295118726043715 18616324654942678089065573)
                    ·
                      refine ⟨3490560872801752141699795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18616324654942678089065573 3490560872801752141699795)
                      ·
                        rfl

theorem cell23_6797843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_6797843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797843 prefixEnd_6797843 := by exact prefixLift 6797843
  have htrace : WordTrace (prefixWord ++ tailWord_6797843) baseStart_6797843 baseEnd_6797843 := by
    simpa [prefixWord, tailWord_6797843, baseEnd_6797843] using wordTrace_append hprefix tailTrace_6797843
  have hstable : (prefixWord ++ tailWord_6797843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797843).length < 2 ^ (prefixWord ++ tailWord_6797843).sum := by decide
  have hdescent : baseEnd_6797843 < baseStart_6797843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797847 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6797847 : Nat := 118140960795 + 6797847 * 2 ^ 59
def prefixEnd_6797847 : Nat := 4983230072969 + 3 ^ 40 * 6797847 * 2
def baseEnd_6797847 : Nat := 3490562926724370126049777

theorem tailTrace_6797847 : CollatzResearch.WordTrace tailWord_6797847 prefixEnd_6797847 3490562926724370126049777 := by
  unfold tailWord_6797847
  simp only [CollatzResearch.WordTrace]
  refine ⟨247937849003568773682383795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165291899335712515788255863 247937849003568773682383795)
  ·
    refine ⟨371906773505353160523575693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247937849003568773682383795 371906773505353160523575693)
    ·
      refine ⟨139465040064507435196340885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371906773505353160523575693 139465040064507435196340885)
      ·
        refine ⟨6537423753023786024828479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139465040064507435196340885 6537423753023786024828479)
        ·
          refine ⟨9806135629535679037242719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537423753023786024828479 9806135629535679037242719)
          ·
            refine ⟨14709203444303518555864079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806135629535679037242719 14709203444303518555864079)
            ·
              refine ⟨22063805166455277833796119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14709203444303518555864079 22063805166455277833796119)
              ·
                refine ⟨33095707749682916750694179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22063805166455277833796119 33095707749682916750694179)
                ·
                  refine ⟨49643561624524375126041269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33095707749682916750694179 49643561624524375126041269)
                  ·
                    refine ⟨4654083902299160168066369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49643561624524375126041269 4654083902299160168066369)
                    ·
                      refine ⟨3490562926724370126049777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654083902299160168066369 3490562926724370126049777)
                      ·
                        rfl

theorem cell23_6797847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6797847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797847 prefixEnd_6797847 := by exact prefixLift 6797847
  have htrace : WordTrace (prefixWord ++ tailWord_6797847) baseStart_6797847 baseEnd_6797847 := by
    simpa [prefixWord, tailWord_6797847, baseEnd_6797847] using wordTrace_append hprefix tailTrace_6797847
  have hstable : (prefixWord ++ tailWord_6797847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797847).length < 2 ^ (prefixWord ++ tailWord_6797847).sum := by decide
  have hdescent : baseEnd_6797847 < baseStart_6797847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797853 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6797853 : Nat := 118140960795 + 6797853 * 2 ^ 59
def prefixEnd_6797853 : Nat := 4983230072969 + 3 ^ 40 * 6797853 * 2
def baseEnd_6797853 : Nat := 1163522002536099034191583

theorem tailTrace_6797853 : CollatzResearch.WordTrace tailWord_6797853 prefixEnd_6797853 1163522002536099034191583 := by
  unfold tailWord_6797853
  simp only [CollatzResearch.WordTrace]
  refine ⟨247938067841547036707102213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165292045227698024471401475 247938067841547036707102213)
  ·
    refine ⟨46488387720290069382581665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247938067841547036707102213 46488387720290069382581665)
    ·
      refine ⟨34866290790217552036936249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46488387720290069382581665 34866290790217552036936249)
      ·
        refine ⟨26149718092663164027702187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34866290790217552036936249 26149718092663164027702187)
        ·
          refine ⟨39224577138994746041553281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26149718092663164027702187 39224577138994746041553281)
          ·
            refine ⟨29418432854246059531164961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39224577138994746041553281 29418432854246059531164961)
            ·
              refine ⟨22063824640684544648373721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29418432854246059531164961 22063824640684544648373721)
              ·
                refine ⟨16547868480513408486280291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22063824640684544648373721 16547868480513408486280291)
                ·
                  refine ⟨24821802720770112729420437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16547868480513408486280291 24821802720770112729420437)
                  ·
                    refine ⟨1163522002536099034191583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24821802720770112729420437 1163522002536099034191583)
                    ·
                      rfl

theorem cell23_6797853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6797853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797853 prefixEnd_6797853 := by exact prefixLift 6797853
  have htrace : WordTrace (prefixWord ++ tailWord_6797853) baseStart_6797853 baseEnd_6797853 := by
    simpa [prefixWord, tailWord_6797853, baseEnd_6797853] using wordTrace_append hprefix tailTrace_6797853
  have hstable : (prefixWord ++ tailWord_6797853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797853).length < 2 ^ (prefixWord ++ tailWord_6797853).sum := by decide
  have hdescent : baseEnd_6797853 < baseStart_6797853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797877 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_6797877 : Nat := 118140960795 + 6797877 * 2 ^ 59
def prefixEnd_6797877 : Nat := 4983230072969 + 3 ^ 40 * 6797877 * 2
def baseEnd_6797877 : Nat := 3490578331144005008674639

theorem tailTrace_6797877 : CollatzResearch.WordTrace tailWord_6797877 prefixEnd_6797877 3490578331144005008674639 := by
  unfold tailWord_6797877
  simp only [CollatzResearch.WordTrace]
  refine ⟨247938943193460088805975885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165292628795640059203983923 247938943193460088805975885)
  ·
    refine ⟨92977103697547533302240957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247938943193460088805975885 92977103697547533302240957)
    ·
      refine ⟨34866413886580324988340359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92977103697547533302240957 34866413886580324988340359)
      ·
        refine ⟨52299620829870487482510539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34866413886580324988340359 52299620829870487482510539)
        ·
          refine ⟨78449431244805731223765809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52299620829870487482510539 78449431244805731223765809)
          ·
            refine ⟨58837073433604298417824357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78449431244805731223765809 58837073433604298417824357)
            ·
              refine ⟨11031951268800805953342067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58837073433604298417824357 11031951268800805953342067)
              ·
                refine ⟨16547926903201208930013101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11031951268800805953342067 16547926903201208930013101)
                ·
                  refine ⟨6205472588700453348754913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16547926903201208930013101 6205472588700453348754913)
                  ·
                    refine ⟨4654104441525340011566185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6205472588700453348754913 4654104441525340011566185)
                    ·
                      refine ⟨3490578331144005008674639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654104441525340011566185 3490578331144005008674639)
                      ·
                        rfl

theorem cell23_6797877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_6797877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797877 prefixEnd_6797877 := by exact prefixLift 6797877
  have htrace : WordTrace (prefixWord ++ tailWord_6797877) baseStart_6797877 baseEnd_6797877 := by
    simpa [prefixWord, tailWord_6797877, baseEnd_6797877] using wordTrace_append hprefix tailTrace_6797877
  have hstable : (prefixWord ++ tailWord_6797877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797877).length < 2 ^ (prefixWord ++ tailWord_6797877).sum := by decide
  have hdescent : baseEnd_6797877 < baseStart_6797877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797894 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6797894 : Nat := 118140960795 + 6797894 * 2 ^ 59
def prefixEnd_6797894 : Nat := 4983230072969 + 3 ^ 40 * 6797894 * 2
def baseEnd_6797894 : Nat := 3490587060315131442162061

theorem tailTrace_6797894 : CollatzResearch.WordTrace tailWord_6797894 prefixEnd_6797894 3490587060315131442162061 := by
  unfold tailWord_6797894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748111351074953147167023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165293042156265667139563157 7748111351074953147167023)
  ·
    refine ⟨11622167026612429720750535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748111351074953147167023 11622167026612429720750535)
    ·
      refine ⟨17433250539918644581125803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11622167026612429720750535 17433250539918644581125803)
      ·
        refine ⟨26149875809877966871688705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17433250539918644581125803 26149875809877966871688705)
        ·
          refine ⟨19612406857408475153766529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26149875809877966871688705 19612406857408475153766529)
          ·
            refine ⟨14709305143056356365324897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19612406857408475153766529 14709305143056356365324897)
            ·
              refine ⟨11031978857292267273993673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14709305143056356365324897 11031978857292267273993673)
              ·
                refine ⟨8273984142969200455495255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11031978857292267273993673 8273984142969200455495255)
                ·
                  refine ⟨12410976214453800683242883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8273984142969200455495255 12410976214453800683242883)
                  ·
                    refine ⟨18616464321680701024864325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12410976214453800683242883 18616464321680701024864325)
                    ·
                      refine ⟨3490587060315131442162061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18616464321680701024864325 3490587060315131442162061)
                      ·
                        rfl

theorem cell23_6797894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6797894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797894 prefixEnd_6797894 := by exact prefixLift 6797894
  have htrace : WordTrace (prefixWord ++ tailWord_6797894) baseStart_6797894 baseEnd_6797894 := by
    simpa [prefixWord, tailWord_6797894, baseEnd_6797894] using wordTrace_append hprefix tailTrace_6797894
  have hstable : (prefixWord ++ tailWord_6797894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797894).length < 2 ^ (prefixWord ++ tailWord_6797894).sum := by decide
  have hdescent : baseEnd_6797894 < baseStart_6797894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797896 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 2, 7]
def baseStart_6797896 : Nat := 118140960795 + 6797896 * 2 ^ 59
def prefixEnd_6797896 : Nat := 4983230072969 + 3 ^ 40 * 6797896 * 2
def baseEnd_6797896 : Nat := 1163529362425480144779017

theorem tailTrace_6797896 : CollatzResearch.WordTrace tailWord_6797896 prefixEnd_6797896 1163529362425480144779017 := by
  unfold tailWord_6797896
  simp only [CollatzResearch.WordTrace]
  refine ⟨123969818090195627525458771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165293090786927503367278361 123969818090195627525458771)
  ·
    refine ⟨185954727135293441288188157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123969818090195627525458771 185954727135293441288188157)
    ·
      refine ⟨69733022675735040483070559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185954727135293441288188157 69733022675735040483070559)
      ·
        refine ⟨104599534013602560724605839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69733022675735040483070559 104599534013602560724605839)
        ·
          refine ⟨156899301020403841086908759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104599534013602560724605839 156899301020403841086908759)
          ·
            refine ⟨235348951530605761630363139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156899301020403841086908759 235348951530605761630363139)
            ·
              refine ⟨353023427295908642445544709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235348951530605761630363139 353023427295908642445544709)
              ·
                refine ⟨66191892617982870458539633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353023427295908642445544709 66191892617982870458539633)
                ·
                  refine ⟨49643919463487152843904725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66191892617982870458539633 49643919463487152843904725)
                  ·
                    refine ⟨1163529362425480144779017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49643919463487152843904725 1163529362425480144779017)
                    ·
                      rfl

theorem cell23_6797896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_6797896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797896 prefixEnd_6797896 := by exact prefixLift 6797896
  have htrace : WordTrace (prefixWord ++ tailWord_6797896) baseStart_6797896 baseEnd_6797896 := by
    simpa [prefixWord, tailWord_6797896, baseEnd_6797896] using wordTrace_append hprefix tailTrace_6797896
  have hstable : (prefixWord ++ tailWord_6797896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797896).length < 2 ^ (prefixWord ++ tailWord_6797896).sum := by decide
  have hdescent : baseEnd_6797896 < baseStart_6797896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797928 : List Nat := [2, 1, 4, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6797928 : Nat := 118140960795 + 6797928 * 2 ^ 59
def prefixEnd_6797928 : Nat := 4983230072969 + 3 ^ 40 * 6797928 * 2
def baseEnd_6797928 : Nat := 3490604518657384309136905

theorem tailTrace_6797928 : CollatzResearch.WordTrace tailWord_6797928 prefixEnd_6797928 3490604518657384309136905 := by
  unfold tailWord_6797928
  simp only [CollatzResearch.WordTrace]
  refine ⟨123970401658137662258041219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165293868877516883010721625 123970401658137662258041219)
  ·
    refine ⟨185955602487206493387061829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123970401658137662258041219 185955602487206493387061829)
    ·
      refine ⟨34866675466351217510074093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185955602487206493387061829 34866675466351217510074093)
      ·
        refine ⟨13075003299881706566277785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34866675466351217510074093 13075003299881706566277785)
        ·
          refine ⟨9806252474911279924708339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13075003299881706566277785 9806252474911279924708339)
          ·
            refine ⟨14709378712366919887062509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806252474911279924708339 14709378712366919887062509)
            ·
              refine ⟨5516017017137594957648441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14709378712366919887062509 5516017017137594957648441)
              ·
                refine ⟨4137012762853196218236331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516017017137594957648441 4137012762853196218236331)
                ·
                  refine ⟨6205519144279794327354497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137012762853196218236331 6205519144279794327354497)
                  ·
                    refine ⟨4654139358209845745515873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6205519144279794327354497 4654139358209845745515873)
                    ·
                      refine ⟨3490604518657384309136905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654139358209845745515873 3490604518657384309136905)
                      ·
                        rfl

theorem cell23_6797928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6797928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797928 prefixEnd_6797928 := by exact prefixLift 6797928
  have htrace : WordTrace (prefixWord ++ tailWord_6797928) baseStart_6797928 baseEnd_6797928 := by
    simpa [prefixWord, tailWord_6797928, baseEnd_6797928] using wordTrace_append hprefix tailTrace_6797928
  have hstable : (prefixWord ++ tailWord_6797928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797928).length < 2 ^ (prefixWord ++ tailWord_6797928).sum := by decide
  have hdescent : baseEnd_6797928 < baseStart_6797928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797953 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6797953 : Nat := 118140960795 + 6797953 * 2 ^ 59
def prefixEnd_6797953 : Nat := 4983230072969 + 3 ^ 40 * 6797953 * 2
def baseEnd_6797953 : Nat := 3490617355673746711324289

theorem tailTrace_6797953 : CollatzResearch.WordTrace tailWord_6797953 prefixEnd_6797953 3490617355673746711324289 := by
  unfold tailWord_6797953
  simp only [CollatzResearch.WordTrace]
  refine ⟨247941715141184753785742513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165294476760789835857161675 247941715141184753785742513)
  ·
    refine ⟨185956286355888565339306885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247941715141184753785742513 185956286355888565339306885)
    ·
      refine ⟨34866803691729106001120041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185956286355888565339306885 34866803691729106001120041)
      ·
        refine ⟨26150102768796829500840031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34866803691729106001120041 26150102768796829500840031)
        ·
          refine ⟨39225154153195244251260047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26150102768796829500840031 39225154153195244251260047)
          ·
            refine ⟨58837731229792866376890071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39225154153195244251260047 58837731229792866376890071)
            ·
              refine ⟨88256596844689299565335107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58837731229792866376890071 88256596844689299565335107)
              ·
                refine ⟨132384895267033949348002661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88256596844689299565335107 132384895267033949348002661)
                ·
                  refine ⟨24822167862568865502750499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132384895267033949348002661 24822167862568865502750499)
                  ·
                    refine ⟨37233251793853298254125749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24822167862568865502750499 37233251793853298254125749)
                    ·
                      refine ⟨3490617355673746711324289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37233251793853298254125749 3490617355673746711324289)
                      ·
                        rfl

theorem cell23_6797953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6797953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797953 prefixEnd_6797953 := by exact prefixLift 6797953
  have htrace : WordTrace (prefixWord ++ tailWord_6797953) baseStart_6797953 baseEnd_6797953 := by
    simpa [prefixWord, tailWord_6797953, baseEnd_6797953] using wordTrace_append hprefix tailTrace_6797953
  have hstable : (prefixWord ++ tailWord_6797953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797953).length < 2 ^ (prefixWord ++ tailWord_6797953).sum := by decide
  have hdescent : baseEnd_6797953 < baseStart_6797953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6797970 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6797970 : Nat := 118140960795 + 6797970 * 2 ^ 59
def prefixEnd_6797970 : Nat := 4983230072969 + 3 ^ 40 * 6797970 * 2
def baseEnd_6797970 : Nat := 3490626084844873144811711

theorem tailTrace_6797970 : CollatzResearch.WordTrace tailWord_6797970 prefixEnd_6797970 3490626084844873144811711 := by
  unfold tailWord_6797970
  simp only [CollatzResearch.WordTrace]
  refine ⟨61985583795530791422277841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165294890121415443792740909 61985583795530791422277841)
  ·
    refine ⟨46489187846648093566708381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61985583795530791422277841 46489187846648093566708381)
    ·
      refine ⟨17433445442493035087515643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46489187846648093566708381 17433445442493035087515643)
      ·
        refine ⟨26150168163739552631273465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17433445442493035087515643 26150168163739552631273465)
        ·
          refine ⟨19612626122804664473455099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26150168163739552631273465 19612626122804664473455099)
          ·
            refine ⟨29418939184206996710182649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19612626122804664473455099 29418939184206996710182649)
            ·
              refine ⟨22064204388155247532636987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29418939184206996710182649 22064204388155247532636987)
              ·
                refine ⟨33096306582232871298955481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22064204388155247532636987 33096306582232871298955481)
                ·
                  refine ⟨24822229936674653474216611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33096306582232871298955481 24822229936674653474216611)
                  ·
                    refine ⟨37233344905011980211324917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24822229936674653474216611 37233344905011980211324917)
                    ·
                      refine ⟨3490626084844873144811711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37233344905011980211324917 3490626084844873144811711)
                      ·
                        rfl

theorem cell23_6797970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6797970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6797970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6797970 prefixEnd_6797970 := by exact prefixLift 6797970
  have htrace : WordTrace (prefixWord ++ tailWord_6797970) baseStart_6797970 baseEnd_6797970 := by
    simpa [prefixWord, tailWord_6797970, baseEnd_6797970] using wordTrace_append hprefix tailTrace_6797970
  have hstable : (prefixWord ++ tailWord_6797970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6797970).length < 2 ^ (prefixWord ++ tailWord_6797970).sum := by decide
  have hdescent : baseEnd_6797970 < baseStart_6797970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6797970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798010 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2]
def baseStart_6798010 : Nat := 118140960795 + 6798010 * 2 ^ 59
def prefixEnd_6798010 : Nat := 4983230072969 + 3 ^ 40 * 6798010 * 2
def baseEnd_6798010 : Nat := 3490646624071052988311527

theorem tailTrace_6798010 : CollatzResearch.WordTrace tailWord_6798010 prefixEnd_6798010 3490646624071052988311527 := by
  unfold tailWord_6798010
  simp only [CollatzResearch.WordTrace]
  refine ⟨61985948525494563130141871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165295862734652168347044989 61985948525494563130141871)
  ·
    refine ⟨92978922788241844695212807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61985948525494563130141871 92978922788241844695212807)
    ·
      refine ⟨139468384182362767042819211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92978922788241844695212807 139468384182362767042819211)
      ·
        refine ⟨209202576273544150564228817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139468384182362767042819211 209202576273544150564228817)
        ·
          refine ⟨156901932205158112923171613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209202576273544150564228817 156901932205158112923171613)
          ·
            refine ⟨58838224576934292346189355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156901932205158112923171613 58838224576934292346189355)
            ·
              refine ⟨88257336865401438519284033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58838224576934292346189355 88257336865401438519284033)
              ·
                refine ⟨66193002649051078889463025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88257336865401438519284033 66193002649051078889463025)
                ·
                  refine ⟨49644751986788309167097269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66193002649051078889463025 49644751986788309167097269)
                  ·
                    refine ⟨4654195498761403984415369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49644751986788309167097269 4654195498761403984415369)
                    ·
                      refine ⟨3490646624071052988311527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654195498761403984415369 3490646624071052988311527)
                      ·
                        rfl

theorem cell23_6798010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_6798010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798010 prefixEnd_6798010 := by exact prefixLift 6798010
  have htrace : WordTrace (prefixWord ++ tailWord_6798010) baseStart_6798010 baseEnd_6798010 := by
    simpa [prefixWord, tailWord_6798010, baseEnd_6798010] using wordTrace_append hprefix tailTrace_6798010
  have hstable : (prefixWord ++ tailWord_6798010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798010).length < 2 ^ (prefixWord ++ tailWord_6798010).sum := by decide
  have hdescent : baseEnd_6798010 < baseStart_6798010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798020 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6798020 : Nat := 118140960795 + 6798020 * 2 ^ 59
def prefixEnd_6798020 : Nat := 4983230072969 + 3 ^ 40 * 6798020 * 2
def baseEnd_6798020 : Nat := 1163550586292532649728827

theorem tailTrace_6798020 : CollatzResearch.WordTrace tailWord_6798020 prefixEnd_6798020 1163550586292532649728827 := by
  unfold tailWord_6798020
  simp only [CollatzResearch.WordTrace]
  refine ⟨123972079415971012114215757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165296105887961349485621009 123972079415971012114215757)
  ·
    refine ⟨46489529780989129542830909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123972079415971012114215757 46489529780989129542830909)
    ·
      refine ⟨17433573667870923578561591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46489529780989129542830909 17433573667870923578561591)
      ·
        refine ⟨26150360501806385367842387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17433573667870923578561591 26150360501806385367842387)
        ·
          refine ⟨39225540752709578051763581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26150360501806385367842387 39225540752709578051763581)
          ·
            refine ⟨14709577782266091769411343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39225540752709578051763581 14709577782266091769411343)
            ·
              refine ⟨22064366673399137654117015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14709577782266091769411343 22064366673399137654117015)
              ·
                refine ⟨33096550010098706481175523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22064366673399137654117015 33096550010098706481175523)
                ·
                  refine ⟨49644825015148059721763285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33096550010098706481175523 49644825015148059721763285)
                  ·
                    refine ⟨1163550586292532649728827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49644825015148059721763285 1163550586292532649728827)
                    ·
                      rfl

theorem cell23_6798020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6798020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798020 prefixEnd_6798020 := by exact prefixLift 6798020
  have htrace : WordTrace (prefixWord ++ tailWord_6798020) baseStart_6798020 baseEnd_6798020 := by
    simpa [prefixWord, tailWord_6798020, baseEnd_6798020] using wordTrace_append hprefix tailTrace_6798020
  have hstable : (prefixWord ++ tailWord_6798020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798020).length < 2 ^ (prefixWord ++ tailWord_6798020).sum := by decide
  have hdescent : baseEnd_6798020 < baseStart_6798020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798022 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6798022 : Nat := 118140960795 + 6798022 * 2 ^ 59
def prefixEnd_6798022 : Nat := 4983230072969 + 3 ^ 40 * 6798022 * 2
def baseEnd_6798022 : Nat := 3490652785838906941361473

theorem tailTrace_6798022 : CollatzResearch.WordTrace tailWord_6798022 prefixEnd_6798022 3490652785838906941361473 := by
  unfold tailWord_6798022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7748257243060461830312635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165296154518623185713336213 7748257243060461830312635)
  ·
    refine ⟨11622385864590692745468953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7748257243060461830312635 11622385864590692745468953)
    ·
      refine ⟨8716789398443019559101715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11622385864590692745468953 8716789398443019559101715)
      ·
        refine ⟨13075184097664529338652573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8716789398443019559101715 13075184097664529338652573)
        ·
          refine ⟨4903194036624198501994715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13075184097664529338652573 4903194036624198501994715)
          ·
            refine ⟨7354791054936297752992073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903194036624198501994715 7354791054936297752992073)
            ·
              refine ⟨5516093291202223314744055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7354791054936297752992073 5516093291202223314744055)
              ·
                refine ⟨8274139936803334972116083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516093291202223314744055 8274139936803334972116083)
                ·
                  refine ⟨12411209905205002458174125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274139936803334972116083 12411209905205002458174125)
                  ·
                    refine ⟨4654203714451875921815297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12411209905205002458174125 4654203714451875921815297)
                    ·
                      refine ⟨3490652785838906941361473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654203714451875921815297 3490652785838906941361473)
                      ·
                        rfl

theorem cell23_6798022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6798022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798022 prefixEnd_6798022 := by exact prefixLift 6798022
  have htrace : WordTrace (prefixWord ++ tailWord_6798022) baseStart_6798022 baseEnd_6798022 := by
    simpa [prefixWord, tailWord_6798022, baseEnd_6798022] using wordTrace_append hprefix tailTrace_6798022
  have hstable : (prefixWord ++ tailWord_6798022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798022).length < 2 ^ (prefixWord ++ tailWord_6798022).sum := by decide
  have hdescent : baseEnd_6798022 < baseStart_6798022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798043 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 3]
def baseStart_6798043 : Nat := 118140960795 + 6798043 * 2 ^ 59
def prefixEnd_6798043 : Nat := 4983230072969 + 3 ^ 40 * 6798043 * 2
def baseEnd_6798043 : Nat := 3490663568932651359198875

theorem tailTrace_6798043 : CollatzResearch.WordTrace tailWord_6798043 prefixEnd_6798043 3490663568932651359198875 := by
  unfold tailWord_6798043
  simp only [CollatzResearch.WordTrace]
  refine ⟨247944997710858699156518783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165296665140572466104345855 247944997710858699156518783)
  ·
    refine ⟨371917496566288048734778175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247944997710858699156518783 371917496566288048734778175)
    ·
      refine ⟨557876244849432073102167263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371917496566288048734778175 557876244849432073102167263)
      ·
        refine ⟨836814367274148109653250895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557876244849432073102167263 836814367274148109653250895)
        ·
          refine ⟨1255221550911222164479876343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836814367274148109653250895 1255221550911222164479876343)
          ·
            refine ⟨1882832326366833246719814515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255221550911222164479876343 1882832326366833246719814515)
            ·
              refine ⟨2824248489550249870079721773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882832326366833246719814515 2824248489550249870079721773)
              ·
                refine ⟨1059093183581343701279895665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2824248489550249870079721773 1059093183581343701279895665)
                ·
                  refine ⟨794319887686007775959921749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059093183581343701279895665 794319887686007775959921749)
                  ·
                    refine ⟨9308436183820403624530333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 794319887686007775959921749 9308436183820403624530333)
                    ·
                      refine ⟨3490663568932651359198875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9308436183820403624530333 3490663568932651359198875)
                      ·
                        rfl

theorem cell23_6798043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 3].length) (baseStart_6798043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798043 prefixEnd_6798043 := by exact prefixLift 6798043
  have htrace : WordTrace (prefixWord ++ tailWord_6798043) baseStart_6798043 baseEnd_6798043 := by
    simpa [prefixWord, tailWord_6798043, baseEnd_6798043] using wordTrace_append hprefix tailTrace_6798043
  have hstable : (prefixWord ++ tailWord_6798043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798043).length < 2 ^ (prefixWord ++ tailWord_6798043).sum := by decide
  have hdescent : baseEnd_6798043 < baseStart_6798043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798070 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6798070 : Nat := 118140960795 + 6798070 * 2 ^ 59
def prefixEnd_6798070 : Nat := 4983230072969 + 3 ^ 40 * 6798070 * 2
def baseEnd_6798070 : Nat := 3490677432910322753561251

theorem tailTrace_6798070 : CollatzResearch.WordTrace tailWord_6798070 prefixEnd_6798070 3490677432910322753561251 := by
  unfold tailWord_6798070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15496623905110055172984479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165297321654507255178501109 15496623905110055172984479)
  ·
    refine ⟨23244935857665082759476719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15496623905110055172984479 23244935857665082759476719)
    ·
      refine ⟨34867403786497624139215079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23244935857665082759476719 34867403786497624139215079)
      ·
        refine ⟨52301105679746436208822619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34867403786497624139215079 52301105679746436208822619)
        ·
          refine ⟨78451658519619654313233929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52301105679746436208822619 78451658519619654313233929)
          ·
            refine ⟨58838743889714740734925447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78451658519619654313233929 58838743889714740734925447)
            ·
              refine ⟨88258115834572111102388171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58838743889714740734925447 88258115834572111102388171)
              ·
                refine ⟨132387173751858166653582257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88258115834572111102388171 132387173751858166653582257)
                ·
                  refine ⟨99290380313893624990186693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132387173751858166653582257 99290380313893624990186693)
                  ·
                    refine ⟨18616946308855054685660005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99290380313893624990186693 18616946308855054685660005)
                    ·
                      refine ⟨3490677432910322753561251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18616946308855054685660005 3490677432910322753561251)
                      ·
                        rfl

theorem cell23_6798070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6798070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798070 prefixEnd_6798070 := by exact prefixLift 6798070
  have htrace : WordTrace (prefixWord ++ tailWord_6798070) baseStart_6798070 baseEnd_6798070 := by
    simpa [prefixWord, tailWord_6798070, baseEnd_6798070] using wordTrace_append hprefix tailTrace_6798070
  have hstable : (prefixWord ++ tailWord_6798070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798070).length < 2 ^ (prefixWord ++ tailWord_6798070).sum := by decide
  have hdescent : baseEnd_6798070 < baseStart_6798070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798114 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 6]
def baseStart_6798114 : Nat := 118140960795 + 6798114 * 2 ^ 59
def prefixEnd_6798114 : Nat := 4983230072969 + 3 ^ 40 * 6798114 * 2
def baseEnd_6798114 : Nat := 387855558451013397934561

theorem tailTrace_6798114 : CollatzResearch.WordTrace tailWord_6798114 prefixEnd_6798114 387855558451013397934561 := by
  unfold tailWord_6798114
  simp only [CollatzResearch.WordTrace]
  refine ⟨61986896823400369570588349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165298391529067652188235597 61986896823400369570588349)
  ·
    refine ⟨23245086308775138588970631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61986896823400369570588349 23245086308775138588970631)
    ·
      refine ⟨34867629463162707883455947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23245086308775138588970631 34867629463162707883455947)
      ·
        refine ⟨52301444194744061825183921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34867629463162707883455947 52301444194744061825183921)
        ·
          refine ⟨39226083146058046368887941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52301444194744061825183921 39226083146058046368887941)
          ·
            refine ⟨7354890589885883694166489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39226083146058046368887941 7354890589885883694166489)
            ·
              refine ⟨5516167942414412770624867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7354890589885883694166489 5516167942414412770624867)
              ·
                refine ⟨8274251913621619155937301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516167942414412770624867 8274251913621619155937301)
                ·
                  refine ⟨387855558451013397934561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8274251913621619155937301 387855558451013397934561)
                  ·
                    rfl

theorem cell23_6798114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_6798114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798114 prefixEnd_6798114 := by exact prefixLift 6798114
  have htrace : WordTrace (prefixWord ++ tailWord_6798114) baseStart_6798114 baseEnd_6798114 := by
    simpa [prefixWord, tailWord_6798114, baseEnd_6798114] using wordTrace_append hprefix tailTrace_6798114
  have hstable : (prefixWord ++ tailWord_6798114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798114).length < 2 ^ (prefixWord ++ tailWord_6798114).sum := by decide
  have hdescent : baseEnd_6798114 < baseStart_6798114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798117 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 4, 3, 2]
def baseStart_6798117 : Nat := 118140960795 + 6798117 * 2 ^ 59
def prefixEnd_6798117 : Nat := 4983230072969 + 3 ^ 40 * 6798117 * 2
def baseEnd_6798117 : Nat := 3490701566501084069673535

theorem tailTrace_6798117 : CollatzResearch.WordTrace tailWord_6798117 prefixEnd_6798117 3490701566501084069673535 := by
  unfold tailWord_6798117
  simp only [CollatzResearch.WordTrace]
  refine ⟨247947696712590609794712605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165298464475060406529808403 247947696712590609794712605)
  ·
    refine ⟨92980386267221478673017227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247947696712590609794712605 92980386267221478673017227)
    ·
      refine ⟨139470579400832218009525841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92980386267221478673017227 139470579400832218009525841)
      ·
        refine ⟨104602934550624163507144381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139470579400832218009525841 104602934550624163507144381)
        ·
          refine ⟨39226100456484061315179143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104602934550624163507144381 39226100456484061315179143)
          ·
            refine ⟨58839150684726091972768715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39226100456484061315179143 58839150684726091972768715)
            ·
              refine ⟨88258726027089137959153073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58839150684726091972768715 88258726027089137959153073)
              ·
                refine ⟨66194044520316853469364805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88258726027089137959153073 66194044520316853469364805)
                ·
                  refine ⟨12411383347559410025505901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66194044520316853469364805 12411383347559410025505901)
                  ·
                    refine ⟨4654268755334778759564713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12411383347559410025505901 4654268755334778759564713)
                    ·
                      refine ⟨3490701566501084069673535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654268755334778759564713 3490701566501084069673535)
                      ·
                        rfl

theorem cell23_6798117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_6798117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798117 prefixEnd_6798117 := by exact prefixLift 6798117
  have htrace : WordTrace (prefixWord ++ tailWord_6798117) baseStart_6798117 baseEnd_6798117 := by
    simpa [prefixWord, tailWord_6798117, baseEnd_6798117] using wordTrace_append hprefix tailTrace_6798117
  have hstable : (prefixWord ++ tailWord_6798117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798117).length < 2 ^ (prefixWord ++ tailWord_6798117).sum := by decide
  have hdescent : baseEnd_6798117 < baseStart_6798117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798153 : List Nat := [1, 2, 1, 1, 2, 16]
def baseStart_6798153 : Nat := 118140960795 + 6798153 * 2 ^ 59
def prefixEnd_6798153 : Nat := 4983230072969 + 3 ^ 40 * 6798153 * 2
def baseEnd_6798153 : Nat := 14365103093846279542483

theorem tailTrace_6798153 : CollatzResearch.WordTrace tailWord_6798153 prefixEnd_6798153 14365103093846279542483 := by
  unfold tailWord_6798153
  simp only [CollatzResearch.WordTrace]
  refine ⟨247949009740460187943023113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165299339826973458628682075 247949009740460187943023113)
  ·
    refine ⟨185961757305345140957267335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247949009740460187943023113 185961757305345140957267335)
    ·
      refine ⟨278942635958017711435901003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185961757305345140957267335 278942635958017711435901003)
      ·
        refine ⟨418413953937026567153851505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278942635958017711435901003 418413953937026567153851505)
        ·
          refine ⟨313810465452769925365388629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418413953937026567153851505 313810465452769925365388629)
          ·
            refine ⟨14365103093846279542483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 313810465452769925365388629 14365103093846279542483)
            ·
              rfl

theorem cell23_6798153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 16].length) (baseStart_6798153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798153 prefixEnd_6798153 := by exact prefixLift 6798153
  have htrace : WordTrace (prefixWord ++ tailWord_6798153) baseStart_6798153 baseEnd_6798153 := by
    simpa [prefixWord, tailWord_6798153, baseEnd_6798153] using wordTrace_append hprefix tailTrace_6798153
  have hstable : (prefixWord ++ tailWord_6798153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798153).length < 2 ^ (prefixWord ++ tailWord_6798153).sum := by decide
  have hdescent : baseEnd_6798153 < baseStart_6798153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798167 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_6798167 : Nat := 118140960795 + 6798167 * 2 ^ 59
def prefixEnd_6798167 : Nat := 4983230072969 + 3 ^ 40 * 6798167 * 2
def baseEnd_6798167 : Nat := 3490727240533808874048305

theorem tailTrace_6798167 : CollatzResearch.WordTrace tailWord_6798167 prefixEnd_6798167 3490727240533808874048305 := by
  unfold tailWord_6798167
  simp only [CollatzResearch.WordTrace]
  refine ⟨247949520362409468334032755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165299680241606312222688503 247949520362409468334032755)
  ·
    refine ⟨371924280543614202501049133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247949520362409468334032755 371924280543614202501049133)
    ·
      refine ⟨139471605203855325937893425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371924280543614202501049133 139471605203855325937893425)
      ·
        refine ⟨104603703902891494453420069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139471605203855325937893425 104603703902891494453420069)
        ·
          refine ⟨19613194481792155210016263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104603703902891494453420069 19613194481792155210016263)
          ·
            refine ⟨29419791722688232815024395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19613194481792155210016263 29419791722688232815024395)
            ·
              refine ⟨44129687584032349222536593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29419791722688232815024395 44129687584032349222536593)
              ·
                refine ⟨33097265688024261916902445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44129687584032349222536593 33097265688024261916902445)
                ·
                  refine ⟨12411474633009098218838417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33097265688024261916902445 12411474633009098218838417)
                  ·
                    refine ⟨9308605974756823664128813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12411474633009098218838417 9308605974756823664128813)
                    ·
                      refine ⟨3490727240533808874048305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9308605974756823664128813 3490727240533808874048305)
                      ·
                        rfl

theorem cell23_6798167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_6798167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798167 prefixEnd_6798167 := by exact prefixLift 6798167
  have htrace : WordTrace (prefixWord ++ tailWord_6798167) baseStart_6798167 baseEnd_6798167 := by
    simpa [prefixWord, tailWord_6798167, baseEnd_6798167] using wordTrace_append hprefix tailTrace_6798167
  have hstable : (prefixWord ++ tailWord_6798167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798167).length < 2 ^ (prefixWord ++ tailWord_6798167).sum := by decide
  have hdescent : baseEnd_6798167 < baseStart_6798167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798170 : List Nat := [3, 1, 1, 2, 1, 4, 3, 8]
def baseStart_6798170 : Nat := 118140960795 + 6798170 * 2 ^ 59
def prefixEnd_6798170 : Nat := 4983230072969 + 3 ^ 40 * 6798170 * 2
def baseEnd_6798170 : Nat := 129286251147250828233733

theorem tailTrace_6798170 : CollatzResearch.WordTrace tailWord_6798170 prefixEnd_6798170 129286251147250828233733 := by
  unfold tailWord_6798170
  simp only [CollatzResearch.WordTrace]
  refine ⟨61987407445349649961597991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165299753187599066564261309 61987407445349649961597991)
  ·
    refine ⟨92981111168024474942396987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61987407445349649961597991 92981111168024474942396987)
    ·
      refine ⟨139471666752036712413595481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92981111168024474942396987 139471666752036712413595481)
      ·
        refine ⟨104603750064027534310196611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139471666752036712413595481 104603750064027534310196611)
        ·
          refine ⟨156905625096041301465294917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104603750064027534310196611 156905625096041301465294917)
          ·
            refine ⟨29419804705507744024742797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156905625096041301465294917 29419804705507744024742797)
            ·
              refine ⟨11032426764565404009278549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29419804705507744024742797 11032426764565404009278549)
              ·
                refine ⟨129286251147250828233733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11032426764565404009278549 129286251147250828233733)
                ·
                  rfl

theorem cell23_6798170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_6798170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798170 prefixEnd_6798170 := by exact prefixLift 6798170
  have htrace : WordTrace (prefixWord ++ tailWord_6798170) baseStart_6798170 baseEnd_6798170 := by
    simpa [prefixWord, tailWord_6798170, baseEnd_6798170] using wordTrace_append hprefix tailTrace_6798170
  have hstable : (prefixWord ++ tailWord_6798170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798170).length < 2 ^ (prefixWord ++ tailWord_6798170).sum := by decide
  have hdescent : baseEnd_6798170 < baseStart_6798170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798198 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6798198 : Nat := 118140960795 + 6798198 * 2 ^ 59
def prefixEnd_6798198 : Nat := 4983230072969 + 3 ^ 40 * 6798198 * 2
def baseEnd_6798198 : Nat := 3490743158434098252760663

theorem tailTrace_6798198 : CollatzResearch.WordTrace tailWord_6798198 prefixEnd_6798198 3490743158434098252760663 := by
  unfold tailWord_6798198
  simp only [CollatzResearch.WordTrace]
  refine ⟨15496915689081072539275703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165300434016864773752274165 15496915689081072539275703)
  ·
    refine ⟨23245373533621608808913555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15496915689081072539275703 23245373533621608808913555)
    ·
      refine ⟨34868060300432413213370333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23245373533621608808913555 34868060300432413213370333)
      ·
        refine ⟨13075522612662154955013875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34868060300432413213370333 13075522612662154955013875)
        ·
          refine ⟨19613283918993232432520813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075522612662154955013875 19613283918993232432520813)
          ·
            refine ⟨7354981469622462162195305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19613283918993232432520813 7354981469622462162195305)
            ·
              refine ⟨5516236102216846621646479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7354981469622462162195305 5516236102216846621646479)
              ·
                refine ⟨8274354153325269932469719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516236102216846621646479 8274354153325269932469719)
                ·
                  refine ⟨12411531229987904898704579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274354153325269932469719 12411531229987904898704579)
                  ·
                    refine ⟨18617296844981857348056869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12411531229987904898704579 18617296844981857348056869)
                    ·
                      refine ⟨3490743158434098252760663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18617296844981857348056869 3490743158434098252760663)
                      ·
                        rfl

theorem cell23_6798198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6798198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798198 prefixEnd_6798198 := by exact prefixLift 6798198
  have htrace : WordTrace (prefixWord ++ tailWord_6798198) baseStart_6798198 baseEnd_6798198 := by
    simpa [prefixWord, tailWord_6798198, baseEnd_6798198] using wordTrace_append hprefix tailTrace_6798198
  have hstable : (prefixWord ++ tailWord_6798198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798198).length < 2 ^ (prefixWord ++ tailWord_6798198).sum := by decide
  have hdescent : baseEnd_6798198 < baseStart_6798198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798201 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 1, 2, 3]
def baseStart_6798201 : Nat := 118140960795 + 6798201 * 2 ^ 59
def prefixEnd_6798201 : Nat := 4983230072969 + 3 ^ 40 * 6798201 * 2
def baseEnd_6798201 : Nat := 3490744698876061741023149

theorem tailTrace_6798201 : CollatzResearch.WordTrace tailWord_6798201 prefixEnd_6798201 3490744698876061741023149 := by
  unfold tailWord_6798201
  simp only [CollatzResearch.WordTrace]
  refine ⟨247950760444286292140770457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165300506962857528093846971 247950760444286292140770457)
  ·
    refine ⟨185963070333214719105577843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247950760444286292140770457 185963070333214719105577843)
    ·
      refine ⟨278944605499822078658366765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185963070333214719105577843 278944605499822078658366765)
      ·
        refine ⟨104604227062433279496887537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278944605499822078658366765 104604227062433279496887537)
        ·
          refine ⟨78453170296824959622665653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104604227062433279496887537 78453170296824959622665653)
          ·
            refine ⟨7354984715327339964624905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78453170296824959622665653 7354984715327339964624905)
            ·
              refine ⟨5516238536495504973468679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7354984715327339964624905 5516238536495504973468679)
              ·
                refine ⟨8274357804743257460203019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516238536495504973468679 8274357804743257460203019)
                ·
                  refine ⟨12411536707114886190304529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274357804743257460203019 12411536707114886190304529)
                  ·
                    refine ⟨9308652530336164642728397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12411536707114886190304529 9308652530336164642728397)
                    ·
                      refine ⟨3490744698876061741023149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9308652530336164642728397 3490744698876061741023149)
                      ·
                        rfl

theorem cell23_6798201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_6798201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798201 prefixEnd_6798201 := by exact prefixLift 6798201
  have htrace : WordTrace (prefixWord ++ tailWord_6798201) baseStart_6798201 baseEnd_6798201 := by
    simpa [prefixWord, tailWord_6798201, baseEnd_6798201] using wordTrace_append hprefix tailTrace_6798201
  have hstable : (prefixWord ++ tailWord_6798201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798201).length < 2 ^ (prefixWord ++ tailWord_6798201).sum := by decide
  have hdescent : baseEnd_6798201 < baseStart_6798201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798220 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6798220 : Nat := 118140960795 + 6798220 * 2 ^ 59
def prefixEnd_6798220 : Nat := 4983230072969 + 3 ^ 40 * 6798220 * 2
def baseEnd_6798220 : Nat := 3490754455008497166685561

theorem tailTrace_6798220 : CollatzResearch.WordTrace tailWord_6798220 prefixEnd_6798220 3490754455008497166685561 := by
  unfold tailWord_6798220
  simp only [CollatzResearch.WordTrace]
  refine ⟨123975726715608729192856057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165300968954144972257141409 123975726715608729192856057)
  ·
    refine ⟨92981795036706546894642043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123975726715608729192856057 92981795036706546894642043)
    ·
      refine ⟨139472692555059820341963065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92981795036706546894642043 139472692555059820341963065)
      ·
        refine ⟨104604519416294865256472299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139472692555059820341963065 104604519416294865256472299)
        ·
          refine ⟨156906779124442297884708449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104604519416294865256472299 156906779124442297884708449)
          ·
            refine ⟨117680084343331723413531337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156906779124442297884708449 117680084343331723413531337)
            ·
              refine ⟨88260063257498792560148503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117680084343331723413531337 88260063257498792560148503)
              ·
                refine ⟨132390094886248188840222755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88260063257498792560148503 132390094886248188840222755)
                ·
                  refine ⟨198585142329372283260334133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132390094886248188840222755 198585142329372283260334133)
                  ·
                    refine ⟨18617357093378651555656325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 198585142329372283260334133 18617357093378651555656325)
                    ·
                      refine ⟨3490754455008497166685561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18617357093378651555656325 3490754455008497166685561)
                      ·
                        rfl

theorem cell23_6798220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6798220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798220 prefixEnd_6798220 := by exact prefixLift 6798220
  have htrace : WordTrace (prefixWord ++ tailWord_6798220) baseStart_6798220 baseEnd_6798220 := by
    simpa [prefixWord, tailWord_6798220, baseEnd_6798220] using wordTrace_append hprefix tailTrace_6798220
  have hstable : (prefixWord ++ tailWord_6798220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798220).length < 2 ^ (prefixWord ++ tailWord_6798220).sum := by decide
  have hdescent : baseEnd_6798220 < baseStart_6798220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798231 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 2, 1, 3]
def baseStart_6798231 : Nat := 118140960795 + 6798231 * 2 ^ 59
def prefixEnd_6798231 : Nat := 4983230072969 + 3 ^ 40 * 6798231 * 2
def baseEnd_6798231 : Nat := 3490760103295696623648011

theorem tailTrace_6798231 : CollatzResearch.WordTrace tailWord_6798231 prefixEnd_6798231 3490760103295696623648011 := by
  unfold tailWord_6798231
  simp only [CollatzResearch.WordTrace]
  refine ⟨247951854634177607264362547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165301236422785071509575031 247951854634177607264362547)
  ·
    refine ⟨371927781951266410896543821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247951854634177607264362547 371927781951266410896543821)
    ·
      refine ⟨139472918231724904086203933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371927781951266410896543821 139472918231724904086203933)
      ·
        refine ⟨52302344336896839032326475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139472918231724904086203933 52302344336896839032326475)
        ·
          refine ⟨78453516505345258548489713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52302344336896839032326475 78453516505345258548489713)
          ·
            refine ⟨58840137379008943911367285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78453516505345258548489713 58840137379008943911367285)
            ·
              refine ⟨5516262879282088491690683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58840137379008943911367285 5516262879282088491690683)
              ·
                refine ⟨8274394318923132737536025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516262879282088491690683 8274394318923132737536025)
                ·
                  refine ⟨6205795739192349553152019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8274394318923132737536025 6205795739192349553152019)
                  ·
                    refine ⟨9308693608788524329728029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6205795739192349553152019 9308693608788524329728029)
                    ·
                      refine ⟨3490760103295696623648011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9308693608788524329728029 3490760103295696623648011)
                      ·
                        rfl

theorem cell23_6798231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_6798231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798231 prefixEnd_6798231 := by exact prefixLift 6798231
  have htrace : WordTrace (prefixWord ++ tailWord_6798231) baseStart_6798231 baseEnd_6798231 := by
    simpa [prefixWord, tailWord_6798231, baseEnd_6798231] using wordTrace_append hprefix tailTrace_6798231
  have hstable : (prefixWord ++ tailWord_6798231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798231).length < 2 ^ (prefixWord ++ tailWord_6798231).sum := by decide
  have hdescent : baseEnd_6798231 < baseStart_6798231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798241 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6798241 : Nat := 118140960795 + 6798241 * 2 ^ 59
def prefixEnd_6798241 : Nat := 4983230072969 + 3 ^ 40 * 6798241 * 2
def baseEnd_6798241 : Nat := 3490765238102241584522965

theorem tailTrace_6798241 : CollatzResearch.WordTrace tailWord_6798241 prefixEnd_6798241 3490765238102241584522965 := by
  unfold tailWord_6798241
  simp only [CollatzResearch.WordTrace]
  refine ⟨247952219364141378972226577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165301479576094252648151051 247952219364141378972226577)
  ·
    refine ⟨185964164523106034229169933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247952219364141378972226577 185964164523106034229169933)
    ·
      refine ⟨69736561696164762835938725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185964164523106034229169933 69736561696164762835938725)
      ·
        refine ⟨13075605318030893031738511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69736561696164762835938725 13075605318030893031738511)
        ·
          refine ⟨19613407977046339547607767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075605318030893031738511 19613407977046339547607767)
          ·
            refine ⟨29420111965569509321411651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19613407977046339547607767 29420111965569509321411651)
            ·
              refine ⟨44130167948354263982117477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29420111965569509321411651 44130167948354263982117477)
              ·
                refine ⟨8274406490316424496647027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44130167948354263982117477 8274406490316424496647027)
                ·
                  refine ⟨12411609735474636744970541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274406490316424496647027 12411609735474636744970541)
                  ·
                    refine ⟨4654353650802988779363953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12411609735474636744970541 4654353650802988779363953)
                    ·
                      refine ⟨3490765238102241584522965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654353650802988779363953 3490765238102241584522965)
                      ·
                        rfl

theorem cell23_6798241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6798241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798241 prefixEnd_6798241 := by exact prefixLift 6798241
  have htrace : WordTrace (prefixWord ++ tailWord_6798241) baseStart_6798241 baseEnd_6798241 := by
    simpa [prefixWord, tailWord_6798241, baseEnd_6798241] using wordTrace_append hprefix tailTrace_6798241
  have hstable : (prefixWord ++ tailWord_6798241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798241).length < 2 ^ (prefixWord ++ tailWord_6798241).sum := by decide
  have hdescent : baseEnd_6798241 < baseStart_6798241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798338 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6798338 : Nat := 118140960795 + 6798338 * 2 ^ 59
def prefixEnd_6798338 : Nat := 4983230072969 + 3 ^ 40 * 6798338 * 2
def baseEnd_6798338 : Nat := 3490815045725727705010019

theorem tailTrace_6798338 : CollatzResearch.WordTrace tailWord_6798338 prefixEnd_6798338 3490815045725727705010019 := by
  unfold tailWord_6798338
  simp only [CollatzResearch.WordTrace]
  refine ⟨61988939311197491134626917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165303838163193309692338445 61988939311197491134626917)
  ·
    refine ⟨11622926120849529587742547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61988939311197491134626917 11622926120849529587742547)
    ·
      refine ⟨17434389181274294381613821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11622926120849529587742547 17434389181274294381613821)
      ·
        refine ⟨6537895942977860393105183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17434389181274294381613821 6537895942977860393105183)
        ·
          refine ⟨9806843914466790589657775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6537895942977860393105183 9806843914466790589657775)
          ·
            refine ⟨14710265871700185884486663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9806843914466790589657775 14710265871700185884486663)
            ·
              refine ⟨22065398807550278826729995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14710265871700185884486663 22065398807550278826729995)
              ·
                refine ⟨33098098211325418240094993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22065398807550278826729995 33098098211325418240094993)
                ·
                  refine ⟨24823573658494063680071245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33098098211325418240094993 24823573658494063680071245)
                  ·
                    refine ⟨9308840121935273880026717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24823573658494063680071245 9308840121935273880026717)
                    ·
                      refine ⟨3490815045725727705010019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9308840121935273880026717 3490815045725727705010019)
                      ·
                        rfl

theorem cell23_6798338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6798338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798338 prefixEnd_6798338 := by exact prefixLift 6798338
  have htrace : WordTrace (prefixWord ++ tailWord_6798338) baseStart_6798338 baseEnd_6798338 := by
    simpa [prefixWord, tailWord_6798338, baseEnd_6798338] using wordTrace_append hprefix tailTrace_6798338
  have hstable : (prefixWord ++ tailWord_6798338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798338).length < 2 ^ (prefixWord ++ tailWord_6798338).sum := by decide
  have hdescent : baseEnd_6798338 < baseStart_6798338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798344 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_6798344 : Nat := 118140960795 + 6798344 * 2 ^ 59
def prefixEnd_6798344 : Nat := 4983230072969 + 3 ^ 40 * 6798344 * 2
def baseEnd_6798344 : Nat := 3490818126609654681534991

theorem tailTrace_6798344 : CollatzResearch.WordTrace tailWord_6798344 prefixEnd_6798344 3490818126609654681534991 := by
  unfold tailWord_6798344
  simp only [CollatzResearch.WordTrace]
  refine ⟨123977988041384113781613043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165303984055178818375484057 123977988041384113781613043)
  ·
    refine ⟨185966982062076170672419565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123977988041384113781613043 185966982062076170672419565)
    ·
      refine ⟨69737618273278564002157337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185966982062076170672419565 69737618273278564002157337)
      ·
        refine ⟨52303213704958923001618003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69737618273278564002157337 52303213704958923001618003)
        ·
          refine ⟨78454820557438384502427005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52303213704958923001618003 78454820557438384502427005)
          ·
            refine ⟨29420557709039394188410127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78454820557438384502427005 29420557709039394188410127)
            ·
              refine ⟨44130836563559091282615191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29420557709039394188410127 44130836563559091282615191)
              ·
                refine ⟨66196254845338636923922787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44130836563559091282615191 66196254845338636923922787)
                ·
                  refine ⟨99294382268007955385884181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66196254845338636923922787 99294382268007955385884181)
                  ·
                    refine ⟨4654424168812872908713321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99294382268007955385884181 4654424168812872908713321)
                    ·
                      refine ⟨3490818126609654681534991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654424168812872908713321 3490818126609654681534991)
                      ·
                        rfl

theorem cell23_6798344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_6798344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798344 prefixEnd_6798344 := by exact prefixLift 6798344
  have htrace : WordTrace (prefixWord ++ tailWord_6798344) baseStart_6798344 baseEnd_6798344 := by
    simpa [prefixWord, tailWord_6798344, baseEnd_6798344] using wordTrace_append hprefix tailTrace_6798344
  have hstable : (prefixWord ++ tailWord_6798344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798344).length < 2 ^ (prefixWord ++ tailWord_6798344).sum := by decide
  have hdescent : baseEnd_6798344 < baseStart_6798344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798371 : List Nat := [1, 1, 1, 4, 3, 2, 1, 5, 1, 4]
def baseStart_6798371 : Nat := 118140960795 + 6798371 * 2 ^ 59
def prefixEnd_6798371 : Nat := 4983230072969 + 3 ^ 40 * 6798371 * 2
def baseEnd_6798371 : Nat := 1163610663529108691965789

theorem tailTrace_6798371 : CollatzResearch.WordTrace tailWord_6798371 prefixEnd_6798371 1163610663529108691965789 := by
  unfold tailWord_6798371
  simp only [CollatzResearch.WordTrace]
  refine ⟨247956960853670411174458967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165304640569113607449639311 247956960853670411174458967)
  ·
    refine ⟨371935441280505616761688451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247956960853670411174458967 371935441280505616761688451)
    ·
      refine ⟨557903161920758425142532677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371935441280505616761688451 557903161920758425142532677)
      ·
        refine ⟨104606842860142204714224877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 557903161920758425142532677 104606842860142204714224877)
        ·
          refine ⟨39227566072553326767834329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104606842860142204714224877 39227566072553326767834329)
          ·
            refine ⟨29420674554414995075875747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39227566072553326767834329 29420674554414995075875747)
            ·
              refine ⟨44131011831622492613813621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29420674554414995075875747 44131011831622492613813621)
              ·
                refine ⟨4137282359214608682545027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44131011831622492613813621 4137282359214608682545027)
                ·
                  refine ⟨6205923538821913023817541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137282359214608682545027 6205923538821913023817541)
                  ·
                    refine ⟨1163610663529108691965789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205923538821913023817541 1163610663529108691965789)
                    ·
                      rfl

theorem cell23_6798371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 4].length) (baseStart_6798371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798371 prefixEnd_6798371 := by exact prefixLift 6798371
  have htrace : WordTrace (prefixWord ++ tailWord_6798371) baseStart_6798371 baseEnd_6798371 := by
    simpa [prefixWord, tailWord_6798371, baseEnd_6798371] using wordTrace_append hprefix tailTrace_6798371
  have hstable : (prefixWord ++ tailWord_6798371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798371).length < 2 ^ (prefixWord ++ tailWord_6798371).sum := by decide
  have hdescent : baseEnd_6798371 < baseStart_6798371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798388 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_6798388 : Nat := 118140960795 + 6798388 * 2 ^ 59
def prefixEnd_6798388 : Nat := 4983230072969 + 3 ^ 40 * 6798388 * 2
def baseEnd_6798388 : Nat := 1163613573252817503128263

theorem tailTrace_6798388 : CollatzResearch.WordTrace tailWord_6798388 prefixEnd_6798388 1163613573252817503128263 := by
  unfold tailWord_6798388
  simp only [CollatzResearch.WordTrace]
  refine ⟨123978790447304411538913909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165305053929739215385218545 123978790447304411538913909)
  ·
    refine ⟨11623011604434788581773179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123978790447304411538913909 11623011604434788581773179)
    ·
      refine ⟨17434517406652182872659769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11623011604434788581773179 17434517406652182872659769)
      ·
        refine ⟨13075888054989137154494827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17434517406652182872659769 13075888054989137154494827)
        ·
          refine ⟨19613832082483705731742241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075888054989137154494827 19613832082483705731742241)
          ·
            refine ⟨14710374061862779298806681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19613832082483705731742241 14710374061862779298806681)
            ·
              refine ⟨11032780546397084474105011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14710374061862779298806681 11032780546397084474105011)
              ·
                refine ⟨16549170819595626711157517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11032780546397084474105011 16549170819595626711157517)
                ·
                  refine ⟨6205939057348360016684069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16549170819595626711157517 6205939057348360016684069)
                  ·
                    refine ⟨1163613573252817503128263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205939057348360016684069 1163613573252817503128263)
                    ·
                      rfl

theorem cell23_6798388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_6798388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798388 prefixEnd_6798388 := by exact prefixLift 6798388
  have htrace : WordTrace (prefixWord ++ tailWord_6798388) baseStart_6798388 baseEnd_6798388 := by
    simpa [prefixWord, tailWord_6798388, baseEnd_6798388] using wordTrace_append hprefix tailTrace_6798388
  have hstable : (prefixWord ++ tailWord_6798388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798388).length < 2 ^ (prefixWord ++ tailWord_6798388).sum := by decide
  have hdescent : baseEnd_6798388 < baseStart_6798388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798421 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_6798421 : Nat := 118140960795 + 6798421 * 2 ^ 59
def prefixEnd_6798421 : Nat := 4983230072969 + 3 ^ 40 * 6798421 * 2
def baseEnd_6798421 : Nat := 3490857664620050880272137

theorem tailTrace_6798421 : CollatzResearch.WordTrace tailWord_6798421 prefixEnd_6798421 3490857664620050880272137 := by
  unfold tailWord_6798421
  simp only [CollatzResearch.WordTrace]
  refine ⟨247958784503489269713779117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165305856335659513142519411 247958784503489269713779117)
  ·
    refine ⟨92984544188808476142667169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247958784503489269713779117 92984544188808476142667169)
    ·
      refine ⟨69738408141606357107000377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92984544188808476142667169 69738408141606357107000377)
      ·
        refine ⟨52303806106204767830250283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69738408141606357107000377 52303806106204767830250283)
        ·
          refine ⟨78455709159307151745375425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52303806106204767830250283 78455709159307151745375425)
          ·
            refine ⟨58841781869480363809031569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78455709159307151745375425 58841781869480363809031569)
            ·
              refine ⟨44131336402110272856773677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58841781869480363809031569 44131336402110272856773677)
              ·
                refine ⟨16549251150791352321290129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44131336402110272856773677 16549251150791352321290129)
                ·
                  refine ⟨12411938363093514240967597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16549251150791352321290129 12411938363093514240967597)
                  ·
                    refine ⟨4654476886160067840362849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12411938363093514240967597 4654476886160067840362849)
                    ·
                      refine ⟨3490857664620050880272137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654476886160067840362849 3490857664620050880272137)
                      ·
                        rfl

theorem cell23_6798421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_6798421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798421 prefixEnd_6798421 := by exact prefixLift 6798421
  have htrace : WordTrace (prefixWord ++ tailWord_6798421) baseStart_6798421 baseEnd_6798421 := by
    simpa [prefixWord, tailWord_6798421, baseEnd_6798421] using wordTrace_append hprefix tailTrace_6798421
  have hstable : (prefixWord ++ tailWord_6798421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798421).length < 2 ^ (prefixWord ++ tailWord_6798421).sum := by decide
  have hdescent : baseEnd_6798421 < baseStart_6798421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798444 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_6798444 : Nat := 118140960795 + 6798444 * 2 ^ 59
def prefixEnd_6798444 : Nat := 4983230072969 + 3 ^ 40 * 6798444 * 2
def baseEnd_6798444 : Nat := 1163623158225034763428177

theorem tailTrace_6798444 : CollatzResearch.WordTrace tailWord_6798444 prefixEnd_6798444 1163623158225034763428177 := by
  unfold tailWord_6798444
  simp only [CollatzResearch.WordTrace]
  refine ⟨123979811691202972320933193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165306415588270629761244257 123979811691202972320933193)
  ·
    refine ⟨92984858768402229240699895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123979811691202972320933193 92984858768402229240699895)
    ·
      refine ⟨139477288152603343861049843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92984858768402229240699895 139477288152603343861049843)
      ·
        refine ⟨209215932228905015791574765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139477288152603343861049843 209215932228905015791574765)
        ·
          refine ⟨78455974585839380921840537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209215932228905015791574765 78455974585839380921840537)
          ·
            refine ⟨58841980939379535691380403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78455974585839380921840537 58841980939379535691380403)
            ·
              refine ⟨88262971409069303537070605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58841980939379535691380403 88262971409069303537070605)
              ·
                refine ⟨33098614278400988826401477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88262971409069303537070605 33098614278400988826401477)
                ·
                  refine ⟨6205990177200185404950277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33098614278400988826401477 6205990177200185404950277)
                  ·
                    refine ⟨1163623158225034763428177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6205990177200185404950277 1163623158225034763428177)
                    ·
                      rfl

theorem cell23_6798444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_6798444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798444 prefixEnd_6798444 := by exact prefixLift 6798444
  have htrace : WordTrace (prefixWord ++ tailWord_6798444) baseStart_6798444 baseEnd_6798444 := by
    simpa [prefixWord, tailWord_6798444, baseEnd_6798444] using wordTrace_append hprefix tailTrace_6798444
  have hstable : (prefixWord ++ tailWord_6798444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798444).length < 2 ^ (prefixWord ++ tailWord_6798444).sum := by decide
  have hdescent : baseEnd_6798444 < baseStart_6798444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798447 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_6798447 : Nat := 118140960795 + 6798447 * 2 ^ 59
def prefixEnd_6798447 : Nat := 4983230072969 + 3 ^ 40 * 6798447 * 2
def baseEnd_6798447 : Nat := 3490871015117067778547017

theorem tailTrace_6798447 : CollatzResearch.WordTrace tailWord_6798447 prefixEnd_6798447 3490871015117067778547017 := by
  unfold tailWord_6798447
  simp only [CollatzResearch.WordTrace]
  refine ⟨247959732801395076154225595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165306488534263384102817063 247959732801395076154225595)
  ·
    refine ⟨371939599202092614231338393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247959732801395076154225595 371939599202092614231338393)
    ·
      refine ⟨278954699401569460673503795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371939599202092614231338393 278954699401569460673503795)
      ·
        refine ⟨418432049102354191010255693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278954699401569460673503795 418432049102354191010255693)
        ·
          refine ⟨156912018413382821628845885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418432049102354191010255693 156912018413382821628845885)
          ·
            refine ⟨58842006905018558110817207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156912018413382821628845885 58842006905018558110817207)
            ·
              refine ⟨88263010357527837166225811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58842006905018558110817207 88263010357527837166225811)
              ·
                refine ⟨132394515536291755749338717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88263010357527837166225811 132394515536291755749338717)
                ·
                  refine ⟨49647943326109408406002019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132394515536291755749338717 49647943326109408406002019)
                  ·
                    refine ⟨74471914989164112609003029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49647943326109408406002019 74471914989164112609003029)
                    ·
                      refine ⟨3490871015117067778547017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74471914989164112609003029 3490871015117067778547017)
                      ·
                        rfl

theorem cell23_6798447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_6798447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798447 prefixEnd_6798447 := by exact prefixLift 6798447
  have htrace : WordTrace (prefixWord ++ tailWord_6798447) baseStart_6798447 baseEnd_6798447 := by
    simpa [prefixWord, tailWord_6798447, baseEnd_6798447] using wordTrace_append hprefix tailTrace_6798447
  have hstable : (prefixWord ++ tailWord_6798447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798447).length < 2 ^ (prefixWord ++ tailWord_6798447).sum := by decide
  have hdescent : baseEnd_6798447 < baseStart_6798447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798461 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_6798461 : Nat := 118140960795 + 6798461 * 2 ^ 59
def prefixEnd_6798461 : Nat := 4983230072969 + 3 ^ 40 * 6798461 * 2
def baseEnd_6798461 : Nat := 1163626067948743574590651

theorem tailTrace_6798461 : CollatzResearch.WordTrace tailWord_6798461 prefixEnd_6798461 1163626067948743574590651 := by
  unfold tailWord_6798461
  simp only [CollatzResearch.WordTrace]
  refine ⟨247960243423344356545235237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165306828948896237696823491 247960243423344356545235237)
  ·
    refine ⟨46492545641877066852231607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247960243423344356545235237 46492545641877066852231607)
    ·
      refine ⟨69738818462815600278347411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46492545641877066852231607 69738818462815600278347411)
      ·
        refine ⟨104608227694223400417521117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69738818462815600278347411 104608227694223400417521117)
        ·
          refine ⟨39228085385333775156570419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104608227694223400417521117 39228085385333775156570419)
          ·
            refine ⟨58842128078000662734855629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39228085385333775156570419 58842128078000662734855629)
            ·
              refine ⟨22065798029250248525570861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58842128078000662734855629 22065798029250248525570861)
              ·
                refine ⟨8274674260968843197089073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22065798029250248525570861 8274674260968843197089073)
                ·
                  refine ⟨6206005695726632397816805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8274674260968843197089073 6206005695726632397816805)
                  ·
                    refine ⟨1163626067948743574590651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6206005695726632397816805 1163626067948743574590651)
                    ·
                      rfl

theorem cell23_6798461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_6798461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798461 prefixEnd_6798461 := by exact prefixLift 6798461
  have htrace : WordTrace (prefixWord ++ tailWord_6798461) baseStart_6798461 baseEnd_6798461 := by
    simpa [prefixWord, tailWord_6798461, baseEnd_6798461] using wordTrace_append hprefix tailTrace_6798461
  have hstable : (prefixWord ++ tailWord_6798461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798461).length < 2 ^ (prefixWord ++ tailWord_6798461).sum := by decide
  have hdescent : baseEnd_6798461 < baseStart_6798461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798468 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_6798468 : Nat := 118140960795 + 6798468 * 2 ^ 59
def prefixEnd_6798468 : Nat := 4983230072969 + 3 ^ 40 * 6798468 * 2
def baseEnd_6798468 : Nat := 3490881798210812196384421

theorem tailTrace_6798468 : CollatzResearch.WordTrace tailWord_6798468 prefixEnd_6798468 3490881798210812196384421 := by
  unfold tailWord_6798468
  simp only [CollatzResearch.WordTrace]
  refine ⟨123980249367159498370370029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165306999156212664493826705 123980249367159498370370029)
  ·
    refine ⟨46492593512684811888888761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123980249367159498370370029 46492593512684811888888761)
    ·
      refine ⟨34869445134513608916666571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46492593512684811888888761 34869445134513608916666571)
      ·
        refine ⟨52304167701770413374999857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34869445134513608916666571 52304167701770413374999857)
        ·
          refine ⟨39228125776327810031249893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52304167701770413374999857 39228125776327810031249893)
          ·
            refine ⟨7355273583061464380859355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39228125776327810031249893 7355273583061464380859355)
            ·
              refine ⟨11032910374592196571289033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355273583061464380859355 11032910374592196571289033)
              ·
                refine ⟨8274682780944147428466775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11032910374592196571289033 8274682780944147428466775)
                ·
                  refine ⟨12412024171416221142700163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8274682780944147428466775 12412024171416221142700163)
                  ·
                    refine ⟨18618036257124331714050245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12412024171416221142700163 18618036257124331714050245)
                    ·
                      refine ⟨3490881798210812196384421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18618036257124331714050245 3490881798210812196384421)
                      ·
                        rfl

theorem cell23_6798468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_6798468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798468 prefixEnd_6798468 := by exact prefixLift 6798468
  have htrace : WordTrace (prefixWord ++ tailWord_6798468) baseStart_6798468 baseEnd_6798468 := by
    simpa [prefixWord, tailWord_6798468, baseEnd_6798468] using wordTrace_append hprefix tailTrace_6798468
  have hstable : (prefixWord ++ tailWord_6798468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798468).length < 2 ^ (prefixWord ++ tailWord_6798468).sum := by decide
  have hdescent : baseEnd_6798468 < baseStart_6798468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798511 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 3, 3, 2]
def baseStart_6798511 : Nat := 118140960795 + 6798511 * 2 ^ 59
def prefixEnd_6798511 : Nat := 4983230072969 + 3 ^ 40 * 6798511 * 2
def baseEnd_6798511 : Nat := 3490903877878955528146723

theorem tailTrace_6798511 : CollatzResearch.WordTrace tailWord_6798511 prefixEnd_6798511 3490903877878955528146723 := by
  unfold tailWord_6798511
  simp only [CollatzResearch.WordTrace]
  refine ⟨247962067073163215084555387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165308044715442143389703591 247962067073163215084555387)
  ·
    refine ⟨371943100609744822626833081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247962067073163215084555387 371943100609744822626833081)
    ·
      refine ⟨278957325457308616970124811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371943100609744822626833081 278957325457308616970124811)
      ·
        refine ⟨418435988185962925455187217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278957325457308616970124811 418435988185962925455187217)
        ·
          refine ⟨313826991139472194091390413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418435988185962925455187217 313826991139472194091390413)
          ·
            refine ⟨117685121677302072784271405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313826991139472194091390413 117685121677302072784271405)
            ·
              refine ⟨44131920628988277294101777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117685121677302072784271405 44131920628988277294101777)
              ·
                refine ⟨33098940471741207970576333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44131920628988277294101777 33098940471741207970576333)
                ·
                  refine ⟨12412102676902952988966125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33098940471741207970576333 12412102676902952988966125)
                  ·
                    refine ⟨4654538503838607370862297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12412102676902952988966125 4654538503838607370862297)
                    ·
                      refine ⟨3490903877878955528146723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654538503838607370862297 3490903877878955528146723)
                      ·
                        rfl

theorem cell23_6798511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3, 2].length) (baseStart_6798511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798511 prefixEnd_6798511 := by exact prefixLift 6798511
  have htrace : WordTrace (prefixWord ++ tailWord_6798511) baseStart_6798511 baseEnd_6798511 := by
    simpa [prefixWord, tailWord_6798511, baseEnd_6798511] using wordTrace_append hprefix tailTrace_6798511
  have hstable : (prefixWord ++ tailWord_6798511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798511).length < 2 ^ (prefixWord ++ tailWord_6798511).sum := by decide
  have hdescent : baseEnd_6798511 < baseStart_6798511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798552 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 2, 1, 3]
def baseStart_6798552 : Nat := 118140960795 + 6798552 * 2 ^ 59
def prefixEnd_6798552 : Nat := 4983230072969 + 3 ^ 40 * 6798552 * 2
def baseEnd_6798552 : Nat := 3490924930585789867734035

theorem tailTrace_6798552 : CollatzResearch.WordTrace tailWord_6798552 prefixEnd_6798552 3490924930585789867734035 := by
  unfold tailWord_6798552
  simp only [CollatzResearch.WordTrace]
  refine ⟨123981781233007339543398955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165309041644009786057865273 123981781233007339543398955)
  ·
    refine ⟨185972671849511009315098433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123981781233007339543398955 185972671849511009315098433)
    ·
      refine ⟨139479503887133256986323825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185972671849511009315098433 139479503887133256986323825)
      ·
        refine ⟨104609627915349942739742869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139479503887133256986323825 104609627915349942739742869)
        ·
          refine ⟨4903576308532028565925447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104609627915349942739742869 4903576308532028565925447)
          ·
            refine ⟨7355364462798042848888171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903576308532028565925447 7355364462798042848888171)
            ·
              refine ⟨11033046694197064273332257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355364462798042848888171 11033046694197064273332257)
              ·
                refine ⟨8274785020647798204999193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11033046694197064273332257 8274785020647798204999193)
                ·
                  refine ⟨6206088765485848653749395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8274785020647798204999193 6206088765485848653749395)
                  ·
                    refine ⟨9309133148228772980624093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6206088765485848653749395 9309133148228772980624093)
                    ·
                      refine ⟨3490924930585789867734035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9309133148228772980624093 3490924930585789867734035)
                      ·
                        rfl

theorem cell23_6798552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_6798552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798552 prefixEnd_6798552 := by exact prefixLift 6798552
  have htrace : WordTrace (prefixWord ++ tailWord_6798552) baseStart_6798552 baseEnd_6798552 := by
    simpa [prefixWord, tailWord_6798552, baseEnd_6798552] using wordTrace_append hprefix tailTrace_6798552
  have hstable : (prefixWord ++ tailWord_6798552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798552).length < 2 ^ (prefixWord ++ tailWord_6798552).sum := by decide
  have hdescent : baseEnd_6798552 < baseStart_6798552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798564 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 7]
def baseStart_6798564 : Nat := 118140960795 + 6798564 * 2 ^ 59
def prefixEnd_6798564 : Nat := 4983230072969 + 3 ^ 40 * 6798564 * 2
def baseEnd_6798564 : Nat := 387881232483738202309331

theorem tailTrace_6798564 : CollatzResearch.WordTrace tailWord_6798564 prefixEnd_6798564 387881232483738202309331 := by
  unfold tailWord_6798564
  simp only [CollatzResearch.WordTrace]
  refine ⟨123982000070985602568117373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165309333427980803424156497 123982000070985602568117373)
  ·
    refine ⟨46493250026619600963044015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123982000070985602568117373 46493250026619600963044015)
    ·
      refine ⟨69739875039929401444566023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46493250026619600963044015 69739875039929401444566023)
      ·
        refine ⟨104609812559894102166849035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69739875039929401444566023 104609812559894102166849035)
        ·
          refine ⟨156914718839841153250273553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104609812559894102166849035 156914718839841153250273553)
          ·
            refine ⟨117686039129880864937705165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156914718839841153250273553 117686039129880864937705165)
            ·
              refine ⟨44132264673705324351639437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117686039129880864937705165 44132264673705324351639437)
              ·
                refine ⟨16549599252639496631864789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44132264673705324351639437 16549599252639496631864789)
                ·
                  refine ⟨387881232483738202309331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16549599252639496631864789 387881232483738202309331)
                  ·
                    rfl

theorem cell23_6798564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_6798564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798564 prefixEnd_6798564 := by exact prefixLift 6798564
  have htrace : WordTrace (prefixWord ++ tailWord_6798564) baseStart_6798564 baseEnd_6798564 := by
    simpa [prefixWord, tailWord_6798564, baseEnd_6798564] using wordTrace_append hprefix tailTrace_6798564
  have hstable : (prefixWord ++ tailWord_6798564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798564).length < 2 ^ (prefixWord ++ tailWord_6798564).sum := by decide
  have hdescent : baseEnd_6798564 < baseStart_6798564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798575 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 1, 4, 2]
def baseStart_6798575 : Nat := 118140960795 + 6798575 * 2 ^ 59
def prefixEnd_6798575 : Nat := 4983230072969 + 3 ^ 40 * 6798575 * 2
def baseEnd_6798575 : Nat := 3490936740640843277746429

theorem tailTrace_6798575 : CollatzResearch.WordTrace tailWord_6798575 prefixEnd_6798575 3490936740640843277746429 := by
  unfold tailWord_6798575
  simp only [CollatzResearch.WordTrace]
  refine ⟨247964401344931354014885179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165309600896620902676590119 247964401344931354014885179)
  ·
    refine ⟨371946602017397031022327769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247964401344931354014885179 371946602017397031022327769)
    ·
      refine ⟨278959951513047773266745827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371946602017397031022327769 278959951513047773266745827)
      ·
        refine ⟨418439927269571659900118741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278959951513047773266745827 418439927269571659900118741)
        ·
          refine ⟨9807185795380585778909033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 418439927269571659900118741 9807185795380585778909033)
          ·
            refine ⟨7355389346535439334181775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9807185795380585778909033 7355389346535439334181775)
            ·
              refine ⟨11033084019803159001272663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355389346535439334181775 11033084019803159001272663)
              ·
                refine ⟨16549626029704738501908995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11033084019803159001272663 16549626029704738501908995)
                ·
                  refine ⟨24824439044557107752863493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16549626029704738501908995 24824439044557107752863493)
                  ·
                    refine ⟨4654582320854457703661905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24824439044557107752863493 4654582320854457703661905)
                    ·
                      refine ⟨3490936740640843277746429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654582320854457703661905 3490936740640843277746429)
                      ·
                        rfl

theorem cell23_6798575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 4, 2].length) (baseStart_6798575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798575 prefixEnd_6798575 := by exact prefixLift 6798575
  have htrace : WordTrace (prefixWord ++ tailWord_6798575) baseStart_6798575 baseEnd_6798575 := by
    simpa [prefixWord, tailWord_6798575, baseEnd_6798575] using wordTrace_append hprefix tailTrace_6798575
  have hstable : (prefixWord ++ tailWord_6798575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798575).length < 2 ^ (prefixWord ++ tailWord_6798575).sum := by decide
  have hdescent : baseEnd_6798575 < baseStart_6798575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798621 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6798621 : Nat := 118140960795 + 6798621 * 2 ^ 59
def prefixEnd_6798621 : Nat := 4983230072969 + 3 ^ 40 * 6798621 * 2
def baseEnd_6798621 : Nat := 3490960360750950097771217

theorem tailTrace_6798621 : CollatzResearch.WordTrace tailWord_6798621 prefixEnd_6798621 3490960360750950097771217 := by
  unfold tailWord_6798621
  simp only [CollatzResearch.WordTrace]
  refine ⟨247966079102764703871059717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165310719401843135914039811 247966079102764703871059717)
  ·
    refine ⟨46493639831768381975823697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247966079102764703871059717 46493639831768381975823697)
    ·
      refine ⟨34870229873826286481867773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46493639831768381975823697 34870229873826286481867773)
      ·
        refine ⟨13076336202684857430700415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34870229873826286481867773 13076336202684857430700415)
        ·
          refine ⟨19614504304027286146050623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13076336202684857430700415 19614504304027286146050623)
          ·
            refine ⟨29421756456040929219075935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19614504304027286146050623 29421756456040929219075935)
            ·
              refine ⟨44132634684061393828613903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29421756456040929219075935 44132634684061393828613903)
              ·
                refine ⟨66198952026092090742920855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44132634684061393828613903 66198952026092090742920855)
                ·
                  refine ⟨99298428039138136114381283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66198952026092090742920855 99298428039138136114381283)
                  ·
                    refine ⟨148947642058707204171571925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99298428039138136114381283 148947642058707204171571925)
                    ·
                      refine ⟨3490960360750950097771217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148947642058707204171571925 3490960360750950097771217)
                      ·
                        rfl

theorem cell23_6798621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6798621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798621 prefixEnd_6798621 := by exact prefixLift 6798621
  have htrace : WordTrace (prefixWord ++ tailWord_6798621) baseStart_6798621 baseEnd_6798621 := by
    simpa [prefixWord, tailWord_6798621, baseEnd_6798621] using wordTrace_append hprefix tailTrace_6798621
  have hstable : (prefixWord ++ tailWord_6798621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798621).length < 2 ^ (prefixWord ++ tailWord_6798621).sum := by decide
  have hdescent : baseEnd_6798621 < baseStart_6798621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798626 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_6798626 : Nat := 118140960795 + 6798626 * 2 ^ 59
def prefixEnd_6798626 : Nat := 4983230072969 + 3 ^ 40 * 6798626 * 2
def baseEnd_6798626 : Nat := 3490962928154222578208695

theorem tailTrace_6798626 : CollatzResearch.WordTrace tailWord_6798626 prefixEnd_6798626 3490962928154222578208695 := by
  unfold tailWord_6798626
  simp only [CollatzResearch.WordTrace]
  refine ⟨61991565366936647431247933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165310840978497726483327821 61991565366936647431247933)
  ·
    refine ⟨23246837012601242786717975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61991565366936647431247933 23246837012601242786717975)
    ·
      refine ⟨34870255518901864180076963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23246837012601242786717975 34870255518901864180076963)
      ·
        refine ⟨52305383278352796270115445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34870255518901864180076963 52305383278352796270115445)
        ·
          refine ⟨4903629682345574650323323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52305383278352796270115445 4903629682345574650323323)
          ·
            refine ⟨7355444523518361975484985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4903629682345574650323323 7355444523518361975484985)
            ·
              refine ⟨5516583392638771481613739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7355444523518361975484985 5516583392638771481613739)
              ·
                refine ⟨8274875088958157222420609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516583392638771481613739 8274875088958157222420609)
                ·
                  refine ⟨6206156316718617916815457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8274875088958157222420609 6206156316718617916815457)
                  ·
                    refine ⟨4654617237538963437611593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6206156316718617916815457 4654617237538963437611593)
                    ·
                      refine ⟨3490962928154222578208695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654617237538963437611593 3490962928154222578208695)
                      ·
                        rfl

theorem cell23_6798626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_6798626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798626 prefixEnd_6798626 := by exact prefixLift 6798626
  have htrace : WordTrace (prefixWord ++ tailWord_6798626) baseStart_6798626 baseEnd_6798626 := by
    simpa [prefixWord, tailWord_6798626, baseEnd_6798626] using wordTrace_append hprefix tailTrace_6798626
  have hstable : (prefixWord ++ tailWord_6798626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798626).length < 2 ^ (prefixWord ++ tailWord_6798626).sum := by decide
  have hdescent : baseEnd_6798626 < baseStart_6798626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798668 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_6798668 : Nat := 118140960795 + 6798668 * 2 ^ 59
def prefixEnd_6798668 : Nat := 4983230072969 + 3 ^ 40 * 6798668 * 2
def baseEnd_6798668 : Nat := 3490984494341711413883501

theorem tailTrace_6798668 : CollatzResearch.WordTrace tailWord_6798668 prefixEnd_6798668 3490984494341711413883501 := by
  unfold tailWord_6798668
  simp only [CollatzResearch.WordTrace]
  refine ⟨123983896666797215449010329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165311862222396287265347105 123983896666797215449010329)
  ·
    refine ⟨92987922500097911586757747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123983896666797215449010329 92987922500097911586757747)
    ·
      refine ⟨139481883750146867380136621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92987922500097911586757747 139481883750146867380136621)
      ·
        refine ⟨52305706406305075267551233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139481883750146867380136621 52305706406305075267551233)
        ·
          refine ⟨39229279804728806450663425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52305706406305075267551233 39229279804728806450663425)
          ·
            refine ⟨29421959853546604837997569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39229279804728806450663425 29421959853546604837997569)
            ·
              refine ⟨22066469890159953628498177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29421959853546604837997569 22066469890159953628498177)
              ·
                refine ⟨16549852417619965221373633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22066469890159953628498177 16549852417619965221373633)
                ·
                  refine ⟨12412389313214973916030225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16549852417619965221373633 12412389313214973916030225)
                  ·
                    refine ⟨9309291984911230437022669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12412389313214973916030225 9309291984911230437022669)
                    ·
                      refine ⟨3490984494341711413883501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9309291984911230437022669 3490984494341711413883501)
                      ·
                        rfl

theorem cell23_6798668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_6798668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798668 prefixEnd_6798668 := by exact prefixLift 6798668
  have htrace : WordTrace (prefixWord ++ tailWord_6798668) baseStart_6798668 baseEnd_6798668 := by
    simpa [prefixWord, tailWord_6798668, baseEnd_6798668] using wordTrace_append hprefix tailTrace_6798668
  have hstable : (prefixWord ++ tailWord_6798668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798668).length < 2 ^ (prefixWord ++ tailWord_6798668).sum := by decide
  have hdescent : baseEnd_6798668 < baseStart_6798668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798722 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 6]
def baseStart_6798722 : Nat := 118140960795 + 6798722 * 2 ^ 59
def prefixEnd_6798722 : Nat := 4983230072969 + 3 ^ 40 * 6798722 * 2
def baseEnd_6798722 : Nat := 387890246921894911400917

theorem tailTrace_6798722 : CollatzResearch.WordTrace tailWord_6798722 prefixEnd_6798722 387890246921894911400917 := by
  unfold tailWord_6798722
  simp only [CollatzResearch.WordTrace]
  refine ⟨61992440718849699530121605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165313175250265865413657613 61992440718849699530121605)
  ·
    refine ⟨11623582634784318661897801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61992440718849699530121605 11623582634784318661897801)
    ·
      refine ⟨8717686976088238996423351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11623582634784318661897801 8717686976088238996423351)
      ·
        refine ⟨13076530464132358494635027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717686976088238996423351 13076530464132358494635027)
        ·
          refine ⟨19614795696198537741952541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13076530464132358494635027 19614795696198537741952541)
          ·
            refine ⟨7355548386074451653232203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19614795696198537741952541 7355548386074451653232203)
            ·
              refine ⟨11033322579111677479848305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7355548386074451653232203 11033322579111677479848305)
              ·
                refine ⟨8274991934333758109886229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11033322579111677479848305 8274991934333758109886229)
                ·
                  refine ⟨387890246921894911400917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8274991934333758109886229 387890246921894911400917)
                  ·
                    rfl

theorem cell23_6798722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_6798722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798722 prefixEnd_6798722 := by exact prefixLift 6798722
  have htrace : WordTrace (prefixWord ++ tailWord_6798722) baseStart_6798722 baseEnd_6798722 := by
    simpa [prefixWord, tailWord_6798722, baseEnd_6798722] using wordTrace_append hprefix tailTrace_6798722
  have hstable : (prefixWord ++ tailWord_6798722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798722).length < 2 ^ (prefixWord ++ tailWord_6798722).sum := by decide
  have hdescent : baseEnd_6798722 < baseStart_6798722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798741 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_6798741 : Nat := 118140960795 + 6798741 * 2 ^ 59
def prefixEnd_6798741 : Nat := 4983230072969 + 3 ^ 40 * 6798741 * 2
def baseEnd_6798741 : Nat := 3491021978429489628270665

theorem tailTrace_6798741 : CollatzResearch.WordTrace tailWord_6798741 prefixEnd_6798741 3491021978429489628270665 := by
  unfold tailWord_6798741
  simp only [CollatzResearch.WordTrace]
  refine ⟨247970455862329964365428077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165313637241553309576952051 247970455862329964365428077)
  ·
    refine ⟨92988920948373736637035529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247970455862329964365428077 92988920948373736637035529)
    ·
      refine ⟨69741690711280302477776647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92988920948373736637035529 69741690711280302477776647)
      ·
        refine ⟨104612536066920453716664971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69741690711280302477776647 104612536066920453716664971)
        ·
          refine ⟨156918804100380680574997457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104612536066920453716664971 156918804100380680574997457)
          ·
            refine ⟨117689103075285510431248093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156918804100380680574997457 117689103075285510431248093)
            ·
              refine ⟨44133413653232066411718035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117689103075285510431248093 44133413653232066411718035)
              ·
                refine ⟨66200120479848099617577053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44133413653232066411718035 66200120479848099617577053)
                ·
                  refine ⟨24825045179943037356591395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66200120479848099617577053 24825045179943037356591395)
                  ·
                    refine ⟨37237567769914556034887093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24825045179943037356591395 37237567769914556034887093)
                    ·
                      refine ⟨3491021978429489628270665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37237567769914556034887093 3491021978429489628270665)
                      ·
                        rfl

theorem cell23_6798741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_6798741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798741 prefixEnd_6798741 := by exact prefixLift 6798741
  have htrace : WordTrace (prefixWord ++ tailWord_6798741) baseStart_6798741 baseEnd_6798741 := by
    simpa [prefixWord, tailWord_6798741, baseEnd_6798741] using wordTrace_append hprefix tailTrace_6798741
  have hstable : (prefixWord ++ tailWord_6798741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798741).length < 2 ^ (prefixWord ++ tailWord_6798741).sum := by decide
  have hdescent : baseEnd_6798741 < baseStart_6798741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798755 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 3, 2, 2]
def baseStart_6798755 : Nat := 118140960795 + 6798755 * 2 ^ 59
def prefixEnd_6798755 : Nat := 4983230072969 + 3 ^ 40 * 6798755 * 2
def baseEnd_6798755 : Nat := 3491029167158652573495601

theorem tailTrace_6798755 : CollatzResearch.WordTrace tailWord_6798755 prefixEnd_6798755 3491029167158652573495601 := by
  unfold tailWord_6798755
  simp only [CollatzResearch.WordTrace]
  refine ⟨247970966484279244756437719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165313977656186163170958479 247970966484279244756437719)
  ·
    refine ⟨371956449726418867134656579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247970966484279244756437719 371956449726418867134656579)
    ·
      refine ⟨557934674589628300701984869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371956449726418867134656579 557934674589628300701984869)
      ·
        refine ⟨104612751485555306381622163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 557934674589628300701984869 104612751485555306381622163)
        ·
          refine ⟨156919127228332959572433245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104612751485555306381622163 156919127228332959572433245)
          ·
            refine ⟨58844672710624859839662467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156919127228332959572433245 58844672710624859839662467)
            ·
              refine ⟨88267009065937289759493701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58844672710624859839662467 88267009065937289759493701)
              ·
                refine ⟨16550064199863241829905069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88267009065937289759493701 16550064199863241829905069)
                ·
                  refine ⟨6206274074948715686214401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16550064199863241829905069 6206274074948715686214401)
                  ·
                    refine ⟨4654705556211536764660801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6206274074948715686214401 4654705556211536764660801)
                    ·
                      refine ⟨3491029167158652573495601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654705556211536764660801 3491029167158652573495601)
                      ·
                        rfl

theorem cell23_6798755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_6798755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798755 prefixEnd_6798755 := by exact prefixLift 6798755
  have htrace : WordTrace (prefixWord ++ tailWord_6798755) baseStart_6798755 baseEnd_6798755 := by
    simpa [prefixWord, tailWord_6798755, baseEnd_6798755] using wordTrace_append hprefix tailTrace_6798755
  have hstable : (prefixWord ++ tailWord_6798755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798755).length < 2 ^ (prefixWord ++ tailWord_6798755).sum := by decide
  have hdescent : baseEnd_6798755 < baseStart_6798755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798765 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_6798765 : Nat := 118140960795 + 6798765 * 2 ^ 59
def prefixEnd_6798765 : Nat := 4983230072969 + 3 ^ 40 * 6798765 * 2
def baseEnd_6798765 : Nat := 1163678100655065844790185

theorem tailTrace_6798765 : CollatzResearch.WordTrace tailWord_6798765 prefixEnd_6798765 1163678100655065844790185 := by
  unfold tailWord_6798765
  simp only [CollatzResearch.WordTrace]
  refine ⟨247971331214243016464301749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165314220809495344309534499 247971331214243016464301749)
  ·
    refine ⟨23247312301335282793528289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247971331214243016464301749 23247312301335282793528289)
    ·
      refine ⟨17435484226001462095146217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23247312301335282793528289 17435484226001462095146217)
      ·
        refine ⟨13076613169501096571359663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17435484226001462095146217 13076613169501096571359663)
        ·
          refine ⟨19614919754251644857039495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13076613169501096571359663 19614919754251644857039495)
          ·
            refine ⟨29422379631377467285559243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19614919754251644857039495 29422379631377467285559243)
            ·
              refine ⟨44133569447066200928338865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29422379631377467285559243 44133569447066200928338865)
              ·
                refine ⟨33100177085299650696254149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44133569447066200928338865 33100177085299650696254149)
                ·
                  refine ⟨6206283203493684505547653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33100177085299650696254149 6206283203493684505547653)
                  ·
                    refine ⟨1163678100655065844790185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6206283203493684505547653 1163678100655065844790185)
                    ·
                      rfl

theorem cell23_6798765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_6798765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798765 prefixEnd_6798765 := by exact prefixLift 6798765
  have htrace : WordTrace (prefixWord ++ tailWord_6798765) baseStart_6798765 baseEnd_6798765 := by
    simpa [prefixWord, tailWord_6798765, baseEnd_6798765] using wordTrace_append hprefix tailTrace_6798765
  have hstable : (prefixWord ++ tailWord_6798765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798765).length < 2 ^ (prefixWord ++ tailWord_6798765).sum := by decide
  have hdescent : baseEnd_6798765 < baseStart_6798765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798791 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 2, 7]
def baseStart_6798791 : Nat := 118140960795 + 6798791 * 2 ^ 59
def prefixEnd_6798791 : Nat := 4983230072969 + 3 ^ 40 * 6798791 * 2
def baseEnd_6798791 : Nat := 1163682550820738144215145

theorem tailTrace_6798791 : CollatzResearch.WordTrace tailWord_6798791 prefixEnd_6798791 1163682550820738144215145 := by
  unfold tailWord_6798791
  simp only [CollatzResearch.WordTrace]
  refine ⟨247972279512148822904748227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165314853008099215269832151 247972279512148822904748227)
  ·
    refine ⟨371958419268223234357122341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247972279512148822904748227 371958419268223234357122341)
    ·
      refine ⟨69742203612791856441960439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 371958419268223234357122341 69742203612791856441960439)
      ·
        refine ⟨104613305419187784662940659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69742203612791856441960439 104613305419187784662940659)
        ·
          refine ⟨156919958128781676994410989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104613305419187784662940659 156919958128781676994410989)
          ·
            refine ⟨58844984298293128872904121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156919958128781676994410989 58844984298293128872904121)
            ·
              refine ⟨44133738223719846654678091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58844984298293128872904121 44133738223719846654678091)
              ·
                refine ⟨66200607335579769982017137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44133738223719846654678091 66200607335579769982017137)
                ·
                  refine ⟨49650455501684827486512853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66200607335579769982017137 49650455501684827486512853)
                  ·
                    refine ⟨1163682550820738144215145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49650455501684827486512853 1163682550820738144215145)
                    ·
                      rfl

theorem cell23_6798791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_6798791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798791 prefixEnd_6798791 := by exact prefixLift 6798791
  have htrace : WordTrace (prefixWord ++ tailWord_6798791) baseStart_6798791 baseEnd_6798791 := by
    simpa [prefixWord, tailWord_6798791, baseEnd_6798791] using wordTrace_append hprefix tailTrace_6798791
  have hstable : (prefixWord ++ tailWord_6798791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798791).length < 2 ^ (prefixWord ++ tailWord_6798791).sum := by decide
  have hdescent : baseEnd_6798791 < baseStart_6798791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798815 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 3, 3, 2]
def baseStart_6798815 : Nat := 118140960795 + 6798815 * 2 ^ 59
def prefixEnd_6798815 : Nat := 4983230072969 + 3 ^ 40 * 6798815 * 2
def baseEnd_6798815 : Nat := 3491059975997922338745325

theorem tailTrace_6798815 : CollatzResearch.WordTrace tailWord_6798815 prefixEnd_6798815 3491059975997922338745325 := by
  unfold tailWord_6798815
  simp only [CollatzResearch.WordTrace]
  refine ⟨247973154864061875003621899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165315436576041250002414599 247973154864061875003621899)
  ·
    refine ⟨371959732296092812505432849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247973154864061875003621899 371959732296092812505432849)
    ·
      refine ⟨278969799222069609379074637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371959732296092812505432849 278969799222069609379074637)
      ·
        refine ⟨104613674708276103517152989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278969799222069609379074637 104613674708276103517152989)
        ·
          refine ⟨39230128015603538818932371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104613674708276103517152989 39230128015603538818932371)
          ·
            refine ⟨58845192023405308228398557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39230128015603538818932371 58845192023405308228398557)
            ·
              refine ⟨22066947008776990585649459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58845192023405308228398557 22066947008776990585649459)
              ·
                refine ⟨33100420513165485878474189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22066947008776990585649459 33100420513165485878474189)
                ·
                  refine ⟨12412657692437057204427821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33100420513165485878474189 12412657692437057204427821)
                  ·
                    refine ⟨4654746634663896451660433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12412657692437057204427821 4654746634663896451660433)
                    ·
                      refine ⟨3491059975997922338745325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654746634663896451660433 3491059975997922338745325)
                      ·
                        rfl

theorem cell23_6798815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_6798815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798815 prefixEnd_6798815 := by exact prefixLift 6798815
  have htrace : WordTrace (prefixWord ++ tailWord_6798815) baseStart_6798815 baseEnd_6798815 := by
    simpa [prefixWord, tailWord_6798815, baseEnd_6798815] using wordTrace_append hprefix tailTrace_6798815
  have hstable : (prefixWord ++ tailWord_6798815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798815).length < 2 ^ (prefixWord ++ tailWord_6798815).sum := by decide
  have hdescent : baseEnd_6798815 < baseStart_6798815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798841 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6798841 : Nat := 118140960795 + 6798841 * 2 ^ 59
def prefixEnd_6798841 : Nat := 4983230072969 + 3 ^ 40 * 6798841 * 2
def baseEnd_6798841 : Nat := 3491073326494939237020205

theorem tailTrace_6798841 : CollatzResearch.WordTrace tailWord_6798841 prefixEnd_6798841 3491073326494939237020205 := by
  unfold tailWord_6798841
  simp only [CollatzResearch.WordTrace]
  refine ⟨247974103161967681444068377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165316068774645120962712251 247974103161967681444068377)
  ·
    refine ⟨185980577371475761083051283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247974103161967681444068377 185980577371475761083051283)
    ·
      refine ⟨278970866057213641624576925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185980577371475761083051283 278970866057213641624576925)
      ·
        refine ⟨104614074771455115609216347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278970866057213641624576925 104614074771455115609216347)
        ·
          refine ⟨156921112157182673413824521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104614074771455115609216347 156921112157182673413824521)
          ·
            refine ⟨117690834117887005060368391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156921112157182673413824521 117690834117887005060368391)
            ·
              refine ⟨176536251176830507590552587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117690834117887005060368391 176536251176830507590552587)
              ·
                refine ⟨264804376765245761385828881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176536251176830507590552587 264804376765245761385828881)
                ·
                  refine ⟨198603282573934321039371661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264804376765245761385828881 198603282573934321039371661)
                  ·
                    refine ⟨74476230965225370389764373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198603282573934321039371661 74476230965225370389764373)
                    ·
                      refine ⟨3491073326494939237020205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74476230965225370389764373 3491073326494939237020205)
                      ·
                        rfl

theorem cell23_6798841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6798841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798841 prefixEnd_6798841 := by exact prefixLift 6798841
  have htrace : WordTrace (prefixWord ++ tailWord_6798841) baseStart_6798841 baseEnd_6798841 := by
    simpa [prefixWord, tailWord_6798841, baseEnd_6798841] using wordTrace_append hprefix tailTrace_6798841
  have hstable : (prefixWord ++ tailWord_6798841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798841).length < 2 ^ (prefixWord ++ tailWord_6798841).sum := by decide
  have hdescent : baseEnd_6798841 < baseStart_6798841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798858 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_6798858 : Nat := 118140960795 + 6798858 * 2 ^ 59
def prefixEnd_6798858 : Nat := 4983230072969 + 3 ^ 40 * 6798858 * 2
def baseEnd_6798858 : Nat := 3491082055666065670507627

theorem tailTrace_6798858 : CollatzResearch.WordTrace tailWord_6798858 prefixEnd_6798858 3491082055666065670507627 := by
  unfold tailWord_6798858
  simp only [CollatzResearch.WordTrace]
  refine ⟨61993680800726523336859307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165316482135270728898291485 61993680800726523336859307)
  ·
    refine ⟨92990521201089785005288961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61993680800726523336859307 92990521201089785005288961)
    ·
      refine ⟨69742890900817338753966721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92990521201089785005288961 69742890900817338753966721)
      ·
        refine ⟨52307168175613004065475041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69742890900817338753966721 52307168175613004065475041)
        ·
          refine ⟨39230376131709753049106281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52307168175613004065475041 39230376131709753049106281)
          ·
            refine ⟨29422782098782314786829711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39230376131709753049106281 29422782098782314786829711)
            ·
              refine ⟨44134173148173472180244567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29422782098782314786829711 44134173148173472180244567)
              ·
                refine ⟨66201259722260208270366851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44134173148173472180244567 66201259722260208270366851)
                ·
                  refine ⟨99301889583390312405550277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66201259722260208270366851 99301889583390312405550277)
                  ·
                    refine ⟨18619104296885683576040677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99301889583390312405550277 18619104296885683576040677)
                    ·
                      refine ⟨3491082055666065670507627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18619104296885683576040677 3491082055666065670507627)
                      ·
                        rfl

theorem cell23_6798858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_6798858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798858 prefixEnd_6798858 := by exact prefixLift 6798858
  have htrace : WordTrace (prefixWord ++ tailWord_6798858) baseStart_6798858 baseEnd_6798858 := by
    simpa [prefixWord, tailWord_6798858, baseEnd_6798858] using wordTrace_append hprefix tailTrace_6798858
  have hstable : (prefixWord ++ tailWord_6798858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798858).length < 2 ^ (prefixWord ++ tailWord_6798858).sum := by decide
  have hdescent : baseEnd_6798858 < baseStart_6798858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798898 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_6798898 : Nat := 118140960795 + 6798898 * 2 ^ 59
def prefixEnd_6798898 : Nat := 4983230072969 + 3 ^ 40 * 6798898 * 2
def baseEnd_6798898 : Nat := 1163700864964081838002481

theorem tailTrace_6798898 : CollatzResearch.WordTrace tailWord_6798898 prefixEnd_6798898 1163700864964081838002481 := by
  unfold tailWord_6798898
  simp only [CollatzResearch.WordTrace]
  refine ⟨61994045530690295044723337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165317454748507453452595565 61994045530690295044723337)
  ·
    refine ⟨46495534148017721283542503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61994045530690295044723337 46495534148017721283542503)
    ·
      refine ⟨69743301222026581925313755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46495534148017721283542503 69743301222026581925313755)
      ·
        refine ⟨104614951833039872887970633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69743301222026581925313755 104614951833039872887970633)
        ·
          refine ⟨78461213874779904665977975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104614951833039872887970633 78461213874779904665977975)
          ·
            refine ⟨117691820812169856998966963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78461213874779904665977975 117691820812169856998966963)
            ·
              refine ⟨176537731218254785498450445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117691820812169856998966963 176537731218254785498450445)
              ·
                refine ⟨66201649206845544561918917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176537731218254785498450445 66201649206845544561918917)
                ·
                  refine ⟨12412809226283539605359797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66201649206845544561918917 12412809226283539605359797)
                  ·
                    refine ⟨1163700864964081838002481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12412809226283539605359797 1163700864964081838002481)
                    ·
                      rfl

theorem cell23_6798898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_6798898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798898 prefixEnd_6798898 := by exact prefixLift 6798898
  have htrace : WordTrace (prefixWord ++ tailWord_6798898) baseStart_6798898 baseEnd_6798898 := by
    simpa [prefixWord, tailWord_6798898, baseEnd_6798898] using wordTrace_append hprefix tailTrace_6798898
  have hstable : (prefixWord ++ tailWord_6798898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798898).length < 2 ^ (prefixWord ++ tailWord_6798898).sum := by decide
  have hdescent : baseEnd_6798898 < baseStart_6798898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798902 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_6798902 : Nat := 118140960795 + 6798902 * 2 ^ 59
def prefixEnd_6798902 : Nat := 4983230072969 + 3 ^ 40 * 6798902 * 2
def baseEnd_6798902 : Nat := 387900516534984833150825

theorem tailTrace_6798902 : CollatzResearch.WordTrace tailWord_6798902 prefixEnd_6798902 387900516534984833150825 := by
  unfold tailWord_6798902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15498520500921668053877435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165317552009831125908025973 15498520500921668053877435)
  ·
    refine ⟨23247780751382502080816153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15498520500921668053877435 23247780751382502080816153)
    ·
      refine ⟨17435835563536876560612115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23247780751382502080816153 17435835563536876560612115)
      ·
        refine ⟨26153753345305314840918173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17435835563536876560612115 26153753345305314840918173)
        ·
          refine ⟨9807657504489493065344315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26153753345305314840918173 9807657504489493065344315)
          ·
            refine ⟨14711486256734239598016473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9807657504489493065344315 14711486256734239598016473)
            ·
              refine ⟨11033614692550679698512355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14711486256734239598016473 11033614692550679698512355)
              ·
                refine ⟨16550422038826019547768533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11033614692550679698512355 16550422038826019547768533)
                ·
                  refine ⟨387900516534984833150825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16550422038826019547768533 387900516534984833150825)
                  ·
                    rfl

theorem cell23_6798902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_6798902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798902 prefixEnd_6798902 := by exact prefixLift 6798902
  have htrace : WordTrace (prefixWord ++ tailWord_6798902) baseStart_6798902 baseEnd_6798902 := by
    simpa [prefixWord, tailWord_6798902, baseEnd_6798902] using wordTrace_append hprefix tailTrace_6798902
  have hstable : (prefixWord ++ tailWord_6798902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798902).length < 2 ^ (prefixWord ++ tailWord_6798902).sum := by decide
  have hdescent : baseEnd_6798902 < baseStart_6798902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798952 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6798952 : Nat := 118140960795 + 6798952 * 2 ^ 59
def prefixEnd_6798952 : Nat := 4983230072969 + 3 ^ 40 * 6798952 * 2
def baseEnd_6798952 : Nat := 3491130322847588302732195

theorem tailTrace_6798952 : CollatzResearch.WordTrace tailWord_6798952 prefixEnd_6798952 3491130322847588302732195 := by
  unfold tailWord_6798952
  simp only [CollatzResearch.WordTrace]
  refine ⟨123989075832282773700679555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165318767776377031600906073 123989075832282773700679555)
  ·
    refine ⟨185983613748424160551019333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123989075832282773700679555 185983613748424160551019333)
    ·
      refine ⟨34871927577829530103316125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185983613748424160551019333 34871927577829530103316125)
      ·
        refine ⟨13076972841686073788743547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34871927577829530103316125 13076972841686073788743547)
        ·
          refine ⟨19615459262529110683115321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13076972841686073788743547 19615459262529110683115321)
          ·
            refine ⟨14711594446896833012336491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19615459262529110683115321 14711594446896833012336491)
            ·
              refine ⟨22067391670345249518504737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14711594446896833012336491 22067391670345249518504737)
              ·
                refine ⟨16550543752758937138878553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22067391670345249518504737 16550543752758937138878553)
                ·
                  refine ⟨12412907814569202854158915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16550543752758937138878553 12412907814569202854158915)
                  ·
                    refine ⟨18619361721853804281238373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12412907814569202854158915 18619361721853804281238373)
                    ·
                      refine ⟨3491130322847588302732195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18619361721853804281238373 3491130322847588302732195)
                      ·
                        rfl

theorem cell23_6798952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6798952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798952 prefixEnd_6798952 := by exact prefixLift 6798952
  have htrace : WordTrace (prefixWord ++ tailWord_6798952) baseStart_6798952 baseEnd_6798952 := by
    simpa [prefixWord, tailWord_6798952, baseEnd_6798952] using wordTrace_append hprefix tailTrace_6798952
  have hstable : (prefixWord ++ tailWord_6798952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798952).length < 2 ^ (prefixWord ++ tailWord_6798952).sum := by decide
  have hdescent : baseEnd_6798952 < baseStart_6798952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6798962 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_6798962 : Nat := 118140960795 + 6798962 * 2 ^ 59
def prefixEnd_6798962 : Nat := 4983230072969 + 3 ^ 40 * 6798962 * 2
def baseEnd_6798962 : Nat := 1163711819218044421202383

theorem tailTrace_6798962 : CollatzResearch.WordTrace tailWord_6798962 prefixEnd_6798962 1163711819218044421202383 := by
  unfold tailWord_6798962
  simp only [CollatzResearch.WordTrace]
  refine ⟨61994629098632329777305785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165319010929686212739482093 61994629098632329777305785)
  ·
    refine ⟨46495971823974247332979339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61994629098632329777305785 46495971823974247332979339)
    ·
      refine ⟨69743957735961370999469009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46495971823974247332979339 69743957735961370999469009)
      ·
        refine ⟨52307968301971028249601757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69743957735961370999469009 52307968301971028249601757)
        ·
          refine ⟨19615488113239135593600659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52307968301971028249601757 19615488113239135593600659)
          ·
            refine ⟨29423232169858703390400989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19615488113239135593600659 29423232169858703390400989)
            ·
              refine ⟨11033712063697013771400371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29423232169858703390400989 11033712063697013771400371)
              ·
                refine ⟨16550568095545520657100557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11033712063697013771400371 16550568095545520657100557)
                ·
                  refine ⟨6206463035829570246412709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16550568095545520657100557 6206463035829570246412709)
                  ·
                    refine ⟨1163711819218044421202383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6206463035829570246412709 1163711819218044421202383)
                    ·
                      rfl

theorem cell23_6798962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_6798962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6798962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6798962 prefixEnd_6798962 := by exact prefixLift 6798962
  have htrace : WordTrace (prefixWord ++ tailWord_6798962) baseStart_6798962 baseEnd_6798962 := by
    simpa [prefixWord, tailWord_6798962, baseEnd_6798962] using wordTrace_append hprefix tailTrace_6798962
  have hstable : (prefixWord ++ tailWord_6798962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6798962).length < 2 ^ (prefixWord ++ tailWord_6798962).sum := by decide
  have hdescent : baseEnd_6798962 < baseStart_6798962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6798962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799053 : List Nat := [1, 6, 2, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6799053 : Nat := 118140960795 + 6799053 * 2 ^ 59
def prefixEnd_6799053 : Nat := 4983230072969 + 3 ^ 40 * 6799053 * 2
def baseEnd_6799053 : Nat := 3491182184393692407569231

theorem tailTrace_6799053 : CollatzResearch.WordTrace tailWord_6799053 prefixEnd_6799053 3491182184393692407569231 := by
  unfold tailWord_6799053
  simp only [CollatzResearch.WordTrace]
  refine ⟨247981835437199641650785813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165321223624799761100523875 247981835437199641650785813)
  ·
    refine ⟨11624148536118733202380585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 247981835437199641650785813 11624148536118733202380585)
    ·
      refine ⟨8718111402089049901785439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11624148536118733202380585 8718111402089049901785439)
      ·
        refine ⟨13077167103133574852678159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718111402089049901785439 13077167103133574852678159)
        ·
          refine ⟨19615750654700362279017239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13077167103133574852678159 19615750654700362279017239)
          ·
            refine ⟨29423625982050543418525859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19615750654700362279017239 29423625982050543418525859)
            ·
              refine ⟨44135438973075815127788789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29423625982050543418525859 44135438973075815127788789)
              ·
                refine ⟨4137697403725857668230199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44135438973075815127788789 4137697403725857668230199)
                ·
                  refine ⟨6206546105588786502345299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137697403725857668230199 6206546105588786502345299)
                  ·
                    refine ⟨9309819158383179753517949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6206546105588786502345299 9309819158383179753517949)
                    ·
                      refine ⟨3491182184393692407569231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9309819158383179753517949 3491182184393692407569231)
                      ·
                        rfl

theorem cell23_6799053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6799053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799053 prefixEnd_6799053 := by exact prefixLift 6799053
  have htrace : WordTrace (prefixWord ++ tailWord_6799053) baseStart_6799053 baseEnd_6799053 := by
    simpa [prefixWord, tailWord_6799053, baseEnd_6799053] using wordTrace_append hprefix tailTrace_6799053
  have hstable : (prefixWord ++ tailWord_6799053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799053).length < 2 ^ (prefixWord ++ tailWord_6799053).sum := by decide
  have hdescent : baseEnd_6799053 < baseStart_6799053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799076 : List Nat := [2, 3, 1, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_6799076 : Nat := 118140960795 + 6799076 * 2 ^ 59
def prefixEnd_6799076 : Nat := 4983230072969 + 3 ^ 40 * 6799076 * 2
def baseEnd_6799076 : Nat := 3491193994448745817581625

theorem tailTrace_6799076 : CollatzResearch.WordTrace tailWord_6799076 prefixEnd_6799076 3491193994448745817581625 := by
  unfold tailWord_6799076
  simp only [CollatzResearch.WordTrace]
  refine ⟨123991337158058158289436541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165321782877410877719248721 123991337158058158289436541)
  ·
    refine ⟨46496751434271809358538703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123991337158058158289436541 46496751434271809358538703)
    ·
      refine ⟨69745127151407714037808055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46496751434271809358538703 69745127151407714037808055)
      ·
        refine ⟨104617690727111571056712083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69745127151407714037808055 104617690727111571056712083)
        ·
          refine ⟨156926536090667356585068125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104617690727111571056712083 156926536090667356585068125)
          ·
            refine ⟨58847451034000258719400547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156926536090667356585068125 58847451034000258719400547)
            ·
              refine ⟨88271176551000388079100821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58847451034000258719400547 88271176551000388079100821)
              ·
                refine ⟨4137711400828143191207851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88271176551000388079100821 4137711400828143191207851)
                ·
                  refine ⟨6206567101242214786811777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4137711400828143191207851 6206567101242214786811777)
                  ·
                    refine ⟨4654925325931661090108833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6206567101242214786811777 4654925325931661090108833)
                    ·
                      refine ⟨3491193994448745817581625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654925325931661090108833 3491193994448745817581625)
                      ·
                        rfl

theorem cell23_6799076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_6799076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799076 prefixEnd_6799076 := by exact prefixLift 6799076
  have htrace : WordTrace (prefixWord ++ tailWord_6799076) baseStart_6799076 baseEnd_6799076 := by
    simpa [prefixWord, tailWord_6799076, baseEnd_6799076] using wordTrace_append hprefix tailTrace_6799076
  have hstable : (prefixWord ++ tailWord_6799076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799076).length < 2 ^ (prefixWord ++ tailWord_6799076).sum := by decide
  have hdescent : baseEnd_6799076 < baseStart_6799076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799079 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6799079 : Nat := 118140960795 + 6799079 * 2 ^ 59
def prefixEnd_6799079 : Nat := 4983230072969 + 3 ^ 40 * 6799079 * 2
def baseEnd_6799079 : Nat := 3491195534890709305844111

theorem tailTrace_6799079 : CollatzResearch.WordTrace tailWord_6799079 prefixEnd_6799079 3491195534890709305844111 := by
  unfold tailWord_6799079
  simp only [CollatzResearch.WordTrace]
  refine ⟨247982783735105448091232291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165321855823403632060821527 247982783735105448091232291)
  ·
    refine ⟨371974175602658172136848437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247982783735105448091232291 371974175602658172136848437)
    ·
      refine ⟨34872578962749203637829541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 371974175602658172136848437 34872578962749203637829541)
      ·
        refine ⟨6538608555515475682093039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34872578962749203637829541 6538608555515475682093039)
        ·
          refine ⟨9807912833273213523139559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6538608555515475682093039 9807912833273213523139559)
          ·
            refine ⟨14711869249909820284709339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9807912833273213523139559 14711869249909820284709339)
            ·
              refine ⟨22067803874864730427064009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14711869249909820284709339 22067803874864730427064009)
              ·
                refine ⟨16550852906148547820298007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22067803874864730427064009 16550852906148547820298007)
                ·
                  refine ⟨24826279359222821730447011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16550852906148547820298007 24826279359222821730447011)
                  ·
                    refine ⟨37239419038834232595670517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24826279359222821730447011 37239419038834232595670517)
                    ·
                      refine ⟨3491195534890709305844111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37239419038834232595670517 3491195534890709305844111)
                      ·
                        rfl

theorem cell23_6799079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6799079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799079 prefixEnd_6799079 := by exact prefixLift 6799079
  have htrace : WordTrace (prefixWord ++ tailWord_6799079) baseStart_6799079 baseEnd_6799079 := by
    simpa [prefixWord, tailWord_6799079, baseEnd_6799079] using wordTrace_append hprefix tailTrace_6799079
  have hstable : (prefixWord ++ tailWord_6799079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799079).length < 2 ^ (prefixWord ++ tailWord_6799079).sum := by decide
  have hdescent : baseEnd_6799079 < baseStart_6799079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799105 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_6799105 : Nat := 118140960795 + 6799105 * 2 ^ 59
def prefixEnd_6799105 : Nat := 4983230072969 + 3 ^ 40 * 6799105 * 2
def baseEnd_6799105 : Nat := 3491208885387726204118991

theorem tailTrace_6799105 : CollatzResearch.WordTrace tailWord_6799105 prefixEnd_6799105 3491208885387726204118991 := by
  unfold tailWord_6799105
  simp only [CollatzResearch.WordTrace]
  refine ⟨247983732033011254531678769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165322488022007503021119179 247983732033011254531678769)
  ·
    refine ⟨185987799024758440898759077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247983732033011254531678769 185987799024758440898759077)
    ·
      refine ⟨34872712317142207668517327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185987799024758440898759077 34872712317142207668517327)
      ·
        refine ⟨52309068475713311502775991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34872712317142207668517327 52309068475713311502775991)
        ·
          refine ⟨78463602713569967254163987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52309068475713311502775991 78463602713569967254163987)
          ·
            refine ⟨117695404070354950881245981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78463602713569967254163987 117695404070354950881245981)
            ·
              refine ⟨44135776526383106580467243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117695404070354950881245981 44135776526383106580467243)
              ·
                refine ⟨66203664789574659870700865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44135776526383106580467243 66203664789574659870700865)
                ·
                  refine ⟨49652748592180994903025649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66203664789574659870700865 49652748592180994903025649)
                  ·
                    refine ⟨37239561444135746177269237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49652748592180994903025649 37239561444135746177269237)
                    ·
                      refine ⟨3491208885387726204118991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37239561444135746177269237 3491208885387726204118991)
                      ·
                        rfl

theorem cell23_6799105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_6799105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799105 prefixEnd_6799105 := by exact prefixLift 6799105
  have htrace : WordTrace (prefixWord ++ tailWord_6799105) baseStart_6799105 baseEnd_6799105 := by
    simpa [prefixWord, tailWord_6799105, baseEnd_6799105] using wordTrace_append hprefix tailTrace_6799105
  have hstable : (prefixWord ++ tailWord_6799105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799105).length < 2 ^ (prefixWord ++ tailWord_6799105).sum := by decide
  have hdescent : baseEnd_6799105 < baseStart_6799105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799135 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_6799135 : Nat := 118140960795 + 6799135 * 2 ^ 59
def prefixEnd_6799135 : Nat := 4983230072969 + 3 ^ 40 * 6799135 * 2
def baseEnd_6799135 : Nat := 3491224289807361086743853

theorem tailTrace_6799135 : CollatzResearch.WordTrace tailWord_6799135 prefixEnd_6799135 3491224289807361086743853 := by
  unfold tailWord_6799135
  simp only [CollatzResearch.WordTrace]
  refine ⟨247984826222902569655270859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165323217481935046436847239 247984826222902569655270859)
  ·
    refine ⟨371977239334353854482906289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247984826222902569655270859 371977239334353854482906289)
    ·
      refine ⟨278982929500765390862179717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371977239334353854482906289 278982929500765390862179717)
      ·
        refine ⟨52309299281393510786658697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278982929500765390862179717 52309299281393510786658697)
        ·
          refine ⟨39231974461045133089994023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52309299281393510786658697 39231974461045133089994023)
          ·
            refine ⟨58847961691567699634991035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39231974461045133089994023 58847961691567699634991035)
            ·
              refine ⟨88271942537351549452486553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58847961691567699634991035 88271942537351549452486553)
              ·
                refine ⟨66203956903013662089364915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88271942537351549452486553 66203956903013662089364915)
                ·
                  refine ⟨99305935354520493134047373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66203956903013662089364915 99305935354520493134047373)
                  ·
                    refine ⟨37239725757945184925267765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99305935354520493134047373 37239725757945184925267765)
                    ·
                      refine ⟨3491224289807361086743853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37239725757945184925267765 3491224289807361086743853)
                      ·
                        rfl

theorem cell23_6799135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_6799135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799135 prefixEnd_6799135 := by exact prefixLift 6799135
  have htrace : WordTrace (prefixWord ++ tailWord_6799135) baseStart_6799135 baseEnd_6799135 := by
    simpa [prefixWord, tailWord_6799135, baseEnd_6799135] using wordTrace_append hprefix tailTrace_6799135
  have hstable : (prefixWord ++ tailWord_6799135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799135).length < 2 ^ (prefixWord ++ tailWord_6799135).sum := by decide
  have hdescent : baseEnd_6799135 < baseStart_6799135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799166 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_6799166 : Nat := 118140960795 + 6799166 * 2 ^ 59
def prefixEnd_6799166 : Nat := 4983230072969 + 3 ^ 40 * 6799166 * 2
def baseEnd_6799166 : Nat := 3491240207707650465456211

theorem tailTrace_6799166 : CollatzResearch.WordTrace tailWord_6799166 prefixEnd_6799166 3491240207707650465456211 := by
  unfold tailWord_6799166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30998244610723782743706169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165323971257193507966432901 30998244610723782743706169)
  ·
    refine ⟨23248683458042837057779627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30998244610723782743706169 23248683458042837057779627)
    ·
      refine ⟨34873025187064255586669441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23248683458042837057779627 34873025187064255586669441)
      ·
        refine ⟨26154768890298191690002081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34873025187064255586669441 26154768890298191690002081)
        ·
          refine ⟨19616076667723643767501561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26154768890298191690002081 19616076667723643767501561)
          ·
            refine ⟨14712057500792732825626171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19616076667723643767501561 14712057500792732825626171)
            ·
              refine ⟨22068086251189099238439257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14712057500792732825626171 22068086251189099238439257)
              ·
                refine ⟨16551064688391824428829443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22068086251189099238439257 16551064688391824428829443)
                ·
                  refine ⟨24826597032587736643244165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16551064688391824428829443 24826597032587736643244165)
                  ·
                    refine ⟨4654986943610200620608281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24826597032587736643244165 4654986943610200620608281)
                    ·
                      refine ⟨3491240207707650465456211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4654986943610200620608281 3491240207707650465456211)
                      ·
                        rfl

theorem cell23_6799166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_6799166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799166 prefixEnd_6799166 := by exact prefixLift 6799166
  have htrace : WordTrace (prefixWord ++ tailWord_6799166) baseStart_6799166 baseEnd_6799166 := by
    simpa [prefixWord, tailWord_6799166, baseEnd_6799166] using wordTrace_append hprefix tailTrace_6799166
  have hstable : (prefixWord ++ tailWord_6799166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799166).length < 2 ^ (prefixWord ++ tailWord_6799166).sum := by decide
  have hdescent : baseEnd_6799166 < baseStart_6799166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799189 : List Nat := [1, 3, 2, 2, 2, 3, 1, 4, 5]
def baseStart_6799189 : Nat := 118140960795 + 6799189 * 2 ^ 59
def prefixEnd_6799189 : Nat := 4983230072969 + 3 ^ 40 * 6799189 * 2
def baseEnd_6799189 : Nat := 387916890862522652829845

theorem tailTrace_6799189 : CollatzResearch.WordTrace tailWord_6799189 prefixEnd_6799189 387916890862522652829845 := by
  unfold tailWord_6799189
  simp only [CollatzResearch.WordTrace]
  refine ⟨247986795764706936877736621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165324530509804624585157747 247986795764706936877736621)
  ·
    refine ⟨92995048411765101329151233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247986795764706936877736621 92995048411765101329151233)
    ·
      refine ⟨69746286308823825996863425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92995048411765101329151233 69746286308823825996863425)
      ·
        refine ⟨52309714731617869497647569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69746286308823825996863425 52309714731617869497647569)
        ·
          refine ⟨39232286048713402123235677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52309714731617869497647569 39232286048713402123235677)
          ·
            refine ⟨14712107268267525796213379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39232286048713402123235677 14712107268267525796213379)
            ·
              refine ⟨22068160902401288694320069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14712107268267525796213379 22068160902401288694320069)
              ·
                refine ⟨4137780169200241630185013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22068160902401288694320069 4137780169200241630185013)
                ·
                  refine ⟨387916890862522652829845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4137780169200241630185013 387916890862522652829845)
                  ·
                    rfl

theorem cell23_6799189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_6799189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799189 prefixEnd_6799189 := by exact prefixLift 6799189
  have htrace : WordTrace (prefixWord ++ tailWord_6799189) baseStart_6799189 baseEnd_6799189 := by
    simpa [prefixWord, tailWord_6799189, baseEnd_6799189] using wordTrace_append hprefix tailTrace_6799189
  have hstable : (prefixWord ++ tailWord_6799189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799189).length < 2 ^ (prefixWord ++ tailWord_6799189).sum := by decide
  have hdescent : baseEnd_6799189 < baseStart_6799189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799232 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 5, 4]
def baseStart_6799232 : Nat := 118140960795 + 6799232 * 2 ^ 59
def prefixEnd_6799232 : Nat := 4983230072969 + 3 ^ 40 * 6799232 * 2
def baseEnd_6799232 : Nat := 1163758032476949069076969

theorem tailTrace_6799232 : CollatzResearch.WordTrace tailWord_6799232 prefixEnd_6799232 1163758032476949069076969 := by
  unfold tailWord_6799232
  simp only [CollatzResearch.WordTrace]
  refine ⟨123994182051775577610775975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165325576069034103481034633 123994182051775577610775975)
  ·
    refine ⟨185991273077663366416163963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123994182051775577610775975 185991273077663366416163963)
    ·
      refine ⟨278986909616495049624245945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185991273077663366416163963 278986909616495049624245945)
      ·
        refine ⟨209240182212371287218184459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278986909616495049624245945 209240182212371287218184459)
        ·
          refine ⟨313860273318556930827276689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209240182212371287218184459 313860273318556930827276689)
          ·
            refine ⟨235395204988917698120457517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313860273318556930827276689 235395204988917698120457517)
            ·
              refine ⟨88273201870844136795171569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235395204988917698120457517 88273201870844136795171569)
              ·
                refine ⟨66204901403133102596378677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88273201870844136795171569 66204901403133102596378677)
                ·
                  refine ⟨6206709506543728368410501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66204901403133102596378677 6206709506543728368410501)
                  ·
                    refine ⟨1163758032476949069076969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6206709506543728368410501 1163758032476949069076969)
                    ·
                      rfl

theorem cell23_6799232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_6799232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799232 prefixEnd_6799232 := by exact prefixLift 6799232
  have htrace : WordTrace (prefixWord ++ tailWord_6799232) baseStart_6799232 baseEnd_6799232 := by
    simpa [prefixWord, tailWord_6799232, baseEnd_6799232] using wordTrace_append hprefix tailTrace_6799232
  have hstable : (prefixWord ++ tailWord_6799232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799232).length < 2 ^ (prefixWord ++ tailWord_6799232).sum := by decide
  have hdescent : baseEnd_6799232 < baseStart_6799232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799306 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_6799306 : Nat := 118140960795 + 6799306 * 2 ^ 59
def prefixEnd_6799306 : Nat := 4983230072969 + 3 ^ 40 * 6799306 * 2
def baseEnd_6799306 : Nat := 3491312094999279917705567

theorem tailTrace_6799306 : CollatzResearch.WordTrace tailWord_6799306 prefixEnd_6799306 3491312094999279917705567 := by
  unfold tailWord_6799306
  simp only [CollatzResearch.WordTrace]
  refine ⟨61997765776320766464936443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165327375403522043906497181 61997765776320766464936443)
  ·
    refine ⟨92996648664481149697404665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61997765776320766464936443 92996648664481149697404665)
    ·
      refine ⟨69747486498360862273053499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92996648664481149697404665 69747486498360862273053499)
      ·
        refine ⟨104621229747541293409580249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69747486498360862273053499 104621229747541293409580249)
        ·
          refine ⟨78465922310655970057185187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104621229747541293409580249 78465922310655970057185187)
          ·
            refine ⟨117698883465983955085777781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78465922310655970057185187 117698883465983955085777781)
            ·
              refine ⟨11034270324935995789291667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117698883465983955085777781 11034270324935995789291667)
              ·
                refine ⟨16551405487403993683937501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11034270324935995789291667 16551405487403993683937501)
                ·
                  refine ⟨6206777057776497631476563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16551405487403993683937501 6206777057776497631476563)
                  ·
                    refine ⟨9310165586664746447214845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6206777057776497631476563 9310165586664746447214845)
                    ·
                      refine ⟨3491312094999279917705567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9310165586664746447214845 3491312094999279917705567)
                      ·
                        rfl

theorem cell23_6799306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_6799306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799306 prefixEnd_6799306 := by exact prefixLift 6799306
  have htrace : WordTrace (prefixWord ++ tailWord_6799306) baseStart_6799306 baseEnd_6799306 := by
    simpa [prefixWord, tailWord_6799306, baseEnd_6799306] using wordTrace_append hprefix tailTrace_6799306
  have hstable : (prefixWord ++ tailWord_6799306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799306).length < 2 ^ (prefixWord ++ tailWord_6799306).sum := by decide
  have hdescent : baseEnd_6799306 < baseStart_6799306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799316 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_6799316 : Nat := 118140960795 + 6799316 * 2 ^ 59
def prefixEnd_6799316 : Nat := 4983230072969 + 3 ^ 40 * 6799316 * 2
def baseEnd_6799316 : Nat := 3491317229805824878580521

theorem tailTrace_6799316 : CollatzResearch.WordTrace tailWord_6799316 prefixEnd_6799316 3491317229805824878580521 := by
  unfold tailWord_6799316
  simp only [CollatzResearch.WordTrace]
  refine ⟨123995713917623418783804901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165327618556831225045073201 123995713917623418783804901)
  ·
    refine ⟨23249196359554391021963419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123995713917623418783804901 23249196359554391021963419)
    ·
      refine ⟨34873794539331586532945129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23249196359554391021963419 34873794539331586532945129)
      ·
        refine ⟨26155345904498689899708847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34873794539331586532945129 26155345904498689899708847)
        ·
          refine ⟨39233018856748034849563271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26155345904498689899708847 39233018856748034849563271)
          ·
            refine ⟨58849528285122052274344907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39233018856748034849563271 58849528285122052274344907)
            ·
              refine ⟨88274292427683078411517361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58849528285122052274344907 88274292427683078411517361)
              ·
                refine ⟨66205719320762308808638021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88274292427683078411517361 66205719320762308808638021)
                ·
                  refine ⟨12413572372642932901619629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66205719320762308808638021 12413572372642932901619629)
                  ·
                    refine ⟨4655089639741099838107361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12413572372642932901619629 4655089639741099838107361)
                    ·
                      refine ⟨3491317229805824878580521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655089639741099838107361 3491317229805824878580521)
                      ·
                        rfl

theorem cell23_6799316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_6799316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799316 prefixEnd_6799316 := by exact prefixLift 6799316
  have htrace : WordTrace (prefixWord ++ tailWord_6799316) baseStart_6799316 baseEnd_6799316 := by
    simpa [prefixWord, tailWord_6799316, baseEnd_6799316] using wordTrace_append hprefix tailTrace_6799316
  have hstable : (prefixWord ++ tailWord_6799316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799316).length < 2 ^ (prefixWord ++ tailWord_6799316).sum := by decide
  have hdescent : baseEnd_6799316 < baseStart_6799316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799329 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_6799329 : Nat := 118140960795 + 6799329 * 2 ^ 59
def prefixEnd_6799329 : Nat := 4983230072969 + 3 ^ 40 * 6799329 * 2
def baseEnd_6799329 : Nat := 3491323905054333327717961

theorem tailTrace_6799329 : CollatzResearch.WordTrace tailWord_6799329 prefixEnd_6799329 3491323905054333327717961 := by
  unfold tailWord_6799329
  simp only [CollatzResearch.WordTrace]
  refine ⟨247991901984199740787833041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165327934656133160525222027 247991901984199740787833041)
  ·
    refine ⟨185993926488149805590874781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247991901984199740787833041 185993926488149805590874781)
    ·
      refine ⟨69747722433056177096578043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185993926488149805590874781 69747722433056177096578043)
      ·
        refine ⟨104621583649584265644867065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69747722433056177096578043 104621583649584265644867065)
        ·
          refine ⟨78466187737188199233650299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104621583649584265644867065 78466187737188199233650299)
          ·
            refine ⟨117699281605782298850475449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78466187737188199233650299 117699281605782298850475449)
            ·
              refine ⟨88274461204336724137856587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117699281605782298850475449 88274461204336724137856587)
              ·
                refine ⟨132411691806505086206784881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88274461204336724137856587 132411691806505086206784881)
                ·
                  refine ⟨99308768854878814655088661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132411691806505086206784881 99308768854878814655088661)
                  ·
                    refine ⟨4655098540072444436957281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99308768854878814655088661 4655098540072444436957281)
                    ·
                      refine ⟨3491323905054333327717961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655098540072444436957281 3491323905054333327717961)
                      ·
                        rfl

theorem cell23_6799329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_6799329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799329 prefixEnd_6799329 := by exact prefixLift 6799329
  have htrace : WordTrace (prefixWord ++ tailWord_6799329) baseStart_6799329 baseEnd_6799329 := by
    simpa [prefixWord, tailWord_6799329, baseEnd_6799329] using wordTrace_append hprefix tailTrace_6799329
  have hstable : (prefixWord ++ tailWord_6799329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799329).length < 2 ^ (prefixWord ++ tailWord_6799329).sum := by decide
  have hdescent : baseEnd_6799329 < baseStart_6799329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799356 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_6799356 : Nat := 118140960795 + 6799356 * 2 ^ 59
def prefixEnd_6799356 : Nat := 4983230072969 + 3 ^ 40 * 6799356 * 2
def baseEnd_6799356 : Nat := 1163779256344001574026779

theorem tailTrace_6799356 : CollatzResearch.WordTrace tailWord_6799356 prefixEnd_6799356 1163779256344001574026779 := by
  unfold tailWord_6799356
  simp only [CollatzResearch.WordTrace]
  refine ⟨123996443377550962199532961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165328591170067949599377281 123996443377550962199532961)
  ·
    refine ⟨92997332533163221649649721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123996443377550962199532961 92997332533163221649649721)
    ·
      refine ⟨69747999399872416237237291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92997332533163221649649721 69747999399872416237237291)
      ·
        refine ⟨104621999099808624355855937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69747999399872416237237291 104621999099808624355855937)
        ·
          refine ⟨78466499324856468266891953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104621999099808624355855937 78466499324856468266891953)
          ·
            refine ⟨58849874493642351200168965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78466499324856468266891953 58849874493642351200168965)
            ·
              refine ⟨11034351467557940850031681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58849874493642351200168965 11034351467557940850031681)
              ·
                refine ⟨8275763600668455637523761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11034351467557940850031681 8275763600668455637523761)
                ·
                  refine ⟨6206822700501341728142821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8275763600668455637523761 6206822700501341728142821)
                  ·
                    refine ⟨1163779256344001574026779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6206822700501341728142821 1163779256344001574026779)
                    ·
                      rfl

theorem cell23_6799356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_6799356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799356 prefixEnd_6799356 := by exact prefixLift 6799356
  have htrace : WordTrace (prefixWord ++ tailWord_6799356) baseStart_6799356 baseEnd_6799356 := by
    simpa [prefixWord, tailWord_6799356, baseEnd_6799356] using wordTrace_append hprefix tailTrace_6799356
  have hstable : (prefixWord ++ tailWord_6799356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799356).length < 2 ^ (prefixWord ++ tailWord_6799356).sum := by decide
  have hdescent : baseEnd_6799356 < baseStart_6799356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799379 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 3]
def baseStart_6799379 : Nat := 118140960795 + 6799379 * 2 ^ 59
def prefixEnd_6799379 : Nat := 4983230072969 + 3 ^ 40 * 6799379 * 2
def baseEnd_6799379 : Nat := 3491349579087058132092731

theorem tailTrace_6799379 : CollatzResearch.WordTrace tailWord_6799379 prefixEnd_6799379 3491349579087058132092731 := by
  unfold tailWord_6799379
  simp only [CollatzResearch.WordTrace]
  refine ⟨247993725634018599327153191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165329150422679066218102127 247993725634018599327153191)
  ·
    refine ⟨371990588451027898990729787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247993725634018599327153191 371990588451027898990729787)
    ·
      refine ⟨557985882676541848486094681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371990588451027898990729787 557985882676541848486094681)
      ·
        refine ⟨418489412007406386364571011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557985882676541848486094681 418489412007406386364571011)
        ·
          refine ⟨627734118011109579546856517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418489412007406386364571011 627734118011109579546856517)
          ·
            refine ⟨117700147127083046165035597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 627734118011109579546856517 117700147127083046165035597)
            ·
              refine ⟨44137555172656142311888349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117700147127083046165035597 44137555172656142311888349)
              ·
                refine ⟨16551583189746053366958131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44137555172656142311888349 16551583189746053366958131)
                ·
                  refine ⟨24827374784619080050437197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16551583189746053366958131 24827374784619080050437197)
                  ·
                    refine ⟨9310265544232155018913949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24827374784619080050437197 9310265544232155018913949)
                    ·
                      refine ⟨3491349579087058132092731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9310265544232155018913949 3491349579087058132092731)
                      ·
                        rfl

theorem cell23_6799379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_6799379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799379 prefixEnd_6799379 := by exact prefixLift 6799379
  have htrace : WordTrace (prefixWord ++ tailWord_6799379) baseStart_6799379 baseEnd_6799379 := by
    simpa [prefixWord, tailWord_6799379, baseEnd_6799379] using wordTrace_append hprefix tailTrace_6799379
  have hstable : (prefixWord ++ tailWord_6799379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799379).length < 2 ^ (prefixWord ++ tailWord_6799379).sum := by decide
  have hdescent : baseEnd_6799379 < baseStart_6799379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799400 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6799400 : Nat := 118140960795 + 6799400 * 2 ^ 59
def prefixEnd_6799400 : Nat := 4983230072969 + 3 ^ 40 * 6799400 * 2
def baseEnd_6799400 : Nat := 3491360362180802549930135

theorem tailTrace_6799400 : CollatzResearch.WordTrace tailWord_6799400 prefixEnd_6799400 3491360362180802549930135 := by
  unfold tailWord_6799400
  simp only [CollatzResearch.WordTrace]
  refine ⟨123997245783471259956833827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165329661044628346609111769 123997245783471259956833827)
  ·
    refine ⟨185995868675206889935250741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123997245783471259956833827 185995868675206889935250741)
    ·
      refine ⟨17437112688300645931429757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185995868675206889935250741 17437112688300645931429757)
      ·
        refine ⟨6538917258112742224286159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17437112688300645931429757 6538917258112742224286159)
        ·
          refine ⟨9808375887169113336429239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6538917258112742224286159 9808375887169113336429239)
          ·
            refine ⟨14712563830753670004643859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808375887169113336429239 14712563830753670004643859)
            ·
              refine ⟨22068845746130505006965789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14712563830753670004643859 22068845746130505006965789)
              ·
                refine ⟨8275817154798939377612171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22068845746130505006965789 8275817154798939377612171)
                ·
                  refine ⟨12413725732198409066418257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8275817154798939377612171 12413725732198409066418257)
                  ·
                    refine ⟨9310294299148806799813693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12413725732198409066418257 9310294299148806799813693)
                    ·
                      refine ⟨3491360362180802549930135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9310294299148806799813693 3491360362180802549930135)
                      ·
                        rfl

theorem cell23_6799400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6799400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799400 prefixEnd_6799400 := by exact prefixLift 6799400
  have htrace : WordTrace (prefixWord ++ tailWord_6799400) baseStart_6799400 baseEnd_6799400 := by
    simpa [prefixWord, tailWord_6799400, baseEnd_6799400] using wordTrace_append hprefix tailTrace_6799400
  have hstable : (prefixWord ++ tailWord_6799400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799400).length < 2 ^ (prefixWord ++ tailWord_6799400).sum := by decide
  have hdescent : baseEnd_6799400 < baseStart_6799400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799413 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_6799413 : Nat := 118140960795 + 6799413 * 2 ^ 59
def prefixEnd_6799413 : Nat := 4983230072969 + 3 ^ 40 * 6799413 * 2
def baseEnd_6799413 : Nat := 3491367037429310999067575

theorem tailTrace_6799413 : CollatzResearch.WordTrace tailWord_6799413 prefixEnd_6799413 3491367037429310999067575 := by
  unfold tailWord_6799413
  simp only [CollatzResearch.WordTrace]
  refine ⟨247994965715895423133890893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165329977143930282089260595 247994965715895423133890893)
  ·
    refine ⟨92998112143460783675209085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247994965715895423133890893 92998112143460783675209085)
    ·
      refine ⟨34874292053797793878203407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92998112143460783675209085 34874292053797793878203407)
      ·
        refine ⟨52311438080696690817305111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34874292053797793878203407 52311438080696690817305111)
        ·
          refine ⟨78467157121045036225957667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52311438080696690817305111 78467157121045036225957667)
          ·
            refine ⟨117700735681567554338936501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78467157121045036225957667 117700735681567554338936501)
            ·
              refine ⟨11034443970146958219275297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117700735681567554338936501 11034443970146958219275297)
              ·
                refine ⟨8275832977610218664456473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11034443970146958219275297 8275832977610218664456473)
                ·
                  refine ⟨6206874733207663998342355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8275832977610218664456473 6206874733207663998342355)
                  ·
                    refine ⟨9310312099811495997513533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6206874733207663998342355 9310312099811495997513533)
                    ·
                      refine ⟨3491367037429310999067575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9310312099811495997513533 3491367037429310999067575)
                      ·
                        rfl

theorem cell23_6799413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_6799413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799413 prefixEnd_6799413 := by exact prefixLift 6799413
  have htrace : WordTrace (prefixWord ++ tailWord_6799413) baseStart_6799413 baseEnd_6799413 := by
    simpa [prefixWord, tailWord_6799413, baseEnd_6799413] using wordTrace_append hprefix tailTrace_6799413
  have hstable : (prefixWord ++ tailWord_6799413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799413).length < 2 ^ (prefixWord ++ tailWord_6799413).sum := by decide
  have hdescent : baseEnd_6799413 < baseStart_6799413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799469 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6799469 : Nat := 118140960795 + 6799469 * 2 ^ 59
def prefixEnd_6799469 : Nat := 4983230072969 + 3 ^ 40 * 6799469 * 2
def baseEnd_6799469 : Nat := 3491395792345962779967317

theorem tailTrace_6799469 : CollatzResearch.WordTrace tailWord_6799469 prefixEnd_6799469 3491395792345962779967317 := by
  unfold tailWord_6799469
  simp only [CollatzResearch.WordTrace]
  refine ⟨247997008203692544697929461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165331338802461696465286307 247997008203692544697929461)
  ·
    refine ⟨23249719519096176065430887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 247997008203692544697929461 23249719519096176065430887)
    ·
      refine ⟨34874579278644264098146331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23249719519096176065430887 34874579278644264098146331)
      ·
        refine ⟨52311868917966396147219497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34874579278644264098146331 52311868917966396147219497)
        ·
          refine ⟨39233901688474797110414623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52311868917966396147219497 39233901688474797110414623)
          ·
            refine ⟨58850852532712195665621935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39233901688474797110414623 58850852532712195665621935)
            ·
              refine ⟨88276278799068293498432903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58850852532712195665621935 88276278799068293498432903)
              ·
                refine ⟨132414418198602440247649355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88276278799068293498432903 132414418198602440247649355)
                ·
                  refine ⟨198621627297903660371474033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132414418198602440247649355 198621627297903660371474033)
                  ·
                    refine ⟨148966220473427745278605525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198621627297903660371474033 148966220473427745278605525)
                    ·
                      refine ⟨3491395792345962779967317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148966220473427745278605525 3491395792345962779967317)
                      ·
                        rfl

theorem cell23_6799469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6799469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799469 prefixEnd_6799469 := by exact prefixLift 6799469
  have htrace : WordTrace (prefixWord ++ tailWord_6799469) baseStart_6799469 baseEnd_6799469 := by
    simpa [prefixWord, tailWord_6799469, baseEnd_6799469] using wordTrace_append hprefix tailTrace_6799469
  have hstable : (prefixWord ++ tailWord_6799469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799469).length < 2 ^ (prefixWord ++ tailWord_6799469).sum := by decide
  have hdescent : baseEnd_6799469 < baseStart_6799469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799470 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_6799470 : Nat := 118140960795 + 6799470 * 2 ^ 59
def prefixEnd_6799470 : Nat := 4983230072969 + 3 ^ 40 * 6799470 * 2
def baseEnd_6799470 : Nat := 3491396305826617276054813

theorem tailTrace_6799470 : CollatzResearch.WordTrace tailWord_6799470 prefixEnd_6799470 3491396305826617276054813 := by
  unfold tailWord_6799470
  simp only [CollatzResearch.WordTrace]
  refine ⟨30999630584586115233589483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165331363117792614579143909 30999630584586115233589483)
  ·
    refine ⟨46499445876879172850384225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30999630584586115233589483 46499445876879172850384225)
    ·
      refine ⟨34874584407659379637788169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46499445876879172850384225 34874584407659379637788169)
      ·
        refine ⟨26155938305744534728341127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34874584407659379637788169 26155938305744534728341127)
        ·
          refine ⟨39233907458616802092511691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26155938305744534728341127 39233907458616802092511691)
          ·
            refine ⟨58850861187925203138767537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39233907458616802092511691 58850861187925203138767537)
            ·
              refine ⟨44138145890943902354075653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58850861187925203138767537 44138145890943902354075653)
              ·
                refine ⟨8275902354551981691389185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44138145890943902354075653 8275902354551981691389185)
                ·
                  refine ⟨6206926765913986268541889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8275902354551981691389185 6206926765913986268541889)
                  ·
                    refine ⟨4655195074435489701406417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6206926765913986268541889 4655195074435489701406417)
                    ·
                      refine ⟨3491396305826617276054813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655195074435489701406417 3491396305826617276054813)
                      ·
                        rfl

theorem cell23_6799470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_6799470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799470 prefixEnd_6799470 := by exact prefixLift 6799470
  have htrace : WordTrace (prefixWord ++ tailWord_6799470) baseStart_6799470 baseEnd_6799470 := by
    simpa [prefixWord, tailWord_6799470, baseEnd_6799470] using wordTrace_append hprefix tailTrace_6799470
  have hstable : (prefixWord ++ tailWord_6799470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799470).length < 2 ^ (prefixWord ++ tailWord_6799470).sum := by decide
  have hdescent : baseEnd_6799470 < baseStart_6799470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799527 : List Nat := [1, 1, 6, 2, 2, 2, 2, 2, 5]
def baseStart_6799527 : Nat := 118140960795 + 6799527 * 2 ^ 59
def prefixEnd_6799527 : Nat := 4983230072969 + 3 ^ 40 * 6799527 * 2
def baseEnd_6799527 : Nat := 387936174913769283671339

theorem tailTrace_6799527 : CollatzResearch.WordTrace tailWord_6799527 prefixEnd_6799527 387936174913769283671339 := by
  unfold tailWord_6799527
  simp only [CollatzResearch.WordTrace]
  refine ⟨247999123637482420603540835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165332749091654947069027223 247999123637482420603540835)
  ·
    refine ⟨371998685456223630905311253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247999123637482420603540835 371998685456223630905311253)
    ·
      refine ⟨17437438380760482698686465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 371998685456223630905311253 17437438380760482698686465)
      ·
        refine ⟨13078078785570362024014849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17437438380760482698686465 13078078785570362024014849)
        ·
          refine ⟨9808559089177771518011137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13078078785570362024014849 9808559089177771518011137)
          ·
            refine ⟨7356419316883328638508353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9808559089177771518011137 7356419316883328638508353)
            ·
              refine ⟨5517314487662496478881265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7356419316883328638508353 5517314487662496478881265)
              ·
                refine ⟨4137985865746872359160949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517314487662496478881265 4137985865746872359160949)
                ·
                  refine ⟨387936174913769283671339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4137985865746872359160949 387936174913769283671339)
                  ·
                    rfl

theorem cell23_6799527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 5].length) (baseStart_6799527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799527 prefixEnd_6799527 := by exact prefixLift 6799527
  have htrace : WordTrace (prefixWord ++ tailWord_6799527) baseStart_6799527 baseEnd_6799527 := by
    simpa [prefixWord, tailWord_6799527, baseEnd_6799527] using wordTrace_append hprefix tailTrace_6799527
  have hstable : (prefixWord ++ tailWord_6799527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799527).length < 2 ^ (prefixWord ++ tailWord_6799527).sum := by decide
  have hdescent : baseEnd_6799527 < baseStart_6799527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799539 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4]
def baseStart_6799539 : Nat := 118140960795 + 6799539 * 2 ^ 59
def prefixEnd_6799539 : Nat := 4983230072969 + 3 ^ 40 * 6799539 * 2
def baseEnd_6799539 : Nat := 3491431735991777506091995

theorem tailTrace_6799539 : CollatzResearch.WordTrace tailWord_6799539 prefixEnd_6799539 3491431735991777506091995 := by
  unfold tailWord_6799539
  simp only [CollatzResearch.WordTrace]
  refine ⟨247999561313438946652977671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165333040875625964435318447 247999561313438946652977671)
  ·
    refine ⟨371999341970158419979466507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247999561313438946652977671 371999341970158419979466507)
    ·
      refine ⟨557999012955237629969199761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371999341970158419979466507 557999012955237629969199761)
      ·
        refine ⟨418499259716428222476899821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557999012955237629969199761 418499259716428222476899821)
        ·
          refine ⟨156937222393660583428837433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418499259716428222476899821 156937222393660583428837433)
          ·
            refine ⟨117702916795245437571628075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156937222393660583428837433 117702916795245437571628075)
            ·
              refine ⟨176554375192868156357442113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117702916795245437571628075 176554375192868156357442113)
              ·
                refine ⟨132415781394651117268081585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176554375192868156357442113 132415781394651117268081585)
                ·
                  refine ⟨99311836045988337951061189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132415781394651117268081585 99311836045988337951061189)
                  ·
                    refine ⟨18620969258622813365823973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99311836045988337951061189 18620969258622813365823973)
                    ·
                      refine ⟨3491431735991777506091995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18620969258622813365823973 3491431735991777506091995)
                      ·
                        rfl

theorem cell23_6799539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_6799539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799539 prefixEnd_6799539 := by exact prefixLift 6799539
  have htrace : WordTrace (prefixWord ++ tailWord_6799539) baseStart_6799539 baseEnd_6799539 := by
    simpa [prefixWord, tailWord_6799539, baseEnd_6799539] using wordTrace_append hprefix tailTrace_6799539
  have hstable : (prefixWord ++ tailWord_6799539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799539).length < 2 ^ (prefixWord ++ tailWord_6799539).sum := by decide
  have hdescent : baseEnd_6799539 < baseStart_6799539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799543 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 2, 4, 2]
def baseStart_6799543 : Nat := 118140960795 + 6799543 * 2 ^ 59
def prefixEnd_6799543 : Nat := 4983230072969 + 3 ^ 40 * 6799543 * 2
def baseEnd_6799543 : Nat := 3491433789914395490441977

theorem tailTrace_6799543 : CollatzResearch.WordTrace tailWord_6799543 prefixEnd_6799543 3491433789914395490441977 := by
  unfold tailWord_6799543
  simp only [CollatzResearch.WordTrace]
  refine ⟨247999707205424455336123283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165333138136949636890748855 247999707205424455336123283)
  ·
    refine ⟨371999560808136683004184925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 247999707205424455336123283 371999560808136683004184925)
    ·
      refine ⟨139499835303051256126569347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 371999560808136683004184925 139499835303051256126569347)
      ·
        refine ⟨209249752954576884189854021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139499835303051256126569347 209249752954576884189854021)
        ·
          refine ⟨39234328678983165785597629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209249752954576884189854021 39234328678983165785597629)
          ·
            refine ⟨14712873254618687169599111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39234328678983165785597629 14712873254618687169599111)
            ·
              refine ⟨22069309881928030754398667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14712873254618687169599111 22069309881928030754398667)
              ·
                refine ⟨33103964822892046131598001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22069309881928030754398667 33103964822892046131598001)
                ·
                  refine ⟨24827973617169034598698501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33103964822892046131598001 24827973617169034598698501)
                  ·
                    refine ⟨4655245053219193987255969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24827973617169034598698501 4655245053219193987255969)
                    ·
                      refine ⟨3491433789914395490441977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4655245053219193987255969 3491433789914395490441977)
                      ·
                        rfl

theorem cell23_6799543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_6799543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799543 prefixEnd_6799543 := by exact prefixLift 6799543
  have htrace : WordTrace (prefixWord ++ tailWord_6799543) baseStart_6799543 baseEnd_6799543 := by
    simpa [prefixWord, tailWord_6799543, baseEnd_6799543] using wordTrace_append hprefix tailTrace_6799543
  have hstable : (prefixWord ++ tailWord_6799543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799543).length < 2 ^ (prefixWord ++ tailWord_6799543).sum := by decide
  have hdescent : baseEnd_6799543 < baseStart_6799543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799546 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_6799546 : Nat := 118140960795 + 6799546 * 2 ^ 59
def prefixEnd_6799546 : Nat := 4983230072969 + 3 ^ 40 * 6799546 * 2
def baseEnd_6799546 : Nat := 3491435330356358978704463

theorem tailTrace_6799546 : CollatzResearch.WordTrace tailWord_6799546 prefixEnd_6799546 3491435330356358978704463 := by
  unfold tailWord_6799546
  simp only [CollatzResearch.WordTrace]
  refine ⟨61999954156103396712120623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165333211082942391232321661 61999954156103396712120623)
  ·
    refine ⟨92999931234155095068180935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61999954156103396712120623 92999931234155095068180935)
    ·
      refine ⟨139499896851232642602271403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92999931234155095068180935 139499896851232642602271403)
      ·
        refine ⟨209249845276848963903407105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139499896851232642602271403 209249845276848963903407105)
        ·
          refine ⟨156937383957636722927555329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209249845276848963903407105 156937383957636722927555329)
          ·
            refine ⟨117703037968227542195666497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156937383957636722927555329 117703037968227542195666497)
            ·
              refine ⟨88277278476170656646749873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117703037968227542195666497 88277278476170656646749873)
              ·
                refine ⟨66207958857127992485062405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88277278476170656646749873 66207958857127992485062405)
                ·
                  refine ⟨12413992285711498590949201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66207958857127992485062405 12413992285711498590949201)
                  ·
                    refine ⟨9310494214283623943211901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12413992285711498590949201 9310494214283623943211901)
                    ·
                      refine ⟨3491435330356358978704463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9310494214283623943211901 3491435330356358978704463)
                      ·
                        rfl

theorem cell23_6799546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_6799546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799546 prefixEnd_6799546 := by exact prefixLift 6799546
  have htrace : WordTrace (prefixWord ++ tailWord_6799546) baseStart_6799546 baseEnd_6799546 := by
    simpa [prefixWord, tailWord_6799546, baseEnd_6799546] using wordTrace_append hprefix tailTrace_6799546
  have hstable : (prefixWord ++ tailWord_6799546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799546).length < 2 ^ (prefixWord ++ tailWord_6799546).sum := by decide
  have hdescent : baseEnd_6799546 < baseStart_6799546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6799549 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 10]
def baseStart_6799549 : Nat := 118140960795 + 6799549 * 2 ^ 59
def prefixEnd_6799549 : Nat := 4983230072969 + 3 ^ 40 * 6799549 * 2
def baseEnd_6799549 : Nat := 387937430088702496329661

theorem tailTrace_6799549 : CollatzResearch.WordTrace tailWord_6799549 prefixEnd_6799549 387937430088702496329661 := by
  unfold tailWord_6799549
  simp only [CollatzResearch.WordTrace]
  refine ⟨247999926043402718360841701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165333284028935145573894467 247999926043402718360841701)
  ·
    refine ⟨46499986133138009692657819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 247999926043402718360841701 46499986133138009692657819)
    ·
      refine ⟨69749979199707014538986729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46499986133138009692657819 69749979199707014538986729)
      ·
        refine ⟨52312484399780260904240047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69749979199707014538986729 52312484399780260904240047)
        ·
          refine ⟨78468726599670391356360071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52312484399780260904240047 78468726599670391356360071)
          ·
            refine ⟨117703089899505587034540107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78468726599670391356360071 117703089899505587034540107)
            ·
              refine ⟨176554634849258380551810161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117703089899505587034540107 176554634849258380551810161)
              ·
                refine ⟨132415976136943785413857621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176554634849258380551810161 132415976136943785413857621)
                ·
                  refine ⟨387937430088702496329661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132415976136943785413857621 387937430088702496329661)
                  ·
                    rfl

theorem cell23_6799549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_6799549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6799549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6799549 prefixEnd_6799549 := by exact prefixLift 6799549
  have htrace : WordTrace (prefixWord ++ tailWord_6799549) baseStart_6799549 baseEnd_6799549 := by
    simpa [prefixWord, tailWord_6799549, baseEnd_6799549] using wordTrace_append hprefix tailTrace_6799549
  have hstable : (prefixWord ++ tailWord_6799549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6799549).length < 2 ^ (prefixWord ++ tailWord_6799549).sum := by decide
  have hdescent : baseEnd_6799549 < baseStart_6799549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6799549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
