import V185TrunkScan22Chunk315

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2819023 : List Nat := [1, 1, 2, 1, 1, 6, 4, 2, 1, 3]
def baseStart_2819023 : Nat := 118140960795 + 2819023 * 2 ^ 59
def prefixEnd_2819023 : Nat := 4983230072969 + 3 ^ 40 * 2819023 * 2
def baseEnd_2819023 : Nat := 965009183386419528832037

theorem tailTrace_2819023 : CollatzResearch.WordTrace tailWord_2819023 prefixEnd_2819023 965009183386419528832037 := by
  unfold tailWord_2819023
  simp only [CollatzResearch.WordTrace]
  refine ⟨102818215666168596643253723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68545477110779064428835815 102818215666168596643253723)
  ·
    refine ⟨154227323499252894964880585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102818215666168596643253723 154227323499252894964880585)
    ·
      refine ⟨115670492624439671223660439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154227323499252894964880585 115670492624439671223660439)
      ·
        refine ⟨173505738936659506835490659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115670492624439671223660439 173505738936659506835490659)
        ·
          refine ⟨260258608404989260253235989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173505738936659506835490659 260258608404989260253235989)
          ·
            refine ⟨12199622268983871574370437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 260258608404989260253235989 12199622268983871574370437)
            ·
              refine ⟨2287429175434475920194457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12199622268983871574370437 2287429175434475920194457)
              ·
                refine ⟨1715571881575856940145843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2287429175434475920194457 1715571881575856940145843)
                ·
                  refine ⟨2573357822363785410218765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715571881575856940145843 2573357822363785410218765)
                  ·
                    refine ⟨965009183386419528832037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573357822363785410218765 965009183386419528832037)
                    ·
                      rfl

theorem cell22_2819023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 1, 3].length) (baseStart_2819023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819023 prefixEnd_2819023 := by exact prefixLift 2819023
  have htrace : WordTrace (prefixWord ++ tailWord_2819023) baseStart_2819023 baseEnd_2819023 := by
    simpa [prefixWord, tailWord_2819023, baseEnd_2819023] using wordTrace_append hprefix tailTrace_2819023
  have hstable : (prefixWord ++ tailWord_2819023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819023).length < 2 ^ (prefixWord ++ tailWord_2819023).sum := by decide
  have hdescent : baseEnd_2819023 < baseStart_2819023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819034 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_2819034 : Nat := 118140960795 + 2819034 * 2 ^ 59
def prefixEnd_2819034 : Nat := 4983230072969 + 3 ^ 40 * 2819034 * 2
def baseEnd_2819034 : Nat := 965012948911219166807003

theorem tailTrace_2819034 : CollatzResearch.WordTrace tailWord_2819034 prefixEnd_2819034 965012948911219166807003 := by
  unfold tailWord_2819034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25704654217282186380476039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68545744579419163681269437 25704654217282186380476039)
  ·
    refine ⟨38556981325923279570714059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25704654217282186380476039 38556981325923279570714059)
    ·
      refine ⟨57835471988884919356071089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38556981325923279570714059 57835471988884919356071089)
      ·
        refine ⟨43376603991663689517053317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57835471988884919356071089 43376603991663689517053317)
        ·
          refine ⟨8133113248436941784447497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43376603991663689517053317 8133113248436941784447497)
          ·
            refine ⟨6099834936327706338335623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8133113248436941784447497 6099834936327706338335623)
            ·
              refine ⟨9149752404491559507503435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6099834936327706338335623 9149752404491559507503435)
              ·
                refine ⟨13724628606737339261255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9149752404491559507503435 13724628606737339261255153)
                ·
                  refine ⟨10293471455053004445941365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13724628606737339261255153 10293471455053004445941365)
                  ·
                    refine ⟨965012948911219166807003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10293471455053004445941365 965012948911219166807003)
                    ·
                      rfl

theorem cell22_2819034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_2819034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819034 prefixEnd_2819034 := by exact prefixLift 2819034
  have htrace : WordTrace (prefixWord ++ tailWord_2819034) baseStart_2819034 baseEnd_2819034 := by
    simpa [prefixWord, tailWord_2819034, baseEnd_2819034] using wordTrace_append hprefix tailTrace_2819034
  have hstable : (prefixWord ++ tailWord_2819034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819034).length < 2 ^ (prefixWord ++ tailWord_2819034).sum := by decide
  have hdescent : baseEnd_2819034 < baseStart_2819034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819070 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2819070 : Nat := 118140960795 + 2819070 * 2 ^ 59
def prefixEnd_2819070 : Nat := 4983230072969 + 3 ^ 40 * 2819070 * 2
def baseEnd_2819070 : Nat := 321675090815642357635631

theorem tailTrace_2819070 : CollatzResearch.WordTrace tailWord_2819070 prefixEnd_2819070 321675090815642357635631 := by
  unfold tailWord_2819070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12852491237124790458776833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68546619931332215780143109 12852491237124790458776833)
  ·
    refine ⟨9639368427843592844082625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12852491237124790458776833 9639368427843592844082625)
    ·
      refine ⟨7229526320882694633061969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9639368427843592844082625 7229526320882694633061969)
      ·
        refine ⟨5422144740662020974796477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7229526320882694633061969 5422144740662020974796477)
        ·
          refine ⟨2033304277748257865548679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5422144740662020974796477 2033304277748257865548679)
          ·
            refine ⟨3049956416622386798323019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033304277748257865548679 3049956416622386798323019)
            ·
              refine ⟨4574934624933580197484529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049956416622386798323019 4574934624933580197484529)
              ·
                refine ⟨3431200968700185148113397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4574934624933580197484529 3431200968700185148113397)
                ·
                  refine ⟨321675090815642357635631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3431200968700185148113397 321675090815642357635631)
                  ·
                    rfl

theorem cell22_2819070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2819070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819070 prefixEnd_2819070 := by exact prefixLift 2819070
  have htrace : WordTrace (prefixWord ++ tailWord_2819070) baseStart_2819070 baseEnd_2819070 := by
    simpa [prefixWord, tailWord_2819070, baseEnd_2819070] using wordTrace_append hprefix tailTrace_2819070
  have hstable : (prefixWord ++ tailWord_2819070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819070).length < 2 ^ (prefixWord ++ tailWord_2819070).sum := by decide
  have hdescent : baseEnd_2819070 < baseStart_2819070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819096 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 1, 5]
def baseStart_2819096 : Nat := 118140960795 + 2819096 * 2 ^ 59
def prefixEnd_2819096 : Nat := 4983230072969 + 3 ^ 40 * 2819096 * 2
def baseEnd_2819096 : Nat := 965034172778271671756813

theorem tailTrace_2819096 : CollatzResearch.WordTrace tailWord_2819096 prefixEnd_2819096 965034172778271671756813 := by
  unfold tailWord_2819096
  simp only [CollatzResearch.WordTrace]
  refine ⟨51410439097452065055330571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68547252129936086740440761 51410439097452065055330571)
  ·
    refine ⟨77115658646178097582995857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51410439097452065055330571 77115658646178097582995857)
    ·
      refine ⟨57836743984633573187246893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77115658646178097582995857 57836743984633573187246893)
      ·
        refine ⟨21688778994237589945217585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57836743984633573187246893 21688778994237589945217585)
        ·
          refine ⟨16266584245678192458913189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21688778994237589945217585 16266584245678192458913189)
          ·
            refine ⟨3049984546064661086046223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16266584245678192458913189 3049984546064661086046223)
            ·
              refine ⟨4574976819096991629069335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049984546064661086046223 4574976819096991629069335)
              ·
                refine ⟨6862465228645487443604003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574976819096991629069335 6862465228645487443604003)
                ·
                  refine ⟨10293697842968231165406005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6862465228645487443604003 10293697842968231165406005)
                  ·
                    refine ⟨965034172778271671756813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10293697842968231165406005 965034172778271671756813)
                    ·
                      rfl

theorem cell22_2819096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_2819096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819096 prefixEnd_2819096 := by exact prefixLift 2819096
  have htrace : WordTrace (prefixWord ++ tailWord_2819096) baseStart_2819096 baseEnd_2819096 := by
    simpa [prefixWord, tailWord_2819096, baseEnd_2819096] using wordTrace_append hprefix tailTrace_2819096
  have hstable : (prefixWord ++ tailWord_2819096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819096).length < 2 ^ (prefixWord ++ tailWord_2819096).sum := by decide
  have hdescent : baseEnd_2819096 < baseStart_2819096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819111 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2819111 : Nat := 118140960795 + 2819111 * 2 ^ 59
def prefixEnd_2819111 : Nat := 4983230072969 + 3 ^ 40 * 2819111 * 2
def baseEnd_2819111 : Nat := 965039307584816632631767

theorem tailTrace_2819111 : CollatzResearch.WordTrace tailWord_2819111 prefixEnd_2819111 965039307584816632631767 := by
  unfold tailWord_2819111
  simp only [CollatzResearch.WordTrace]
  refine ⟨102821425289849787672457187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68547616859899858448304791 102821425289849787672457187)
  ·
    refine ⟨154232137934774681508685781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102821425289849787672457187 154232137934774681508685781)
    ·
      refine ⟨3614815732846281597859823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 154232137934774681508685781 3614815732846281597859823)
      ·
        refine ⟨5422223599269422396789735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614815732846281597859823 5422223599269422396789735)
        ·
          refine ⟨8133335398904133595184603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422223599269422396789735 8133335398904133595184603)
          ·
            refine ⟨12200003098356200392776905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8133335398904133595184603 12200003098356200392776905)
            ·
              refine ⟨9150002323767150294582679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12200003098356200392776905 9150002323767150294582679)
              ·
                refine ⟨13725003485650725441874019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150002323767150294582679 13725003485650725441874019)
                ·
                  refine ⟨20587505228476088162811029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13725003485650725441874019 20587505228476088162811029)
                  ·
                    refine ⟨965039307584816632631767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20587505228476088162811029 965039307584816632631767)
                    ·
                      rfl

theorem cell22_2819111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2819111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819111 prefixEnd_2819111 := by exact prefixLift 2819111
  have htrace : WordTrace (prefixWord ++ tailWord_2819111) baseStart_2819111 baseEnd_2819111 := by
    simpa [prefixWord, tailWord_2819111, baseEnd_2819111] using wordTrace_append hprefix tailTrace_2819111
  have hstable : (prefixWord ++ tailWord_2819111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819111).length < 2 ^ (prefixWord ++ tailWord_2819111).sum := by decide
  have hdescent : baseEnd_2819111 < baseStart_2819111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819126 : List Nat := [5, 1, 2, 1, 1, 4, 8]
def baseStart_2819126 : Nat := 118140960795 + 2819126 * 2 ^ 59
def prefixEnd_2819126 : Nat := 4983230072969 + 3 ^ 40 * 2819126 * 2
def baseEnd_2819126 : Nat := 35742386755235614574323

theorem tailTrace_2819126 : CollatzResearch.WordTrace tailWord_2819126 prefixEnd_2819126 35742386755235614574323 := by
  unfold tailWord_2819126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426373274049715327140827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68547981589863630156168821 6426373274049715327140827)
  ·
    refine ⟨9639559911074572990711241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6426373274049715327140827 9639559911074572990711241)
    ·
      refine ⟨7229669933305929743033431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9639559911074572990711241 7229669933305929743033431)
      ·
        refine ⟨10844504899958894614550147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7229669933305929743033431 10844504899958894614550147)
        ·
          refine ⟨16266757349938341921825221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10844504899958894614550147 16266757349938341921825221)
          ·
            refine ⟨3050017003113439110342229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16266757349938341921825221 3050017003113439110342229)
            ·
              refine ⟨35742386755235614574323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3050017003113439110342229 35742386755235614574323)
              ·
                rfl

theorem cell22_2819126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 8].length) (baseStart_2819126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819126 prefixEnd_2819126 := by exact prefixLift 2819126
  have htrace : WordTrace (prefixWord ++ tailWord_2819126) baseStart_2819126 baseEnd_2819126 := by
    simpa [prefixWord, tailWord_2819126, baseEnd_2819126] using wordTrace_append hprefix tailTrace_2819126
  have hstable : (prefixWord ++ tailWord_2819126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819126).length < 2 ^ (prefixWord ++ tailWord_2819126).sum := by decide
  have hdescent : baseEnd_2819126 < baseStart_2819126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819141 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_2819141 : Nat := 118140960795 + 2819141 * 2 ^ 59
def prefixEnd_2819141 : Nat := 4983230072969 + 3 ^ 40 * 2819141 * 2
def baseEnd_2819141 : Nat := 965049577197906554381675

theorem tailTrace_2819141 : CollatzResearch.WordTrace tailWord_2819141 prefixEnd_2819141 965049577197906554381675 := by
  unfold tailWord_2819141
  simp only [CollatzResearch.WordTrace]
  refine ⟨102822519479741102796049277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68548346319827401864032851 102822519479741102796049277)
  ·
    refine ⟨38558444804902913548518479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102822519479741102796049277 38558444804902913548518479)
    ·
      refine ⟨57837667207354370322777719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38558444804902913548518479 57837667207354370322777719)
      ·
        refine ⟨86756500811031555484166579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57837667207354370322777719 86756500811031555484166579)
        ·
          refine ⟨130134751216547333226249869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86756500811031555484166579 130134751216547333226249869)
          ·
            refine ⟨48800531706205249959843701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130134751216547333226249869 48800531706205249959843701)
            ·
              refine ⟨4575049847456742183735347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48800531706205249959843701 4575049847456742183735347)
              ·
                refine ⟨6862574771185113275603021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575049847456742183735347 6862574771185113275603021)
                ·
                  refine ⟨2573465539194417478351133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6862574771185113275603021 2573465539194417478351133)
                  ·
                    refine ⟨965049577197906554381675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573465539194417478351133 965049577197906554381675)
                    ·
                      rfl

theorem cell22_2819141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_2819141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819141 prefixEnd_2819141 := by exact prefixLift 2819141
  have htrace : WordTrace (prefixWord ++ tailWord_2819141) baseStart_2819141 baseEnd_2819141 := by
    simpa [prefixWord, tailWord_2819141, baseEnd_2819141] using wordTrace_append hprefix tailTrace_2819141
  have hstable : (prefixWord ++ tailWord_2819141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819141).length < 2 ^ (prefixWord ++ tailWord_2819141).sum := by decide
  have hdescent : baseEnd_2819141 < baseStart_2819141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819201 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2819201 : Nat := 118140960795 + 2819201 * 2 ^ 59
def prefixEnd_2819201 : Nat := 4983230072969 + 3 ^ 40 * 2819201 * 2
def baseEnd_2819201 : Nat := 965070116424086397881491

theorem tailTrace_2819201 : CollatzResearch.WordTrace tailWord_2819201 prefixEnd_2819201 965070116424086397881491 := by
  unfold tailWord_2819201
  simp only [CollatzResearch.WordTrace]
  refine ⟨102824707859523733043233457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68549805239682488695488971 102824707859523733043233457)
  ·
    refine ⟨77118530894642799782425093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102824707859523733043233457 77118530894642799782425093)
    ·
      refine ⟨14459724542745524959204705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77118530894642799782425093 14459724542745524959204705)
      ·
        refine ⟨10844793407059143719403529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14459724542745524959204705 10844793407059143719403529)
        ·
          refine ⟨8133595055294357789552647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10844793407059143719403529 8133595055294357789552647)
          ·
            refine ⟨12200392582941536684328971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8133595055294357789552647 12200392582941536684328971)
            ·
              refine ⟨18300588874412305026493457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12200392582941536684328971 18300588874412305026493457)
              ·
                refine ⟨13725441655809228769870093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18300588874412305026493457 13725441655809228769870093)
                ·
                  refine ⟨5147040620928460788701285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13725441655809228769870093 5147040620928460788701285)
                  ·
                    refine ⟨965070116424086397881491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5147040620928460788701285 965070116424086397881491)
                    ·
                      rfl

theorem cell22_2819201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2819201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819201 prefixEnd_2819201 := by exact prefixLift 2819201
  have htrace : WordTrace (prefixWord ++ tailWord_2819201) baseStart_2819201 baseEnd_2819201 := by
    simpa [prefixWord, tailWord_2819201, baseEnd_2819201] using wordTrace_append hprefix tailTrace_2819201
  have hstable : (prefixWord ++ tailWord_2819201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819201).length < 2 ^ (prefixWord ++ tailWord_2819201).sum := by decide
  have hdescent : baseEnd_2819201 < baseStart_2819201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819233 : List Nat := [1, 2, 3, 3, 1, 1, 4, 3, 4]
def baseStart_2819233 : Nat := 118140960795 + 2819233 * 2 ^ 59
def prefixEnd_2819233 : Nat := 4983230072969 + 3 ^ 40 * 2819233 * 2
def baseEnd_2819233 : Nat := 321693690226016327027131

theorem tailTrace_2819233 : CollatzResearch.WordTrace tailWord_2819233 prefixEnd_2819233 321693690226016327027131 := by
  unfold tailWord_2819233
  simp only [CollatzResearch.WordTrace]
  refine ⟨102825874995407802508398353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68550583330271868338932235 102825874995407802508398353)
  ·
    refine ⟨77119406246555851881298765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102825874995407802508398353 77119406246555851881298765)
    ·
      refine ⟨28919777342458444455487037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77119406246555851881298765 28919777342458444455487037)
      ·
        refine ⟨10844916503421916670807639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28919777342458444455487037 10844916503421916670807639)
        ·
          refine ⟨16267374755132875006211459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10844916503421916670807639 16267374755132875006211459)
          ·
            refine ⟨24401062132699312509317189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16267374755132875006211459 24401062132699312509317189)
            ·
              refine ⟨4575199149881121095496973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24401062132699312509317189 4575199149881121095496973)
              ·
                refine ⟨1715699681205420410811365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4575199149881121095496973 1715699681205420410811365)
                ·
                  refine ⟨321693690226016327027131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1715699681205420410811365 321693690226016327027131)
                  ·
                    rfl

theorem cell22_2819233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_2819233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819233 prefixEnd_2819233 := by exact prefixLift 2819233
  have htrace : WordTrace (prefixWord ++ tailWord_2819233) baseStart_2819233 baseEnd_2819233 := by
    simpa [prefixWord, tailWord_2819233, baseEnd_2819233] using wordTrace_append hprefix tailTrace_2819233
  have hstable : (prefixWord ++ tailWord_2819233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819233).length < 2 ^ (prefixWord ++ tailWord_2819233).sum := by decide
  have hdescent : baseEnd_2819233 < baseStart_2819233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819265 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2819265 : Nat := 118140960795 + 2819265 * 2 ^ 59
def prefixEnd_2819265 : Nat := 4983230072969 + 3 ^ 40 * 2819265 * 2
def baseEnd_2819265 : Nat := 965092024932011564281295

theorem tailTrace_2819265 : CollatzResearch.WordTrace tailWord_2819265 prefixEnd_2819265 965092024932011564281295 := by
  unfold tailWord_2819265
  simp only [CollatzResearch.WordTrace]
  refine ⟨102827042131291871973563249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68551361420861247982375499 102827042131291871973563249)
  ·
    refine ⟨77120281598468903980172437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102827042131291871973563249 77120281598468903980172437)
    ·
      refine ⟨3615013199928229874070583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77120281598468903980172437 3615013199928229874070583)
      ·
        refine ⟨5422519799892344811105875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615013199928229874070583 5422519799892344811105875)
        ·
          refine ⟨8133779699838517216658813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5422519799892344811105875 8133779699838517216658813)
          ·
            refine ⟨3050167387439443956247055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8133779699838517216658813 3050167387439443956247055)
            ·
              refine ⟨4575251081159165934370583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050167387439443956247055 4575251081159165934370583)
              ·
                refine ⟨6862876621738748901555875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575251081159165934370583 6862876621738748901555875)
                ·
                  refine ⟨10294314932608123352333813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6862876621738748901555875 10294314932608123352333813)
                  ·
                    refine ⟨965092024932011564281295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10294314932608123352333813 965092024932011564281295)
                    ·
                      rfl

theorem cell22_2819265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2819265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819265 prefixEnd_2819265 := by exact prefixLift 2819265
  have htrace : WordTrace (prefixWord ++ tailWord_2819265) baseStart_2819265 baseEnd_2819265 := by
    simpa [prefixWord, tailWord_2819265, baseEnd_2819265] using wordTrace_append hprefix tailTrace_2819265
  have hstable : (prefixWord ++ tailWord_2819265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819265).length < 2 ^ (prefixWord ++ tailWord_2819265).sum := by decide
  have hdescent : baseEnd_2819265 < baseStart_2819265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819284 : List Nat := [2, 4, 1, 4, 2, 1, 1, 3, 4]
def baseStart_2819284 : Nat := 118140960795 + 2819284 * 2 ^ 59
def prefixEnd_2819284 : Nat := 4983230072969 + 3 ^ 40 * 2819284 * 2
def baseEnd_2819284 : Nat := 321699509673433949352079

theorem tailTrace_2819284 : CollatzResearch.WordTrace tailWord_2819284 prefixEnd_2819284 321699509673433949352079 := by
  unfold tailWord_2819284
  simp only [CollatzResearch.WordTrace]
  refine ⟨51413867559111519109252453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68551823412148692145669937 51413867559111519109252453)
  ·
    refine ⟨9640100167333409832984835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51413867559111519109252453 9640100167333409832984835)
    ·
      refine ⟨14460150251000114749477253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9640100167333409832984835 14460150251000114749477253)
      ·
        refine ⟨2711278172062521515526985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14460150251000114749477253 2711278172062521515526985)
        ·
          refine ⟨2033458629046891136645239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2711278172062521515526985 2033458629046891136645239)
          ·
            refine ⟨3050187943570336704967859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033458629046891136645239 3050187943570336704967859)
            ·
              refine ⟨4575281915355505057451789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050187943570336704967859 4575281915355505057451789)
              ·
                refine ⟨1715730718258314396544421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4575281915355505057451789 1715730718258314396544421)
                ·
                  refine ⟨321699509673433949352079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1715730718258314396544421 321699509673433949352079)
                  ·
                    rfl

theorem cell22_2819284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_2819284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819284 prefixEnd_2819284 := by exact prefixLift 2819284
  have htrace : WordTrace (prefixWord ++ tailWord_2819284) baseStart_2819284 baseEnd_2819284 := by
    simpa [prefixWord, tailWord_2819284, baseEnd_2819284] using wordTrace_append hprefix tailTrace_2819284
  have hstable : (prefixWord ++ tailWord_2819284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819284).length < 2 ^ (prefixWord ++ tailWord_2819284).sum := by decide
  have hdescent : baseEnd_2819284 < baseStart_2819284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819306 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_2819306 : Nat := 118140960795 + 2819306 * 2 ^ 59
def prefixEnd_2819306 : Nat := 4983230072969 + 3 ^ 40 * 2819306 * 2
def baseEnd_2819306 : Nat := 321702020023300374668723

theorem tailTrace_2819306 : CollatzResearch.WordTrace tailWord_2819306 prefixEnd_2819306 321702020023300374668723 := by
  unfold tailWord_2819306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25707134381035833993951443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68552358349428890650537181 25707134381035833993951443)
  ·
    refine ⟨38560701571553750990927165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25707134381035833993951443 38560701571553750990927165)
    ·
      refine ⟨14460263089332656621597687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38560701571553750990927165 14460263089332656621597687)
      ·
        refine ⟨21690394633998984932396531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14460263089332656621597687 21690394633998984932396531)
        ·
          refine ⟨32535591950998477398594797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21690394633998984932396531 32535591950998477398594797)
          ·
            refine ⟨12200846981624429024473049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32535591950998477398594797 12200846981624429024473049)
            ·
              refine ⟨9150635236218321768354787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12200846981624429024473049 9150635236218321768354787)
              ·
                refine ⟨13725952854327482652532181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9150635236218321768354787 13725952854327482652532181)
                ·
                  refine ⟨321702020023300374668723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13725952854327482652532181 321702020023300374668723)
                  ·
                    rfl

theorem cell22_2819306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_2819306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819306 prefixEnd_2819306 := by exact prefixLift 2819306
  have htrace : WordTrace (prefixWord ++ tailWord_2819306) baseStart_2819306 baseEnd_2819306 := by
    simpa [prefixWord, tailWord_2819306, baseEnd_2819306] using wordTrace_append hprefix tailTrace_2819306
  have hstable : (prefixWord ++ tailWord_2819306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819306).length < 2 ^ (prefixWord ++ tailWord_2819306).sum := by decide
  have hdescent : baseEnd_2819306 < baseStart_2819306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819310 : List Nat := [4, 1, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_2819310 : Nat := 118140960795 + 2819310 * 2 ^ 59
def prefixEnd_2819310 : Nat := 4983230072969 + 3 ^ 40 * 2819310 * 2
def baseEnd_2819310 : Nat := 965107429351646446906157

theorem tailTrace_2819310 : CollatzResearch.WordTrace tailWord_2819310 prefixEnd_2819310 965107429351646446906157 := by
  unfold tailWord_2819310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12853585427016105582368923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68552455610752563105967589 12853585427016105582368923)
  ·
    refine ⟨19280378140524158373553385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12853585427016105582368923 19280378140524158373553385)
    ·
      refine ⟨14460283605393118780165039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19280378140524158373553385 14460283605393118780165039)
      ·
        refine ⟨21690425408089678170247559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14460283605393118780165039 21690425408089678170247559)
        ·
          refine ⟨32535638112134517255371339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21690425408089678170247559 32535638112134517255371339)
          ·
            refine ⟨48803457168201775883057009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32535638112134517255371339 48803457168201775883057009)
            ·
              refine ⟨36602592876151331912292757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48803457168201775883057009 36602592876151331912292757)
              ·
                refine ⟨1715746541069593683388723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36602592876151331912292757 1715746541069593683388723)
                ·
                  refine ⟨2573619811604390525083085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715746541069593683388723 2573619811604390525083085)
                  ·
                    refine ⟨965107429351646446906157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573619811604390525083085 965107429351646446906157)
                    ·
                      rfl

theorem cell22_2819310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_2819310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819310 prefixEnd_2819310 := by exact prefixLift 2819310
  have htrace : WordTrace (prefixWord ++ tailWord_2819310) baseStart_2819310 baseEnd_2819310 := by
    simpa [prefixWord, tailWord_2819310, baseEnd_2819310] using wordTrace_append hprefix tailTrace_2819310
  have hstable : (prefixWord ++ tailWord_2819310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819310).length < 2 ^ (prefixWord ++ tailWord_2819310).sum := by decide
  have hdescent : baseEnd_2819310 < baseStart_2819310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819434 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_2819434 : Nat := 118140960795 + 2819434 * 2 ^ 59
def prefixEnd_2819434 : Nat := 4983230072969 + 3 ^ 40 * 2819434 * 2
def baseEnd_2819434 : Nat := 965149877085751456805777

theorem tailTrace_2819434 : CollatzResearch.WordTrace tailWord_2819434 prefixEnd_2819434 965149877085751456805777 := by
  unfold tailWord_2819434
  simp only [CollatzResearch.WordTrace]
  refine ⟨25708301516919903459116339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68555470711786409224310237 25708301516919903459116339)
  ·
    refine ⟨38562452275379855188674509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25708301516919903459116339 38562452275379855188674509)
    ·
      refine ⟨14460919603267445695752941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38562452275379855188674509 14460919603267445695752941)
      ·
        refine ⟨5422844851225292135907353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14460919603267445695752941 5422844851225292135907353)
        ·
          refine ⟨4067133638418969101930515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5422844851225292135907353 4067133638418969101930515)
          ·
            refine ⟨6100700457628453652895773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067133638418969101930515 6100700457628453652895773)
            ·
              refine ⟨2287762671610670119835915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6100700457628453652895773 2287762671610670119835915)
              ·
                refine ⟨3431644007416005179753873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287762671610670119835915 3431644007416005179753873)
                ·
                  refine ⟨2573733005562003884815405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431644007416005179753873 2573733005562003884815405)
                  ·
                    refine ⟨965149877085751456805777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573733005562003884815405 965149877085751456805777)
                    ·
                      rfl

theorem cell22_2819434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_2819434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819434 prefixEnd_2819434 := by exact prefixLift 2819434
  have htrace : WordTrace (prefixWord ++ tailWord_2819434) baseStart_2819434 baseEnd_2819434 := by
    simpa [prefixWord, tailWord_2819434, baseEnd_2819434] using wordTrace_append hprefix tailTrace_2819434
  have hstable : (prefixWord ++ tailWord_2819434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819434).length < 2 ^ (prefixWord ++ tailWord_2819434).sum := by decide
  have hdescent : baseEnd_2819434 < baseStart_2819434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819456 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_2819456 : Nat := 118140960795 + 2819456 * 2 ^ 59
def prefixEnd_2819456 : Nat := 4983230072969 + 3 ^ 40 * 2819456 * 2
def baseEnd_2819456 : Nat := 965157408135350732755709

theorem tailTrace_2819456 : CollatzResearch.WordTrace tailWord_2819456 prefixEnd_2819456 965157408135350732755709 := by
  unfold tailWord_2819456
  simp only [CollatzResearch.WordTrace]
  refine ⟨51417004236799955796883111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68556005649066607729177481 51417004236799955796883111)
  ·
    refine ⟨77125506355199933695324667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51417004236799955796883111 77125506355199933695324667)
    ·
      refine ⟨115688259532799900542987001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77125506355199933695324667 115688259532799900542987001)
      ·
        refine ⟨86766194649599925407240251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115688259532799900542987001 86766194649599925407240251)
        ·
          refine ⟨130149291974399888110860377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86766194649599925407240251 130149291974399888110860377)
          ·
            refine ⟨97611968980799916083145283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130149291974399888110860377 97611968980799916083145283)
            ·
              refine ⟨146417953471199874124717925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97611968980799916083145283 146417953471199874124717925)
              ·
                refine ⟨27453366275849976398384611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146417953471199874124717925 27453366275849976398384611)
                ·
                  refine ⟨41180049413774964597576917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27453366275849976398384611 41180049413774964597576917)
                  ·
                    refine ⟨965157408135350732755709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41180049413774964597576917 965157408135350732755709)
                    ·
                      rfl

theorem cell22_2819456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_2819456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819456 prefixEnd_2819456 := by exact prefixLift 2819456
  have htrace : WordTrace (prefixWord ++ tailWord_2819456) baseStart_2819456 baseEnd_2819456 := by
    simpa [prefixWord, tailWord_2819456, baseEnd_2819456] using wordTrace_append hprefix tailTrace_2819456
  have hstable : (prefixWord ++ tailWord_2819456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819456).length < 2 ^ (prefixWord ++ tailWord_2819456).sum := by decide
  have hdescent : baseEnd_2819456 < baseStart_2819456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819488 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_2819488 : Nat := 118140960795 + 2819488 * 2 ^ 59
def prefixEnd_2819488 : Nat := 4983230072969 + 3 ^ 40 * 2819488 * 2
def baseEnd_2819488 : Nat := 965168362389313315955611

theorem tailTrace_2819488 : CollatzResearch.WordTrace tailWord_2819488 prefixEnd_2819488 965168362389313315955611 := by
  unfold tailWord_2819488
  simp only [CollatzResearch.WordTrace]
  refine ⟨51417587804741990529465559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68556783739655987372620745 51417587804741990529465559)
  ·
    refine ⟨77126381707112985794198339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51417587804741990529465559 77126381707112985794198339)
    ·
      refine ⟨115689572560669478691297509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77126381707112985794198339 115689572560669478691297509)
      ·
        refine ⟨21691794855125527254618283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115689572560669478691297509 21691794855125527254618283)
        ·
          refine ⟨32537692282688290881927425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21691794855125527254618283 32537692282688290881927425)
          ·
            refine ⟨24403269212016218161445569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32537692282688290881927425 24403269212016218161445569)
            ·
              refine ⟨18302451909012163621084177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24403269212016218161445569 18302451909012163621084177)
              ·
                refine ⟨13726838931759122715813133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18302451909012163621084177 13726838931759122715813133)
                ·
                  refine ⟨5147564599409671018429925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13726838931759122715813133 5147564599409671018429925)
                  ·
                    refine ⟨965168362389313315955611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5147564599409671018429925 965168362389313315955611)
                    ·
                      rfl

theorem cell22_2819488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_2819488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819488 prefixEnd_2819488 := by exact prefixLift 2819488
  have htrace : WordTrace (prefixWord ++ tailWord_2819488) baseStart_2819488 baseEnd_2819488 := by
    simpa [prefixWord, tailWord_2819488, baseEnd_2819488] using wordTrace_append hprefix tailTrace_2819488
  have hstable : (prefixWord ++ tailWord_2819488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819488).length < 2 ^ (prefixWord ++ tailWord_2819488).sum := by decide
  have hdescent : baseEnd_2819488 < baseStart_2819488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819535 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 2, 3]
def baseStart_2819535 : Nat := 118140960795 + 2819535 * 2 ^ 59
def prefixEnd_2819535 : Nat := 4983230072969 + 3 ^ 40 * 2819535 * 2
def baseEnd_2819535 : Nat := 965184451449820860030467

theorem tailTrace_2819535 : CollatzResearch.WordTrace tailWord_2819535 prefixEnd_2819535 965184451449820860030467 := by
  unfold tailWord_2819535
  simp only [CollatzResearch.WordTrace]
  refine ⟨102836889840313708085892059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68557926560209138723928039 102836889840313708085892059)
  ·
    refine ⟨154255334760470562128838089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102836889840313708085892059 154255334760470562128838089)
    ·
      refine ⟨115691501070352921596628567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154255334760470562128838089 115691501070352921596628567)
      ·
        refine ⟨173537251605529382394942851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115691501070352921596628567 173537251605529382394942851)
        ·
          refine ⟨260305877408294073592414277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173537251605529382394942851 260305877408294073592414277)
          ·
            refine ⟨48807352014055138798577677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260305877408294073592414277 48807352014055138798577677)
            ·
              refine ⟨18302757005270677049466629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48807352014055138798577677 18302757005270677049466629)
              ·
                refine ⟨3431766938488251946774993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18302757005270677049466629 3431766938488251946774993)
                ·
                  refine ⟨2573825203866188960081245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431766938488251946774993 2573825203866188960081245)
                  ·
                    refine ⟨965184451449820860030467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573825203866188960081245 965184451449820860030467)
                    ·
                      rfl

theorem cell22_2819535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_2819535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819535 prefixEnd_2819535 := by exact prefixLift 2819535
  have htrace : WordTrace (prefixWord ++ tailWord_2819535) baseStart_2819535 baseEnd_2819535 := by
    simpa [prefixWord, tailWord_2819535, baseEnd_2819535] using wordTrace_append hprefix tailTrace_2819535
  have hstable : (prefixWord ++ tailWord_2819535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819535).length < 2 ^ (prefixWord ++ tailWord_2819535).sum := by decide
  have hdescent : baseEnd_2819535 < baseStart_2819535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819582 : List Nat := [4, 2, 2, 3, 1, 1, 9]
def baseStart_2819582 : Nat := 118140960795 + 2819582 * 2 ^ 59
def prefixEnd_2819582 : Nat := 4983230072969 + 3 ^ 40 * 2819582 * 2
def baseEnd_2819582 : Nat := 35748168167049200152049

theorem tailTrace_2819582 : CollatzResearch.WordTrace tailWord_2819582 prefixEnd_2819582 35748168167049200152049 := by
  unfold tailWord_2819582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12854825508892929389106625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68559069380762290075235333 12854825508892929389106625)
  ·
    refine ⟨9641119131669697041829969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12854825508892929389106625 9641119131669697041829969)
    ·
      refine ⟨7230839348752272781372477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9641119131669697041829969 7230839348752272781372477)
      ·
        refine ⟨2711564755782102293014679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7230839348752272781372477 2711564755782102293014679)
        ·
          refine ⟨4067347133673153439522019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711564755782102293014679 4067347133673153439522019)
          ·
            refine ⟨6101020700509730159283029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067347133673153439522019 6101020700509730159283029)
            ·
              refine ⟨35748168167049200152049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6101020700509730159283029 35748168167049200152049)
              ·
                rfl

theorem cell22_2819582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 9].length) (baseStart_2819582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819582 prefixEnd_2819582 := by exact prefixLift 2819582
  have htrace : WordTrace (prefixWord ++ tailWord_2819582) baseStart_2819582 baseEnd_2819582 := by
    simpa [prefixWord, tailWord_2819582, baseEnd_2819582] using wordTrace_append hprefix tailTrace_2819582
  have hstable : (prefixWord ++ tailWord_2819582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819582).length < 2 ^ (prefixWord ++ tailWord_2819582).sum := by decide
  have hdescent : baseEnd_2819582 < baseStart_2819582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819586 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2819586 : Nat := 118140960795 + 2819586 * 2 ^ 59
def prefixEnd_2819586 : Nat := 4983230072969 + 3 ^ 40 * 2819586 * 2
def baseEnd_2819586 : Nat := 965201909792073727005311

theorem tailTrace_2819586 : CollatzResearch.WordTrace tailWord_2819586 prefixEnd_2819586 965201909792073727005311 := by
  unfold tailWord_2819586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25709687490782235948999653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68559166642085962530665741 25709687490782235948999653)
  ·
    refine ⟨4820566404521669240437435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25709687490782235948999653 4820566404521669240437435)
    ·
      refine ⟨7230849606782503860656153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4820566404521669240437435 7230849606782503860656153)
      ·
        refine ⟨5423137205086877895492115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7230849606782503860656153 5423137205086877895492115)
        ·
          refine ⟨8134705807630316843238173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5423137205086877895492115 8134705807630316843238173)
          ·
            refine ⟨3050514677861368816214315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8134705807630316843238173 3050514677861368816214315)
            ·
              refine ⟨4575772016792053224321473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050514677861368816214315 4575772016792053224321473)
              ·
                refine ⟨3431829012594039918241105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4575772016792053224321473 3431829012594039918241105)
                ·
                  refine ⟨2573871759445529938680829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431829012594039918241105 2573871759445529938680829)
                  ·
                    refine ⟨965201909792073727005311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573871759445529938680829 965201909792073727005311)
                    ·
                      rfl

theorem cell22_2819586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2819586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819586 prefixEnd_2819586 := by exact prefixLift 2819586
  have htrace : WordTrace (prefixWord ++ tailWord_2819586) baseStart_2819586 baseEnd_2819586 := by
    simpa [prefixWord, tailWord_2819586, baseEnd_2819586] using wordTrace_append hprefix tailTrace_2819586
  have hstable : (prefixWord ++ tailWord_2819586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819586).length < 2 ^ (prefixWord ++ tailWord_2819586).sum := by decide
  have hdescent : baseEnd_2819586 < baseStart_2819586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819593 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 7]
def baseStart_2819593 : Nat := 118140960795 + 2819593 * 2 ^ 59
def prefixEnd_2819593 : Nat := 4983230072969 + 3 ^ 40 * 2819593 * 2
def baseEnd_2819593 : Nat := 321734768678376014026763

theorem tailTrace_2819593 : CollatzResearch.WordTrace tailWord_2819593 prefixEnd_2819593 321734768678376014026763 := by
  unfold tailWord_2819593
  simp only [CollatzResearch.WordTrace]
  refine ⟨102839005274103583991503433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68559336849402389327668955 102839005274103583991503433)
  ·
    refine ⟨77129253955577687993627575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102839005274103583991503433 77129253955577687993627575)
    ·
      refine ⟨115693880933366531990441363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77129253955577687993627575 115693880933366531990441363)
      ·
        refine ⟨173540821400049797985662045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115693880933366531990441363 173540821400049797985662045)
        ·
          refine ⟨65077808025018674244623267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173540821400049797985662045 65077808025018674244623267)
          ·
            refine ⟨97616712037528011366934901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65077808025018674244623267 97616712037528011366934901)
            ·
              refine ⟨9151566753518251065650147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97616712037528011366934901 9151566753518251065650147)
              ·
                refine ⟨13727350130277376598475221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9151566753518251065650147 13727350130277376598475221)
                ·
                  refine ⟨321734768678376014026763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13727350130277376598475221 321734768678376014026763)
                  ·
                    rfl

theorem cell22_2819593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_2819593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819593 prefixEnd_2819593 := by exact prefixLift 2819593
  have htrace : WordTrace (prefixWord ++ tailWord_2819593) baseStart_2819593 baseEnd_2819593 := by
    simpa [prefixWord, tailWord_2819593, baseEnd_2819593] using wordTrace_append hprefix tailTrace_2819593
  have hstable : (prefixWord ++ tailWord_2819593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819593).length < 2 ^ (prefixWord ++ tailWord_2819593).sum := by decide
  have hdescent : baseEnd_2819593 < baseStart_2819593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819661 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2819661 : Nat := 118140960795 + 2819661 * 2 ^ 59
def prefixEnd_2819661 : Nat := 4983230072969 + 3 ^ 40 * 2819661 * 2
def baseEnd_2819661 : Nat := 321742527941599510460027

theorem tailTrace_2819661 : CollatzResearch.WordTrace tailWord_2819661 prefixEnd_2819661 321742527941599510460027 := by
  unfold tailWord_2819661
  simp only [CollatzResearch.WordTrace]
  refine ⟨102841485437857231604978837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68560990291904821069985891 102841485437857231604978837)
  ·
    refine ⟨4820694629899557731483383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102841485437857231604978837 4820694629899557731483383)
    ·
      refine ⟨7231041944849336597225075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4820694629899557731483383 7231041944849336597225075)
      ·
        refine ⟨10846562917274004895837613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7231041944849336597225075 10846562917274004895837613)
        ·
          refine ⟨4067461093977751835939105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10846562917274004895837613 4067461093977751835939105)
          ·
            refine ⟨3050595820483313876954329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067461093977751835939105 3050595820483313876954329)
            ·
              refine ⟨2287946865362485407715747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3050595820483313876954329 2287946865362485407715747)
              ·
                refine ⟨3431920298043728111573621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287946865362485407715747 3431920298043728111573621)
                ·
                  refine ⟨321742527941599510460027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3431920298043728111573621 321742527941599510460027)
                  ·
                    rfl

theorem cell22_2819661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2819661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819661 prefixEnd_2819661 := by exact prefixLift 2819661
  have htrace : WordTrace (prefixWord ++ tailWord_2819661) baseStart_2819661 baseEnd_2819661 := by
    simpa [prefixWord, tailWord_2819661, baseEnd_2819661] using wordTrace_append hprefix tailTrace_2819661
  have hstable : (prefixWord ++ tailWord_2819661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819661).length < 2 ^ (prefixWord ++ tailWord_2819661).sum := by decide
  have hdescent : baseEnd_2819661 < baseStart_2819661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819749 : List Nat := [1, 3, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_2819749 : Nat := 118140960795 + 2819749 * 2 ^ 59
def prefixEnd_2819749 : Nat := 4983230072969 + 3 ^ 40 * 2819749 * 2
def baseEnd_2819749 : Nat := 965257708023195635179811

theorem tailTrace_2819749 : CollatzResearch.WordTrace tailWord_2819749 prefixEnd_2819749 965257708023195635179811 := by
  unfold tailWord_2819749
  simp only [CollatzResearch.WordTrace]
  refine ⟨102844695061538422634182301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68563130041025615089454867 102844695061538422634182301)
  ·
    refine ⟨38566760648076908487818363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102844695061538422634182301 38566760648076908487818363)
    ·
      refine ⟨57850140972115362731727545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38566760648076908487818363 57850140972115362731727545)
      ·
        refine ⟨43387605729086522048795659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57850140972115362731727545 43387605729086522048795659)
        ·
          refine ⟨65081408593629783073193489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43387605729086522048795659 65081408593629783073193489)
          ·
            refine ⟨48811056445222337304895117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65081408593629783073193489 48811056445222337304895117)
            ·
              refine ⟨18304146166958376489335669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48811056445222337304895117 18304146166958376489335669)
              ·
                refine ⟨1716013703152347795875219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18304146166958376489335669 1716013703152347795875219)
                ·
                  refine ⟨2574020554728521693812829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716013703152347795875219 2574020554728521693812829)
                  ·
                    refine ⟨965257708023195635179811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574020554728521693812829 965257708023195635179811)
                    ·
                      rfl

theorem cell22_2819749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_2819749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819749 prefixEnd_2819749 := by exact prefixLift 2819749
  have htrace : WordTrace (prefixWord ++ tailWord_2819749) baseStart_2819749 baseEnd_2819749 := by
    simpa [prefixWord, tailWord_2819749, baseEnd_2819749] using wordTrace_append hprefix tailTrace_2819749
  have hstable : (prefixWord ++ tailWord_2819749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819749).length < 2 ^ (prefixWord ++ tailWord_2819749).sum := by decide
  have hdescent : baseEnd_2819749 < baseStart_2819749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819760 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_2819760 : Nat := 118140960795 + 2819760 * 2 ^ 59
def prefixEnd_2819760 : Nat := 4983230072969 + 3 ^ 40 * 2819760 * 2
def baseEnd_2819760 : Nat := 965261473547995273154777

theorem tailTrace_2819760 : CollatzResearch.WordTrace tailWord_2819760 prefixEnd_2819760 965261473547995273154777 := by
  unfold tailWord_2819760
  simp only [CollatzResearch.WordTrace]
  refine ⟨51422548132249285756416367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68563397509665714341888489 51422548132249285756416367)
  ·
    refine ⟨77133822198373928634624551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51422548132249285756416367 77133822198373928634624551)
    ·
      refine ⟨115700733297560892951936827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77133822198373928634624551 115700733297560892951936827)
      ·
        refine ⟨173551099946341339427905241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115700733297560892951936827 173551099946341339427905241)
        ·
          refine ⟨130163324959756004570928931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173551099946341339427905241 130163324959756004570928931)
          ·
            refine ⟨195244987439634006856393397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130163324959756004570928931 195244987439634006856393397)
            ·
              refine ⟨18304217572465688142786881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195244987439634006856393397 18304217572465688142786881)
              ·
                refine ⟨13728163179349266107090161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18304217572465688142786881 13728163179349266107090161)
                ·
                  refine ⟨10296122384511949580317621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13728163179349266107090161 10296122384511949580317621)
                  ·
                    refine ⟨965261473547995273154777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10296122384511949580317621 965261473547995273154777)
                    ·
                      rfl

theorem cell22_2819760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_2819760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819760 prefixEnd_2819760 := by exact prefixLift 2819760
  have htrace : WordTrace (prefixWord ++ tailWord_2819760) baseStart_2819760 baseEnd_2819760 := by
    simpa [prefixWord, tailWord_2819760, baseEnd_2819760] using wordTrace_append hprefix tailTrace_2819760
  have hstable : (prefixWord ++ tailWord_2819760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819760).length < 2 ^ (prefixWord ++ tailWord_2819760).sum := by decide
  have hdescent : baseEnd_2819760 < baseStart_2819760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819762 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_2819762 : Nat := 118140960795 + 2819762 * 2 ^ 59
def prefixEnd_2819762 : Nat := 4983230072969 + 3 ^ 40 * 2819762 * 2
def baseEnd_2819762 : Nat := 321754052729622644868257

theorem tailTrace_2819762 : CollatzResearch.WordTrace tailWord_2819762 prefixEnd_2819762 321754052729622644868257 := by
  unfold tailWord_2819762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711292302622831463601385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68563446140327550569603693 25711292302622831463601385)
  ·
    refine ⟨19283469226967123597701039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25711292302622831463601385 19283469226967123597701039)
    ·
      refine ⟨28925203840450685396551559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19283469226967123597701039 28925203840450685396551559)
      ·
        refine ⟨43387805760676028094827339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28925203840450685396551559 43387805760676028094827339)
        ·
          refine ⟨65081708641014042142241009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43387805760676028094827339 65081708641014042142241009)
          ·
            refine ⟨48811281480760531606680757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65081708641014042142241009 48811281480760531606680757)
            ·
              refine ⟨4576057638821299838126321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48811281480760531606680757 4576057638821299838126321)
              ·
                refine ⟨3432043229115974878594741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4576057638821299838126321 3432043229115974878594741)
                ·
                  refine ⟨321754052729622644868257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432043229115974878594741 321754052729622644868257)
                  ·
                    rfl

theorem cell22_2819762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_2819762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819762 prefixEnd_2819762 := by exact prefixLift 2819762
  have htrace : WordTrace (prefixWord ++ tailWord_2819762) baseStart_2819762 baseEnd_2819762 := by
    simpa [prefixWord, tailWord_2819762, baseEnd_2819762] using wordTrace_append hprefix tailTrace_2819762
  have hstable : (prefixWord ++ tailWord_2819762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819762).length < 2 ^ (prefixWord ++ tailWord_2819762).sum := by decide
  have hdescent : baseEnd_2819762 < baseStart_2819762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819766 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2819766 : Nat := 118140960795 + 2819766 * 2 ^ 59
def prefixEnd_2819766 : Nat := 4983230072969 + 3 ^ 40 * 2819766 * 2
def baseEnd_2819766 : Nat := 965263527470613257504759

theorem tailTrace_2819766 : CollatzResearch.WordTrace tailWord_2819766 prefixEnd_2819766 965263527470613257504759 := by
  unfold tailWord_2819766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6427832193904802158596947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68563543401651223025034101 6427832193904802158596947)
  ·
    refine ⟨9641748290857203237895421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6427832193904802158596947 9641748290857203237895421)
    ·
      refine ⟨3615655609071451214210783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9641748290857203237895421 3615655609071451214210783)
      ·
        refine ⟨5423483413607176821316175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615655609071451214210783 5423483413607176821316175)
        ·
          refine ⟨8135225120410765231974263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5423483413607176821316175 8135225120410765231974263)
          ·
            refine ⟨12202837680616147847961395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8135225120410765231974263 12202837680616147847961395)
            ·
              refine ⟨18304256520924221771942093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12202837680616147847961395 18304256520924221771942093)
              ·
                refine ⟨6864096195346583164478285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18304256520924221771942093 6864096195346583164478285)
                ·
                  refine ⟨2574036073254968686679357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6864096195346583164478285 2574036073254968686679357)
                  ·
                    refine ⟨965263527470613257504759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574036073254968686679357 965263527470613257504759)
                    ·
                      rfl

theorem cell22_2819766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2819766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819766 prefixEnd_2819766 := by exact prefixLift 2819766
  have htrace : WordTrace (prefixWord ++ tailWord_2819766) baseStart_2819766 baseEnd_2819766 := by
    simpa [prefixWord, tailWord_2819766, baseEnd_2819766] using wordTrace_append hprefix tailTrace_2819766
  have hstable : (prefixWord ++ tailWord_2819766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819766).length < 2 ^ (prefixWord ++ tailWord_2819766).sum := by decide
  have hdescent : baseEnd_2819766 < baseStart_2819766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819867 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 5, 3]
def baseStart_2819867 : Nat := 118140960795 + 2819867 * 2 ^ 59
def prefixEnd_2819867 : Nat := 4983230072969 + 3 ^ 40 * 2819867 * 2
def baseEnd_2819867 : Nat := 965298101834682660729449

theorem tailTrace_2819867 : CollatzResearch.WordTrace tailWord_2819867 prefixEnd_2819867 965298101834682660729449 := by
  unfold tailWord_2819867
  simp only [CollatzResearch.WordTrace]
  refine ⟨102848998875110928786977855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68565999250073952524651903 102848998875110928786977855)
  ·
    refine ⟨154273498312666393180466783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102848998875110928786977855 154273498312666393180466783)
    ·
      refine ⟨231410247468999589770700175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154273498312666393180466783 231410247468999589770700175)
      ·
        refine ⟨347115371203499384656050263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231410247468999589770700175 347115371203499384656050263)
        ·
          refine ⟨520673056805249076984075395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347115371203499384656050263 520673056805249076984075395)
          ·
            refine ⟨781009585207873615476113093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520673056805249076984075395 781009585207873615476113093)
            ·
              refine ⟨146439297226476302901771205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 781009585207873615476113093 146439297226476302901771205)
              ·
                refine ⟨27457368229964306794082101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146439297226476302901771205 27457368229964306794082101)
                ·
                  refine ⟨2574128271559153761945197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27457368229964306794082101 2574128271559153761945197)
                  ·
                    refine ⟨965298101834682660729449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574128271559153761945197 965298101834682660729449)
                    ·
                      rfl

theorem cell22_2819867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 3].length) (baseStart_2819867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819867 prefixEnd_2819867 := by exact prefixLift 2819867
  have htrace : WordTrace (prefixWord ++ tailWord_2819867) baseStart_2819867 baseEnd_2819867 := by
    simpa [prefixWord, tailWord_2819867, baseEnd_2819867] using wordTrace_append hprefix tailTrace_2819867
  have hstable : (prefixWord ++ tailWord_2819867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819867).length < 2 ^ (prefixWord ++ tailWord_2819867).sum := by decide
  have hdescent : baseEnd_2819867 < baseStart_2819867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819886 : List Nat := [4, 1, 3, 2, 2, 2, 1, 7]
def baseStart_2819886 : Nat := 118140960795 + 2819886 * 2 ^ 59
def prefixEnd_2819886 : Nat := 4983230072969 + 3 ^ 40 * 2819886 * 2
def baseEnd_2819886 : Nat := 107256067324774771611599

theorem tailTrace_2819886 : CollatzResearch.WordTrace tailWord_2819886 prefixEnd_2819886 107256067324774771611599 := by
  unfold tailWord_2819886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856211482755261878989939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68566461241361396687946341 12856211482755261878989939)
  ·
    refine ⟨19284317224132892818484909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12856211482755261878989939 19284317224132892818484909)
    ·
      refine ⟨7231618959049834806931841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19284317224132892818484909 7231618959049834806931841)
      ·
        refine ⟨5423714219287376105198881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7231618959049834806931841 5423714219287376105198881)
        ·
          refine ⟨4067785664465532078899161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5423714219287376105198881 4067785664465532078899161)
          ·
            refine ⟨3050839248349149059174371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067785664465532078899161 3050839248349149059174371)
            ·
              refine ⟨4576258872523723588761557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050839248349149059174371 4576258872523723588761557)
              ·
                refine ⟨107256067324774771611599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4576258872523723588761557 107256067324774771611599)
                ·
                  rfl

theorem cell22_2819886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_2819886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819886 prefixEnd_2819886 := by exact prefixLift 2819886
  have htrace : WordTrace (prefixWord ++ tailWord_2819886) baseStart_2819886 baseEnd_2819886 := by
    simpa [prefixWord, tailWord_2819886, baseEnd_2819886] using wordTrace_append hprefix tailTrace_2819886
  have hstable : (prefixWord ++ tailWord_2819886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819886).length < 2 ^ (prefixWord ++ tailWord_2819886).sum := by decide
  have hdescent : baseEnd_2819886 < baseStart_2819886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819901 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2819901 : Nat := 118140960795 + 2819901 * 2 ^ 59
def prefixEnd_2819901 : Nat := 4983230072969 + 3 ^ 40 * 2819901 * 2
def baseEnd_2819901 : Nat := 965309740729517905379345

theorem tailTrace_2819901 : CollatzResearch.WordTrace tailWord_2819901 prefixEnd_2819901 965309740729517905379345 := by
  unfold tailWord_2819901
  simp only [CollatzResearch.WordTrace]
  refine ⟨102850238956987752593715557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68566825971325168395810371 102850238956987752593715557)
  ·
    refine ⟨19284419804435203611321667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102850238956987752593715557 19284419804435203611321667)
    ·
      refine ⟨28926629706652805416982501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19284419804435203611321667 28926629706652805416982501)
      ·
        refine ⟨5423743069997401015684219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28926629706652805416982501 5423743069997401015684219)
        ·
          refine ⟨8135614604996101523526329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5423743069997401015684219 8135614604996101523526329)
          ·
            refine ⟨6101710953747076142644747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8135614604996101523526329 6101710953747076142644747)
            ·
              refine ⟨9152566430620614213967121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6101710953747076142644747 9152566430620614213967121)
              ·
                refine ⟨6864424822965460660475341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9152566430620614213967121 6864424822965460660475341)
                ·
                  refine ⟨2574159308612047747678253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6864424822965460660475341 2574159308612047747678253)
                  ·
                    refine ⟨965309740729517905379345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574159308612047747678253 965309740729517905379345)
                    ·
                      rfl

theorem cell22_2819901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2819901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819901 prefixEnd_2819901 := by exact prefixLift 2819901
  have htrace : WordTrace (prefixWord ++ tailWord_2819901) baseStart_2819901 baseEnd_2819901 := by
    simpa [prefixWord, tailWord_2819901, baseEnd_2819901] using wordTrace_append hprefix tailTrace_2819901
  have hstable : (prefixWord ++ tailWord_2819901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819901).length < 2 ^ (prefixWord ++ tailWord_2819901).sum := by decide
  have hdescent : baseEnd_2819901 < baseStart_2819901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819989 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2819989 : Nat := 118140960795 + 2819989 * 2 ^ 59
def prefixEnd_2819989 : Nat := 4983230072969 + 3 ^ 40 * 2819989 * 2
def baseEnd_2819989 : Nat := 965339864927915009179075

theorem tailTrace_2819989 : CollatzResearch.WordTrace tailWord_2819989 prefixEnd_2819989 965339864927915009179075 := by
  unfold tailWord_2819989
  simp only [CollatzResearch.WordTrace]
  refine ⟨102853448580668943622919021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68568965720445962415279347 102853448580668943622919021)
  ·
    refine ⟨38570043217750853858594633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102853448580668943622919021 38570043217750853858594633)
    ·
      refine ⟨28927532413313140393945975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38570043217750853858594633 28927532413313140393945975)
      ·
        refine ⟨43391298619969710590918963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28927532413313140393945975 43391298619969710590918963)
        ·
          refine ⟨65086947929954565886378445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43391298619969710590918963 65086947929954565886378445)
          ·
            refine ⟨24407605473732962207391917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65086947929954565886378445 24407605473732962207391917)
            ·
              refine ⟨9152852052649860827771969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24407605473732962207391917 9152852052649860827771969)
              ·
                refine ⟨6864639039487395620828977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9152852052649860827771969 6864639039487395620828977)
                ·
                  refine ⟨5148479279615546715621733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6864639039487395620828977 5148479279615546715621733)
                  ·
                    refine ⟨965339864927915009179075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148479279615546715621733 965339864927915009179075)
                    ·
                      rfl

theorem cell22_2819989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2819989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819989 prefixEnd_2819989 := by exact prefixLift 2819989
  have htrace : WordTrace (prefixWord ++ tailWord_2819989) baseStart_2819989 baseEnd_2819989 := by
    simpa [prefixWord, tailWord_2819989, baseEnd_2819989] using wordTrace_append hprefix tailTrace_2819989
  have hstable : (prefixWord ++ tailWord_2819989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819989).length < 2 ^ (prefixWord ++ tailWord_2819989).sum := by decide
  have hdescent : baseEnd_2819989 < baseStart_2819989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820004 : List Nat := [2, 3, 1, 2, 1, 4, 2, 7]
def baseStart_2820004 : Nat := 118140960795 + 2820004 * 2 ^ 59
def prefixEnd_2820004 : Nat := 4983230072969 + 3 ^ 40 * 2820004 * 2
def baseEnd_2820004 : Nat := 107260555526051107783781

theorem tailTrace_2820004 : CollatzResearch.WordTrace tailWord_2820004 prefixEnd_2820004 107260555526051107783781 := by
  unfold tailWord_2820004
  simp only [CollatzResearch.WordTrace]
  refine ⟨51426997837807300592357533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68569330450409734123143377 51426997837807300592357533)
  ·
    refine ⟨19285124189177737722134075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51426997837807300592357533 19285124189177737722134075)
    ·
      refine ⟨28927686283766606583201113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19285124189177737722134075 28927686283766606583201113)
      ·
        refine ⟨21695764712824954937400835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28927686283766606583201113 21695764712824954937400835)
        ·
          refine ⟨32543647069237432406101253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21695764712824954937400835 32543647069237432406101253)
          ·
            refine ⟨6101933825482018576143985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32543647069237432406101253 6101933825482018576143985)
            ·
              refine ⟨4576450369111513932107989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6101933825482018576143985 4576450369111513932107989)
              ·
                refine ⟨107260555526051107783781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4576450369111513932107989 107260555526051107783781)
                ·
                  rfl

theorem cell22_2820004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 7].length) (baseStart_2820004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820004 prefixEnd_2820004 := by exact prefixLift 2820004
  have htrace : WordTrace (prefixWord ++ tailWord_2820004) baseStart_2820004 baseEnd_2820004 := by
    simpa [prefixWord, tailWord_2820004, baseEnd_2820004] using wordTrace_append hprefix tailTrace_2820004
  have hstable : (prefixWord ++ tailWord_2820004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820004).length < 2 ^ (prefixWord ++ tailWord_2820004).sum := by decide
  have hdescent : baseEnd_2820004 < baseStart_2820004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820019 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 5, 3]
def baseStart_2820019 : Nat := 118140960795 + 2820019 * 2 ^ 59
def prefixEnd_2820019 : Nat := 4983230072969 + 3 ^ 40 * 2820019 * 2
def baseEnd_2820019 : Nat := 965350134541004930928983

theorem tailTrace_2820019 : CollatzResearch.WordTrace tailWord_2820019 prefixEnd_2820019 965350134541004930928983 := by
  unfold tailWord_2820019
  simp only [CollatzResearch.WordTrace]
  refine ⟨102854542770560258746511111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68569695180373505831007407 102854542770560258746511111)
  ·
    refine ⟨154281814155840388119766667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102854542770560258746511111 154281814155840388119766667)
    ·
      refine ⟨231422721233760582179650001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154281814155840388119766667 231422721233760582179650001)
      ·
        refine ⟨173567040925320436634737501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231422721233760582179650001 173567040925320436634737501)
        ·
          refine ⟨65087640346995163738026563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173567040925320436634737501 65087640346995163738026563)
          ·
            refine ⟨97631460520492745607039845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65087640346995163738026563 97631460520492745607039845)
            ·
              refine ⟨18305898847592389801319971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97631460520492745607039845 18305898847592389801319971)
              ·
                refine ⟨27458848271388584701979957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18305898847592389801319971 27458848271388584701979957)
                ·
                  refine ⟨2574267025442679815810621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27458848271388584701979957 2574267025442679815810621)
                  ·
                    refine ⟨965350134541004930928983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574267025442679815810621 965350134541004930928983)
                    ·
                      rfl

theorem cell22_2820019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 3].length) (baseStart_2820019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820019 prefixEnd_2820019 := by exact prefixLift 2820019
  have htrace : WordTrace (prefixWord ++ tailWord_2820019) baseStart_2820019 baseEnd_2820019 := by
    simpa [prefixWord, tailWord_2820019, baseEnd_2820019] using wordTrace_append hprefix tailTrace_2820019
  have hstable : (prefixWord ++ tailWord_2820019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820019).length < 2 ^ (prefixWord ++ tailWord_2820019).sum := by decide
  have hdescent : baseEnd_2820019 < baseStart_2820019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820079 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 3, 4]
def baseStart_2820079 : Nat := 118140960795 + 2820079 * 2 ^ 59
def prefixEnd_2820079 : Nat := 4983230072969 + 3 ^ 40 * 2820079 * 2
def baseEnd_2820079 : Nat := 965370673767184774428799

theorem tailTrace_2820079 : CollatzResearch.WordTrace tailWord_2820079 prefixEnd_2820079 965370673767184774428799 := by
  unfold tailWord_2820079
  simp only [CollatzResearch.WordTrace]
  refine ⟨102856731150342888993695291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68571154100228592662463527 102856731150342888993695291)
  ·
    refine ⟨154285096725514333490542937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102856731150342888993695291 154285096725514333490542937)
    ·
      refine ⟨115713822544135750117907203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154285096725514333490542937 115713822544135750117907203)
      ·
        refine ⟨173570733816203625176860805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115713822544135750117907203 173570733816203625176860805)
        ·
          refine ⟨32544512590538179720661401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173570733816203625176860805 32544512590538179720661401)
          ·
            refine ⟨24408384442903634790496051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32544512590538179720661401 24408384442903634790496051)
            ·
              refine ⟨36612576664355452185744077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24408384442903634790496051 36612576664355452185744077)
              ·
                refine ⟨13729716249133294569654029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36612576664355452185744077 13729716249133294569654029)
                ·
                  refine ⟨5148643593424985463620261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13729716249133294569654029 5148643593424985463620261)
                  ·
                    refine ⟨965370673767184774428799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148643593424985463620261 965370673767184774428799)
                    ·
                      rfl

theorem cell22_2820079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_2820079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820079 prefixEnd_2820079 := by exact prefixLift 2820079
  have htrace : WordTrace (prefixWord ++ tailWord_2820079) baseStart_2820079 baseEnd_2820079 := by
    simpa [prefixWord, tailWord_2820079, baseEnd_2820079] using wordTrace_append hprefix tailTrace_2820079
  have hstable : (prefixWord ++ tailWord_2820079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820079).length < 2 ^ (prefixWord ++ tailWord_2820079).sum := by decide
  have hdescent : baseEnd_2820079 < baseStart_2820079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820100 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 5]
def baseStart_2820100 : Nat := 118140960795 + 2820100 * 2 ^ 59
def prefixEnd_2820100 : Nat := 4983230072969 + 3 ^ 40 * 2820100 * 2
def baseEnd_2820100 : Nat := 321792620832115906551245

theorem tailTrace_2820100 : CollatzResearch.WordTrace tailWord_2820100 prefixEnd_2820100 321792620832115906551245 := by
  unfold tailWord_2820100
  simp only [CollatzResearch.WordTrace]
  refine ⟨51428748541633404790104877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68571664722177873053473169 51428748541633404790104877)
  ·
    refine ⟨19285780703112526796289329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51428748541633404790104877 19285780703112526796289329)
    ·
      refine ⟨14464335527334395097216997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19285780703112526796289329 14464335527334395097216997)
      ·
        refine ⟨2712062911375199080728187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14464335527334395097216997 2712062911375199080728187)
        ·
          refine ⟨4068094367062798621092281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712062911375199080728187 4068094367062798621092281)
          ·
            refine ⟨3051070775297098965819211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4068094367062798621092281 3051070775297098965819211)
            ·
              refine ⟨4576606162945648448728817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051070775297098965819211 4576606162945648448728817)
              ·
                refine ⟨3432454622209236336546613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4576606162945648448728817 3432454622209236336546613)
                ·
                  refine ⟨321792620832115906551245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432454622209236336546613 321792620832115906551245)
                  ·
                    rfl

theorem cell22_2820100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_2820100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820100 prefixEnd_2820100 := by exact prefixLift 2820100
  have htrace : WordTrace (prefixWord ++ tailWord_2820100) baseStart_2820100 baseEnd_2820100 := by
    simpa [prefixWord, tailWord_2820100, baseEnd_2820100] using wordTrace_append hprefix tailTrace_2820100
  have hstable : (prefixWord ++ tailWord_2820100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820100).length < 2 ^ (prefixWord ++ tailWord_2820100).sum := by decide
  have hdescent : baseEnd_2820100 < baseStart_2820100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820169 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_2820169 : Nat := 118140960795 + 2820169 * 2 ^ 59
def prefixEnd_2820169 : Nat := 4983230072969 + 3 ^ 40 * 2820169 * 2
def baseEnd_2820169 : Nat := 965401482606454539678523

theorem tailTrace_2820169 : CollatzResearch.WordTrace tailWord_2820169 prefixEnd_2820169 965401482606454539678523 := by
  unfold tailWord_2820169
  simp only [CollatzResearch.WordTrace]
  refine ⟨102860013720016834364471561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68573342480011222909647707 102860013720016834364471561)
  ·
    refine ⟨77145010290012625773353671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102860013720016834364471561 77145010290012625773353671)
    ·
      refine ⟨115717515435018938660030507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77145010290012625773353671 115717515435018938660030507)
      ·
        refine ⟨173576273152528407990045761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115717515435018938660030507 173576273152528407990045761)
        ·
          refine ⟨130182204864396305992534321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173576273152528407990045761 130182204864396305992534321)
          ·
            refine ⟨97636653648297229494400741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130182204864396305992534321 97636653648297229494400741)
            ·
              refine ⟨18306872559055730530200139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97636653648297229494400741 18306872559055730530200139)
              ·
                refine ⟨27460308838583595795300209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18306872559055730530200139 27460308838583595795300209)
                ·
                  refine ⟨20595231628937696846475157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27460308838583595795300209 20595231628937696846475157)
                  ·
                    refine ⟨965401482606454539678523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20595231628937696846475157 965401482606454539678523)
                    ·
                      rfl

theorem cell22_2820169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_2820169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820169 prefixEnd_2820169 := by exact prefixLift 2820169
  have htrace : WordTrace (prefixWord ++ tailWord_2820169) baseStart_2820169 baseEnd_2820169 := by
    simpa [prefixWord, tailWord_2820169, baseEnd_2820169] using wordTrace_append hprefix tailTrace_2820169
  have hstable : (prefixWord ++ tailWord_2820169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820169).length < 2 ^ (prefixWord ++ tailWord_2820169).sum := by decide
  have hdescent : baseEnd_2820169 < baseStart_2820169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820205 : List Nat := [1, 5, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_2820205 : Nat := 118140960795 + 2820205 * 2 ^ 59
def prefixEnd_2820205 : Nat := 4983230072969 + 3 ^ 40 * 2820205 * 2
def baseEnd_2820205 : Nat := 965413806142162445778413

theorem tailTrace_2820205 : CollatzResearch.WordTrace tailWord_2820205 prefixEnd_2820205 965413806142162445778413 := by
  unfold tailWord_2820205
  simp only [CollatzResearch.WordTrace]
  refine ⟨102861326747886412512782069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68574217831924275008521379 102861326747886412512782069)
  ·
    refine ⟨9643249382614351173073319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102861326747886412512782069 9643249382614351173073319)
    ·
      refine ⟨14464874073921526759609979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9643249382614351173073319 14464874073921526759609979)
      ·
        refine ⟨21697311110882290139414969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14464874073921526759609979 21697311110882290139414969)
        ·
          refine ⟨16272983333161717604561227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21697311110882290139414969 16272983333161717604561227)
          ·
            refine ⟨24409474999742576406841841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16272983333161717604561227 24409474999742576406841841)
            ·
              refine ⟨18307106249806932305131381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24409474999742576406841841 18307106249806932305131381)
              ·
                refine ⟨1716291210919399903606067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18307106249806932305131381 1716291210919399903606067)
                ·
                  refine ⟨2574436816379099855409101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716291210919399903606067 2574436816379099855409101)
                  ·
                    refine ⟨965413806142162445778413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574436816379099855409101 965413806142162445778413)
                    ·
                      rfl

theorem cell22_2820205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_2820205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820205 prefixEnd_2820205 := by exact prefixLift 2820205
  have htrace : WordTrace (prefixWord ++ tailWord_2820205) baseStart_2820205 baseEnd_2820205 := by
    simpa [prefixWord, tailWord_2820205, baseEnd_2820205] using wordTrace_append hprefix tailTrace_2820205
  have hstable : (prefixWord ++ tailWord_2820205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820205).length < 2 ^ (prefixWord ++ tailWord_2820205).sum := by decide
  have hdescent : baseEnd_2820205 < baseStart_2820205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820231 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 3, 4]
def baseStart_2820231 : Nat := 118140960795 + 2820231 * 2 ^ 59
def prefixEnd_2820231 : Nat := 4983230072969 + 3 ^ 40 * 2820231 * 2
def baseEnd_2820231 : Nat := 965422706473507044628333

theorem tailTrace_2820231 : CollatzResearch.WordTrace tailWord_2820231 prefixEnd_2820231 965422706473507044628333 := by
  unfold tailWord_2820231
  simp only [CollatzResearch.WordTrace]
  refine ⟨102862275045792218953228547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68574850030528145968819031 102862275045792218953228547)
  ·
    refine ⟨154293412568688328429842821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102862275045792218953228547 154293412568688328429842821)
    ·
      refine ⟨28930014856629061580595529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154293412568688328429842821 28930014856629061580595529)
      ·
        refine ⟨21697511142471796185446647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28930014856629061580595529 21697511142471796185446647)
        ·
          refine ⟨32546266713707694278169971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21697511142471796185446647 32546266713707694278169971)
          ·
            refine ⟨48819400070561541417254957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32546266713707694278169971 48819400070561541417254957)
            ·
              refine ⟨18307275026460578031470609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48819400070561541417254957 18307275026460578031470609)
              ·
                refine ⟨13730456269845433523602957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18307275026460578031470609 13730456269845433523602957)
                ·
                  refine ⟨5148921101192037571351109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13730456269845433523602957 5148921101192037571351109)
                  ·
                    refine ⟨965422706473507044628333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5148921101192037571351109 965422706473507044628333)
                    ·
                      rfl

theorem cell22_2820231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_2820231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820231 prefixEnd_2820231 := by exact prefixLift 2820231
  have htrace : WordTrace (prefixWord ++ tailWord_2820231) baseStart_2820231 baseEnd_2820231 := by
    simpa [prefixWord, tailWord_2820231, baseEnd_2820231] using wordTrace_append hprefix tailTrace_2820231
  have hstable : (prefixWord ++ tailWord_2820231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820231).length < 2 ^ (prefixWord ++ tailWord_2820231).sum := by decide
  have hdescent : baseEnd_2820231 < baseStart_2820231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820261 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_2820261 : Nat := 118140960795 + 2820261 * 2 ^ 59
def prefixEnd_2820261 : Nat := 4983230072969 + 3 ^ 40 * 2820261 * 2
def baseEnd_2820261 : Nat := 965432976086596966378241

theorem tailTrace_2820261 : CollatzResearch.WordTrace tailWord_2820261 prefixEnd_2820261 965432976086596966378241 := by
  unfold tailWord_2820261
  simp only [CollatzResearch.WordTrace]
  refine ⟨102863369235683534076820637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68575579490455689384547091 102863369235683534076820637)
  ·
    refine ⟨38573763463381325278807739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102863369235683534076820637 38573763463381325278807739)
    ·
      refine ⟨57860645195071987918211609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38573763463381325278807739 57860645195071987918211609)
      ·
        refine ⟨43395483896303990938658707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57860645195071987918211609 43395483896303990938658707)
        ·
          refine ⟨65093225844455986407988061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43395483896303990938658707 65093225844455986407988061)
          ·
            refine ⟨24409959691670994902995523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65093225844455986407988061 24409959691670994902995523)
            ·
              refine ⟨36614939537506492354493285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24409959691670994902995523 36614939537506492354493285)
              ·
                refine ⟨6865301163282467316467491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36614939537506492354493285 6865301163282467316467491)
                ·
                  refine ⟨10297951744923700974701237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6865301163282467316467491 10297951744923700974701237)
                  ·
                    refine ⟨965432976086596966378241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10297951744923700974701237 965432976086596966378241)
                    ·
                      rfl

theorem cell22_2820261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_2820261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820261 prefixEnd_2820261 := by exact prefixLift 2820261
  have htrace : WordTrace (prefixWord ++ tailWord_2820261) baseStart_2820261 baseEnd_2820261 := by
    simpa [prefixWord, tailWord_2820261, baseEnd_2820261] using wordTrace_append hprefix tailTrace_2820261
  have hstable : (prefixWord ++ tailWord_2820261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820261).length < 2 ^ (prefixWord ++ tailWord_2820261).sum := by decide
  have hdescent : baseEnd_2820261 < baseStart_2820261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820310 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2820310 : Nat := 118140960795 + 2820310 * 2 ^ 59
def prefixEnd_2820310 : Nat := 4983230072969 + 3 ^ 40 * 2820310 * 2
def baseEnd_2820310 : Nat := 965449749787977171903091

theorem tailTrace_2820310 : CollatzResearch.WordTrace tailWord_2820310 prefixEnd_2820310 965449749787977171903091 := by
  unfold tailWord_2820310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6429072275781625965334649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68576770941670676963569589 6429072275781625965334649)
  ·
    refine ⟨4821804206836219474000987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6429072275781625965334649 4821804206836219474000987)
    ·
      refine ⟨7232706310254329211001481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4821804206836219474000987 7232706310254329211001481)
      ·
        refine ⟨5424529732690746908251111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7232706310254329211001481 5424529732690746908251111)
        ·
          refine ⟨8136794599036120362376667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5424529732690746908251111 8136794599036120362376667)
          ·
            refine ⟨12205191898554180543565001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8136794599036120362376667 12205191898554180543565001)
            ·
              refine ⟨9153893923915635407673751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12205191898554180543565001 9153893923915635407673751)
              ·
                refine ⟨13730840885873453111510627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9153893923915635407673751 13730840885873453111510627)
                ·
                  refine ⟨20596261328810179667265941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13730840885873453111510627 20596261328810179667265941)
                  ·
                    refine ⟨965449749787977171903091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20596261328810179667265941 965449749787977171903091)
                    ·
                      rfl

theorem cell22_2820310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2820310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820310 prefixEnd_2820310 := by exact prefixLift 2820310
  have htrace : WordTrace (prefixWord ++ tailWord_2820310) baseStart_2820310 baseEnd_2820310 := by
    simpa [prefixWord, tailWord_2820310, baseEnd_2820310] using wordTrace_append hprefix tailTrace_2820310
  have hstable : (prefixWord ++ tailWord_2820310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820310).length < 2 ^ (prefixWord ++ tailWord_2820310).sum := by decide
  have hdescent : baseEnd_2820310 < baseStart_2820310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820351 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 1, 7]
def baseStart_2820351 : Nat := 118140960795 + 2820351 * 2 ^ 59
def prefixEnd_2820351 : Nat := 4983230072969 + 3 ^ 40 * 2820351 * 2
def baseEnd_2820351 : Nat := 965463784925866731627965

theorem tailTrace_2820351 : CollatzResearch.WordTrace tailWord_2820351 prefixEnd_2820351 965463784925866731627965 := by
  unfold tailWord_2820351
  simp only [CollatzResearch.WordTrace]
  refine ⟨102866651805357479447596907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68577767870238319631731271 102866651805357479447596907)
  ·
    refine ⟨154299977708036219171395361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102866651805357479447596907 154299977708036219171395361)
    ·
      refine ⟨115724983281027164378546521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154299977708036219171395361 115724983281027164378546521)
      ·
        refine ⟨86793737460770373283909891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115724983281027164378546521 86793737460770373283909891)
        ·
          refine ⟨130190606191155559925864837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86793737460770373283909891 130190606191155559925864837)
          ·
            refine ⟨24410738660841667486099657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130190606191155559925864837 24410738660841667486099657)
            ·
              refine ⟨18308053995631250614574743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24410738660841667486099657 18308053995631250614574743)
              ·
                refine ⟨27462080993446875921862115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18308053995631250614574743 27462080993446875921862115)
                ·
                  refine ⟨41193121490170313882793173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27462080993446875921862115 41193121490170313882793173)
                  ·
                    refine ⟨965463784925866731627965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41193121490170313882793173 965463784925866731627965)
                    ·
                      rfl

theorem cell22_2820351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_2820351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820351 prefixEnd_2820351 := by exact prefixLift 2820351
  have htrace : WordTrace (prefixWord ++ tailWord_2820351) baseStart_2820351 baseEnd_2820351 := by
    simpa [prefixWord, tailWord_2820351, baseEnd_2820351] using wordTrace_append hprefix tailTrace_2820351
  have hstable : (prefixWord ++ tailWord_2820351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820351).length < 2 ^ (prefixWord ++ tailWord_2820351).sum := by decide
  have hdescent : baseEnd_2820351 < baseStart_2820351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820353 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 5]
def baseStart_2820353 : Nat := 118140960795 + 2820353 * 2 ^ 59
def prefixEnd_2820353 : Nat := 4983230072969 + 3 ^ 40 * 2820353 * 2
def baseEnd_2820353 : Nat := 321821489855579797692653

theorem tailTrace_2820353 : CollatzResearch.WordTrace tailWord_2820353 prefixEnd_2820353 321821489855579797692653 := by
  unfold tailWord_2820353
  simp only [CollatzResearch.WordTrace]
  refine ⟨102866724751350233789169713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68577816500900155859446475 102866724751350233789169713)
  ·
    refine ⟨77150043563512675341877285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102866724751350233789169713 77150043563512675341877285)
    ·
      refine ⟨14465633168158626626601991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77150043563512675341877285 14465633168158626626601991)
      ·
        refine ⟨21698449752237939939902987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14465633168158626626601991 21698449752237939939902987)
        ·
          refine ⟨32547674628356909909854481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21698449752237939939902987 32547674628356909909854481)
          ·
            refine ⟨24410755971267682432390861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32547674628356909909854481 24410755971267682432390861)
            ·
              refine ⟨9154033489225380912146573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24410755971267682432390861 9154033489225380912146573)
              ·
                refine ⟨3432762558459517842054965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9154033489225380912146573 3432762558459517842054965)
                ·
                  refine ⟨321821489855579797692653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3432762558459517842054965 321821489855579797692653)
                  ·
                    rfl

theorem cell22_2820353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_2820353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820353 prefixEnd_2820353 := by exact prefixLift 2820353
  have htrace : WordTrace (prefixWord ++ tailWord_2820353) baseStart_2820353 baseEnd_2820353 := by
    simpa [prefixWord, tailWord_2820353, baseEnd_2820353] using wordTrace_append hprefix tailTrace_2820353
  have hstable : (prefixWord ++ tailWord_2820353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820353).length < 2 ^ (prefixWord ++ tailWord_2820353).sum := by decide
  have hdescent : baseEnd_2820353 < baseStart_2820353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820428 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_2820428 : Nat := 118140960795 + 2820428 * 2 ^ 59
def prefixEnd_2820428 : Nat := 4983230072969 + 3 ^ 40 * 2820428 * 2
def baseEnd_2820428 : Nat := 965490143599464197452729

theorem tailTrace_2820428 : CollatzResearch.WordTrace tailWord_2820428 prefixEnd_2820428 965490143599464197452729 := by
  unfold tailWord_2820428
  simp only [CollatzResearch.WordTrace]
  refine ⟨51434730113039260799074969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68579640150719014398766625 51434730113039260799074969)
  ·
    refine ⟨38576047584779445599306227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51434730113039260799074969 38576047584779445599306227)
    ·
      refine ⟨57864071377169168398959341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38576047584779445599306227 57864071377169168398959341)
      ·
        refine ⟨21699026766438438149609753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57864071377169168398959341 21699026766438438149609753)
        ·
          refine ⟨16274270074828828612207315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21699026766438438149609753 16274270074828828612207315)
          ·
            refine ⟨24411405112243242918310973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16274270074828828612207315 24411405112243242918310973)
            ·
              refine ⟨9154276917091216094366615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24411405112243242918310973 9154276917091216094366615)
              ·
                refine ⟨13731415375636824141549923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154276917091216094366615 13731415375636824141549923)
                ·
                  refine ⟨20597123063455236212324885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13731415375636824141549923 20597123063455236212324885)
                  ·
                    refine ⟨965490143599464197452729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20597123063455236212324885 965490143599464197452729)
                    ·
                      rfl

theorem cell22_2820428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_2820428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820428 prefixEnd_2820428 := by exact prefixLift 2820428
  have htrace : WordTrace (prefixWord ++ tailWord_2820428) baseStart_2820428 baseEnd_2820428 := by
    simpa [prefixWord, tailWord_2820428, baseEnd_2820428] using wordTrace_append hprefix tailTrace_2820428
  have hstable : (prefixWord ++ tailWord_2820428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820428).length < 2 ^ (prefixWord ++ tailWord_2820428).sum := by decide
  have hdescent : baseEnd_2820428 < baseStart_2820428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820475 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 3, 3]
def baseStart_2820475 : Nat := 118140960795 + 2820475 * 2 ^ 59
def prefixEnd_2820475 : Nat := 4983230072969 + 3 ^ 40 * 2820475 * 2
def baseEnd_2820475 : Nat := 965506232659971741527585

theorem tailTrace_2820475 : CollatzResearch.WordTrace tailWord_2820475 prefixEnd_2820475 965506232659971741527585 := by
  unfold tailWord_2820475
  simp only [CollatzResearch.WordTrace]
  refine ⟨102871174456908248625110879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68580782971272165750073919 102871174456908248625110879)
  ·
    refine ⟨154306761685362372937666319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102871174456908248625110879 154306761685362372937666319)
    ·
      refine ⟨231460142528043559406499479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154306761685362372937666319 231460142528043559406499479)
      ·
        refine ⟨347190213792065339109749219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231460142528043559406499479 347190213792065339109749219)
        ·
          refine ⟨520785320688098008664623829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347190213792065339109749219 520785320688098008664623829)
          ·
            refine ⟨12205905953627297078077121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 520785320688098008664623829 12205905953627297078077121)
            ·
              refine ⟨9154429465220472808557841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12205905953627297078077121 9154429465220472808557841)
              ·
                refine ⟨6865822098915354606418381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9154429465220472808557841 6865822098915354606418381)
                ·
                  refine ⟨2574683287093257977406893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6865822098915354606418381 2574683287093257977406893)
                  ·
                    refine ⟨965506232659971741527585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574683287093257977406893 965506232659971741527585)
                    ·
                      rfl

theorem cell22_2820475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3, 3].length) (baseStart_2820475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820475 prefixEnd_2820475 := by exact prefixLift 2820475
  have htrace : WordTrace (prefixWord ++ tailWord_2820475) baseStart_2820475 baseEnd_2820475 := by
    simpa [prefixWord, tailWord_2820475, baseEnd_2820475] using wordTrace_append hprefix tailTrace_2820475
  have hstable : (prefixWord ++ tailWord_2820475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820475).length < 2 ^ (prefixWord ++ tailWord_2820475).sum := by decide
  have hdescent : baseEnd_2820475 < baseStart_2820475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820488 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 9]
def baseStart_2820488 : Nat := 118140960795 + 2820488 * 2 ^ 59
def prefixEnd_2820488 : Nat := 4983230072969 + 3 ^ 40 * 2820488 * 2
def baseEnd_2820488 : Nat := 321836894275214680317515

theorem tailTrace_2820488 : CollatzResearch.WordTrace tailWord_2820488 prefixEnd_2820488 321836894275214680317515 := by
  unfold tailWord_2820488
  simp only [CollatzResearch.WordTrace]
  refine ⟨51435824302930575922667059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68581099070574101230222745 51435824302930575922667059)
  ·
    refine ⟨77153736454395863884000589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51435824302930575922667059 77153736454395863884000589)
    ·
      refine ⟨28932651170398448956500221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77153736454395863884000589 28932651170398448956500221)
      ·
        refine ⟨10849744188899418358687583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28932651170398448956500221 10849744188899418358687583)
        ·
          refine ⟨16274616283349127538031375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10849744188899418358687583 16274616283349127538031375)
          ·
            refine ⟨24411924425023691307047063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16274616283349127538031375 24411924425023691307047063)
            ·
              refine ⟨36617886637535536960570595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24411924425023691307047063 36617886637535536960570595)
              ·
                refine ⟨54926829956303305440855893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36617886637535536960570595 54926829956303305440855893)
                ·
                  refine ⟨321836894275214680317515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54926829956303305440855893 321836894275214680317515)
                  ·
                    rfl

theorem cell22_2820488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_2820488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820488 prefixEnd_2820488 := by exact prefixLift 2820488
  have htrace : WordTrace (prefixWord ++ tailWord_2820488) baseStart_2820488 baseEnd_2820488 := by
    simpa [prefixWord, tailWord_2820488, baseEnd_2820488] using wordTrace_append hprefix tailTrace_2820488
  have hstable : (prefixWord ++ tailWord_2820488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820488).length < 2 ^ (prefixWord ++ tailWord_2820488).sum := by decide
  have hdescent : baseEnd_2820488 < baseStart_2820488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820503 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 4, 5]
def baseStart_2820503 : Nat := 118140960795 + 2820503 * 2 ^ 59
def prefixEnd_2820503 : Nat := 4983230072969 + 3 ^ 40 * 2820503 * 2
def baseEnd_2820503 : Nat := 965515817632189001827499

theorem tailTrace_2820503 : CollatzResearch.WordTrace tailWord_2820503 prefixEnd_2820503 965515817632189001827499 := by
  unfold tailWord_2820503
  simp only [CollatzResearch.WordTrace]
  refine ⟨102872195700806809407130163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68581463800537872938086775 102872195700806809407130163)
  ·
    refine ⟨154308293551210214110695245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102872195700806809407130163 154308293551210214110695245)
    ·
      refine ⟨57865610081703830291510717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154308293551210214110695245 57865610081703830291510717)
      ·
        refine ⟨21699603780638936359316519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57865610081703830291510717 21699603780638936359316519)
        ·
          refine ⟨32549405670958404538974779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21699603780638936359316519 32549405670958404538974779)
          ·
            refine ⟨48824108506437606808462169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32549405670958404538974779 48824108506437606808462169)
            ·
              refine ⟨36618081379828205106346627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48824108506437606808462169 36618081379828205106346627)
              ·
                refine ⟨54927122069742307659519941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36618081379828205106346627 54927122069742307659519941)
                ·
                  refine ⟨10298835388076682686159989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54927122069742307659519941 10298835388076682686159989)
                  ·
                    refine ⟨965515817632189001827499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10298835388076682686159989 965515817632189001827499)
                    ·
                      rfl

theorem cell22_2820503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_2820503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820503 prefixEnd_2820503 := by exact prefixLift 2820503
  have htrace : WordTrace (prefixWord ++ tailWord_2820503) baseStart_2820503 baseEnd_2820503 := by
    simpa [prefixWord, tailWord_2820503, baseEnd_2820503] using wordTrace_append hprefix tailTrace_2820503
  have hstable : (prefixWord ++ tailWord_2820503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820503).length < 2 ^ (prefixWord ++ tailWord_2820503).sum := by decide
  have hdescent : baseEnd_2820503 < baseStart_2820503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820509 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2820509 : Nat := 118140960795 + 2820509 * 2 ^ 59
def prefixEnd_2820509 : Nat := 4983230072969 + 3 ^ 40 * 2820509 * 2
def baseEnd_2820509 : Nat := 965517871554806986177481

theorem tailTrace_2820509 : CollatzResearch.WordTrace tailWord_2820509 prefixEnd_2820509 965517871554806986177481 := by
  unfold tailWord_2820509
  simp only [CollatzResearch.WordTrace]
  refine ⟨102872414538785072431848581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68581609692523381621232387 102872414538785072431848581)
  ·
    refine ⟨19288577726022201080971609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102872414538785072431848581 19288577726022201080971609)
    ·
      refine ⟨14466433294516650810728707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19288577726022201080971609 14466433294516650810728707)
      ·
        refine ⟨21699649941774976216093061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14466433294516650810728707 21699649941774976216093061)
        ·
          refine ⟨4068684364082808040517449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21699649941774976216093061 4068684364082808040517449)
          ·
            refine ⟨3051513273062106030388087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4068684364082808040517449 3051513273062106030388087)
            ·
              refine ⟨4577269909593159045582131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051513273062106030388087 4577269909593159045582131)
              ·
                refine ⟨6865904864389738568373197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577269909593159045582131 6865904864389738568373197)
                ·
                  refine ⟨2574714324146151963139949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6865904864389738568373197 2574714324146151963139949)
                  ·
                    refine ⟨965517871554806986177481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574714324146151963139949 965517871554806986177481)
                    ·
                      rfl

theorem cell22_2820509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2820509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820509 prefixEnd_2820509 := by exact prefixLift 2820509
  have htrace : WordTrace (prefixWord ++ tailWord_2820509) baseStart_2820509 baseEnd_2820509 := by
    simpa [prefixWord, tailWord_2820509, baseEnd_2820509] using wordTrace_append hprefix tailTrace_2820509
  have hstable : (prefixWord ++ tailWord_2820509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820509).length < 2 ^ (prefixWord ++ tailWord_2820509).sum := by decide
  have hdescent : baseEnd_2820509 < baseStart_2820509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820535 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 3, 4]
def baseStart_2820535 : Nat := 118140960795 + 2820535 * 2 ^ 59
def prefixEnd_2820535 : Nat := 4983230072969 + 3 ^ 40 * 2820535 * 2
def baseEnd_2820535 : Nat := 965526771886151585027401

theorem tailTrace_2820535 : CollatzResearch.WordTrace tailWord_2820535 prefixEnd_2820535 965526771886151585027401 := by
  unfold tailWord_2820535
  simp only [CollatzResearch.WordTrace]
  refine ⟨102873362836690878872295059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68582241891127252581530039 102873362836690878872295059)
  ·
    refine ⟨154310044255036318308442589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102873362836690878872295059 154310044255036318308442589)
    ·
      refine ⟨57866266595638619365665971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154310044255036318308442589 57866266595638619365665971)
      ·
        refine ⟨86799399893457929048498957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57866266595638619365665971 86799399893457929048498957)
        ·
          refine ⟨32549774960046723393187109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86799399893457929048498957 32549774960046723393187109)
          ·
            refine ⟨6103082805008760636222583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32549774960046723393187109 6103082805008760636222583)
            ·
              refine ⟨9154624207513140954333875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103082805008760636222583 9154624207513140954333875)
              ·
                refine ⟨13731936311269711431500813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154624207513140954333875 13731936311269711431500813)
                ·
                  refine ⟨5149476116726141786812805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13731936311269711431500813 5149476116726141786812805)
                  ·
                    refine ⟨965526771886151585027401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149476116726141786812805 965526771886151585027401)
                    ·
                      rfl

theorem cell22_2820535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_2820535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820535 prefixEnd_2820535 := by exact prefixLift 2820535
  have htrace : WordTrace (prefixWord ++ tailWord_2820535) baseStart_2820535 baseEnd_2820535 := by
    simpa [prefixWord, tailWord_2820535, baseEnd_2820535] using wordTrace_append hprefix tailTrace_2820535
  have hstable : (prefixWord ++ tailWord_2820535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820535).length < 2 ^ (prefixWord ++ tailWord_2820535).sum := by decide
  have hdescent : baseEnd_2820535 < baseStart_2820535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820595 : List Nat := [1, 1, 1, 2, 2, 2, 7, 6]
def baseStart_2820595 : Nat := 118140960795 + 2820595 * 2 ^ 59
def prefixEnd_2820595 : Nat := 4983230072969 + 3 ^ 40 * 2820595 * 2
def baseEnd_2820595 : Nat := 107283034568036825391913

theorem tailTrace_2820595 : CollatzResearch.WordTrace tailWord_2820595 prefixEnd_2820595 107283034568036825391913 := by
  unfold tailWord_2820595
  simp only [CollatzResearch.WordTrace]
  refine ⟨102875551216473509119479239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68583700810982339412986159 102875551216473509119479239)
  ·
    refine ⟨154313326824710263679218859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102875551216473509119479239 154313326824710263679218859)
    ·
      refine ⟨231469990237065395518828289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154313326824710263679218859 231469990237065395518828289)
      ·
        refine ⟨173602492677799046639121217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231469990237065395518828289 173602492677799046639121217)
        ·
          refine ⟨130201869508349284979340913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173602492677799046639121217 130201869508349284979340913)
          ·
            refine ⟨97651402131261963734505685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130201869508349284979340913 97651402131261963734505685)
            ·
              refine ⟨2288704737451452275027477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 97651402131261963734505685 2288704737451452275027477)
              ·
                refine ⟨107283034568036825391913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2288704737451452275027477 107283034568036825391913)
                ·
                  rfl

theorem cell22_2820595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 6].length) (baseStart_2820595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820595 prefixEnd_2820595 := by exact prefixLift 2820595
  have htrace : WordTrace (prefixWord ++ tailWord_2820595) baseStart_2820595 baseEnd_2820595 := by
    simpa [prefixWord, tailWord_2820595, baseEnd_2820595] using wordTrace_append hprefix tailTrace_2820595
  have hstable : (prefixWord ++ tailWord_2820595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820595).length < 2 ^ (prefixWord ++ tailWord_2820595).sum := by decide
  have hdescent : baseEnd_2820595 < baseStart_2820595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820627 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 3, 3]
def baseStart_2820627 : Nat := 118140960795 + 2820627 * 2 ^ 59
def prefixEnd_2820627 : Nat := 4983230072969 + 3 ^ 40 * 2820627 * 2
def baseEnd_2820627 : Nat := 965558265366294011727119

theorem tailTrace_2820627 : CollatzResearch.WordTrace tailWord_2820627 prefixEnd_2820627 965558265366294011727119 := by
  unfold tailWord_2820627
  simp only [CollatzResearch.WordTrace]
  refine ⟨102876718352357578584644135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68584478901571719056429423 102876718352357578584644135)
  ·
    refine ⟨154315077528536367876966203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102876718352357578584644135 154315077528536367876966203)
    ·
      refine ⟨231472616292804551815449305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154315077528536367876966203 231472616292804551815449305)
      ·
        refine ⟨173604462219603413861586979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231472616292804551815449305 173604462219603413861586979)
        ·
          refine ⟨260406693329405120792380469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173604462219603413861586979 260406693329405120792380469)
          ·
            refine ⟨24413127499631730074285669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260406693329405120792380469 24413127499631730074285669)
            ·
              refine ⟨4577461406180949388928563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24413127499631730074285669 4577461406180949388928563)
              ·
                refine ⟨6866192109271424083392845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577461406180949388928563 6866192109271424083392845)
                ·
                  refine ⟨2574822040976784031272317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6866192109271424083392845 2574822040976784031272317)
                  ·
                    refine ⟨965558265366294011727119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574822040976784031272317 965558265366294011727119)
                    ·
                      rfl

theorem cell22_2820627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 3].length) (baseStart_2820627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820627 prefixEnd_2820627 := by exact prefixLift 2820627
  have htrace : WordTrace (prefixWord ++ tailWord_2820627) baseStart_2820627 baseEnd_2820627 := by
    simpa [prefixWord, tailWord_2820627, baseEnd_2820627] using wordTrace_append hprefix tailTrace_2820627
  have hstable : (prefixWord ++ tailWord_2820627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820627).length < 2 ^ (prefixWord ++ tailWord_2820627).sum := by decide
  have hdescent : baseEnd_2820627 < baseStart_2820627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820678 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2820678 : Nat := 118140960795 + 2820678 * 2 ^ 59
def prefixEnd_2820678 : Nat := 4983230072969 + 3 ^ 40 * 2820678 * 2
def baseEnd_2820678 : Nat := 965575723708546878701963

theorem tailTrace_2820678 : CollatzResearch.WordTrace tailWord_2820678 prefixEnd_2820678 965575723708546878701963 := by
  unfold tailWord_2820678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214955577349150446710959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68585718983448542863167125 3214955577349150446710959)
  ·
    refine ⟨4822433366023725670066439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3214955577349150446710959 4822433366023725670066439)
    ·
      refine ⟨7233650049035588505099659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822433366023725670066439 7233650049035588505099659)
      ·
        refine ⟨10850475073553382757649489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7233650049035588505099659 10850475073553382757649489)
        ·
          refine ⟨8137856305165037068237117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10850475073553382757649489 8137856305165037068237117)
          ·
            refine ⟨3051696114436888900588919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8137856305165037068237117 3051696114436888900588919)
            ·
              refine ⟨4577544171655333350883379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051696114436888900588919 4577544171655333350883379)
              ·
                refine ⟨6866316257483000026325069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577544171655333350883379 6866316257483000026325069)
                ·
                  refine ⟨2574868596556125009871901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6866316257483000026325069 2574868596556125009871901)
                  ·
                    refine ⟨965575723708546878701963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574868596556125009871901 965575723708546878701963)
                    ·
                      rfl

theorem cell22_2820678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2820678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820678 prefixEnd_2820678 := by exact prefixLift 2820678
  have htrace : WordTrace (prefixWord ++ tailWord_2820678) baseStart_2820678 baseEnd_2820678 := by
    simpa [prefixWord, tailWord_2820678, baseEnd_2820678] using wordTrace_append hprefix tailTrace_2820678
  have hstable : (prefixWord ++ tailWord_2820678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820678).length < 2 ^ (prefixWord ++ tailWord_2820678).sum := by decide
  have hdescent : baseEnd_2820678 < baseStart_2820678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820717 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2820717 : Nat := 118140960795 + 2820717 * 2 ^ 59
def prefixEnd_2820717 : Nat := 4983230072969 + 3 ^ 40 * 2820717 * 2
def baseEnd_2820717 : Nat := 965589074205563776976843

theorem tailTrace_2820717 : CollatzResearch.WordTrace tailWord_2820717 prefixEnd_2820717 965589074205563776976843 := by
  unfold tailWord_2820717
  simp only [CollatzResearch.WordTrace]
  refine ⟨102880000922031523955420405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68586667281354349303613603 102880000922031523955420405)
  ·
    refine ⟨9645000086440455370820663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102880000922031523955420405 9645000086440455370820663)
    ·
      refine ⟨14467500129660683056230995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9645000086440455370820663 14467500129660683056230995)
      ·
        refine ⟨21701250194491024584346493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14467500129660683056230995 21701250194491024584346493)
        ·
          refine ⟨8137968822934134219129935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21701250194491024584346493 8137968822934134219129935)
          ·
            refine ⟨12206953234401201328694903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8137968822934134219129935 12206953234401201328694903)
            ·
              refine ⟨18310429851601801993042355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12206953234401201328694903 18310429851601801993042355)
              ·
                refine ⟨27465644777402702989563533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18310429851601801993042355 27465644777402702989563533)
                ·
                  refine ⟨10299616791526013621086325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27465644777402702989563533 10299616791526013621086325)
                  ·
                    refine ⟨965589074205563776976843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10299616791526013621086325 965589074205563776976843)
                    ·
                      rfl

theorem cell22_2820717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2820717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820717 prefixEnd_2820717 := by exact prefixLift 2820717
  have htrace : WordTrace (prefixWord ++ tailWord_2820717) baseStart_2820717 baseEnd_2820717 := by
    simpa [prefixWord, tailWord_2820717, baseEnd_2820717] using wordTrace_append hprefix tailTrace_2820717
  have hstable : (prefixWord ++ tailWord_2820717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820717).length < 2 ^ (prefixWord ++ tailWord_2820717).sum := by decide
  have hdescent : baseEnd_2820717 < baseStart_2820717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820732 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_2820732 : Nat := 118140960795 + 2820732 * 2 ^ 59
def prefixEnd_2820732 : Nat := 4983230072969 + 3 ^ 40 * 2820732 * 2
def baseEnd_2820732 : Nat := 965594209012108737851797

theorem tailTrace_2820732 : CollatzResearch.WordTrace tailWord_2820732 prefixEnd_2820732 965594209012108737851797 := by
  unfold tailWord_2820732
  simp only [CollatzResearch.WordTrace]
  refine ⟨51440274008488590758608225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68587032011318121011477633 51440274008488590758608225)
  ·
    refine ⟨38580205506366443068956169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51440274008488590758608225 38580205506366443068956169)
    ·
      refine ⟨28935154129774832301717127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38580205506366443068956169 28935154129774832301717127)
      ·
        refine ⟨43402731194662248452575691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28935154129774832301717127 43402731194662248452575691)
        ·
          refine ⟨65104096791993372678863537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43402731194662248452575691 65104096791993372678863537)
          ·
            refine ⟨48828072593995029509147653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65104096791993372678863537 48828072593995029509147653)
            ·
              refine ⟨9155263611374068032965185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48828072593995029509147653 9155263611374068032965185)
              ·
                refine ⟨6866447708530551024723889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9155263611374068032965185 6866447708530551024723889)
                ·
                  refine ⟨5149835781397913268542917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6866447708530551024723889 5149835781397913268542917)
                  ·
                    refine ⟨965594209012108737851797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5149835781397913268542917 965594209012108737851797)
                    ·
                      rfl

theorem cell22_2820732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_2820732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820732 prefixEnd_2820732 := by exact prefixLift 2820732
  have htrace : WordTrace (prefixWord ++ tailWord_2820732) baseStart_2820732 baseEnd_2820732 := by
    simpa [prefixWord, tailWord_2820732, baseEnd_2820732] using wordTrace_append hprefix tailTrace_2820732
  have hstable : (prefixWord ++ tailWord_2820732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820732).length < 2 ^ (prefixWord ++ tailWord_2820732).sum := by decide
  have hdescent : baseEnd_2820732 < baseStart_2820732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820736 : List Nat := [2, 1, 1, 2, 1, 7, 2, 2, 4]
def baseStart_2820736 : Nat := 118140960795 + 2820736 * 2 ^ 59
def prefixEnd_2820736 : Nat := 4983230072969 + 3 ^ 40 * 2820736 * 2
def baseEnd_2820736 : Nat := 321865192764618020250595

theorem tailTrace_2820736 : CollatzResearch.WordTrace tailWord_2820736 prefixEnd_2820736 321865192764618020250595 := by
  unfold tailWord_2820736
  simp only [CollatzResearch.WordTrace]
  refine ⟨51440346954481345100181031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68587129272641793466908041 51440346954481345100181031)
  ·
    refine ⟨77160520431722017650271547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51440346954481345100181031 77160520431722017650271547)
    ·
      refine ⟨115740780647583026475407321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77160520431722017650271547 115740780647583026475407321)
      ·
        refine ⟨86805585485687269856555491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115740780647583026475407321 86805585485687269856555491)
        ·
          refine ⟨130208378228530904784833237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86805585485687269856555491 130208378228530904784833237)
          ·
            refine ⟨3051758864731193080894529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 130208378228530904784833237 3051758864731193080894529)
            ·
              refine ⟨2288819148548394810670897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3051758864731193080894529 2288819148548394810670897)
              ·
                refine ⟨1716614361411296108003173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2288819148548394810670897 1716614361411296108003173)
                ·
                  refine ⟨321865192764618020250595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1716614361411296108003173 321865192764618020250595)
                  ·
                    rfl

theorem cell22_2820736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_2820736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820736 prefixEnd_2820736 := by exact prefixLift 2820736
  have htrace : WordTrace (prefixWord ++ tailWord_2820736) baseStart_2820736 baseEnd_2820736 := by
    simpa [prefixWord, tailWord_2820736, baseEnd_2820736] using wordTrace_append hprefix tailTrace_2820736
  have hstable : (prefixWord ++ tailWord_2820736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820736).length < 2 ^ (prefixWord ++ tailWord_2820736).sum := by decide
  have hdescent : baseEnd_2820736 < baseStart_2820736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820745 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_2820745 : Nat := 118140960795 + 2820745 * 2 ^ 59
def prefixEnd_2820745 : Nat := 4983230072969 + 3 ^ 40 * 2820745 * 2
def baseEnd_2820745 : Nat := 965598659177781037276757

theorem tailTrace_2820745 : CollatzResearch.WordTrace tailWord_2820745 prefixEnd_2820745 965598659177781037276757 := by
  unfold tailWord_2820745
  simp only [CollatzResearch.WordTrace]
  refine ⟨102881022165930084737439689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68587348110620056491626459 102881022165930084737439689)
  ·
    refine ⟨77160766624447563553079767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102881022165930084737439689 77160766624447563553079767)
    ·
      refine ⟨115741149936671345329619651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77160766624447563553079767 115741149936671345329619651)
      ·
        refine ⟨173611724905007017994429477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115741149936671345329619651 173611724905007017994429477)
        ·
          refine ⟨32552198419688815873955527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173611724905007017994429477 32552198419688815873955527)
          ·
            refine ⟨48828297629533223810933291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32552198419688815873955527 48828297629533223810933291)
            ·
              refine ⟨73242446444299835716399937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48828297629533223810933291 73242446444299835716399937)
              ·
                refine ⟨54931834833224876787299953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73242446444299835716399937 54931834833224876787299953)
                ·
                  refine ⟨41198876124918657590474965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54931834833224876787299953 41198876124918657590474965)
                  ·
                    refine ⟨965598659177781037276757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41198876124918657590474965 965598659177781037276757)
                    ·
                      rfl

theorem cell22_2820745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_2820745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820745 prefixEnd_2820745 := by exact prefixLift 2820745
  have htrace : WordTrace (prefixWord ++ tailWord_2820745) baseStart_2820745 baseEnd_2820745 := by
    simpa [prefixWord, tailWord_2820745, baseEnd_2820745] using wordTrace_append hprefix tailTrace_2820745
  have hstable : (prefixWord ++ tailWord_2820745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820745).length < 2 ^ (prefixWord ++ tailWord_2820745).sum := by decide
  have hdescent : baseEnd_2820745 < baseStart_2820745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820764 : List Nat := [2, 2, 3, 2, 2, 2, 3, 6]
def baseStart_2820764 : Nat := 118140960795 + 2820764 * 2 ^ 59
def prefixEnd_2820764 : Nat := 4983230072969 + 3 ^ 40 * 2820764 * 2
def baseEnd_2820764 : Nat := 107289462585119035672411

theorem tailTrace_2820764 : CollatzResearch.WordTrace tailWord_2820764 prefixEnd_2820764 107289462585119035672411 := by
  unfold tailWord_2820764
  simp only [CollatzResearch.WordTrace]
  refine ⟨51440857576430625491190673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68587810101907500654920897 51440857576430625491190673)
  ·
    refine ⟨38580643182322969118393005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51440857576430625491190673 38580643182322969118393005)
    ·
      refine ⟨14467741193371113419397377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38580643182322969118393005 14467741193371113419397377)
      ·
        refine ⟨10850805895028335064548033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14467741193371113419397377 10850805895028335064548033)
        ·
          refine ⟨8138104421271251298411025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10850805895028335064548033 8138104421271251298411025)
          ·
            refine ⟨6103578315953438473808269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8138104421271251298411025 6103578315953438473808269)
            ·
              refine ⟨2288841868482539427678101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6103578315953438473808269 2288841868482539427678101)
              ·
                refine ⟨107289462585119035672411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2288841868482539427678101 107289462585119035672411)
                ·
                  rfl

theorem cell22_2820764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 6].length) (baseStart_2820764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820764 prefixEnd_2820764 := by exact prefixLift 2820764
  have htrace : WordTrace (prefixWord ++ tailWord_2820764) baseStart_2820764 baseEnd_2820764 := by
    simpa [prefixWord, tailWord_2820764, baseEnd_2820764] using wordTrace_append hprefix tailTrace_2820764
  have hstable : (prefixWord ++ tailWord_2820764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820764).length < 2 ^ (prefixWord ++ tailWord_2820764).sum := by decide
  have hdescent : baseEnd_2820764 < baseStart_2820764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820785 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 2, 3]
def baseStart_2820785 : Nat := 118140960795 + 2820785 * 2 ^ 59
def prefixEnd_2820785 : Nat := 4983230072969 + 3 ^ 40 * 2820785 * 2
def baseEnd_2820785 : Nat := 965612351995234266276635

theorem tailTrace_2820785 : CollatzResearch.WordTrace tailWord_2820785 prefixEnd_2820785 965612351995234266276635 := by
  unfold tailWord_2820785
  simp only [CollatzResearch.WordTrace]
  refine ⟨102882481085785171568895809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68588320723856781045930539 102882481085785171568895809)
  ·
    refine ⟨77161860814338878676671857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102882481085785171568895809 77161860814338878676671857)
    ·
      refine ⟨57871395610754159007503893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77161860814338878676671857 57871395610754159007503893)
      ·
        refine ⟨2712721669254101203476745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57871395610754159007503893 2712721669254101203476745)
        ·
          refine ⟨2034541251940575902607559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2712721669254101203476745 2034541251940575902607559)
          ·
            refine ⟨3051811877910863853911339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034541251940575902607559 3051811877910863853911339)
            ·
              refine ⟨4577717816866295780867009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3051811877910863853911339 4577717816866295780867009)
              ·
                refine ⟨3433288362649721835650257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4577717816866295780867009 3433288362649721835650257)
                ·
                  refine ⟨2574966271987291376737693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3433288362649721835650257 2574966271987291376737693)
                  ·
                    refine ⟨965612351995234266276635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574966271987291376737693 965612351995234266276635)
                    ·
                      rfl

theorem cell22_2820785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_2820785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820785 prefixEnd_2820785 := by exact prefixLift 2820785
  have htrace : WordTrace (prefixWord ++ tailWord_2820785) baseStart_2820785 baseEnd_2820785 := by
    simpa [prefixWord, tailWord_2820785, baseEnd_2820785] using wordTrace_append hprefix tailTrace_2820785
  have hstable : (prefixWord ++ tailWord_2820785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820785).length < 2 ^ (prefixWord ++ tailWord_2820785).sum := by decide
  have hdescent : baseEnd_2820785 < baseStart_2820785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820796 : List Nat := [2, 2, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_2820796 : Nat := 118140960795 + 2820796 * 2 ^ 59
def prefixEnd_2820796 : Nat := 4983230072969 + 3 ^ 40 * 2820796 * 2
def baseEnd_2820796 : Nat := 965616117520033904251601

theorem tailTrace_2820796 : CollatzResearch.WordTrace tailWord_2820796 prefixEnd_2820796 965616117520033904251601 := by
  unfold tailWord_2820796
  simp only [CollatzResearch.WordTrace]
  refine ⟨51441441144372660223773121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68588588192496880298364161 51441441144372660223773121)
  ·
    refine ⟨38581080858279495167829841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51441441144372660223773121 38581080858279495167829841)
    ·
      refine ⟨28935810643709621375872381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38581080858279495167829841 28935810643709621375872381)
      ·
        refine ⟨10850928991391108015952143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28935810643709621375872381 10850928991391108015952143)
        ·
          refine ⟨16276393487086662023928215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10850928991391108015952143 16276393487086662023928215)
          ·
            refine ⟨24414590230629993035892323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16276393487086662023928215 24414590230629993035892323)
            ·
              refine ⟨36621885345944989553838485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24414590230629993035892323 36621885345944989553838485)
              ·
                refine ⟨1716650875591171385336179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36621885345944989553838485 1716650875591171385336179)
                ·
                  refine ⟨2574976313386757078004269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716650875591171385336179 2574976313386757078004269)
                  ·
                    refine ⟨965616117520033904251601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2574976313386757078004269 965616117520033904251601)
                    ·
                      rfl

theorem cell22_2820796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_2820796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820796 prefixEnd_2820796 := by exact prefixLift 2820796
  have htrace : WordTrace (prefixWord ++ tailWord_2820796) baseStart_2820796 baseEnd_2820796 := by
    simpa [prefixWord, tailWord_2820796, baseEnd_2820796] using wordTrace_append hprefix tailTrace_2820796
  have hstable : (prefixWord ++ tailWord_2820796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820796).length < 2 ^ (prefixWord ++ tailWord_2820796).sum := by decide
  have hdescent : baseEnd_2820796 < baseStart_2820796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820867 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 6, 4]
def baseStart_2820867 : Nat := 118140960795 + 2820867 * 2 ^ 59
def prefixEnd_2820867 : Nat := 4983230072969 + 3 ^ 40 * 2820867 * 2
def baseEnd_2820867 : Nat := 965640422271013385726383

theorem tailTrace_2820867 : CollatzResearch.WordTrace tailWord_2820867 prefixEnd_2820867 965640422271013385726383 := by
  unfold tailWord_2820867
  simp only [CollatzResearch.WordTrace]
  refine ⟨102885471871488099573380855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68590314580992066382253903 102885471871488099573380855)
  ·
    refine ⟨154328207807232149360071283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102885471871488099573380855 154328207807232149360071283)
    ·
      refine ⟨231492311710848224040106925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154328207807232149360071283 231492311710848224040106925)
      ·
        refine ⟨86809616891568084015040097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231492311710848224040106925 86809616891568084015040097)
        ·
          refine ⟨65107212668676063011280073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86809616891568084015040097 65107212668676063011280073)
          ·
            refine ⟨48830409501507047258460055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65107212668676063011280073 48830409501507047258460055)
            ·
              refine ⟨73245614252260570887690083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48830409501507047258460055 73245614252260570887690083)
              ·
                refine ⟨109868421378390856331535125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73245614252260570887690083 109868421378390856331535125)
                ·
                  refine ⟨5150082252112071390540709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109868421378390856331535125 5150082252112071390540709)
                  ·
                    refine ⟨965640422271013385726383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150082252112071390540709 965640422271013385726383)
                    ·
                      rfl

theorem cell22_2820867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_2820867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820867 prefixEnd_2820867 := by exact prefixLift 2820867
  have htrace : WordTrace (prefixWord ++ tailWord_2820867) baseStart_2820867 baseEnd_2820867 := by
    simpa [prefixWord, tailWord_2820867, baseEnd_2820867] using wordTrace_append hprefix tailTrace_2820867
  have hstable : (prefixWord ++ tailWord_2820867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820867).length < 2 ^ (prefixWord ++ tailWord_2820867).sum := by decide
  have hdescent : baseEnd_2820867 < baseStart_2820867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2820989 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 6]
def baseStart_2820989 : Nat := 118140960795 + 2820989 * 2 ^ 59
def prefixEnd_2820989 : Nat := 4983230072969 + 3 ^ 40 * 2820989 * 2
def baseEnd_2820989 : Nat := 321894061788081911392003

theorem tailTrace_2820989 : CollatzResearch.WordTrace tailWord_2820989 prefixEnd_2820989 321894061788081911392003 := by
  unfold tailWord_2820989
  simp only [CollatzResearch.WordTrace]
  refine ⟨102889921577046114409322021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68593281051364076272881347 102889921577046114409322021)
  ·
    refine ⟨19291860295696146451747879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102889921577046114409322021 19291860295696146451747879)
    ·
      refine ⟨28937790443544219677621819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19291860295696146451747879 28937790443544219677621819)
      ·
        refine ⟨43406685665316329516432729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28937790443544219677621819 43406685665316329516432729)
        ·
          refine ⟨32555014248987247137324547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43406685665316329516432729 32555014248987247137324547)
          ·
            refine ⟨48832521373480870705986821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32555014248987247137324547 48832521373480870705986821)
            ·
              refine ⟨9156097757527663257372529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48832521373480870705986821 9156097757527663257372529)
              ·
                refine ⟨6867073318145747443029397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9156097757527663257372529 6867073318145747443029397)
                ·
                  refine ⟨321894061788081911392003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6867073318145747443029397 321894061788081911392003)
                  ·
                    rfl

theorem cell22_2820989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_2820989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2820989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2820989 prefixEnd_2820989 := by exact prefixLift 2820989
  have htrace : WordTrace (prefixWord ++ tailWord_2820989) baseStart_2820989 baseEnd_2820989 := by
    simpa [prefixWord, tailWord_2820989, baseEnd_2820989] using wordTrace_append hprefix tailTrace_2820989
  have hstable : (prefixWord ++ tailWord_2820989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2820989).length < 2 ^ (prefixWord ++ tailWord_2820989).sum := by decide
  have hdescent : baseEnd_2820989 < baseStart_2820989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2820989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821004 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_2821004 : Nat := 118140960795 + 2821004 * 2 ^ 59
def prefixEnd_2821004 : Nat := 4983230072969 + 3 ^ 40 * 2821004 * 2
def baseEnd_2821004 : Nat := 965687320170790695050963

theorem tailTrace_2821004 : CollatzResearch.WordTrace tailWord_2821004 prefixEnd_2821004 965687320170790695050963 := by
  unfold tailWord_2821004
  simp only [CollatzResearch.WordTrace]
  refine ⟨51445234335995885985559033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68593645781327847980745377 51445234335995885985559033)
  ·
    refine ⟨38583925751996914489169275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51445234335995885985559033 38583925751996914489169275)
    ·
      refine ⟨57875888627995371733753913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38583925751996914489169275 57875888627995371733753913)
      ·
        refine ⟨43406916470996528800315435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57875888627995371733753913 43406916470996528800315435)
        ·
          refine ⟨65110374706494793200473153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43406916470996528800315435 65110374706494793200473153)
          ·
            refine ⟨48832781029871094900354865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65110374706494793200473153 48832781029871094900354865)
            ·
              refine ⟨36624585772403321175266149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48832781029871094900354865 36624585772403321175266149)
              ·
                refine ⟨6867109832325622720362403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36624585772403321175266149 6867109832325622720362403)
                ·
                  refine ⟨10300664748488434080543605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6867109832325622720362403 10300664748488434080543605)
                  ·
                    refine ⟨965687320170790695050963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10300664748488434080543605 965687320170790695050963)
                    ·
                      rfl

theorem cell22_2821004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_2821004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821004 prefixEnd_2821004 := by exact prefixLift 2821004
  have htrace : WordTrace (prefixWord ++ tailWord_2821004) baseStart_2821004 baseEnd_2821004 := by
    simpa [prefixWord, tailWord_2821004, baseEnd_2821004] using wordTrace_append hprefix tailTrace_2821004
  have hstable : (prefixWord ++ tailWord_2821004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821004).length < 2 ^ (prefixWord ++ tailWord_2821004).sum := by decide
  have hdescent : baseEnd_2821004 < baseStart_2821004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821021 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2821021 : Nat := 118140960795 + 2821021 * 2 ^ 59
def prefixEnd_2821021 : Nat := 4983230072969 + 3 ^ 40 * 2821021 * 2
def baseEnd_2821021 : Nat := 965693139618208317375911

theorem tailTrace_2821021 : CollatzResearch.WordTrace tailWord_2821021 prefixEnd_2821021 965693139618208317375911 := by
  unfold tailWord_2821021
  simp only [CollatzResearch.WordTrace]
  refine ⟨102891088712930183874486917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68594059141953455916324611 102891088712930183874486917)
  ·
    refine ⟨19292079133674409476466297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102891088712930183874486917 19292079133674409476466297)
    ·
      refine ⟨14469059350255807107349723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19292079133674409476466297 14469059350255807107349723)
      ·
        refine ⟨21703589025383710661024585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14469059350255807107349723 21703589025383710661024585)
        ·
          refine ⟨16277691769037782995768439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21703589025383710661024585 16277691769037782995768439)
          ·
            refine ⟨24416537653556674493652659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16277691769037782995768439 24416537653556674493652659)
            ·
              refine ⟨36624806480335011740478989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24416537653556674493652659 36624806480335011740478989)
              ·
                refine ⟨13734302430125629402679621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36624806480335011740478989 13734302430125629402679621)
                ·
                  refine ⟨2575181705648555513002429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13734302430125629402679621 2575181705648555513002429)
                  ·
                    refine ⟨965693139618208317375911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2575181705648555513002429 965693139618208317375911)
                    ·
                      rfl

theorem cell22_2821021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2821021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821021 prefixEnd_2821021 := by exact prefixLift 2821021
  have htrace : WordTrace (prefixWord ++ tailWord_2821021) baseStart_2821021 baseEnd_2821021 := by
    simpa [prefixWord, tailWord_2821021, baseEnd_2821021] using wordTrace_append hprefix tailTrace_2821021
  have hstable : (prefixWord ++ tailWord_2821021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821021).length < 2 ^ (prefixWord ++ tailWord_2821021).sum := by decide
  have hdescent : baseEnd_2821021 < baseStart_2821021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821053 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2821053 : Nat := 118140960795 + 2821053 * 2 ^ 59
def prefixEnd_2821053 : Nat := 4983230072969 + 3 ^ 40 * 2821053 * 2
def baseEnd_2821053 : Nat := 965704093872170900575813

theorem tailTrace_2821053 : CollatzResearch.WordTrace tailWord_2821053 prefixEnd_2821053 965704093872170900575813 := by
  unfold tailWord_2821053
  simp only [CollatzResearch.WordTrace]
  refine ⟨102892255848814253339651813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68594837232542835559767875 102892255848814253339651813)
  ·
    refine ⟨19292297971652672501184715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102892255848814253339651813 19292297971652672501184715)
    ·
      refine ⟨28938446957479008751777073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19292297971652672501184715 28938446957479008751777073)
      ·
        refine ⟨21703835218109256563832805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28938446957479008751777073 21703835218109256563832805)
        ·
          refine ⟨4069469103395485605718651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21703835218109256563832805 4069469103395485605718651)
          ·
            refine ⟨6104203655093228408577977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4069469103395485605718651 6104203655093228408577977)
            ·
              refine ⟨4578152741319921306433483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104203655093228408577977 4578152741319921306433483)
              ·
                refine ⟨6867229111979881959650225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578152741319921306433483 6867229111979881959650225)
                ·
                  refine ⟨5150421833984911469737669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6867229111979881959650225 5150421833984911469737669)
                  ·
                    refine ⟨965704093872170900575813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150421833984911469737669 965704093872170900575813)
                    ·
                      rfl

theorem cell22_2821053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2821053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821053 prefixEnd_2821053 := by exact prefixLift 2821053
  have htrace : WordTrace (prefixWord ++ tailWord_2821053) baseStart_2821053 baseEnd_2821053 := by
    simpa [prefixWord, tailWord_2821053, baseEnd_2821053] using wordTrace_append hprefix tailTrace_2821053
  have hstable : (prefixWord ++ tailWord_2821053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821053).length < 2 ^ (prefixWord ++ tailWord_2821053).sum := by decide
  have hdescent : baseEnd_2821053 < baseStart_2821053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821096 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 5]
def baseStart_2821096 : Nat := 118140960795 + 2821096 * 2 ^ 59
def prefixEnd_2821096 : Nat := 4983230072969 + 3 ^ 40 * 2821096 * 2
def baseEnd_2821096 : Nat := 321906271216977707250227

theorem tailTrace_2821096 : CollatzResearch.WordTrace tailWord_2821096 prefixEnd_2821096 321906271216977707250227 := by
  unfold tailWord_2821096
  simp only [CollatzResearch.WordTrace]
  refine ⟨51446912093829235841733571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68595882791772314455644761 51446912093829235841733571)
  ·
    refine ⟨77170368140743853762600357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51446912093829235841733571 77170368140743853762600357)
    ·
      refine ⟨14469444026389472580487567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77170368140743853762600357 14469444026389472580487567)
      ·
        refine ⟨21704166039584208870731351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14469444026389472580487567 21704166039584208870731351)
        ·
          refine ⟨32556249059376313306097027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21704166039584208870731351 32556249059376313306097027)
          ·
            refine ⟨48834373589064469959145541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32556249059376313306097027 48834373589064469959145541)
            ·
              refine ⟨9156445047949588117339789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48834373589064469959145541 9156445047949588117339789)
              ·
                refine ⟨3433666892981095544002421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9156445047949588117339789 3433666892981095544002421)
                ·
                  refine ⟨321906271216977707250227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3433666892981095544002421 321906271216977707250227)
                  ·
                    rfl

theorem cell22_2821096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_2821096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821096 prefixEnd_2821096 := by exact prefixLift 2821096
  have htrace : WordTrace (prefixWord ++ tailWord_2821096) baseStart_2821096 baseEnd_2821096 := by
    simpa [prefixWord, tailWord_2821096, baseEnd_2821096] using wordTrace_append hprefix tailTrace_2821096
  have hstable : (prefixWord ++ tailWord_2821096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821096).length < 2 ^ (prefixWord ++ tailWord_2821096).sum := by decide
  have hdescent : baseEnd_2821096 < baseStart_2821096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821141 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 6]
def baseStart_2821141 : Nat := 118140960795 + 2821141 * 2 ^ 59
def prefixEnd_2821141 : Nat := 4983230072969 + 3 ^ 40 * 2821141 * 2
def baseEnd_2821141 : Nat := 321911406023522668125181

theorem tailTrace_2821141 : CollatzResearch.WordTrace tailWord_2821141 prefixEnd_2821141 321911406023522668125181 := by
  unfold tailWord_2821141
  simp only [CollatzResearch.WordTrace]
  refine ⟨102895465472495444368855277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68596976981663629579236851 102895465472495444368855277)
  ·
    refine ⟨38585799552185791638320729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102895465472495444368855277 38585799552185791638320729)
    ·
      refine ⟨28939349664139343728740547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38585799552185791638320729 28939349664139343728740547)
      ·
        refine ⟨43409024496209015593110821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28939349664139343728740547 43409024496209015593110821)
        ·
          refine ⟨8139192093039190423708279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43409024496209015593110821 8139192093039190423708279)
          ·
            refine ⟨12208788139558785635562419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8139192093039190423708279 12208788139558785635562419)
            ·
              refine ⟨18313182209338178453343629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12208788139558785635562419 18313182209338178453343629)
              ·
                refine ⟨6867443328501816920003861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18313182209338178453343629 6867443328501816920003861)
                ·
                  refine ⟨321911406023522668125181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6867443328501816920003861 321911406023522668125181)
                  ·
                    rfl

theorem cell22_2821141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_2821141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821141 prefixEnd_2821141 := by exact prefixLift 2821141
  have htrace : WordTrace (prefixWord ++ tailWord_2821141) baseStart_2821141 baseEnd_2821141 := by
    simpa [prefixWord, tailWord_2821141, baseEnd_2821141] using wordTrace_append hprefix tailTrace_2821141
  have hstable : (prefixWord ++ tailWord_2821141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821141).length < 2 ^ (prefixWord ++ tailWord_2821141).sum := by decide
  have hdescent : baseEnd_2821141 < baseStart_2821141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821171 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 2, 4]
def baseStart_2821171 : Nat := 118140960795 + 2821171 * 2 ^ 59
def prefixEnd_2821171 : Nat := 4983230072969 + 3 ^ 40 * 2821171 * 2
def baseEnd_2821171 : Nat := 965744487683657926125451

theorem tailTrace_2821171 : CollatzResearch.WordTrace tailWord_2821171 prefixEnd_2821171 965744487683657926125451 := by
  unfold tailWord_2821171
  simp only [CollatzResearch.WordTrace]
  refine ⟨102896559662386759492447367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68597706441591172994964911 102896559662386759492447367)
  ·
    refine ⟨154344839493580139238671051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102896559662386759492447367 154344839493580139238671051)
    ·
      refine ⟨231517259240370208858006577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154344839493580139238671051 231517259240370208858006577)
      ·
        refine ⟨173637944430277656643504933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231517259240370208858006577 173637944430277656643504933)
        ·
          refine ⟨32557114580677060620657175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173637944430277656643504933 32557114580677060620657175)
          ·
            refine ⟨48835671871015590930985763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32557114580677060620657175 48835671871015590930985763)
            ·
              refine ⟨73253507806523386396478645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48835671871015590930985763 73253507806523386396478645)
              ·
                refine ⟨6867516356861567474669873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73253507806523386396478645 6867516356861567474669873)
                ·
                  refine ⟨5150637267646175606002405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6867516356861567474669873 5150637267646175606002405)
                  ·
                    refine ⟨965744487683657926125451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150637267646175606002405 965744487683657926125451)
                    ·
                      rfl

theorem cell22_2821171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 4].length) (baseStart_2821171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821171 prefixEnd_2821171 := by exact prefixLift 2821171
  have htrace : WordTrace (prefixWord ++ tailWord_2821171) baseStart_2821171 baseEnd_2821171 := by
    simpa [prefixWord, tailWord_2821171, baseEnd_2821171] using wordTrace_append hprefix tailTrace_2821171
  have hstable : (prefixWord ++ tailWord_2821171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821171).length < 2 ^ (prefixWord ++ tailWord_2821171).sum := by decide
  have hdescent : baseEnd_2821171 < baseStart_2821171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821252 : List Nat := [2, 3, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2821252 : Nat := 118140960795 + 2821252 * 2 ^ 59
def prefixEnd_2821252 : Nat := 4983230072969 + 3 ^ 40 * 2821252 * 2
def baseEnd_2821252 : Nat := 965772215639000714850203

theorem tailTrace_2821252 : CollatzResearch.WordTrace tailWord_2821252 prefixEnd_2821252 965772215639000714850203 := by
  unfold tailWord_2821252
  simp only [CollatzResearch.WordTrace]
  refine ⟨51449756987546655163073005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68599675983395540217430673 51449756987546655163073005)
  ·
    refine ⟨19293658870329995686152377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51449756987546655163073005 19293658870329995686152377)
    ·
      refine ⟨14470244152747496764614283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19293658870329995686152377 14470244152747496764614283)
      ·
        refine ⟨21705366229121245146921425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14470244152747496764614283 21705366229121245146921425)
        ·
          refine ⟨16279024671840933860191069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21705366229121245146921425 16279024671840933860191069)
          ·
            refine ⟨6104634251940350197571651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16279024671840933860191069 6104634251940350197571651)
            ·
              refine ⟨9156951377910525296357477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104634251940350197571651 9156951377910525296357477)
              ·
                refine ⟨1716928383358223493067027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9156951377910525296357477 1716928383358223493067027)
                ·
                  refine ⟨2575392575037335239600541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716928383358223493067027 2575392575037335239600541)
                  ·
                    refine ⟨965772215639000714850203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2575392575037335239600541 965772215639000714850203)
                    ·
                      rfl

theorem cell22_2821252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2821252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821252 prefixEnd_2821252 := by exact prefixLift 2821252
  have htrace : WordTrace (prefixWord ++ tailWord_2821252) baseStart_2821252 baseEnd_2821252 := by
    simpa [prefixWord, tailWord_2821252, baseEnd_2821252] using wordTrace_append hprefix tailTrace_2821252
  have hstable : (prefixWord ++ tailWord_2821252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821252).length < 2 ^ (prefixWord ++ tailWord_2821252).sum := by decide
  have hdescent : baseEnd_2821252 < baseStart_2821252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821295 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 1, 4]
def baseStart_2821295 : Nat := 118140960795 + 2821295 * 2 ^ 59
def prefixEnd_2821295 : Nat := 4983230072969 + 3 ^ 40 * 2821295 * 2
def baseEnd_2821295 : Nat := 965786935417762936025071

theorem tailTrace_2821295 : CollatzResearch.WordTrace tailWord_2821295 prefixEnd_2821295 965786935417762936025071 := by
  unfold tailWord_2821295
  simp only [CollatzResearch.WordTrace]
  refine ⟨102901082313937528669961339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68600721542625019113307559 102901082313937528669961339)
  ·
    refine ⟨154351623470906293004942009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102901082313937528669961339 154351623470906293004942009)
    ·
      refine ⟨115763717603179719753706507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154351623470906293004942009 115763717603179719753706507)
      ·
        refine ⟨173645576404769579630559761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115763717603179719753706507 173645576404769579630559761)
        ·
          refine ⟨130234182303577184722919821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173645576404769579630559761 130234182303577184722919821)
          ·
            refine ⟨48837818363841444271094933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130234182303577184722919821 48837818363841444271094933)
            ·
              refine ⟨2289272735805067700207575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48837818363841444271094933 2289272735805067700207575)
              ·
                refine ⟨3433909103707601550311363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289272735805067700207575 3433909103707601550311363)
                ·
                  refine ⟨5150863655561402325467045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433909103707601550311363 5150863655561402325467045)
                  ·
                    refine ⟨965786935417762936025071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5150863655561402325467045 965786935417762936025071)
                    ·
                      rfl

theorem cell22_2821295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_2821295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821295 prefixEnd_2821295 := by exact prefixLift 2821295
  have htrace : WordTrace (prefixWord ++ tailWord_2821295) baseStart_2821295 baseEnd_2821295 := by
    simpa [prefixWord, tailWord_2821295, baseEnd_2821295] using wordTrace_append hprefix tailTrace_2821295
  have hstable : (prefixWord ++ tailWord_2821295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821295).length < 2 ^ (prefixWord ++ tailWord_2821295).sum := by decide
  have hdescent : baseEnd_2821295 < baseStart_2821295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821310 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2821310 : Nat := 118140960795 + 2821310 * 2 ^ 59
def prefixEnd_2821310 : Nat := 4983230072969 + 3 ^ 40 * 2821310 * 2
def baseEnd_2821310 : Nat := 321930690074769298966675

theorem tailTrace_2821310 : CollatzResearch.WordTrace tailWord_2821310 prefixEnd_2821310 321930690074769298966675 := by
  unfold tailWord_2821310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12862703676110398278969673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68601086272588790821171589 12862703676110398278969673)
  ·
    refine ⟨9647027757082798709227255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12862703676110398278969673 9647027757082798709227255)
    ·
      refine ⟨14470541635624198063840883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647027757082798709227255 14470541635624198063840883)
      ·
        refine ⟨21705812453436297095761325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14470541635624198063840883 21705812453436297095761325)
        ·
          refine ⟨8139679670038611410910497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21705812453436297095761325 8139679670038611410910497)
          ·
            refine ⟨6104759752528958558182873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139679670038611410910497 6104759752528958558182873)
            ·
              refine ⟨4578569814396718918637155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104759752528958558182873 4578569814396718918637155)
              ·
                refine ⟨6867854721595078377955733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578569814396718918637155 6867854721595078377955733)
                ·
                  refine ⟨321930690074769298966675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6867854721595078377955733 321930690074769298966675)
                  ·
                    rfl

theorem cell22_2821310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2821310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821310 prefixEnd_2821310 := by exact prefixLift 2821310
  have htrace : WordTrace (prefixWord ++ tailWord_2821310) baseStart_2821310 baseEnd_2821310 := by
    simpa [prefixWord, tailWord_2821310, baseEnd_2821310] using wordTrace_append hprefix tailTrace_2821310
  have hstable : (prefixWord ++ tailWord_2821310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821310).length < 2 ^ (prefixWord ++ tailWord_2821310).sum := by decide
  have hdescent : baseEnd_2821310 < baseStart_2821310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821421 : List Nat := [1, 5, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2821421 : Nat := 118140960795 + 2821421 * 2 ^ 59
def prefixEnd_2821421 : Nat := 4983230072969 + 3 ^ 40 * 2821421 * 2
def baseEnd_2821421 : Nat := 965830067792740607374685

theorem tailTrace_2821421 : CollatzResearch.WordTrace tailWord_2821421 prefixEnd_2821421 965830067792740607374685 := by
  unfold tailWord_2821421
  simp only [CollatzResearch.WordTrace]
  refine ⟨102905677911481052189048117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68603785274320701459365411 102905677911481052189048117)
  ·
    refine ⟨9647407304201348642723261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102905677911481052189048117 9647407304201348642723261)
    ·
      refine ⟨3617777739075505741021223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9647407304201348642723261 3617777739075505741021223)
      ·
        refine ⟨5426666608613258611531835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3617777739075505741021223 5426666608613258611531835)
        ·
          refine ⟨8139999912919887917297753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426666608613258611531835 8139999912919887917297753)
          ·
            refine ⟨6104999934689915937973315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139999912919887917297753 6104999934689915937973315)
            ·
              refine ⟨9157499902034873906959973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104999934689915937973315 9157499902034873906959973)
              ·
                refine ⟨1717031231631538857554995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9157499902034873906959973 1717031231631538857554995)
                ·
                  refine ⟨2575546847447308286332493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717031231631538857554995 2575546847447308286332493)
                  ·
                    refine ⟨965830067792740607374685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2575546847447308286332493 965830067792740607374685)
                    ·
                      rfl

theorem cell22_2821421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2821421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821421 prefixEnd_2821421 := by exact prefixLift 2821421
  have htrace : WordTrace (prefixWord ++ tailWord_2821421) baseStart_2821421 baseEnd_2821421 := by
    simpa [prefixWord, tailWord_2821421, baseEnd_2821421] using wordTrace_append hprefix tailTrace_2821421
  have hstable : (prefixWord ++ tailWord_2821421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821421).length < 2 ^ (prefixWord ++ tailWord_2821421).sum := by decide
  have hdescent : baseEnd_2821421 < baseStart_2821421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821460 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2821460 : Nat := 118140960795 + 2821460 * 2 ^ 59
def prefixEnd_2821460 : Nat := 4983230072969 + 3 ^ 40 * 2821460 * 2
def baseEnd_2821460 : Nat := 965843418289757505649565

theorem tailTrace_2821460 : CollatzResearch.WordTrace tailWord_2821460 prefixEnd_2821460 965843418289757505649565 := by
  unfold tailWord_2821460
  simp only [CollatzResearch.WordTrace]
  refine ⟨51453550179169880924858917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68604733572226507899811889 51453550179169880924858917)
  ·
    refine ⟨9647540658594352673411047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51453550179169880924858917 9647540658594352673411047)
    ·
      refine ⟨14471310987891529010116571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647540658594352673411047 14471310987891529010116571)
      ·
        refine ⟨21706966481837293515174857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14471310987891529010116571 21706966481837293515174857)
        ·
          refine ⟨16280224861377970136381143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21706966481837293515174857 16280224861377970136381143)
          ·
            refine ⟨24420337292066955204571715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16280224861377970136381143 24420337292066955204571715)
            ·
              refine ⟨36630505938100432806857573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24420337292066955204571715 36630505938100432806857573)
              ·
                refine ⟨6868219863393831151285795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36630505938100432806857573 6868219863393831151285795)
                ·
                  refine ⟨10302329795090746726928693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6868219863393831151285795 10302329795090746726928693)
                  ·
                    refine ⟨965843418289757505649565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10302329795090746726928693 965843418289757505649565)
                    ·
                      rfl

theorem cell22_2821460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2821460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821460 prefixEnd_2821460 := by exact prefixLift 2821460
  have htrace : WordTrace (prefixWord ++ tailWord_2821460) baseStart_2821460 baseEnd_2821460 := by
    simpa [prefixWord, tailWord_2821460, baseEnd_2821460] using wordTrace_append hprefix tailTrace_2821460
  have hstable : (prefixWord ++ tailWord_2821460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821460).length < 2 ^ (prefixWord ++ tailWord_2821460).sum := by decide
  have hdescent : baseEnd_2821460 < baseStart_2821460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821507 : List Nat := [1, 1, 1, 3, 5, 3, 2, 6]
def baseStart_2821507 : Nat := 118140960795 + 2821507 * 2 ^ 59
def prefixEnd_2821507 : Nat := 4983230072969 + 3 ^ 40 * 2821507 * 2
def baseEnd_2821507 : Nat := 107317723038918338858269

theorem tailTrace_2821507 : CollatzResearch.WordTrace tailWord_2821507 prefixEnd_2821507 107317723038918338858269 := by
  unfold tailWord_2821507
  simp only [CollatzResearch.WordTrace]
  refine ⟨102908814589169488876678775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68605876392779659251119183 102908814589169488876678775)
  ·
    refine ⟨154363221883754233315018163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102908814589169488876678775 154363221883754233315018163)
    ·
      refine ⟨231544832825631349972527245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154363221883754233315018163 231544832825631349972527245)
      ·
        refine ⟨86829312309611756239697717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231544832825631349972527245 86829312309611756239697717)
        ·
          refine ⟨8140248029026102147471661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86829312309611756239697717 8140248029026102147471661)
          ·
            refine ⟨3052593010884788305301873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8140248029026102147471661 3052593010884788305301873)
            ·
              refine ⟨2289444758163591228976405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052593010884788305301873 2289444758163591228976405)
              ·
                refine ⟨107317723038918338858269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2289444758163591228976405 107317723038918338858269)
                ·
                  rfl

theorem cell22_2821507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 6].length) (baseStart_2821507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821507 prefixEnd_2821507 := by exact prefixLift 2821507
  have htrace : WordTrace (prefixWord ++ tailWord_2821507) baseStart_2821507 baseEnd_2821507 := by
    simpa [prefixWord, tailWord_2821507, baseEnd_2821507] using wordTrace_append hprefix tailTrace_2821507
  have hstable : (prefixWord ++ tailWord_2821507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821507).length < 2 ^ (prefixWord ++ tailWord_2821507).sum := by decide
  have hdescent : baseEnd_2821507 < baseStart_2821507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821535 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 7]
def baseStart_2821535 : Nat := 118140960795 + 2821535 * 2 ^ 59
def prefixEnd_2821535 : Nat := 4983230072969 + 3 ^ 40 * 2821535 * 2
def baseEnd_2821535 : Nat := 321956364107494103341445

theorem tailTrace_2821535 : CollatzResearch.WordTrace tailWord_2821535 prefixEnd_2821535 321956364107494103341445 := by
  unfold tailWord_2821535
  simp only [CollatzResearch.WordTrace]
  refine ⟨102909835833068049658698059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68606557222045366439132039 102909835833068049658698059)
  ·
    refine ⟨154364753749602074488047089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102909835833068049658698059 154364753749602074488047089)
    ·
      refine ⟨115773565312201555866035317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154364753749602074488047089 115773565312201555866035317)
      ·
        refine ⟨10853771748018895862440811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115773565312201555866035317 10853771748018895862440811)
        ·
          refine ⟨16280657622028343793661217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10853771748018895862440811 16280657622028343793661217)
          ·
            refine ⟨12210493216521257845245913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16280657622028343793661217 12210493216521257845245913)
            ·
              refine ⟨9157869912390943383934435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12210493216521257845245913 9157869912390943383934435)
              ·
                refine ⟨13736804868586415075901653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157869912390943383934435 13736804868586415075901653)
                ·
                  refine ⟨321956364107494103341445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13736804868586415075901653 321956364107494103341445)
                  ·
                    rfl

theorem cell22_2821535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 7].length) (baseStart_2821535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821535 prefixEnd_2821535 := by exact prefixLift 2821535
  have htrace : WordTrace (prefixWord ++ tailWord_2821535) baseStart_2821535 baseEnd_2821535 := by
    simpa [prefixWord, tailWord_2821535, baseEnd_2821535] using wordTrace_append hprefix tailTrace_2821535
  have hstable : (prefixWord ++ tailWord_2821535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821535).length < 2 ^ (prefixWord ++ tailWord_2821535).sum := by decide
  have hdescent : baseEnd_2821535 < baseStart_2821535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821582 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_2821582 : Nat := 118140960795 + 2821582 * 2 ^ 59
def prefixEnd_2821582 : Nat := 4983230072969 + 3 ^ 40 * 2821582 * 2
def baseEnd_2821582 : Nat := 965885181382989854099191

theorem tailTrace_2821582 : CollatzResearch.WordTrace tailWord_2821582 prefixEnd_2821582 965885181382989854099191 := by
  unfold tailWord_2821582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863943757987222085707375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68607700042598517790439333 12863943757987222085707375)
  ·
    refine ⟨19295915636980833128561063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12863943757987222085707375 19295915636980833128561063)
    ·
      refine ⟨28943873455471249692841595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19295915636980833128561063 28943873455471249692841595)
      ·
        refine ⟨43415810183206874539262393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28943873455471249692841595 43415810183206874539262393)
        ·
          refine ⟨32561857637405155904446795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43415810183206874539262393 32561857637405155904446795)
          ·
            refine ⟨48842786456107733856670193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32561857637405155904446795 48842786456107733856670193)
            ·
              refine ⟨36632089842080800392502645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48842786456107733856670193 36632089842080800392502645)
              ·
                refine ⟨3434258422695075036797123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36632089842080800392502645 3434258422695075036797123)
                ·
                  refine ⟨5151387634042612555195685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434258422695075036797123 5151387634042612555195685)
                  ·
                    refine ⟨965885181382989854099191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5151387634042612555195685 965885181382989854099191)
                    ·
                      rfl

theorem cell22_2821582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_2821582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821582 prefixEnd_2821582 := by exact prefixLift 2821582
  have htrace : WordTrace (prefixWord ++ tailWord_2821582) baseStart_2821582 baseEnd_2821582 := by
    simpa [prefixWord, tailWord_2821582, baseEnd_2821582] using wordTrace_append hprefix tailTrace_2821582
  have hstable : (prefixWord ++ tailWord_2821582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821582).length < 2 ^ (prefixWord ++ tailWord_2821582).sum := by decide
  have hdescent : baseEnd_2821582 < baseStart_2821582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821590 : List Nat := [5, 2, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2821590 : Nat := 118140960795 + 2821590 * 2 ^ 59
def prefixEnd_2821590 : Nat := 4983230072969 + 3 ^ 40 * 2821590 * 2
def baseEnd_2821590 : Nat := 965887919946480499899167

theorem tailTrace_2821590 : CollatzResearch.WordTrace tailWord_2821590 prefixEnd_2821590 965887919946480499899167 := by
  unfold tailWord_2821590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6431990115491799628246889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68607894565245862701300149 6431990115491799628246889)
  ·
    refine ⟨4823992586618849721185167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6431990115491799628246889 4823992586618849721185167)
    ·
      refine ⟨7235988879928274581777751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4823992586618849721185167 7235988879928274581777751)
      ·
        refine ⟨10853983319892411872666627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7235988879928274581777751 10853983319892411872666627)
        ·
          refine ⟨16280974979838617808999941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10853983319892411872666627 16280974979838617808999941)
          ·
            refine ⟨3052682808719740839187489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16280974979838617808999941 3052682808719740839187489)
            ·
              refine ⟨2289512106539805629390617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052682808719740839187489 2289512106539805629390617)
              ·
                refine ⟨1717134079904854222042963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289512106539805629390617 1717134079904854222042963)
                ·
                  refine ⟨2575701119857281333064445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717134079904854222042963 2575701119857281333064445)
                  ·
                    refine ⟨965887919946480499899167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2575701119857281333064445 965887919946480499899167)
                    ·
                      rfl

theorem cell22_2821590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2821590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821590 prefixEnd_2821590 := by exact prefixLift 2821590
  have htrace : WordTrace (prefixWord ++ tailWord_2821590) baseStart_2821590 baseEnd_2821590 := by
    simpa [prefixWord, tailWord_2821590, baseEnd_2821590] using wordTrace_append hprefix tailTrace_2821590
  have hstable : (prefixWord ++ tailWord_2821590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821590).length < 2 ^ (prefixWord ++ tailWord_2821590).sum := by decide
  have hdescent : baseEnd_2821590 < baseStart_2821590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821633 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2821633 : Nat := 118140960795 + 2821633 * 2 ^ 59
def prefixEnd_2821633 : Nat := 4983230072969 + 3 ^ 40 * 2821633 * 2
def baseEnd_2821633 : Nat := 965902639725242721074035

theorem tailTrace_2821633 : CollatzResearch.WordTrace tailWord_2821633 prefixEnd_2821633 965902639725242721074035 := by
  unfold tailWord_2821633
  simp only [CollatzResearch.WordTrace]
  refine ⟨102913410186713012395765553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68608940124475341597177035 102913410186713012395765553)
  ·
    refine ⟨77185057640034759296824165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102913410186713012395765553 77185057640034759296824165)
    ·
      refine ⟨14472198307506517368154531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77185057640034759296824165 14472198307506517368154531)
      ·
        refine ⟨21708297461259776052231797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14472198307506517368154531 21708297461259776052231797)
        ·
          refine ⟨2035152886993104004896731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21708297461259776052231797 2035152886993104004896731)
          ·
            refine ⟨3052729330489656007345097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035152886993104004896731 3052729330489656007345097)
            ·
              refine ⟨2289546997867242005508823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052729330489656007345097 2289546997867242005508823)
              ·
                refine ⟨3434320496800863008263235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289546997867242005508823 3434320496800863008263235)
                ·
                  refine ⟨5151480745201294512394853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434320496800863008263235 5151480745201294512394853)
                  ·
                    refine ⟨965902639725242721074035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5151480745201294512394853 965902639725242721074035)
                    ·
                      rfl

theorem cell22_2821633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2821633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821633 prefixEnd_2821633 := by exact prefixLift 2821633
  have htrace : WordTrace (prefixWord ++ tailWord_2821633) baseStart_2821633 baseEnd_2821633 := by
    simpa [prefixWord, tailWord_2821633, baseEnd_2821633] using wordTrace_append hprefix tailTrace_2821633
  have hstable : (prefixWord ++ tailWord_2821633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821633).length < 2 ^ (prefixWord ++ tailWord_2821633).sum := by decide
  have hdescent : baseEnd_2821633 < baseStart_2821633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821674 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2821674 : Nat := 118140960795 + 2821674 * 2 ^ 59
def prefixEnd_2821674 : Nat := 4983230072969 + 3 ^ 40 * 2821674 * 2
def baseEnd_2821674 : Nat := 965916674863132280798909

theorem tailTrace_2821674 : CollatzResearch.WordTrace tailWord_2821674 prefixEnd_2821674 965916674863132280798909 := by
  unfold tailWord_2821674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25728726394891119099502019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68609937053042984265338717 25728726394891119099502019)
  ·
    refine ⟨38593089592336678649253029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25728726394891119099502019 38593089592336678649253029)
    ·
      refine ⟨7236204298563127246734943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38593089592336678649253029 7236204298563127246734943)
      ·
        refine ⟨10854306447844690870102415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7236204298563127246734943 10854306447844690870102415)
        ·
          refine ⟨16281459671767036305153623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10854306447844690870102415 16281459671767036305153623)
          ·
            refine ⟨24422189507650554457730435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16281459671767036305153623 24422189507650554457730435)
            ·
              refine ⟨36633284261475831686595653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24422189507650554457730435 36633284261475831686595653)
              ·
                refine ⟨6868740799026718441236685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36633284261475831686595653 6868740799026718441236685)
                ·
                  refine ⟨2575777799635019415463757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6868740799026718441236685 2575777799635019415463757)
                  ·
                    refine ⟨965916674863132280798909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2575777799635019415463757 965916674863132280798909)
                    ·
                      rfl

theorem cell22_2821674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2821674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821674 prefixEnd_2821674 := by exact prefixLift 2821674
  have htrace : WordTrace (prefixWord ++ tailWord_2821674) baseStart_2821674 baseEnd_2821674 := by
    simpa [prefixWord, tailWord_2821674, baseEnd_2821674] using wordTrace_append hprefix tailTrace_2821674
  have hstable : (prefixWord ++ tailWord_2821674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821674).length < 2 ^ (prefixWord ++ tailWord_2821674).sum := by decide
  have hdescent : baseEnd_2821674 < baseStart_2821674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821708 : List Nat := [2, 2, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_2821708 : Nat := 118140960795 + 2821708 * 2 ^ 59
def prefixEnd_2821708 : Nat := 4983230072969 + 3 ^ 40 * 2821708 * 2
def baseEnd_2821708 : Nat := 965928313757967525448805

theorem tailTrace_2821708 : CollatzResearch.WordTrace tailWord_2821708 prefixEnd_2821708 965928313757967525448805 := by
  unfold tailWord_2821708
  simp only [CollatzResearch.WordTrace]
  refine ⟨51458072830720650102372889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68610763774294200136497185 51458072830720650102372889)
  ·
    refine ⟨38593554623040487576779667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51458072830720650102372889 38593554623040487576779667)
    ·
      refine ⟨57890331934560731365169501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38593554623040487576779667 57890331934560731365169501)
      ·
        refine ⟨21708874475460274261938563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57890331934560731365169501 21708874475460274261938563)
        ·
          refine ⟨32563311713190411392907845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21708874475460274261938563 32563311713190411392907845)
          ·
            refine ⟨6105620946223202136170221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32563311713190411392907845 6105620946223202136170221)
            ·
              refine ⟨2289607854833700801063833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6105620946223202136170221 2289607854833700801063833)
              ·
                refine ⟨1717205891125275600797875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289607854833700801063833 1717205891125275600797875)
                ·
                  refine ⟨2575808836687913401196813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717205891125275600797875 2575808836687913401196813)
                  ·
                    refine ⟨965928313757967525448805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2575808836687913401196813 965928313757967525448805)
                    ·
                      rfl

theorem cell22_2821708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_2821708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821708 prefixEnd_2821708 := by exact prefixLift 2821708
  have htrace : WordTrace (prefixWord ++ tailWord_2821708) baseStart_2821708 baseEnd_2821708 := by
    simpa [prefixWord, tailWord_2821708, baseEnd_2821708] using wordTrace_append hprefix tailTrace_2821708
  have hstable : (prefixWord ++ tailWord_2821708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821708).length < 2 ^ (prefixWord ++ tailWord_2821708).sum := by decide
  have hdescent : baseEnd_2821708 < baseStart_2821708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821715 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 12]
def baseStart_2821715 : Nat := 118140960795 + 2821715 * 2 ^ 59
def prefixEnd_2821715 : Nat := 4983230072969 + 3 ^ 40 * 2821715 * 2
def baseEnd_2821715 : Nat := 321976903333673946841261

theorem tailTrace_2821715 : CollatzResearch.WordTrace tailWord_2821715 prefixEnd_2821715 321976903333673946841261 := by
  unfold tailWord_2821715
  simp only [CollatzResearch.WordTrace]
  refine ⟨102916400972415940400250599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68610933981610626933500399 102916400972415940400250599)
  ·
    refine ⟨154374601458623910600375899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102916400972415940400250599 154374601458623910600375899)
    ·
      refine ⟨231561902187935865900563849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154374601458623910600375899 231561902187935865900563849)
      ·
        refine ⟨173671426640951899425422887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231561902187935865900563849 173671426640951899425422887)
        ·
          refine ⟨260507139961427849138134331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173671426640951899425422887 260507139961427849138134331)
          ·
            refine ⟨390760709942141773707201497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260507139961427849138134331 390760709942141773707201497)
            ·
              refine ⟨293070532456606330280401123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390760709942141773707201497 293070532456606330280401123)
              ·
                refine ⟨439605798684909495420601685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293070532456606330280401123 439605798684909495420601685)
                ·
                  refine ⟨321976903333673946841261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 439605798684909495420601685 321976903333673946841261)
                  ·
                    rfl

theorem cell22_2821715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_2821715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821715 prefixEnd_2821715 := by exact prefixLift 2821715
  have htrace : WordTrace (prefixWord ++ tailWord_2821715) baseStart_2821715 baseEnd_2821715 := by
    simpa [prefixWord, tailWord_2821715, baseEnd_2821715] using wordTrace_append hprefix tailTrace_2821715
  have hstable : (prefixWord ++ tailWord_2821715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821715).length < 2 ^ (prefixWord ++ tailWord_2821715).sum := by decide
  have hdescent : baseEnd_2821715 < baseStart_2821715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821717 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2821717 : Nat := 118140960795 + 2821717 * 2 ^ 59
def prefixEnd_2821717 : Nat := 4983230072969 + 3 ^ 40 * 2821717 * 2
def baseEnd_2821717 : Nat := 965931394641894501973777

theorem tailTrace_2821717 : CollatzResearch.WordTrace tailWord_2821717 prefixEnd_2821717 965931394641894501973777 := by
  unfold tailWord_2821717
  simp only [CollatzResearch.WordTrace]
  refine ⟨102916473918408694741823405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68610982612272463161215603 102916473918408694741823405)
  ·
    refine ⟨38593677719403260528183777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102916473918408694741823405 38593677719403260528183777)
    ·
      refine ⟨28945258289552445396137833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38593677719403260528183777 28945258289552445396137833)
      ·
        refine ⟨21708943717164334047103375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28945258289552445396137833 21708943717164334047103375)
        ·
          refine ⟨32563415575746501070655063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21708943717164334047103375 32563415575746501070655063)
          ·
            refine ⟨48845123363619751605982595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32563415575746501070655063 48845123363619751605982595)
            ·
              refine ⟨73267685045429627408973893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48845123363619751605982595 73267685045429627408973893)
              ·
                refine ⟨13737690946018055139182605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73267685045429627408973893 13737690946018055139182605)
                ·
                  refine ⟨5151634104756770677193477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13737690946018055139182605 5151634104756770677193477)
                  ·
                    refine ⟨965931394641894501973777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5151634104756770677193477 965931394641894501973777)
                    ·
                      rfl

theorem cell22_2821717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2821717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821717 prefixEnd_2821717 := by exact prefixLift 2821717
  have htrace : WordTrace (prefixWord ++ tailWord_2821717) baseStart_2821717 baseEnd_2821717 := by
    simpa [prefixWord, tailWord_2821717, baseEnd_2821717] using wordTrace_append hprefix tailTrace_2821717
  have hstable : (prefixWord ++ tailWord_2821717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821717).length < 2 ^ (prefixWord ++ tailWord_2821717).sum := by decide
  have hdescent : baseEnd_2821717 < baseStart_2821717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821796 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_2821796 : Nat := 118140960795 + 2821796 * 2 ^ 59
def prefixEnd_2821796 : Nat := 4983230072969 + 3 ^ 40 * 2821796 * 2
def baseEnd_2821796 : Nat := 965958437956364629248535

theorem tailTrace_2821796 : CollatzResearch.WordTrace tailWord_2821796 prefixEnd_2821796 965958437956364629248535 := by
  unfold tailWord_2821796
  simp only [CollatzResearch.WordTrace]
  refine ⟨51459677642561245616974621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68612903523414994155966161 51459677642561245616974621)
  ·
    refine ⟨19297379115960467106365483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51459677642561245616974621 19297379115960467106365483)
    ·
      refine ⟨28946068673940700659548225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19297379115960467106365483 28946068673940700659548225)
      ·
        refine ⟨21709551505455525494661169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28946068673940700659548225 21709551505455525494661169)
        ·
          refine ⟨16282163629091644120995877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21709551505455525494661169 16282163629091644120995877)
          ·
            refine ⟨3052905680454683272686727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16282163629091644120995877 3052905680454683272686727)
            ·
              refine ⟨4579358520682024909030091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052905680454683272686727 4579358520682024909030091)
              ·
                refine ⟨6869037781023037363545137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579358520682024909030091 6869037781023037363545137)
                ·
                  refine ⟨5151778335767278022658853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6869037781023037363545137 5151778335767278022658853)
                  ·
                    refine ⟨965958437956364629248535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5151778335767278022658853 965958437956364629248535)
                    ·
                      rfl

theorem cell22_2821796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_2821796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821796 prefixEnd_2821796 := by exact prefixLift 2821796
  have htrace : WordTrace (prefixWord ++ tailWord_2821796) baseStart_2821796 baseEnd_2821796 := by
    simpa [prefixWord, tailWord_2821796, baseEnd_2821796] using wordTrace_append hprefix tailTrace_2821796
  have hstable : (prefixWord ++ tailWord_2821796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821796).length < 2 ^ (prefixWord ++ tailWord_2821796).sum := by decide
  have hdescent : baseEnd_2821796 < baseStart_2821796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821867 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 8]
def baseStart_2821867 : Nat := 118140960795 + 2821867 * 2 ^ 59
def prefixEnd_2821867 : Nat := 4983230072969 + 3 ^ 40 * 2821867 * 2
def baseEnd_2821867 : Nat := 321994247569114703574439

theorem tailTrace_2821867 : CollatzResearch.WordTrace tailWord_2821867 prefixEnd_2821867 321994247569114703574439 := by
  unfold tailWord_2821867
  simp only [CollatzResearch.WordTrace]
  refine ⟨102921944867865270359783855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68614629911910180239855903 102921944867865270359783855)
  ·
    refine ⟨154382917301797905539675783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102921944867865270359783855 154382917301797905539675783)
    ·
      refine ⟨231574375952696858309513675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154382917301797905539675783 231574375952696858309513675)
      ·
        refine ⟨347361563929045287464270513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231574375952696858309513675 347361563929045287464270513)
        ·
          refine ⟨260521172946783965598202885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347361563929045287464270513 260521172946783965598202885)
          ·
            refine ⟨48847719927521993549663041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260521172946783965598202885 48847719927521993549663041)
            ·
              refine ⟨36635789945641495162247281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48847719927521993549663041 36635789945641495162247281)
              ·
                refine ⟨27476842459231121371685461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36635789945641495162247281 27476842459231121371685461)
                ·
                  refine ⟨321994247569114703574439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27476842459231121371685461 321994247569114703574439)
                  ·
                    rfl

theorem cell22_2821867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_2821867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821867 prefixEnd_2821867 := by exact prefixLift 2821867
  have htrace : WordTrace (prefixWord ++ tailWord_2821867) baseStart_2821867 baseEnd_2821867 := by
    simpa [prefixWord, tailWord_2821867, baseEnd_2821867] using wordTrace_append hprefix tailTrace_2821867
  have hstable : (prefixWord ++ tailWord_2821867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821867).length < 2 ^ (prefixWord ++ tailWord_2821867).sum := by decide
  have hdescent : baseEnd_2821867 < baseStart_2821867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821946 : List Nat := [3, 1, 1, 1, 5, 3, 1, 7]
def baseStart_2821946 : Nat := 118140960795 + 2821946 * 2 ^ 59
def prefixEnd_2821946 : Nat := 4983230072969 + 3 ^ 40 * 2821946 * 2
def baseEnd_2821946 : Nat := 107334420669090470888675

theorem tailTrace_2821946 : CollatzResearch.WordTrace tailWord_2821946 prefixEnd_2821946 107334420669090470888675 := by
  unfold tailWord_2821946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25731206558644766712977423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68616550823052711234606461 25731206558644766712977423)
  ·
    refine ⟨38596809837967150069466135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25731206558644766712977423 38596809837967150069466135)
    ·
      refine ⟨57895214756950725104199203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38596809837967150069466135 57895214756950725104199203)
      ·
        refine ⟨86842822135426087656298805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57895214756950725104199203 86842822135426087656298805)
        ·
          refine ⟨8141514575196195717778013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86842822135426087656298805 8141514575196195717778013)
          ·
            refine ⟨3053067965698573394166755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8141514575196195717778013 3053067965698573394166755)
            ·
              refine ⟨4579601948547860091250133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053067965698573394166755 4579601948547860091250133)
              ·
                refine ⟨107334420669090470888675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4579601948547860091250133 107334420669090470888675)
                ·
                  rfl

theorem cell22_2821946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_2821946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821946 prefixEnd_2821946 := by exact prefixLift 2821946
  have htrace : WordTrace (prefixWord ++ tailWord_2821946) baseStart_2821946 baseEnd_2821946 := by
    simpa [prefixWord, tailWord_2821946, baseEnd_2821946] using wordTrace_append hprefix tailTrace_2821946
  have hstable : (prefixWord ++ tailWord_2821946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821946).length < 2 ^ (prefixWord ++ tailWord_2821946).sum := by decide
  have hdescent : baseEnd_2821946 < baseStart_2821946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821961 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 3, 3]
def baseStart_2821961 : Nat := 118140960795 + 2821961 * 2 ^ 59
def prefixEnd_2821961 : Nat := 4983230072969 + 3 ^ 40 * 2821961 * 2
def baseEnd_2821961 : Nat := 966014920828359198873029

theorem tailTrace_2821961 : CollatzResearch.WordTrace tailWord_2821961 prefixEnd_2821961 966014920828359198873029 := by
  unfold tailWord_2821961
  simp only [CollatzResearch.WordTrace]
  refine ⟨102925373329524724413705737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68616915553016482942470491 102925373329524724413705737)
  ·
    refine ⟨77194029997143543310279303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102925373329524724413705737 77194029997143543310279303)
    ·
      refine ⟨115791044995715314965418955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77194029997143543310279303 115791044995715314965418955)
      ·
        refine ⟨173686567493572972448128433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115791044995715314965418955 173686567493572972448128433)
        ·
          refine ⟨130264925620179729336096325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173686567493572972448128433 130264925620179729336096325)
          ·
            refine ⟨24424673553783699250518061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130264925620179729336096325 24424673553783699250518061)
            ·
              refine ⟨9159252582668887218944273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24424673553783699250518061 9159252582668887218944273)
              ·
                refine ⟨6869439437001665414208205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9159252582668887218944273 6869439437001665414208205)
                ·
                  refine ⟨2576039788875624530328077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6869439437001665414208205 2576039788875624530328077)
                  ·
                    refine ⟨966014920828359198873029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576039788875624530328077 966014920828359198873029)
                    ·
                      rfl

theorem cell22_2821961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_2821961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821961 prefixEnd_2821961 := by exact prefixLift 2821961
  have htrace : WordTrace (prefixWord ++ tailWord_2821961) baseStart_2821961 baseEnd_2821961 := by
    simpa [prefixWord, tailWord_2821961, baseEnd_2821961] using wordTrace_append hprefix tailTrace_2821961
  have hstable : (prefixWord ++ tailWord_2821961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821961).length < 2 ^ (prefixWord ++ tailWord_2821961).sum := by decide
  have hdescent : baseEnd_2821961 < baseStart_2821961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821965 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2821965 : Nat := 118140960795 + 2821965 * 2 ^ 59
def prefixEnd_2821965 : Nat := 4983230072969 + 3 ^ 40 * 2821965 * 2
def baseEnd_2821965 : Nat := 966016290110104521773017

theorem tailTrace_2821965 : CollatzResearch.WordTrace tailWord_2821965 prefixEnd_2821965 966016290110104521773017 := by
  unfold tailWord_2821965
  simp only [CollatzResearch.WordTrace]
  refine ⟨102925519221510233096851349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68617012814340155397900899 102925519221510233096851349)
  ·
    refine ⟨4824633713508292176414907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102925519221510233096851349 4824633713508292176414907)
    ·
      refine ⟨7236950570262438264622361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824633713508292176414907 7236950570262438264622361)
      ·
        refine ⟨5427712927696828698466771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7236950570262438264622361 5427712927696828698466771)
        ·
          refine ⟨8141569391545243047700157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427712927696828698466771 8141569391545243047700157)
          ·
            refine ⟨3053088521829466142887559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8141569391545243047700157 3053088521829466142887559)
            ·
              refine ⟨4579632782744199214331339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053088521829466142887559 4579632782744199214331339)
              ·
                refine ⟨6869449174116298821497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579632782744199214331339 6869449174116298821497009)
                ·
                  refine ⟨5152086880587224116122757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6869449174116298821497009 5152086880587224116122757)
                  ·
                    refine ⟨966016290110104521773017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152086880587224116122757 966016290110104521773017)
                    ·
                      rfl

theorem cell22_2821965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2821965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2821965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2821965 prefixEnd_2821965 := by exact prefixLift 2821965
  have htrace : WordTrace (prefixWord ++ tailWord_2821965) baseStart_2821965 baseEnd_2821965 := by
    simpa [prefixWord, tailWord_2821965, baseEnd_2821965] using wordTrace_append hprefix tailTrace_2821965
  have hstable : (prefixWord ++ tailWord_2821965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821965).length < 2 ^ (prefixWord ++ tailWord_2821965).sum := by decide
  have hdescent : baseEnd_2821965 < baseStart_2821965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822046 : List Nat := [4, 3, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2822046 : Nat := 118140960795 + 2822046 * 2 ^ 59
def prefixEnd_2822046 : Nat := 4983230072969 + 3 ^ 40 * 2822046 * 2
def baseEnd_2822046 : Nat := 966044018065447310497769

theorem tailTrace_2822046 : CollatzResearch.WordTrace tailWord_2822046 prefixEnd_2822046 966044018065447310497769 := by
  unfold tailWord_2822046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12866059191777097991318749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68618982356144522620366661 12866059191777097991318749)
  ·
    refine ⟨4824772196916411746744531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12866059191777097991318749 4824772196916411746744531)
    ·
      refine ⟨7237158295374617620116797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4824772196916411746744531 7237158295374617620116797)
      ·
        refine ⟨2713934360765481607543799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7237158295374617620116797 2713934360765481607543799)
        ·
          refine ⟨4070901541148222411315699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713934360765481607543799 4070901541148222411315699)
          ·
            refine ⟨6106352311722333616973549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070901541148222411315699 6106352311722333616973549)
            ·
              refine ⟨2289882116895875106365081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6106352311722333616973549 2289882116895875106365081)
              ·
                refine ⟨1717411587671906329773811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289882116895875106365081 1717411587671906329773811)
                ·
                  refine ⟨2576117381507859494660717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717411587671906329773811 2576117381507859494660717)
                  ·
                    refine ⟨966044018065447310497769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576117381507859494660717 966044018065447310497769)
                    ·
                      rfl

theorem cell22_2822046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2822046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822046 prefixEnd_2822046 := by exact prefixLift 2822046
  have htrace : WordTrace (prefixWord ++ tailWord_2822046) baseStart_2822046 baseEnd_2822046 := by
    simpa [prefixWord, tailWord_2822046, baseEnd_2822046] using wordTrace_append hprefix tailTrace_2822046
  have hstable : (prefixWord ++ tailWord_2822046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822046).length < 2 ^ (prefixWord ++ tailWord_2822046).sum := by decide
  have hdescent : baseEnd_2822046 < baseStart_2822046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822098 : List Nat := [3, 2, 2, 3, 3, 9]
def baseStart_2822098 : Nat := 118140960795 + 2822098 * 2 ^ 59
def prefixEnd_2822098 : Nat := 4983230072969 + 3 ^ 40 * 2822098 * 2
def baseEnd_2822098 : Nat := 11926689120100450718489

theorem tailTrace_2822098 : CollatzResearch.WordTrace tailWord_2822098 prefixEnd_2822098 11926689120100450718489 := by
  unfold tailWord_2822098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25732592532507099202860737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68620246753352264540961965 25732592532507099202860737)
  ·
    refine ⟨19299444399380324402145553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25732592532507099202860737 19299444399380324402145553)
    ·
      refine ⟨14474583299535243301609165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19299444399380324402145553 14474583299535243301609165)
      ·
        refine ⟨5427968737325716238103437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14474583299535243301609165 5427968737325716238103437)
        ·
          refine ⟨2035488276497143589288789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5427968737325716238103437 2035488276497143589288789)
          ·
            refine ⟨11926689120100450718489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2035488276497143589288789 11926689120100450718489)
            ·
              rfl

theorem cell22_2822098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 9].length) (baseStart_2822098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822098 prefixEnd_2822098 := by exact prefixLift 2822098
  have htrace : WordTrace (prefixWord ++ tailWord_2822098) baseStart_2822098 baseEnd_2822098 := by
    simpa [prefixWord, tailWord_2822098, baseEnd_2822098] using wordTrace_append hprefix tailTrace_2822098
  have hstable : (prefixWord ++ tailWord_2822098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822098).length < 2 ^ (prefixWord ++ tailWord_2822098).sum := by decide
  have hdescent : baseEnd_2822098 < baseStart_2822098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822111 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 2, 6]
def baseStart_2822111 : Nat := 118140960795 + 2822111 * 2 ^ 59
def prefixEnd_2822111 : Nat := 4983230072969 + 3 ^ 40 * 2822111 * 2
def baseEnd_2822111 : Nat := 966066268893808807622569

theorem tailTrace_2822111 : CollatzResearch.WordTrace tailWord_2822111 prefixEnd_2822111 966066268893808807622569 := by
  unfold tailWord_2822111
  simp only [CollatzResearch.WordTrace]
  refine ⟨102930844278981300031666187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68620562852654200021110791 102930844278981300031666187)
  ·
    refine ⟨154396266418471950047499281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102930844278981300031666187 154396266418471950047499281)
    ·
      refine ⟨115797199813853962535624461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154396266418471950047499281 115797199813853962535624461)
      ·
        refine ⟨43423949930195235950859173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115797199813853962535624461 43423949930195235950859173)
        ·
          refine ⟨8141990611911606740786095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43423949930195235950859173 8141990611911606740786095)
          ·
            refine ⟨12212985917867410111179143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8141990611911606740786095 12212985917867410111179143)
            ·
              refine ⟨18319478876801115166768715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12212985917867410111179143 18319478876801115166768715)
              ·
                refine ⟨27479218315201672750153073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18319478876801115166768715 27479218315201672750153073)
                ·
                  refine ⟨20609413736401254562614805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27479218315201672750153073 20609413736401254562614805)
                  ·
                    refine ⟨966066268893808807622569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20609413736401254562614805 966066268893808807622569)
                    ·
                      rfl

theorem cell22_2822111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_2822111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822111 prefixEnd_2822111 := by exact prefixLift 2822111
  have htrace : WordTrace (prefixWord ++ tailWord_2822111) baseStart_2822111 baseEnd_2822111 := by
    simpa [prefixWord, tailWord_2822111, baseEnd_2822111] using wordTrace_append hprefix tailTrace_2822111
  have hstable : (prefixWord ++ tailWord_2822111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822111).length < 2 ^ (prefixWord ++ tailWord_2822111).sum := by decide
  have hdescent : baseEnd_2822111 < baseStart_2822111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822164 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2822164 : Nat := 118140960795 + 2822164 * 2 ^ 59
def prefixEnd_2822164 : Nat := 4983230072969 + 3 ^ 40 * 2822164 * 2
def baseEnd_2822164 : Nat := 966084411876934336047407

theorem tailTrace_2822164 : CollatzResearch.WordTrace tailWord_2822164 prefixEnd_2822164 966084411876934336047407 := by
  unfold tailWord_2822164
  simp only [CollatzResearch.WordTrace]
  refine ⟨51466388673894645041672773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68621851565192860055563697 51466388673894645041672773)
  ·
    refine ⟨9649947876355245945313645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51466388673894645041672773 9649947876355245945313645)
    ·
      refine ⟨3618730453633217229492617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9649947876355245945313645 3618730453633217229492617)
      ·
        refine ⟨2714047840224912922119463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3618730453633217229492617 2714047840224912922119463)
        ·
          refine ⟨4071071760337369383179195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714047840224912922119463 4071071760337369383179195)
          ·
            refine ⟨6106607640506054074768793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071071760337369383179195 6106607640506054074768793)
            ·
              refine ⟨4579955730379540556076595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106607640506054074768793 4579955730379540556076595)
              ·
                refine ⟨6869933595569310834114893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579955730379540556076595 6869933595569310834114893)
                ·
                  refine ⟨2576225098338491562793085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6869933595569310834114893 2576225098338491562793085)
                  ·
                    refine ⟨966084411876934336047407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576225098338491562793085 966084411876934336047407)
                    ·
                      rfl

theorem cell22_2822164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2822164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822164 prefixEnd_2822164 := by exact prefixLift 2822164
  have htrace : WordTrace (prefixWord ++ tailWord_2822164) baseStart_2822164 baseEnd_2822164 := by
    simpa [prefixWord, tailWord_2822164, baseEnd_2822164] using wordTrace_append hprefix tailTrace_2822164
  have hstable : (prefixWord ++ tailWord_2822164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822164).length < 2 ^ (prefixWord ++ tailWord_2822164).sum := by decide
  have hdescent : baseEnd_2822164 < baseStart_2822164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822190 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2822190 : Nat := 118140960795 + 2822190 * 2 ^ 59
def prefixEnd_2822190 : Nat := 4983230072969 + 3 ^ 40 * 2822190 * 2
def baseEnd_2822190 : Nat := 966093312208278934897327

theorem tailTrace_2822190 : CollatzResearch.WordTrace tailWord_2822190 prefixEnd_2822190 966093312208278934897327 := by
  unfold tailWord_2822190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12866715705711887065474003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68622483763796731015861349 12866715705711887065474003)
  ·
    refine ⟨19300073558567830598211005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12866715705711887065474003 19300073558567830598211005)
    ·
      refine ⟨7237527584462936474329127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19300073558567830598211005 7237527584462936474329127)
      ·
        refine ⟨10856291376694404711493691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7237527584462936474329127 10856291376694404711493691)
        ·
          refine ⟨16284437065041607067240537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10856291376694404711493691 16284437065041607067240537)
          ·
            refine ⟨12213327798781205300430403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16284437065041607067240537 12213327798781205300430403)
            ·
              refine ⟨18319991698171807950645605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12213327798781205300430403 18319991698171807950645605)
              ·
                refine ⟨3434998443407213990746051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18319991698171807950645605 3434998443407213990746051)
                ·
                  refine ⟨5152497665110820986119077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434998443407213990746051 5152497665110820986119077)
                  ·
                    refine ⟨966093312208278934897327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152497665110820986119077 966093312208278934897327)
                    ·
                      rfl

theorem cell22_2822190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2822190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822190 prefixEnd_2822190 := by exact prefixLift 2822190
  have htrace : WordTrace (prefixWord ++ tailWord_2822190) baseStart_2822190 baseEnd_2822190 := by
    simpa [prefixWord, tailWord_2822190, baseEnd_2822190] using wordTrace_append hprefix tailTrace_2822190
  have hstable : (prefixWord ++ tailWord_2822190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822190).length < 2 ^ (prefixWord ++ tailWord_2822190).sum := by decide
  have hdescent : baseEnd_2822190 < baseStart_2822190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822222 : List Nat := [4, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_2822222 : Nat := 118140960795 + 2822222 * 2 ^ 59
def prefixEnd_2822222 : Nat := 4983230072969 + 3 ^ 40 * 2822222 * 2
def baseEnd_2822222 : Nat := 322034755487413839365743

theorem tailTrace_2822222 : CollatzResearch.WordTrace tailWord_2822222 prefixEnd_2822222 322034755487413839365743 := by
  unfold tailWord_2822222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12866861597697395748619615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68623261854386110659304613 12866861597697395748619615)
  ·
    refine ⟨19300292396546093622929423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12866861597697395748619615 19300292396546093622929423)
    ·
      refine ⟨28950438594819140434394135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19300292396546093622929423 28950438594819140434394135)
      ·
        refine ⟨43425657892228710651591203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28950438594819140434394135 43425657892228710651591203)
        ·
          refine ⟨65138486838343065977386805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43425657892228710651591203 65138486838343065977386805)
          ·
            refine ⟨6106733141094662435380013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65138486838343065977386805 6106733141094662435380013)
            ·
              refine ⟨2290024927910498413267505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6106733141094662435380013 2290024927910498413267505)
              ·
                refine ⟨1717518695932873809950629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290024927910498413267505 1717518695932873809950629)
                ·
                  refine ⟨322034755487413839365743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717518695932873809950629 322034755487413839365743)
                  ·
                    rfl

theorem cell22_2822222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_2822222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822222 prefixEnd_2822222 := by exact prefixLift 2822222
  have htrace : WordTrace (prefixWord ++ tailWord_2822222) baseStart_2822222 baseEnd_2822222 := by
    simpa [prefixWord, tailWord_2822222, baseEnd_2822222] using wordTrace_append hprefix tailTrace_2822222
  have hstable : (prefixWord ++ tailWord_2822222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822222).length < 2 ^ (prefixWord ++ tailWord_2822222).sum := by decide
  have hdescent : baseEnd_2822222 < baseStart_2822222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822293 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2822293 : Nat := 118140960795 + 2822293 * 2 ^ 59
def prefixEnd_2822293 : Nat := 4983230072969 + 3 ^ 40 * 2822293 * 2
def baseEnd_2822293 : Nat := 966128571213220999572011

theorem tailTrace_2822293 : CollatzResearch.WordTrace tailWord_2822293 prefixEnd_2822293 966128571213220999572011 := by
  unfold tailWord_2822293
  simp only [CollatzResearch.WordTrace]
  refine ⟨102937482364321945114791533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68624988242881296743194355 102937482364321945114791533)
  ·
    refine ⟨38601555886620729418046825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102937482364321945114791533 38601555886620729418046825)
    ·
      refine ⟨28951166914965547063535119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38601555886620729418046825 28951166914965547063535119)
      ·
        refine ⟨43426750372448320595302679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28951166914965547063535119 43426750372448320595302679)
        ·
          refine ⟨65140125558672480892954019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43426750372448320595302679 65140125558672480892954019)
          ·
            refine ⟨97710188338008721339431029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65140125558672480892954019 97710188338008721339431029)
            ·
              refine ⟨9160330156688317625571659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97710188338008721339431029 9160330156688317625571659)
              ·
                refine ⟨13740495235032476438357489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9160330156688317625571659 13740495235032476438357489)
                ·
                  refine ⟨10305371426274357328768117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13740495235032476438357489 10305371426274357328768117)
                  ·
                    refine ⟨966128571213220999572011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10305371426274357328768117 966128571213220999572011)
                    ·
                      rfl

theorem cell22_2822293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2822293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822293 prefixEnd_2822293 := by exact prefixLift 2822293
  have htrace : WordTrace (prefixWord ++ tailWord_2822293) baseStart_2822293 baseEnd_2822293 := by
    simpa [prefixWord, tailWord_2822293, baseEnd_2822293] using wordTrace_append hprefix tailTrace_2822293
  have hstable : (prefixWord ++ tailWord_2822293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822293).length < 2 ^ (prefixWord ++ tailWord_2822293).sum := by decide
  have hdescent : baseEnd_2822293 < baseStart_2822293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822340 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 6]
def baseStart_2822340 : Nat := 118140960795 + 2822340 * 2 ^ 59
def prefixEnd_2822340 : Nat := 4983230072969 + 3 ^ 40 * 2822340 * 2
def baseEnd_2822340 : Nat := 322048220091242847882289

theorem tailTrace_2822340 : CollatzResearch.WordTrace tailWord_2822340 prefixEnd_2822340 322048220091242847882289 := by
  unfold tailWord_2822340
  simp only [CollatzResearch.WordTrace]
  refine ⟨51469598297575836070876237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68626131063434448094501649 51469598297575836070876237)
  ·
    refine ⟨19301099361590938526578589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51469598297575836070876237 19301099361590938526578589)
    ·
      refine ⟨7237912260596601947466971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19301099361590938526578589 7237912260596601947466971)
      ·
        refine ⟨10856868390894902921200457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7237912260596601947466971 10856868390894902921200457)
        ·
          refine ⟨8142651293171177190900343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10856868390894902921200457 8142651293171177190900343)
          ·
            refine ⟨12213976939756765786350515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8142651293171177190900343 12213976939756765786350515)
            ·
              refine ⟨18320965409635148679525773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12213976939756765786350515 18320965409635148679525773)
              ·
                refine ⟨6870362028613180754822165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18320965409635148679525773 6870362028613180754822165)
                ·
                  refine ⟨322048220091242847882289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6870362028613180754822165 322048220091242847882289)
                  ·
                    rfl

theorem cell22_2822340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_2822340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822340 prefixEnd_2822340 := by exact prefixLift 2822340
  have htrace : WordTrace (prefixWord ++ tailWord_2822340) baseStart_2822340 baseEnd_2822340 := by
    simpa [prefixWord, tailWord_2822340, baseEnd_2822340] using wordTrace_append hprefix tailTrace_2822340
  have hstable : (prefixWord ++ tailWord_2822340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822340).length < 2 ^ (prefixWord ++ tailWord_2822340).sum := by decide
  have hdescent : baseEnd_2822340 < baseStart_2822340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822353 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_2822353 : Nat := 118140960795 + 2822353 * 2 ^ 59
def prefixEnd_2822353 : Nat := 4983230072969 + 3 ^ 40 * 2822353 * 2
def baseEnd_2822353 : Nat := 966149110439400843071827

theorem tailTrace_2822353 : CollatzResearch.WordTrace tailWord_2822353 prefixEnd_2822353 966149110439400843071827 := by
  unfold tailWord_2822353
  simp only [CollatzResearch.WordTrace]
  refine ⟨102939670744104575361975713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68626447162736383574650475 102939670744104575361975713)
  ·
    refine ⟨77204753058078431521481785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102939670744104575361975713 77204753058078431521481785)
    ·
      refine ⟨57903564793558823641111339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77204753058078431521481785 57903564793558823641111339)
      ·
        refine ⟨86855347190338235461667009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57903564793558823641111339 86855347190338235461667009)
        ·
          refine ⟨65141510392753676596250257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86855347190338235461667009 65141510392753676596250257)
          ·
            refine ⟨48856132794565257447187693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65141510392753676596250257 48856132794565257447187693)
            ·
              refine ⟨18321049797961971542695385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48856132794565257447187693 18321049797961971542695385)
              ·
                refine ⟨13740787348471478657021539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18321049797961971542695385 13740787348471478657021539)
                ·
                  refine ⟨20611181022707217985532309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13740787348471478657021539 20611181022707217985532309)
                  ·
                    refine ⟨966149110439400843071827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20611181022707217985532309 966149110439400843071827)
                    ·
                      rfl

theorem cell22_2822353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_2822353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822353 prefixEnd_2822353 := by exact prefixLift 2822353
  have htrace : WordTrace (prefixWord ++ tailWord_2822353) baseStart_2822353 baseEnd_2822353 := by
    simpa [prefixWord, tailWord_2822353, baseEnd_2822353] using wordTrace_append hprefix tailTrace_2822353
  have hstable : (prefixWord ++ tailWord_2822353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822353).length < 2 ^ (prefixWord ++ tailWord_2822353).sum := by decide
  have hdescent : baseEnd_2822353 < baseStart_2822353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822368 : List Nat := [2, 1, 1, 3, 1, 3, 3, 8]
def baseStart_2822368 : Nat := 118140960795 + 2822368 * 2 ^ 59
def prefixEnd_2822368 : Nat := 4983230072969 + 3 ^ 40 * 2822368 * 2
def baseEnd_2822368 : Nat := 107350471693993978216309

theorem tailTrace_2822368 : CollatzResearch.WordTrace tailWord_2822368 prefixEnd_2822368 107350471693993978216309 := by
  unfold tailWord_2822368
  simp only [CollatzResearch.WordTrace]
  refine ⟨51470108919525116461885879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68626811892700155282514505 51470108919525116461885879)
  ·
    refine ⟨77205163379287674692828819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51470108919525116461885879 77205163379287674692828819)
    ·
      refine ⟨115807745068931512039243229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77205163379287674692828819 115807745068931512039243229)
      ·
        refine ⟨43427904400849317014716211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115807745068931512039243229 43427904400849317014716211)
        ·
          refine ⟨65141856601273975522074317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43427904400849317014716211 65141856601273975522074317)
          ·
            refine ⟨24428196225477740820777869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65141856601273975522074317 24428196225477740820777869)
            ·
              refine ⟨9160573584554152807791701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24428196225477740820777869 9160573584554152807791701)
              ·
                refine ⟨107350471693993978216309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9160573584554152807791701 107350471693993978216309)
                ·
                  rfl

theorem cell22_2822368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_2822368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822368 prefixEnd_2822368 := by exact prefixLift 2822368
  have htrace : WordTrace (prefixWord ++ tailWord_2822368) baseStart_2822368 baseEnd_2822368 := by
    simpa [prefixWord, tailWord_2822368, baseEnd_2822368] using wordTrace_append hprefix tailTrace_2822368
  have hstable : (prefixWord ++ tailWord_2822368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822368).length < 2 ^ (prefixWord ++ tailWord_2822368).sum := by decide
  have hdescent : baseEnd_2822368 < baseStart_2822368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822402 : List Nat := [3, 4, 1, 1, 2, 2, 2, 7]
def baseStart_2822402 : Nat := 118140960795 + 2822402 * 2 ^ 59
def prefixEnd_2822402 : Nat := 4983230072969 + 3 ^ 40 * 2822402 * 2
def baseEnd_2822402 : Nat := 107351764904531227621853

theorem tailTrace_2822402 : CollatzResearch.WordTrace tailWord_2822402 prefixEnd_2822402 107351764904531227621853 := by
  unfold tailWord_2822402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25735364480231764182627365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68627638613951371153672973 25735364480231764182627365)
  ·
    refine ⟨4825380840043455784242631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25735364480231764182627365 4825380840043455784242631)
    ·
      refine ⟨7238071260065183676363947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825380840043455784242631 7238071260065183676363947)
      ·
        refine ⟨10857106890097775514545921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7238071260065183676363947 10857106890097775514545921)
        ·
          refine ⟨8142830167573331635909441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10857106890097775514545921 8142830167573331635909441)
          ·
            refine ⟨6107122625679998726932081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8142830167573331635909441 6107122625679998726932081)
            ·
              refine ⟨4580341969259999045199061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6107122625679998726932081 4580341969259999045199061)
              ·
                refine ⟨107351764904531227621853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4580341969259999045199061 107351764904531227621853)
                ·
                  rfl

theorem cell22_2822402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_2822402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822402 prefixEnd_2822402 := by exact prefixLift 2822402
  have htrace : WordTrace (prefixWord ++ tailWord_2822402) baseStart_2822402 baseEnd_2822402 := by
    simpa [prefixWord, tailWord_2822402, baseEnd_2822402] using wordTrace_append hprefix tailTrace_2822402
  have hstable : (prefixWord ++ tailWord_2822402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822402).length < 2 ^ (prefixWord ++ tailWord_2822402).sum := by decide
  have hdescent : baseEnd_2822402 < baseStart_2822402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822460 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_2822460 : Nat := 118140960795 + 2822460 * 2 ^ 59
def prefixEnd_2822460 : Nat := 4983230072969 + 3 ^ 40 * 2822460 * 2
def baseEnd_2822460 : Nat := 966185738726088230646499

theorem tailTrace_2822460 : CollatzResearch.WordTrace tailWord_2822460 prefixEnd_2822460 966185738726088230646499 := by
  unfold tailWord_2822460
  simp only [CollatzResearch.WordTrace]
  refine ⟨51471786677358466318060417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68629048903144621757413889 51471786677358466318060417)
  ·
    refine ⟨38603840008018849738545313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51471786677358466318060417 38603840008018849738545313)
    ·
      refine ⟨28952880006014137303908985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38603840008018849738545313 28952880006014137303908985)
      ·
        refine ⟨21714660004510602977931739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28952880006014137303908985 21714660004510602977931739)
        ·
          refine ⟨32571990006765904466897609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21714660004510602977931739 32571990006765904466897609)
          ·
            refine ⟨24428992505074428350173207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32571990006765904466897609 24428992505074428350173207)
            ·
              refine ⟨36643488757611642525259811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24428992505074428350173207 36643488757611642525259811)
              ·
                refine ⟨54965233136417463787889717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36643488757611642525259811 54965233136417463787889717)
                ·
                  refine ⟨5152990606539137230114661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54965233136417463787889717 5152990606539137230114661)
                  ·
                    refine ⟨966185738726088230646499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5152990606539137230114661 966185738726088230646499)
                    ·
                      rfl

theorem cell22_2822460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_2822460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822460 prefixEnd_2822460 := by exact prefixLift 2822460
  have htrace : WordTrace (prefixWord ++ tailWord_2822460) baseStart_2822460 baseEnd_2822460 := by
    simpa [prefixWord, tailWord_2822460, baseEnd_2822460] using wordTrace_append hprefix tailTrace_2822460
  have hstable : (prefixWord ++ tailWord_2822460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822460).length < 2 ^ (prefixWord ++ tailWord_2822460).sum := by decide
  have hdescent : baseEnd_2822460 < baseStart_2822460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822462 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2822462 : Nat := 118140960795 + 2822462 * 2 ^ 59
def prefixEnd_2822462 : Nat := 4983230072969 + 3 ^ 40 * 2822462 * 2
def baseEnd_2822462 : Nat := 966186423366960892096493

theorem tailTrace_2822462 : CollatzResearch.WordTrace tailWord_2822462 prefixEnd_2822462 966186423366960892096493 := by
  unfold tailWord_2822462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12867955787588710872211705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68629097533806457985129093 12867955787588710872211705)
  ·
    refine ⟨9650966840691533154158779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12867955787588710872211705 9650966840691533154158779)
    ·
      refine ⟨14476450261037299731238169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9650966840691533154158779 14476450261037299731238169)
      ·
        refine ⟨10857337695777974798428627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14476450261037299731238169 10857337695777974798428627)
        ·
          refine ⟨16286006543666962197642941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10857337695777974798428627 16286006543666962197642941)
          ·
            refine ⟨6107252453875110824116103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16286006543666962197642941 6107252453875110824116103)
            ·
              refine ⟨9160878680812666236174155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107252453875110824116103 9160878680812666236174155)
              ·
                refine ⟨13741318021218999354261233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9160878680812666236174155 13741318021218999354261233)
                ·
                  refine ⟨10305988515914249515695925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13741318021218999354261233 10305988515914249515695925)
                  ·
                    refine ⟨966186423366960892096493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10305988515914249515695925 966186423366960892096493)
                    ·
                      rfl

theorem cell22_2822462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2822462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822462 prefixEnd_2822462 := by exact prefixLift 2822462
  have htrace : WordTrace (prefixWord ++ tailWord_2822462) baseStart_2822462 baseEnd_2822462 := by
    simpa [prefixWord, tailWord_2822462, baseEnd_2822462] using wordTrace_append hprefix tailTrace_2822462
  have hstable : (prefixWord ++ tailWord_2822462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822462).length < 2 ^ (prefixWord ++ tailWord_2822462).sum := by decide
  have hdescent : baseEnd_2822462 < baseStart_2822462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822505 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_2822505 : Nat := 118140960795 + 2822505 * 2 ^ 59
def prefixEnd_2822505 : Nat := 4983230072969 + 3 ^ 40 * 2822505 * 2
def baseEnd_2822505 : Nat := 966201143145723113271361

theorem tailTrace_2822505 : CollatzResearch.WordTrace tailWord_2822505 prefixEnd_2822505 966201143145723113271361 := by
  unfold tailWord_2822505
  simp only [CollatzResearch.WordTrace]
  refine ⟨102945214639553905321508969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68630143093035936881005979 102945214639553905321508969)
  ·
    refine ⟨77208910979665428991131727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102945214639553905321508969 77208910979665428991131727)
    ·
      refine ⟨115813366469498143486697591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77208910979665428991131727 115813366469498143486697591)
      ·
        refine ⟨173720049704247215230046387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115813366469498143486697591 173720049704247215230046387)
        ·
          refine ⟨260580074556370822845069581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173720049704247215230046387 260580074556370822845069581)
          ·
            refine ⟨97717527958639058566901093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260580074556370822845069581 97717527958639058566901093)
            ·
              refine ⟨18322036492244823481293955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97717527958639058566901093 18322036492244823481293955)
              ·
                refine ⟨27483054738367235221940933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18322036492244823481293955 27483054738367235221940933)
                ·
                  refine ⟨5153072763443856604113925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27483054738367235221940933 5153072763443856604113925)
                  ·
                    refine ⟨966201143145723113271361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5153072763443856604113925 966201143145723113271361)
                    ·
                      rfl

theorem cell22_2822505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_2822505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822505 prefixEnd_2822505 := by exact prefixLift 2822505
  have htrace : WordTrace (prefixWord ++ tailWord_2822505) baseStart_2822505 baseEnd_2822505 := by
    simpa [prefixWord, tailWord_2822505, baseEnd_2822505] using wordTrace_append hprefix tailTrace_2822505
  have hstable : (prefixWord ++ tailWord_2822505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822505).length < 2 ^ (prefixWord ++ tailWord_2822505).sum := by decide
  have hdescent : baseEnd_2822505 < baseStart_2822505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822535 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 2, 7]
def baseStart_2822535 : Nat := 118140960795 + 2822535 * 2 ^ 59
def prefixEnd_2822535 : Nat := 4983230072969 + 3 ^ 40 * 2822535 * 2
def baseEnd_2822535 : Nat := 966211412758813035021269

theorem tailTrace_2822535 : CollatzResearch.WordTrace tailWord_2822535 prefixEnd_2822535 966211412758813035021269 := by
  unfold tailWord_2822535
  simp only [CollatzResearch.WordTrace]
  refine ⟨102946308829445220445101059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68630872552963480296734039 102946308829445220445101059)
  ·
    refine ⟨154419463244167830667651589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102946308829445220445101059 154419463244167830667651589)
    ·
      refine ⟨28953649358281468250184673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154419463244167830667651589 28953649358281468250184673)
      ·
        refine ⟨21715237018711101187638505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28953649358281468250184673 21715237018711101187638505)
        ·
          refine ⟨16286427764033325890728879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21715237018711101187638505 16286427764033325890728879)
          ·
            refine ⟨24429641646049988836093319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16286427764033325890728879 24429641646049988836093319)
            ·
              refine ⟨36644462469074983254139979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24429641646049988836093319 36644462469074983254139979)
              ·
                refine ⟨54966693703612474881209969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36644462469074983254139979 54966693703612474881209969)
                ·
                  refine ⟨41225020277709356160907477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54966693703612474881209969 41225020277709356160907477)
                  ·
                    refine ⟨966211412758813035021269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41225020277709356160907477 966211412758813035021269)
                    ·
                      rfl

theorem cell22_2822535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_2822535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822535 prefixEnd_2822535 := by exact prefixLift 2822535
  have htrace : WordTrace (prefixWord ++ tailWord_2822535) baseStart_2822535 baseEnd_2822535 := by
    simpa [prefixWord, tailWord_2822535, baseEnd_2822535] using wordTrace_append hprefix tailTrace_2822535
  have hstable : (prefixWord ++ tailWord_2822535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822535).length < 2 ^ (prefixWord ++ tailWord_2822535).sum := by decide
  have hdescent : baseEnd_2822535 < baseStart_2822535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822537 : List Nat := [1, 2, 1, 1, 6, 1, 4, 6]
def baseStart_2822537 : Nat := 118140960795 + 2822537 * 2 ^ 59
def prefixEnd_2822537 : Nat := 4983230072969 + 3 ^ 40 * 2822537 * 2
def baseEnd_2822537 : Nat := 107356899711076188496807

theorem tailTrace_2822537 : CollatzResearch.WordTrace tailWord_2822537 prefixEnd_2822537 107356899711076188496807 := by
  unfold tailWord_2822537
  simp only [CollatzResearch.WordTrace]
  refine ⟨102946381775437974786673865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68630921183625316524449243 102946381775437974786673865)
  ·
    refine ⟨77209786331578481090005399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102946381775437974786673865 77209786331578481090005399)
    ·
      refine ⟨115814679497367721635008099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77209786331578481090005399 115814679497367721635008099)
      ·
        refine ⟨173722019246051582452512149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115814679497367721635008099 173722019246051582452512149)
        ·
          refine ⟨8143219652158667927461507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173722019246051582452512149 8143219652158667927461507)
          ·
            refine ⟨12214829478238001891192261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8143219652158667927461507 12214829478238001891192261)
            ·
              refine ⟨2290280527169625354598549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12214829478238001891192261 2290280527169625354598549)
              ·
                refine ⟨107356899711076188496807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2290280527169625354598549 107356899711076188496807)
                ·
                  rfl

theorem cell22_2822537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 6].length) (baseStart_2822537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822537 prefixEnd_2822537 := by exact prefixLift 2822537
  have htrace : WordTrace (prefixWord ++ tailWord_2822537) baseStart_2822537 baseEnd_2822537 := by
    simpa [prefixWord, tailWord_2822537, baseEnd_2822537] using wordTrace_append hprefix tailTrace_2822537
  have hstable : (prefixWord ++ tailWord_2822537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822537).length < 2 ^ (prefixWord ++ tailWord_2822537).sum := by decide
  have hdescent : baseEnd_2822537 < baseStart_2822537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822565 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 7]
def baseStart_2822565 : Nat := 118140960795 + 2822565 * 2 ^ 59
def prefixEnd_2822565 : Nat := 4983230072969 + 3 ^ 40 * 2822565 * 2
def baseEnd_2822565 : Nat := 322073894123967652257059

theorem tailTrace_2822565 : CollatzResearch.WordTrace tailWord_2822565 prefixEnd_2822565 322073894123967652257059 := by
  unfold tailWord_2822565
  simp only [CollatzResearch.WordTrace]
  refine ⟨102947403019336535568693149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68631602012891023712462099 102947403019336535568693149)
  ·
    refine ⟨38605276132251200838259931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102947403019336535568693149 38605276132251200838259931)
    ·
      refine ⟨57907914198376801257389897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38605276132251200838259931 57907914198376801257389897)
      ·
        refine ⟨43430935648782600943042423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57907914198376801257389897 43430935648782600943042423)
        ·
          refine ⟨65146403473173901414563635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43430935648782600943042423 65146403473173901414563635)
          ·
            refine ⟨97719605209760852121845453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65146403473173901414563635 97719605209760852121845453)
            ·
              refine ⟨36644851953660319545692045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97719605209760852121845453 36644851953660319545692045)
              ·
                refine ⟨13741819482622619829634517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36644851953660319545692045 13741819482622619829634517)
                ·
                  refine ⟨322073894123967652257059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13741819482622619829634517 322073894123967652257059)
                  ·
                    rfl

theorem cell22_2822565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_2822565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822565 prefixEnd_2822565 := by exact prefixLift 2822565
  have htrace : WordTrace (prefixWord ++ tailWord_2822565) baseStart_2822565 baseEnd_2822565 := by
    simpa [prefixWord, tailWord_2822565, baseEnd_2822565] using wordTrace_append hprefix tailTrace_2822565
  have hstable : (prefixWord ++ tailWord_2822565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822565).length < 2 ^ (prefixWord ++ tailWord_2822565).sum := by decide
  have hdescent : baseEnd_2822565 < baseStart_2822565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822569 : List Nat := [1, 2, 1, 1, 1, 1, 3, 8, 1, 3]
def baseStart_2822569 : Nat := 118140960795 + 2822569 * 2 ^ 59
def prefixEnd_2822569 : Nat := 4983230072969 + 3 ^ 40 * 2822569 * 2
def baseEnd_2822569 : Nat := 966223051653648279671165

theorem tailTrace_2822569 : CollatzResearch.WordTrace tailWord_2822569 prefixEnd_2822569 966223051653648279671165 := by
  unfold tailWord_2822569
  simp only [CollatzResearch.WordTrace]
  refine ⟨102947548911322044251838761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68631699274214696167892507 102947548911322044251838761)
  ·
    refine ⟨77210661683491533188879071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102947548911322044251838761 77210661683491533188879071)
    ·
      refine ⟨115815992525237299783318607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77210661683491533188879071 115815992525237299783318607)
      ·
        refine ⟨173723988787855949674977911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115815992525237299783318607 173723988787855949674977911)
        ·
          refine ⟨260585983181783924512466867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173723988787855949674977911 260585983181783924512466867)
          ·
            refine ⟨390878974772675886768700301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260585983181783924512466867 390878974772675886768700301)
            ·
              refine ⟨146579615539753457538262613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 390878974772675886768700301 146579615539753457538262613)
              ·
                refine ⟨1717729869606485830526515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 146579615539753457538262613 1717729869606485830526515)
                ·
                  refine ⟨2576594804409728745789773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717729869606485830526515 2576594804409728745789773)
                  ·
                    refine ⟨966223051653648279671165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576594804409728745789773 966223051653648279671165)
                    ·
                      rfl

theorem cell22_2822569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 3].length) (baseStart_2822569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822569 prefixEnd_2822569 := by exact prefixLift 2822569
  have htrace : WordTrace (prefixWord ++ tailWord_2822569) baseStart_2822569 baseEnd_2822569 := by
    simpa [prefixWord, tailWord_2822569, baseEnd_2822569] using wordTrace_append hprefix tailTrace_2822569
  have hstable : (prefixWord ++ tailWord_2822569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822569).length < 2 ^ (prefixWord ++ tailWord_2822569).sum := by decide
  have hdescent : baseEnd_2822569 < baseStart_2822569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822614 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2822614 : Nat := 118140960795 + 2822614 * 2 ^ 59
def prefixEnd_2822614 : Nat := 4983230072969 + 3 ^ 40 * 2822614 * 2
def baseEnd_2822614 : Nat := 966238456073283162296027

theorem tailTrace_2822614 : CollatzResearch.WordTrace tailWord_2822614 prefixEnd_2822614 966238456073283162296027 := by
  unfold tailWord_2822614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434324387259938558576681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68632793464106011291484597 6434324387259938558576681)
  ·
    refine ⟨4825743290444953918932511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6434324387259938558576681 4825743290444953918932511)
    ·
      refine ⟨7238614935667430878398767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825743290444953918932511 7238614935667430878398767)
      ·
        refine ⟨10857922403501146317598151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7238614935667430878398767 10857922403501146317598151)
        ·
          refine ⟨16286883605251719476397227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10857922403501146317598151 16286883605251719476397227)
          ·
            refine ⟨24430325407877579214595841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16286883605251719476397227 24430325407877579214595841)
            ·
              refine ⟨18322744055908184410946881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24430325407877579214595841 18322744055908184410946881)
              ·
                refine ⟨13742058041931138308210161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18322744055908184410946881 13742058041931138308210161)
                ·
                  refine ⟨10306543531448353731157621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13742058041931138308210161 10306543531448353731157621)
                  ·
                    refine ⟨966238456073283162296027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10306543531448353731157621 966238456073283162296027)
                    ·
                      rfl

theorem cell22_2822614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2822614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822614 prefixEnd_2822614 := by exact prefixLift 2822614
  have htrace : WordTrace (prefixWord ++ tailWord_2822614) baseStart_2822614 baseEnd_2822614 := by
    simpa [prefixWord, tailWord_2822614, baseEnd_2822614] using wordTrace_append hprefix tailTrace_2822614
  have hstable : (prefixWord ++ tailWord_2822614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822614).length < 2 ^ (prefixWord ++ tailWord_2822614).sum := by decide
  have hdescent : baseEnd_2822614 < baseStart_2822614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822663 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 1, 4]
def baseStart_2822663 : Nat := 118140960795 + 2822663 * 2 ^ 59
def prefixEnd_2822663 : Nat := 4983230072969 + 3 ^ 40 * 2822663 * 2
def baseEnd_2822663 : Nat := 966255229774663367820877

theorem tailTrace_2822663 : CollatzResearch.WordTrace tailWord_2822663 prefixEnd_2822663 966255229774663367820877 := by
  unfold tailWord_2822663
  simp only [CollatzResearch.WordTrace]
  refine ⟨102950977372981498305760643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68633984915320998870507095 102950977372981498305760643)
  ·
    refine ⟨154426466059472247458640965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102950977372981498305760643 154426466059472247458640965)
    ·
      refine ⟨28954962386151046398495181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154426466059472247458640965 28954962386151046398495181)
      ·
        refine ⟨10858110894806642399435693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28954962386151046398495181 10858110894806642399435693)
        ·
          refine ⟨4071791585552490899788385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10858110894806642399435693 4071791585552490899788385)
          ·
            refine ⟨3053843689164368174841289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071791585552490899788385 3053843689164368174841289)
            ·
              refine ⟨2290382766873276131130967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3053843689164368174841289 2290382766873276131130967)
              ·
                refine ⟨3435574150309914196696451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290382766873276131130967 3435574150309914196696451)
                ·
                  refine ⟨5153361225464871295044677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435574150309914196696451 5153361225464871295044677)
                  ·
                    refine ⟨966255229774663367820877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5153361225464871295044677 966255229774663367820877)
                    ·
                      rfl

theorem cell22_2822663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_2822663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822663 prefixEnd_2822663 := by exact prefixLift 2822663
  have htrace : WordTrace (prefixWord ++ tailWord_2822663) baseStart_2822663 baseEnd_2822663 := by
    simpa [prefixWord, tailWord_2822663, baseEnd_2822663] using wordTrace_append hprefix tailTrace_2822663
  have hstable : (prefixWord ++ tailWord_2822663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822663).length < 2 ^ (prefixWord ++ tailWord_2822663).sum := by decide
  have hdescent : baseEnd_2822663 < baseStart_2822663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822704 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 3, 3]
def baseStart_2822704 : Nat := 118140960795 + 2822704 * 2 ^ 59
def prefixEnd_2822704 : Nat := 4983230072969 + 3 ^ 40 * 2822704 * 2
def baseEnd_2822704 : Nat := 966269264912552927545751

theorem tailTrace_2822704 : CollatzResearch.WordTrace tailWord_2822704 prefixEnd_2822704 966269264912552927545751 := by
  unfold tailWord_2822704
  simp only [CollatzResearch.WordTrace]
  refine ⟨51476236382916481154001583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68634981843888641538668777 51476236382916481154001583)
  ·
    refine ⟨77214354574374721731002375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51476236382916481154001583 77214354574374721731002375)
    ·
      refine ⟨115821531861562082596503563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77214354574374721731002375 115821531861562082596503563)
      ·
        refine ⟨173732297792343123894755345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115821531861562082596503563 173732297792343123894755345)
        ·
          refine ⟨130299223344257342921066509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173732297792343123894755345 130299223344257342921066509)
          ·
            refine ⟨48862208754096503595399941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130299223344257342921066509 48862208754096503595399941)
            ·
              refine ⟨9161664141393094424137489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48862208754096503595399941 9161664141393094424137489)
              ·
                refine ⟨6871248106044820818103117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9161664141393094424137489 6871248106044820818103117)
                ·
                  refine ⟨2576718039766807806788669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6871248106044820818103117 2576718039766807806788669)
                  ·
                    refine ⟨966269264912552927545751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576718039766807806788669 966269264912552927545751)
                    ·
                      rfl

theorem cell22_2822704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_2822704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822704 prefixEnd_2822704 := by exact prefixLift 2822704
  have htrace : WordTrace (prefixWord ++ tailWord_2822704) baseStart_2822704 baseEnd_2822704 := by
    simpa [prefixWord, tailWord_2822704, baseEnd_2822704] using wordTrace_append hprefix tailTrace_2822704
  have hstable : (prefixWord ++ tailWord_2822704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822704).length < 2 ^ (prefixWord ++ tailWord_2822704).sum := by decide
  have hdescent : baseEnd_2822704 < baseStart_2822704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822830 : List Nat := [4, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_2822830 : Nat := 118140960795 + 2822830 * 2 ^ 59
def prefixEnd_2822830 : Nat := 4983230072969 + 3 ^ 40 * 2822830 * 2
def baseEnd_2822830 : Nat := 322104132429176866298455

theorem tailTrace_2822830 : CollatzResearch.WordTrace tailWord_2822830 prefixEnd_2822830 322104132429176866298455 := by
  unfold tailWord_2822830
  simp only [CollatzResearch.WordTrace]
  refine ⟨12869633545422060728386243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68638045575584323884726629 12869633545422060728386243)
  ·
    refine ⟨19304450318133091092579365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12869633545422060728386243 19304450318133091092579365)
    ·
      refine ⟨3619584434649954579858631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19304450318133091092579365 3619584434649954579858631)
      ·
        refine ⟨5429376651974931869787947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619584434649954579858631 5429376651974931869787947)
        ·
          refine ⟨8144064977962397804681921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429376651974931869787947 8144064977962397804681921)
          ·
            refine ⟨6108048733471798353511441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8144064977962397804681921 6108048733471798353511441)
            ·
              refine ⟨4581036550103848765133581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6108048733471798353511441 4581036550103848765133581)
              ·
                refine ⟨1717888706288943286925093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4581036550103848765133581 1717888706288943286925093)
                ·
                  refine ⟨322104132429176866298455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717888706288943286925093 322104132429176866298455)
                  ·
                    rfl

theorem cell22_2822830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_2822830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822830 prefixEnd_2822830 := by exact prefixLift 2822830
  have htrace : WordTrace (prefixWord ++ tailWord_2822830) baseStart_2822830 baseEnd_2822830 := by
    simpa [prefixWord, tailWord_2822830, baseEnd_2822830] using wordTrace_append hprefix tailTrace_2822830
  have hstable : (prefixWord ++ tailWord_2822830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822830).length < 2 ^ (prefixWord ++ tailWord_2822830).sum := by decide
  have hdescent : baseEnd_2822830 < baseStart_2822830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822856 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 3, 3]
def baseStart_2822856 : Nat := 118140960795 + 2822856 * 2 ^ 59
def prefixEnd_2822856 : Nat := 4983230072969 + 3 ^ 40 * 2822856 * 2
def baseEnd_2822856 : Nat := 966321297618875197745285

theorem tailTrace_2822856 : CollatzResearch.WordTrace tailWord_2822856 prefixEnd_2822856 966321297618875197745285 := by
  unfold tailWord_2822856
  simp only [CollatzResearch.WordTrace]
  refine ⟨51479008330641146133768211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68638677774188194845024281 51479008330641146133768211)
  ·
    refine ⟨77218512495961719200652317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51479008330641146133768211 77218512495961719200652317)
    ·
      refine ⟨28956942185985644700244619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77218512495961719200652317 28956942185985644700244619)
      ·
        refine ⟨43435413278978467050366929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28956942185985644700244619 43435413278978467050366929)
        ·
          refine ⟨32576559959233850287775197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43435413278978467050366929 32576559959233850287775197)
          ·
            refine ⟨12216209984712693857915699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32576559959233850287775197 12216209984712693857915699)
            ·
              refine ⟨18324314977069040786873549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12216209984712693857915699 18324314977069040786873549)
              ·
                refine ⟨6871618116400890295077581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18324314977069040786873549 6871618116400890295077581)
                ·
                  refine ⟨2576856793650333860654093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6871618116400890295077581 2576856793650333860654093)
                  ·
                    refine ⟨966321297618875197745285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576856793650333860654093 966321297618875197745285)
                    ·
                      rfl

theorem cell22_2822856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_2822856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822856 prefixEnd_2822856 := by exact prefixLift 2822856
  have htrace : WordTrace (prefixWord ++ tailWord_2822856) baseStart_2822856 baseEnd_2822856 := by
    simpa [prefixWord, tailWord_2822856, baseEnd_2822856] using wordTrace_append hprefix tailTrace_2822856
  have hstable : (prefixWord ++ tailWord_2822856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822856).length < 2 ^ (prefixWord ++ tailWord_2822856).sum := by decide
  have hdescent : baseEnd_2822856 < baseStart_2822856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822899 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 5, 4]
def baseStart_2822899 : Nat := 118140960795 + 2822899 * 2 ^ 59
def prefixEnd_2822899 : Nat := 4983230072969 + 3 ^ 40 * 2822899 * 2
def baseEnd_2822899 : Nat := 966336017397637418920153

theorem tailTrace_2822899 : CollatzResearch.WordTrace tailWord_2822899 prefixEnd_2822899 966336017397637418920153 := by
  unfold tailWord_2822899
  simp only [CollatzResearch.WordTrace]
  refine ⟨102959585000126510611351751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68639723333417673740901167 102959585000126510611351751)
  ·
    refine ⟨154439377500189765917027627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102959585000126510611351751 154439377500189765917027627)
    ·
      refine ⟨231659066250284648875541441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154439377500189765917027627 231659066250284648875541441)
      ·
        refine ⟨173744299687713486656656081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231659066250284648875541441 173744299687713486656656081)
        ·
          refine ⟨130308224765785114992492061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173744299687713486656656081 130308224765785114992492061)
          ·
            refine ⟨48865584287169418122184523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130308224765785114992492061 48865584287169418122184523)
            ·
              refine ⟨73298376430754127183276785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48865584287169418122184523 73298376430754127183276785)
              ·
                refine ⟨54973782323065595387457589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73298376430754127183276785 54973782323065595387457589)
                ·
                  refine ⟨5153792092787399567574149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54973782323065595387457589 5153792092787399567574149)
                  ·
                    refine ⟨966336017397637418920153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5153792092787399567574149 966336017397637418920153)
                    ·
                      rfl

theorem cell22_2822899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 4].length) (baseStart_2822899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822899 prefixEnd_2822899 := by exact prefixLift 2822899
  have htrace : WordTrace (prefixWord ++ tailWord_2822899) baseStart_2822899 baseEnd_2822899 := by
    simpa [prefixWord, tailWord_2822899, baseEnd_2822899] using wordTrace_append hprefix tailTrace_2822899
  have hstable : (prefixWord ++ tailWord_2822899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822899).length < 2 ^ (prefixWord ++ tailWord_2822899).sum := by decide
  have hdescent : baseEnd_2822899 < baseStart_2822899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822916 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2822916 : Nat := 118140960795 + 2822916 * 2 ^ 59
def prefixEnd_2822916 : Nat := 4983230072969 + 3 ^ 40 * 2822916 * 2
def baseEnd_2822916 : Nat := 966341836845055041245101

theorem tailTrace_2822916 : CollatzResearch.WordTrace tailWord_2822916 prefixEnd_2822916 966341836845055041245101 := by
  unfold tailWord_2822916
  simp only [CollatzResearch.WordTrace]
  refine ⟨51480102520532461257360301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68640136694043281676480401 51480102520532461257360301)
  ·
    refine ⟨19305038445199672971510113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51480102520532461257360301 19305038445199672971510113)
    ·
      refine ⟨14478778833899754728632585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19305038445199672971510113 14478778833899754728632585)
      ·
        refine ⟨10859084125424816046474439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14478778833899754728632585 10859084125424816046474439)
        ·
          refine ⟨16288626188137224069711659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10859084125424816046474439 16288626188137224069711659)
          ·
            refine ⟨24432939282205836104567489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16288626188137224069711659 24432939282205836104567489)
            ·
              refine ⟨18324704461654377078425617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24432939282205836104567489 18324704461654377078425617)
              ·
                refine ⟨13743528346240782808819213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18324704461654377078425617 13743528346240782808819213)
                ·
                  refine ⟨5153823129840293553307205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13743528346240782808819213 5153823129840293553307205)
                  ·
                    refine ⟨966341836845055041245101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5153823129840293553307205 966341836845055041245101)
                    ·
                      rfl

theorem cell22_2822916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2822916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822916 prefixEnd_2822916 := by exact prefixLift 2822916
  have htrace : WordTrace (prefixWord ++ tailWord_2822916) baseStart_2822916 baseEnd_2822916 := by
    simpa [prefixWord, tailWord_2822916, baseEnd_2822916] using wordTrace_append hprefix tailTrace_2822916
  have hstable : (prefixWord ++ tailWord_2822916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822916).length < 2 ^ (prefixWord ++ tailWord_2822916).sum := by decide
  have hdescent : baseEnd_2822916 < baseStart_2822916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822946 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2822946 : Nat := 118140960795 + 2822946 * 2 ^ 59
def prefixEnd_2822946 : Nat := 4983230072969 + 3 ^ 40 * 2822946 * 2
def baseEnd_2822946 : Nat := 966352106458144962995009

theorem tailTrace_2822946 : CollatzResearch.WordTrace tailWord_2822946 prefixEnd_2822946 966352106458144962995009 := by
  unfold tailWord_2822946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25740324807739059409578173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68640866153970825092208461 25740324807739059409578173)
  ·
    refine ⟨9652621802902147278591815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25740324807739059409578173 9652621802902147278591815)
    ·
      refine ⟨14478932704353220917887723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9652621802902147278591815 14478932704353220917887723)
      ·
        refine ⟨21718399056529831376831585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14478932704353220917887723 21718399056529831376831585)
        ·
          refine ⟨16288799292397373532623689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21718399056529831376831585 16288799292397373532623689)
          ·
            refine ⟨12216599469298030149467767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16288799292397373532623689 12216599469298030149467767)
            ·
              refine ⟨18324899203947045224201651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12216599469298030149467767 18324899203947045224201651)
              ·
                refine ⟨27487348805920567836302477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18324899203947045224201651 27487348805920567836302477)
                ·
                  refine ⟨10307755802220212938613429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27487348805920567836302477 10307755802220212938613429)
                  ·
                    refine ⟨966352106458144962995009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10307755802220212938613429 966352106458144962995009)
                    ·
                      rfl

theorem cell22_2822946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2822946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822946 prefixEnd_2822946 := by exact prefixLift 2822946
  have htrace : WordTrace (prefixWord ++ tailWord_2822946) baseStart_2822946 baseEnd_2822946 := by
    simpa [prefixWord, tailWord_2822946, baseEnd_2822946] using wordTrace_append hprefix tailTrace_2822946
  have hstable : (prefixWord ++ tailWord_2822946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822946).length < 2 ^ (prefixWord ++ tailWord_2822946).sum := by decide
  have hdescent : baseEnd_2822946 < baseStart_2822946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822961 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_2822961 : Nat := 118140960795 + 2822961 * 2 ^ 59
def prefixEnd_2822961 : Nat := 4983230072969 + 3 ^ 40 * 2822961 * 2
def baseEnd_2822961 : Nat := 966357241264689923869963

theorem tailTrace_2822961 : CollatzResearch.WordTrace tailWord_2822961 prefixEnd_2822961 966357241264689923869963 := by
  unfold tailWord_2822961
  simp only [CollatzResearch.WordTrace]
  refine ⟨102961846325901895200108737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68641230883934596800072491 102961846325901895200108737)
  ·
    refine ⟨77221384744426421400081553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102961846325901895200108737 77221384744426421400081553)
    ·
      refine ⟨57916038558319816050061165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77221384744426421400081553 57916038558319816050061165)
      ·
        refine ⟨21718514459369931018772937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57916038558319816050061165 21718514459369931018772937)
        ·
          refine ⟨16288885844527448264079703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21718514459369931018772937 16288885844527448264079703)
          ·
            refine ⟨24433328766791172396119555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16288885844527448264079703 24433328766791172396119555)
            ·
              refine ⟨36649993150186758594179333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24433328766791172396119555 36649993150186758594179333)
              ·
                refine ⟨6871873715660017236408625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36649993150186758594179333 6871873715660017236408625)
                ·
                  refine ⟨5153905286745012927306469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6871873715660017236408625 5153905286745012927306469)
                  ·
                    refine ⟨966357241264689923869963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5153905286745012927306469 966357241264689923869963)
                    ·
                      rfl

theorem cell22_2822961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_2822961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822961 prefixEnd_2822961 := by exact prefixLift 2822961
  have htrace : WordTrace (prefixWord ++ tailWord_2822961) baseStart_2822961 baseEnd_2822961 := by
    simpa [prefixWord, tailWord_2822961, baseEnd_2822961] using wordTrace_append hprefix tailTrace_2822961
  have hstable : (prefixWord ++ tailWord_2822961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822961).length < 2 ^ (prefixWord ++ tailWord_2822961).sum := by decide
  have hdescent : baseEnd_2822961 < baseStart_2822961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822963 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 2, 3]
def baseStart_2822963 : Nat := 118140960795 + 2822963 * 2 ^ 59
def prefixEnd_2822963 : Nat := 4983230072969 + 3 ^ 40 * 2822963 * 2
def baseEnd_2822963 : Nat := 966357925905562585319957

theorem tailTrace_2822963 : CollatzResearch.WordTrace tailWord_2822963 prefixEnd_2822963 966357925905562585319957 := by
  unfold tailWord_2822963
  simp only [CollatzResearch.WordTrace]
  refine ⟨102961919271894649541681543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68641279514596433027787695 102961919271894649541681543)
  ·
    refine ⟨154442878907841974312522315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102961919271894649541681543 154442878907841974312522315)
    ·
      refine ⟨231664318361762961468783473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154442878907841974312522315 231664318361762961468783473)
      ·
        refine ⟨173748238771322221101587605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231664318361762961468783473 173748238771322221101587605)
        ·
          refine ⟨8144448692405729114136919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173748238771322221101587605 8144448692405729114136919)
          ·
            refine ⟨12216673038608593671205379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144448692405729114136919 12216673038608593671205379)
            ·
              refine ⟨18325009557912890506808069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12216673038608593671205379 18325009557912890506808069)
              ·
                refine ⟨3435939292108666970026513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18325009557912890506808069 3435939292108666970026513)
                ·
                  refine ⟨2576954469081500227519885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3435939292108666970026513 2576954469081500227519885)
                  ·
                    refine ⟨966357925905562585319957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2576954469081500227519885 966357925905562585319957)
                    ·
                      rfl

theorem cell22_2822963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 3].length) (baseStart_2822963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822963 prefixEnd_2822963 := by exact prefixLift 2822963
  have htrace : WordTrace (prefixWord ++ tailWord_2822963) baseStart_2822963 baseEnd_2822963 := by
    simpa [prefixWord, tailWord_2822963, baseEnd_2822963] using wordTrace_append hprefix tailTrace_2822963
  have hstable : (prefixWord ++ tailWord_2822963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822963).length < 2 ^ (prefixWord ++ tailWord_2822963).sum := by decide
  have hdescent : baseEnd_2822963 < baseStart_2822963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822965 : List Nat := [1, 3, 3, 1, 3, 1, 4, 2, 4]
def baseStart_2822965 : Nat := 118140960795 + 2822965 * 2 ^ 59
def prefixEnd_2822965 : Nat := 4983230072969 + 3 ^ 40 * 2822965 * 2
def baseEnd_2822965 : Nat := 322119536848811748923317

theorem tailTrace_2822965 : CollatzResearch.WordTrace tailWord_2822965 prefixEnd_2822965 322119536848811748923317 := by
  unfold tailWord_2822965
  simp only [CollatzResearch.WordTrace]
  refine ⟨102961992217887403883254349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68641328145258269255502899 102961992217887403883254349)
  ·
    refine ⟨38610747081707776456220381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102961992217887403883254349 38610747081707776456220381)
    ·
      refine ⟨14479030155640416171082643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38610747081707776456220381 14479030155640416171082643)
      ·
        refine ⟨21718545233460624256623965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14479030155640416171082643 21718545233460624256623965)
        ·
          refine ⟨8144454462547734096233987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21718545233460624256623965 8144454462547734096233987)
          ·
            refine ⟨12216681693821601144350981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144454462547734096233987 12216681693821601144350981)
            ·
              refine ⟨2290627817591550214565809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12216681693821601144350981 2290627817591550214565809)
              ·
                refine ⟨1717970863193662660924357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290627817591550214565809 1717970863193662660924357)
                ·
                  refine ⟨322119536848811748923317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1717970863193662660924357 322119536848811748923317)
                  ·
                    rfl

theorem cell22_2822965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_2822965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822965 prefixEnd_2822965 := by exact prefixLift 2822965
  have htrace : WordTrace (prefixWord ++ tailWord_2822965) baseStart_2822965 baseEnd_2822965 := by
    simpa [prefixWord, tailWord_2822965, baseEnd_2822965] using wordTrace_append hprefix tailTrace_2822965
  have hstable : (prefixWord ++ tailWord_2822965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822965).length < 2 ^ (prefixWord ++ tailWord_2822965).sum := by decide
  have hdescent : baseEnd_2822965 < baseStart_2822965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822993 : List Nat := [1, 2, 2, 1, 6, 1, 3, 6]
def baseStart_2822993 : Nat := 118140960795 + 2822993 * 2 ^ 59
def prefixEnd_2822993 : Nat := 4983230072969 + 3 ^ 40 * 2822993 * 2
def baseEnd_2822993 : Nat := 107374243946516945229985

theorem tailTrace_2822993 : CollatzResearch.WordTrace tailWord_2822993 prefixEnd_2822993 107374243946516945229985 := by
  unfold tailWord_2822993
  simp only [CollatzResearch.WordTrace]
  refine ⟨102963013461785964665273633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68642008974523976443515755 102963013461785964665273633)
  ·
    refine ⟨77222260096339473498955225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102963013461785964665273633 77222260096339473498955225)
    ·
      refine ⟨57916695072254605124216419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77222260096339473498955225 57916695072254605124216419)
      ·
        refine ⟨86875042608381907686324629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57916695072254605124216419 86875042608381907686324629)
        ·
          refine ⟨4072267622267901922796467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86875042608381907686324629 4072267622267901922796467)
          ·
            refine ⟨6108401433401852884194701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072267622267901922796467 6108401433401852884194701)
            ·
              refine ⟨2290650537525694831573013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6108401433401852884194701 2290650537525694831573013)
              ·
                refine ⟨107374243946516945229985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2290650537525694831573013 107374243946516945229985)
                ·
                  rfl

theorem cell22_2822993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 6].length) (baseStart_2822993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2822993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2822993 prefixEnd_2822993 := by exact prefixLift 2822993
  have htrace : WordTrace (prefixWord ++ tailWord_2822993) baseStart_2822993 baseEnd_2822993 := by
    simpa [prefixWord, tailWord_2822993, baseEnd_2822993] using wordTrace_append hprefix tailTrace_2822993
  have hstable : (prefixWord ++ tailWord_2822993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822993).length < 2 ^ (prefixWord ++ tailWord_2822993).sum := by decide
  have hdescent : baseEnd_2822993 < baseStart_2822993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823025 : List Nat := [1, 2, 2, 2, 1, 4, 2, 4, 1, 3]
def baseStart_2823025 : Nat := 118140960795 + 2823025 * 2 ^ 59
def prefixEnd_2823025 : Nat := 4983230072969 + 3 ^ 40 * 2823025 * 2
def baseEnd_2823025 : Nat := 966379149772615090269767

theorem tailTrace_2823025 : CollatzResearch.WordTrace tailWord_2823025 prefixEnd_2823025 966379149772615090269767 := by
  unfold tailWord_2823025
  simp only [CollatzResearch.WordTrace]
  refine ⟨102964180597670034130438529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68642787065113356086959019 102964180597670034130438529)
  ·
    refine ⟨77223135448252525597828897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102964180597670034130438529 77223135448252525597828897)
    ·
      refine ⟨57917351586189394198371673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77223135448252525597828897 57917351586189394198371673)
      ·
        refine ⟨43438013689642045648778755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57917351586189394198371673 43438013689642045648778755)
        ·
          refine ⟨65157020534463068473168133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43438013689642045648778755 65157020534463068473168133)
          ·
            refine ⟨12216941350211825338719025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65157020534463068473168133 12216941350211825338719025)
            ·
              refine ⟨9162706012658869004039269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12216941350211825338719025 9162706012658869004039269)
              ·
                refine ⟨1718007377373537938257363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9162706012658869004039269 1718007377373537938257363)
                ·
                  refine ⟨2577011066060306907386045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718007377373537938257363 2577011066060306907386045)
                  ·
                    refine ⟨966379149772615090269767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577011066060306907386045 966379149772615090269767)
                    ·
                      rfl

theorem cell22_2823025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_2823025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823025 prefixEnd_2823025 := by exact prefixLift 2823025
  have htrace : WordTrace (prefixWord ++ tailWord_2823025) baseStart_2823025 baseEnd_2823025 := by
    simpa [prefixWord, tailWord_2823025, baseEnd_2823025] using wordTrace_append hprefix tailTrace_2823025
  have hstable : (prefixWord ++ tailWord_2823025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823025).length < 2 ^ (prefixWord ++ tailWord_2823025).sum := by decide
  have hdescent : baseEnd_2823025 < baseStart_2823025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823051 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 3, 4]
def baseStart_2823051 : Nat := 118140960795 + 2823051 * 2 ^ 59
def prefixEnd_2823051 : Nat := 4983230072969 + 3 ^ 40 * 2823051 * 2
def baseEnd_2823051 : Nat := 966388050103959689119687

theorem tailTrace_2823051 : CollatzResearch.WordTrace tailWord_2823051 prefixEnd_2823051 966388050103959689119687 := by
  unfold tailWord_2823051
  simp only [CollatzResearch.WordTrace]
  refine ⟨102965128895575840570885007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68643419263717227047256671 102965128895575840570885007)
  ·
    refine ⟨154447693343363760856327511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102965128895575840570885007 154447693343363760856327511)
    ·
      refine ⟨231671540015045641284491267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154447693343363760856327511 231671540015045641284491267)
      ·
        refine ⟨347507310022568461926736901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231671540015045641284491267 347507310022568461926736901)
        ·
          refine ⟨65157620629231586611263169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347507310022568461926736901 65157620629231586611263169)
          ·
            refine ⟨48868215471923689958447377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65157620629231586611263169 48868215471923689958447377)
            ·
              refine ⟨36651161603942767468835533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48868215471923689958447377 36651161603942767468835533)
              ·
                refine ⟨13744185601478537800813325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36651161603942767468835533 13744185601478537800813325)
                ·
                  refine ⟨5154069600554451675304997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13744185601478537800813325 5154069600554451675304997)
                  ·
                    refine ⟨966388050103959689119687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5154069600554451675304997 966388050103959689119687)
                    ·
                      rfl

theorem cell22_2823051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 4].length) (baseStart_2823051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823051 prefixEnd_2823051 := by exact prefixLift 2823051
  have htrace : WordTrace (prefixWord ++ tailWord_2823051) baseStart_2823051 baseEnd_2823051 := by
    simpa [prefixWord, tailWord_2823051, baseEnd_2823051] using wordTrace_append hprefix tailTrace_2823051
  have hstable : (prefixWord ++ tailWord_2823051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823051).length < 2 ^ (prefixWord ++ tailWord_2823051).sum := by decide
  have hdescent : baseEnd_2823051 < baseStart_2823051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823111 : List Nat := [1, 1, 4, 1, 1, 2, 4, 8]
def baseStart_2823111 : Nat := 118140960795 + 2823111 * 2 ^ 59
def prefixEnd_2823111 : Nat := 4983230072969 + 3 ^ 40 * 2823111 * 2
def baseEnd_2823111 : Nat := 107378732147793281402167

theorem tailTrace_2823111 : CollatzResearch.WordTrace tailWord_2823111 prefixEnd_2823111 107378732147793281402167 := by
  unfold tailWord_2823111
  simp only [CollatzResearch.WordTrace]
  refine ⟨102967317275358470818069187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68644878183572313878712791 102967317275358470818069187)
  ·
    refine ⟨154450975913037706227103781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102967317275358470818069187 154450975913037706227103781)
    ·
      refine ⟨28959557983694569917581959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154450975913037706227103781 28959557983694569917581959)
      ·
        refine ⟨43439336975541854876372939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28959557983694569917581959 43439336975541854876372939)
        ·
          refine ⟨65159005463312782314559409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43439336975541854876372939 65159005463312782314559409)
          ·
            refine ⟨48869254097484586735919557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65159005463312782314559409 48869254097484586735919557)
            ·
              refine ⟨9162985143278360012984917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48869254097484586735919557 9162985143278360012984917)
              ·
                refine ⟨107378732147793281402167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9162985143278360012984917 107378732147793281402167)
                ·
                  rfl

theorem cell22_2823111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 8].length) (baseStart_2823111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823111 prefixEnd_2823111 := by exact prefixLift 2823111
  have htrace : WordTrace (prefixWord ++ tailWord_2823111) baseStart_2823111 baseEnd_2823111 := by
    simpa [prefixWord, tailWord_2823111, baseEnd_2823111] using wordTrace_append hprefix tailTrace_2823111
  have hstable : (prefixWord ++ tailWord_2823111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823111).length < 2 ^ (prefixWord ++ tailWord_2823111).sum := by decide
  have hdescent : baseEnd_2823111 < baseStart_2823111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823218 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_2823218 : Nat := 118140960795 + 2823218 * 2 ^ 59
def prefixEnd_2823218 : Nat := 4983230072969 + 3 ^ 40 * 2823218 * 2
def baseEnd_2823218 : Nat := 322148405872275640064725

theorem tailTrace_2823218 : CollatzResearch.WordTrace tailWord_2823218 prefixEnd_2823218 322148405872275640064725 := by
  unfold tailWord_2823218
  simp only [CollatzResearch.WordTrace]
  refine ⟨25742804971492707023053577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68647479923980552061476205 25742804971492707023053577)
  ·
    refine ⟨19307103728619530267290183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25742804971492707023053577 19307103728619530267290183)
    ·
      refine ⟨28960655592929295400935275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19307103728619530267290183 28960655592929295400935275)
      ·
        refine ⟨43440983389393943101402913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28960655592929295400935275 43440983389393943101402913)
        ·
          refine ⟨32580737542045457326052185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43440983389393943101402913 32580737542045457326052185)
          ·
            refine ⟨24435553156534092994539139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32580737542045457326052185 24435553156534092994539139)
            ·
              refine ⟨36653329734801139491808709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24435553156534092994539139 36653329734801139491808709)
              ·
                refine ⟨6872499325275213654714133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36653329734801139491808709 6872499325275213654714133)
                ·
                  refine ⟨322148405872275640064725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6872499325275213654714133 322148405872275640064725)
                  ·
                    rfl

theorem cell22_2823218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_2823218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823218 prefixEnd_2823218 := by exact prefixLift 2823218
  have htrace : WordTrace (prefixWord ++ tailWord_2823218) baseStart_2823218 baseEnd_2823218 := by
    simpa [prefixWord, tailWord_2823218, baseEnd_2823218] using wordTrace_append hprefix tailTrace_2823218
  have hstable : (prefixWord ++ tailWord_2823218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823218).length < 2 ^ (prefixWord ++ tailWord_2823218).sum := by decide
  have hdescent : baseEnd_2823218 < baseStart_2823218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823263 : List Nat := [1, 1, 2, 3, 1, 1, 6, 7]
def baseStart_2823263 : Nat := 118140960795 + 2823263 * 2 ^ 59
def prefixEnd_2823263 : Nat := 4983230072969 + 3 ^ 40 * 2823263 * 2
def baseEnd_2823263 : Nat := 107384513559606866979893

theorem tailTrace_2823263 : CollatzResearch.WordTrace tailWord_2823263 prefixEnd_2823263 107384513559606866979893 := by
  unfold tailWord_2823263
  simp only [CollatzResearch.WordTrace]
  refine ⟨102972861170807800777602443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68648574113871867185068295 102972861170807800777602443)
  ·
    refine ⟨154459291756211701166403665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102972861170807800777602443 154459291756211701166403665)
    ·
      refine ⟨115844468817158775874802749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154459291756211701166403665 115844468817158775874802749)
      ·
        refine ⟨43441675806434540953051031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115844468817158775874802749 43441675806434540953051031)
        ·
          refine ⟨65162513709651811429576547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43441675806434540953051031 65162513709651811429576547)
          ·
            refine ⟨97743770564477717144364821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65162513709651811429576547 97743770564477717144364821)
            ·
              refine ⟨4581739245209892991142101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97743770564477717144364821 4581739245209892991142101)
              ·
                refine ⟨107384513559606866979893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4581739245209892991142101 107384513559606866979893)
                ·
                  rfl

theorem cell22_2823263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 7].length) (baseStart_2823263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823263 prefixEnd_2823263 := by exact prefixLift 2823263
  have htrace : WordTrace (prefixWord ++ tailWord_2823263) baseStart_2823263 baseEnd_2823263 := by
    simpa [prefixWord, tailWord_2823263, baseEnd_2823263] using wordTrace_append hprefix tailTrace_2823263
  have hstable : (prefixWord ++ tailWord_2823263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823263).length < 2 ^ (prefixWord ++ tailWord_2823263).sum := by decide
  have hdescent : baseEnd_2823263 < baseStart_2823263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823308 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 7]
def baseStart_2823308 : Nat := 118140960795 + 2823308 * 2 ^ 59
def prefixEnd_2823308 : Nat := 4983230072969 + 3 ^ 40 * 2823308 * 2
def baseEnd_2823308 : Nat := 322158675485365561814633

theorem tailTrace_2823308 : CollatzResearch.WordTrace tailWord_2823308 prefixEnd_2823308 322158675485365561814633 := by
  unfold tailWord_2823308
  simp only [CollatzResearch.WordTrace]
  refine ⟨51487251227822386731495289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68649668303763182308660385 51487251227822386731495289)
  ·
    refine ⟨38615438420866790048621467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51487251227822386731495289 38615438420866790048621467)
    ·
      refine ⟨57923157631300185072932201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38615438420866790048621467 57923157631300185072932201)
      ·
        refine ⟨43442368223475138804699151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57923157631300185072932201 43442368223475138804699151)
        ·
          refine ⟨65163552335212708207048727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43442368223475138804699151 65163552335212708207048727)
          ·
            refine ⟨97745328502819062310573091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65163552335212708207048727 97745328502819062310573091)
            ·
              refine ⟨146617992754228593465859637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97745328502819062310573091 146617992754228593465859637)
              ·
                refine ⟨13745436820708930637424341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146617992754228593465859637 13745436820708930637424341)
                ·
                  refine ⟨322158675485365561814633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13745436820708930637424341 322158675485365561814633)
                  ·
                    rfl

theorem cell22_2823308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_2823308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823308 prefixEnd_2823308 := by exact prefixLift 2823308
  have htrace : WordTrace (prefixWord ++ tailWord_2823308) baseStart_2823308 baseEnd_2823308 := by
    simpa [prefixWord, tailWord_2823308, baseEnd_2823308] using wordTrace_append hprefix tailTrace_2823308
  have hstable : (prefixWord ++ tailWord_2823308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823308).length < 2 ^ (prefixWord ++ tailWord_2823308).sum := by decide
  have hdescent : baseEnd_2823308 < baseStart_2823308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823310 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2823310 : Nat := 118140960795 + 2823310 * 2 ^ 59
def prefixEnd_2823310 : Nat := 4983230072969 + 3 ^ 40 * 2823310 * 2
def baseEnd_2823310 : Nat := 966476711096969346893893

theorem tailTrace_2823310 : CollatzResearch.WordTrace tailWord_2823310 prefixEnd_2823310 966476711096969346893893 := by
  unfold tailWord_2823310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12871821925204690975570423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68649716934425018536375589 12871821925204690975570423)
  ·
    refine ⟨19307732887807036463355635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12871821925204690975570423 19307732887807036463355635)
    ·
      refine ⟨28961599331710554695033453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19307732887807036463355635 28961599331710554695033453)
      ·
        refine ⟨10860599749391458010637545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28961599331710554695033453 10860599749391458010637545)
        ·
          refine ⟨8145449812043593507978159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10860599749391458010637545 8145449812043593507978159)
          ·
            refine ⟨12218174718065390261967239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8145449812043593507978159 12218174718065390261967239)
            ·
              refine ⟨18327262077098085392950859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12218174718065390261967239 18327262077098085392950859)
              ·
                refine ⟨27490893115647128089426289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18327262077098085392950859 27490893115647128089426289)
                ·
                  refine ⟨20618169836735346067069717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27490893115647128089426289 20618169836735346067069717)
                  ·
                    refine ⟨966476711096969346893893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20618169836735346067069717 966476711096969346893893)
                    ·
                      rfl

theorem cell22_2823310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2823310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823310 prefixEnd_2823310 := by exact prefixLift 2823310
  have htrace : WordTrace (prefixWord ++ tailWord_2823310) baseStart_2823310 baseEnd_2823310 := by
    simpa [prefixWord, tailWord_2823310, baseEnd_2823310] using wordTrace_append hprefix tailTrace_2823310
  have hstable : (prefixWord ++ tailWord_2823310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823310).length < 2 ^ (prefixWord ++ tailWord_2823310).sum := by decide
  have hdescent : baseEnd_2823310 < baseStart_2823310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823325 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 5]
def baseStart_2823325 : Nat := 118140960795 + 2823325 * 2 ^ 59
def prefixEnd_2823325 : Nat := 4983230072969 + 3 ^ 40 * 2823325 * 2
def baseEnd_2823325 : Nat := 322160615301171435922949

theorem tailTrace_2823325 : CollatzResearch.WordTrace tailWord_2823325 prefixEnd_2823325 322160615301171435922949 := by
  unfold tailWord_2823325
  simp only [CollatzResearch.WordTrace]
  refine ⟨102975122496583185366359429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68650081664388790244239619 102975122496583185366359429)
  ·
    refine ⟨19307835468109347256192393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102975122496583185366359429 19307835468109347256192393)
    ·
      refine ⟨14480876601082010442144295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19307835468109347256192393 14480876601082010442144295)
      ·
        refine ⟨21721314901623015663216443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14480876601082010442144295 21721314901623015663216443)
        ·
          refine ⟨32581972352434523494824665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21721314901623015663216443 32581972352434523494824665)
          ·
            refine ⟨24436479264325892621118499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32581972352434523494824665 24436479264325892621118499)
            ·
              refine ⟨36654718896488838931677749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24436479264325892621118499 36654718896488838931677749)
              ·
                refine ⟨3436379896545828649844789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36654718896488838931677749 3436379896545828649844789)
                ·
                  refine ⟨322160615301171435922949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3436379896545828649844789 322160615301171435922949)
                  ·
                    rfl

theorem cell22_2823325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_2823325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823325 prefixEnd_2823325 := by exact prefixLift 2823325
  have htrace : WordTrace (prefixWord ++ tailWord_2823325) baseStart_2823325 baseEnd_2823325 := by
    simpa [prefixWord, tailWord_2823325, baseEnd_2823325] using wordTrace_append hprefix tailTrace_2823325
  have hstable : (prefixWord ++ tailWord_2823325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823325).length < 2 ^ (prefixWord ++ tailWord_2823325).sum := by decide
  have hdescent : baseEnd_2823325 < baseStart_2823325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823370 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_2823370 : Nat := 118140960795 + 2823370 * 2 ^ 59
def prefixEnd_2823370 : Nat := 4983230072969 + 3 ^ 40 * 2823370 * 2
def baseEnd_2823370 : Nat := 322165750107716396797903

theorem tailTrace_2823370 : CollatzResearch.WordTrace tailWord_2823370 prefixEnd_2823370 322165750107716396797903 := by
  unfold tailWord_2823370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25744190945355039512936891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68651175854280105367831709 25744190945355039512936891)
  ·
    refine ⟨38616286418032559269405337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25744190945355039512936891 38616286418032559269405337)
    ·
      refine ⟨28962214813524419452054003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38616286418032559269405337 28962214813524419452054003)
      ·
        refine ⟨43443322220286629178081005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28962214813524419452054003 43443322220286629178081005)
        ·
          refine ⟨16291245832607485941780377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43443322220286629178081005 16291245832607485941780377)
          ·
            refine ⟨12218434374455614456335283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16291245832607485941780377 12218434374455614456335283)
            ·
              refine ⟨18327651561683421684502925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12218434374455614456335283 18327651561683421684502925)
              ·
                refine ⟨6872869335631283131688597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18327651561683421684502925 6872869335631283131688597)
                ·
                  refine ⟨322165750107716396797903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6872869335631283131688597 322165750107716396797903)
                  ·
                    rfl

theorem cell22_2823370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_2823370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823370 prefixEnd_2823370 := by exact prefixLift 2823370
  have htrace : WordTrace (prefixWord ++ tailWord_2823370) baseStart_2823370 baseEnd_2823370 := by
    simpa [prefixWord, tailWord_2823370, baseEnd_2823370] using wordTrace_append hprefix tailTrace_2823370
  have hstable : (prefixWord ++ tailWord_2823370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823370).length < 2 ^ (prefixWord ++ tailWord_2823370).sum := by decide
  have hdescent : baseEnd_2823370 < baseStart_2823370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823400 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2823400 : Nat := 118140960795 + 2823400 * 2 ^ 59
def prefixEnd_2823400 : Nat := 4983230072969 + 3 ^ 40 * 2823400 * 2
def baseEnd_2823400 : Nat := 966507519936239112143617

theorem tailTrace_2823400 : CollatzResearch.WordTrace tailWord_2823400 prefixEnd_2823400 966507519936239112143617 := by
  unfold tailWord_2823400
  simp only [CollatzResearch.WordTrace]
  refine ⟨51488928985655736587669827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68651905314207648783559769 51488928985655736587669827)
  ·
    refine ⟨77233393478483604881504741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51488928985655736587669827 77233393478483604881504741)
    ·
      refine ⟨14481261277215675915282139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77233393478483604881504741 14481261277215675915282139)
      ·
        refine ⟨21721891915823513872923209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14481261277215675915282139 21721891915823513872923209)
        ·
          refine ⟨16291418936867635404692407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21721891915823513872923209 16291418936867635404692407)
          ·
            refine ⟨24437128405301453107038611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16291418936867635404692407 24437128405301453107038611)
            ·
              refine ⟨36655692607952179660557917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24437128405301453107038611 36655692607952179660557917)
              ·
                refine ⟨13745884727982067372709219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36655692607952179660557917 13745884727982067372709219)
                ·
                  refine ⟨20618827091973101059063829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13745884727982067372709219 20618827091973101059063829)
                  ·
                    refine ⟨966507519936239112143617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20618827091973101059063829 966507519936239112143617)
                    ·
                      rfl

theorem cell22_2823400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2823400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823400 prefixEnd_2823400 := by exact prefixLift 2823400
  have htrace : WordTrace (prefixWord ++ tailWord_2823400) baseStart_2823400 baseEnd_2823400 := by
    simpa [prefixWord, tailWord_2823400, baseEnd_2823400] using wordTrace_append hprefix tailTrace_2823400
  have hstable : (prefixWord ++ tailWord_2823400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823400).length < 2 ^ (prefixWord ++ tailWord_2823400).sum := by decide
  have hdescent : baseEnd_2823400 < baseStart_2823400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823402 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_2823402 : Nat := 118140960795 + 2823402 * 2 ^ 59
def prefixEnd_2823402 : Nat := 4983230072969 + 3 ^ 40 * 2823402 * 2
def baseEnd_2823402 : Nat := 966508204577111773593611

theorem tailTrace_2823402 : CollatzResearch.WordTrace tailWord_2823402 prefixEnd_2823402 966508204577111773593611 := by
  unfold tailWord_2823402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25744482729326056879228115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68651953944869485011274973 25744482729326056879228115)
  ·
    refine ⟨38616724093989085318842173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25744482729326056879228115 38616724093989085318842173)
    ·
      refine ⟨14481271535245906994565815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38616724093989085318842173 14481271535245906994565815)
      ·
        refine ⟨21721907302868860491848723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14481271535245906994565815 21721907302868860491848723)
        ·
          refine ⟨32582860954303290737773085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21721907302868860491848723 32582860954303290737773085)
          ·
            refine ⟨12218572857863734026664907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32582860954303290737773085 12218572857863734026664907)
            ·
              refine ⟨18327859286795601039997361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12218572857863734026664907 18327859286795601039997361)
              ·
                refine ⟨13745894465096700779998021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18327859286795601039997361 13745894465096700779998021)
                ·
                  refine ⟨2577355212205631396249629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13745894465096700779998021 2577355212205631396249629)
                  ·
                    refine ⟨966508204577111773593611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577355212205631396249629 966508204577111773593611)
                    ·
                      rfl

theorem cell22_2823402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_2823402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823402 prefixEnd_2823402 := by exact prefixLift 2823402
  have htrace : WordTrace (prefixWord ++ tailWord_2823402) baseStart_2823402 baseEnd_2823402 := by
    simpa [prefixWord, tailWord_2823402, baseEnd_2823402] using wordTrace_append hprefix tailTrace_2823402
  have hstable : (prefixWord ++ tailWord_2823402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823402).length < 2 ^ (prefixWord ++ tailWord_2823402).sum := by decide
  have hdescent : baseEnd_2823402 < baseStart_2823402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823404 : List Nat := [2, 2, 1, 1, 2, 6, 1, 3, 4]
def baseStart_2823404 : Nat := 118140960795 + 2823404 * 2 ^ 59
def prefixEnd_2823404 : Nat := 4983230072969 + 3 ^ 40 * 2823404 * 2
def baseEnd_2823404 : Nat := 322169629739328145014535

theorem tailTrace_2823404 : CollatzResearch.WordTrace tailWord_2823404 prefixEnd_2823404 322169629739328145014535 := by
  unfold tailWord_2823404
  simp only [CollatzResearch.WordTrace]
  refine ⟨51489001931648490929242633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68652002575531321238990177 51489001931648490929242633)
  ·
    refine ⟨38616751448736368196931975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51489001931648490929242633 38616751448736368196931975)
    ·
      refine ⟨57925127173104552295397963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38616751448736368196931975 57925127173104552295397963)
      ·
        refine ⟨86887690759656828443096945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57925127173104552295397963 86887690759656828443096945)
        ·
          refine ⟨65165768069742621332322709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86887690759656828443096945 65165768069742621332322709)
          ·
            refine ⟨3054645378269185374952627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65165768069742621332322709 3054645378269185374952627)
            ·
              refine ⟨4581968067403778062428941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054645378269185374952627 4581968067403778062428941)
              ·
                refine ⟨1718238025276416773410853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4581968067403778062428941 1718238025276416773410853)
                ·
                  refine ⟨322169629739328145014535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1718238025276416773410853 322169629739328145014535)
                  ·
                    rfl

theorem cell22_2823404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_2823404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823404 prefixEnd_2823404 := by exact prefixLift 2823404
  have htrace : WordTrace (prefixWord ++ tailWord_2823404) baseStart_2823404 baseEnd_2823404 := by
    simpa [prefixWord, tailWord_2823404, baseEnd_2823404] using wordTrace_append hprefix tailTrace_2823404
  have hstable : (prefixWord ++ tailWord_2823404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823404).length < 2 ^ (prefixWord ++ tailWord_2823404).sum := by decide
  have hdescent : baseEnd_2823404 < baseStart_2823404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823432 : List Nat := [2, 1, 3, 2, 4, 1, 2, 7]
def baseStart_2823432 : Nat := 118140960795 + 2823432 * 2 ^ 59
def prefixEnd_2823432 : Nat := 4983230072969 + 3 ^ 40 * 2823432 * 2
def baseEnd_2823432 : Nat := 107390941576689077260391

theorem tailTrace_2823432 : CollatzResearch.WordTrace tailWord_2823432 prefixEnd_2823432 107390941576689077260391 := by
  unfold tailWord_2823432
  simp only [CollatzResearch.WordTrace]
  refine ⟨51489512553597771320252275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68652683404797028427003033 51489512553597771320252275)
  ·
    refine ⟨77234268830396656980378413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51489512553597771320252275 77234268830396656980378413)
    ·
      refine ⟨28962850811398746367641905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77234268830396656980378413 28962850811398746367641905)
      ·
        refine ⟨21722138108549059775731429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28962850811398746367641905 21722138108549059775731429)
        ·
          refine ⟨4072900895352948707949643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21722138108549059775731429 4072900895352948707949643)
          ·
            refine ⟨6109351343029423061924465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072900895352948707949643 6109351343029423061924465)
            ·
              refine ⟨4582013507272067296443349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6109351343029423061924465 4582013507272067296443349)
              ·
                refine ⟨107390941576689077260391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4582013507272067296443349 107390941576689077260391)
                ·
                  rfl

theorem cell22_2823432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 7].length) (baseStart_2823432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823432 prefixEnd_2823432 := by exact prefixLift 2823432
  have htrace : WordTrace (prefixWord ++ tailWord_2823432) baseStart_2823432 baseEnd_2823432 := by
    simpa [prefixWord, tailWord_2823432, baseEnd_2823432] using wordTrace_append hprefix tailTrace_2823432
  have hstable : (prefixWord ++ tailWord_2823432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823432).length < 2 ^ (prefixWord ++ tailWord_2823432).sum := by decide
  have hdescent : baseEnd_2823432 < baseStart_2823432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823436 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_2823436 : Nat := 118140960795 + 2823436 * 2 ^ 59
def prefixEnd_2823436 : Nat := 4983230072969 + 3 ^ 40 * 2823436 * 2
def baseEnd_2823436 : Nat := 966519843471947018243507

theorem tailTrace_2823436 : CollatzResearch.WordTrace tailWord_2823436 prefixEnd_2823436 966519843471947018243507 := by
  unfold tailWord_2823436
  simp only [CollatzResearch.WordTrace]
  refine ⟨51489585499590525661825081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68652780666120700882433441 51489585499590525661825081)
  ·
    refine ⟨38617189124692894246368811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51489585499590525661825081 38617189124692894246368811)
    ·
      refine ⟨57925783687039341369553217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38617189124692894246368811 57925783687039341369553217)
      ·
        refine ⟨43444337765279506027164913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57925783687039341369553217 43444337765279506027164913)
        ·
          refine ⟨32583253323959629520373685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43444337765279506027164913 32583253323959629520373685)
          ·
            refine ⟨3054679999121215267535033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32583253323959629520373685 3054679999121215267535033)
            ·
              refine ⟨2291009999340911450651275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054679999121215267535033 2291009999340911450651275)
              ·
                refine ⟨3436514999011367175976913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291009999340911450651275 3436514999011367175976913)
                ·
                  refine ⟨2577386249258525381982685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3436514999011367175976913 2577386249258525381982685)
                  ·
                    refine ⟨966519843471947018243507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577386249258525381982685 966519843471947018243507)
                    ·
                      rfl

theorem cell22_2823436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_2823436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823436 prefixEnd_2823436 := by exact prefixLift 2823436
  have htrace : WordTrace (prefixWord ++ tailWord_2823436) baseStart_2823436 baseEnd_2823436 := by
    simpa [prefixWord, tailWord_2823436, baseEnd_2823436] using wordTrace_append hprefix tailTrace_2823436
  have hstable : (prefixWord ++ tailWord_2823436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823436).length < 2 ^ (prefixWord ++ tailWord_2823436).sum := by decide
  have hdescent : baseEnd_2823436 < baseStart_2823436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823447 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 5, 3]
def baseStart_2823447 : Nat := 118140960795 + 2823447 * 2 ^ 59
def prefixEnd_2823447 : Nat := 4983230072969 + 3 ^ 40 * 2823447 * 2
def baseEnd_2823447 : Nat := 966523608996746656218473

theorem tailTrace_2823447 : CollatzResearch.WordTrace tailWord_2823447 prefixEnd_2823447 966523608996746656218473 := by
  unfold tailWord_2823447
  simp only [CollatzResearch.WordTrace]
  refine ⟨102979572202141200202300595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68653048134760800134867063 102979572202141200202300595)
  ·
    refine ⟨154469358303211800303450893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102979572202141200202300595 154469358303211800303450893)
    ·
      refine ⟨57926009363704425113794085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154469358303211800303450893 57926009363704425113794085)
      ·
        refine ⟨10861126755694579708836391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57926009363704425113794085 10861126755694579708836391)
        ·
          refine ⟨16291690133541869563254587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10861126755694579708836391 16291690133541869563254587)
          ·
            refine ⟨24437535200312804344881881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16291690133541869563254587 24437535200312804344881881)
            ·
              refine ⟨18328151400234603258661411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24437535200312804344881881 18328151400234603258661411)
              ·
                refine ⟨27492227100351904887992117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18328151400234603258661411 27492227100351904887992117)
                ·
                  refine ⟨2577396290657991083249261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27492227100351904887992117 2577396290657991083249261)
                  ·
                    refine ⟨966523608996746656218473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577396290657991083249261 966523608996746656218473)
                    ·
                      rfl

theorem cell22_2823447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_2823447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823447 prefixEnd_2823447 := by exact prefixLift 2823447
  have htrace : WordTrace (prefixWord ++ tailWord_2823447) baseStart_2823447 baseEnd_2823447 := by
    simpa [prefixWord, tailWord_2823447, baseEnd_2823447] using wordTrace_append hprefix tailTrace_2823447
  have hstable : (prefixWord ++ tailWord_2823447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823447).length < 2 ^ (prefixWord ++ tailWord_2823447).sum := by decide
  have hdescent : baseEnd_2823447 < baseStart_2823447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823477 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 5]
def baseStart_2823477 : Nat := 118140960795 + 2823477 * 2 ^ 59
def prefixEnd_2823477 : Nat := 4983230072969 + 3 ^ 40 * 2823477 * 2
def baseEnd_2823477 : Nat := 322177959536612192656127

theorem tailTrace_2823477 : CollatzResearch.WordTrace tailWord_2823477 prefixEnd_2823477 322177959536612192656127 := by
  unfold tailWord_2823477
  simp only [CollatzResearch.WordTrace]
  refine ⟨102980666392032515325892685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68653777594688343550595123 102980666392032515325892685)
  ·
    refine ⟨38617749897012193247209757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102980666392032515325892685 38617749897012193247209757)
    ·
      refine ⟨14481656211379572467703659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38617749897012193247209757 14481656211379572467703659)
      ·
        refine ⟨21722484317069358701555489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14481656211379572467703659 21722484317069358701555489)
        ·
          refine ⟨16291863237802019026166617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21722484317069358701555489 16291863237802019026166617)
          ·
            refine ⟨12218897428351514269624963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16291863237802019026166617 12218897428351514269624963)
            ·
              refine ⟨18328346142527271404437445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12218897428351514269624963 18328346142527271404437445)
              ·
                refine ⟨3436564901723863388332021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18328346142527271404437445 3436564901723863388332021)
                ·
                  refine ⟨322177959536612192656127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3436564901723863388332021 322177959536612192656127)
                  ·
                    rfl

theorem cell22_2823477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_2823477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823477 prefixEnd_2823477 := by exact prefixLift 2823477
  have htrace : WordTrace (prefixWord ++ tailWord_2823477) baseStart_2823477 baseEnd_2823477 := by
    simpa [prefixWord, tailWord_2823477, baseEnd_2823477] using wordTrace_append hprefix tailTrace_2823477
  have hstable : (prefixWord ++ tailWord_2823477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823477).length < 2 ^ (prefixWord ++ tailWord_2823477).sum := by decide
  have hdescent : baseEnd_2823477 < baseStart_2823477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823507 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 1, 4]
def baseStart_2823507 : Nat := 118140960795 + 2823507 * 2 ^ 59
def prefixEnd_2823507 : Nat := 4983230072969 + 3 ^ 40 * 2823507 * 2
def baseEnd_2823507 : Nat := 966544148222926499718289

theorem tailTrace_2823507 : CollatzResearch.WordTrace tailWord_2823507 prefixEnd_2823507 966544148222926499718289 := by
  unfold tailWord_2823507
  simp only [CollatzResearch.WordTrace]
  refine ⟨102981760581923830449484775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68654507054615886966323183 102981760581923830449484775)
  ·
    refine ⟨154472640872885745674227163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102981760581923830449484775 154472640872885745674227163)
    ·
      refine ⟨231708961309328618511340745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154472640872885745674227163 231708961309328618511340745)
      ·
        refine ⟨173781720981996463883505559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231708961309328618511340745 173781720981996463883505559)
        ·
          refine ⟨260672581472994695825258339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173781720981996463883505559 260672581472994695825258339)
          ·
            refine ⟨391008872209492043737887509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260672581472994695825258339 391008872209492043737887509)
            ·
              refine ⟨18328540884819939550213477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 391008872209492043737887509 18328540884819939550213477)
              ·
                refine ⟨3436601415903738665665027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18328540884819939550213477 3436601415903738665665027)
                ·
                  refine ⟨5154902123855607998497541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436601415903738665665027 5154902123855607998497541)
                  ·
                    refine ⟨966544148222926499718289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5154902123855607998497541 966544148222926499718289)
                    ·
                      rfl

theorem cell22_2823507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 4].length) (baseStart_2823507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823507 prefixEnd_2823507 := by exact prefixLift 2823507
  have htrace : WordTrace (prefixWord ++ tailWord_2823507) baseStart_2823507 baseEnd_2823507 := by
    simpa [prefixWord, tailWord_2823507, baseEnd_2823507] using wordTrace_append hprefix tailTrace_2823507
  have hstable : (prefixWord ++ tailWord_2823507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823507).length < 2 ^ (prefixWord ++ tailWord_2823507).sum := by decide
  have hdescent : baseEnd_2823507 < baseStart_2823507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823522 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2823522 : Nat := 118140960795 + 2823522 * 2 ^ 59
def prefixEnd_2823522 : Nat := 4983230072969 + 3 ^ 40 * 2823522 * 2
def baseEnd_2823522 : Nat := 322183094343157153531081

theorem tailTrace_2823522 : CollatzResearch.WordTrace tailWord_2823522 prefixEnd_2823522 322183094343157153531081 := by
  unfold tailWord_2823522
  simp only [CollatzResearch.WordTrace]
  refine ⟨25745576919217372002820205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68654871784579658674187213 25745576919217372002820205)
  ·
    refine ⟨9654591344706514501057577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25745576919217372002820205 9654591344706514501057577)
    ·
      refine ⟨7240943508529885875793183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9654591344706514501057577 7240943508529885875793183)
      ·
        refine ⟨10861415262794828813689775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7240943508529885875793183 10861415262794828813689775)
        ·
          refine ⟨16292122894192243220534663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10861415262794828813689775 16292122894192243220534663)
          ·
            refine ⟨24438184341288364830801995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16292122894192243220534663 24438184341288364830801995)
            ·
              refine ⟨36657276511932547246202993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24438184341288364830801995 36657276511932547246202993)
              ·
                refine ⟨27492957383949410434652245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36657276511932547246202993 27492957383949410434652245)
                ·
                  refine ⟨322183094343157153531081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27492957383949410434652245 322183094343157153531081)
                  ·
                    rfl

theorem cell22_2823522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2823522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823522 prefixEnd_2823522 := by exact prefixLift 2823522
  have htrace : WordTrace (prefixWord ++ tailWord_2823522) baseStart_2823522 baseEnd_2823522 := by
    simpa [prefixWord, tailWord_2823522, baseEnd_2823522] using wordTrace_append hprefix tailTrace_2823522
  have hstable : (prefixWord ++ tailWord_2823522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823522).length < 2 ^ (prefixWord ++ tailWord_2823522).sum := by decide
  have hdescent : baseEnd_2823522 < baseStart_2823522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823524 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_2823524 : Nat := 118140960795 + 2823524 * 2 ^ 59
def prefixEnd_2823524 : Nat := 4983230072969 + 3 ^ 40 * 2823524 * 2
def baseEnd_2823524 : Nat := 966549967670344122043237

theorem tailTrace_2823524 : CollatzResearch.WordTrace tailWord_2823524 prefixEnd_2823524 966549967670344122043237 := by
  unfold tailWord_2823524
  simp only [CollatzResearch.WordTrace]
  refine ⟨51491190311431121176426813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68654920415241494901902417 51491190311431121176426813)
  ·
    refine ⟨19309196366786670441160055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51491190311431121176426813 19309196366786670441160055)
    ·
      refine ⟨28963794550180005661740083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19309196366786670441160055 28963794550180005661740083)
      ·
        refine ⟨43445691825270008492610125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28963794550180005661740083 43445691825270008492610125)
        ·
          refine ⟨16292134434476253184728797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43445691825270008492610125 16292134434476253184728797)
          ·
            refine ⟨6109550412928594944273299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16292134434476253184728797 6109550412928594944273299)
            ·
              refine ⟨9164325619392892416409949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6109550412928594944273299 9164325619392892416409949)
              ·
                refine ⟨3436622107272334656153731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9164325619392892416409949 3436622107272334656153731)
                ·
                  refine ⟨5154933160908501984230597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436622107272334656153731 5154933160908501984230597)
                  ·
                    refine ⟨966549967670344122043237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5154933160908501984230597 966549967670344122043237)
                    ·
                      rfl

theorem cell22_2823524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_2823524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823524 prefixEnd_2823524 := by exact prefixLift 2823524
  have htrace : WordTrace (prefixWord ++ tailWord_2823524) baseStart_2823524 baseEnd_2823524 := by
    simpa [prefixWord, tailWord_2823524, baseEnd_2823524] using wordTrace_append hprefix tailTrace_2823524
  have hstable : (prefixWord ++ tailWord_2823524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823524).length < 2 ^ (prefixWord ++ tailWord_2823524).sum := by decide
  have hdescent : baseEnd_2823524 < baseStart_2823524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823661 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_2823661 : Nat := 118140960795 + 2823661 * 2 ^ 59
def prefixEnd_2823661 : Nat := 4983230072969 + 3 ^ 40 * 2823661 * 2
def baseEnd_2823661 : Nat := 966596865570121431367817

theorem tailTrace_2823661 : CollatzResearch.WordTrace tailWord_2823661 prefixEnd_2823661 966596865570121431367817 := by
  unfold tailWord_2823661
  simp only [CollatzResearch.WordTrace]
  refine ⟨102987377423365914750590837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68658251615577276500393891 102987377423365914750590837)
  ·
    refine ⟨9655066633440554507867891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102987377423365914750590837 9655066633440554507867891)
    ·
      refine ⟨14482599950160831761801837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9655066633440554507867891 14482599950160831761801837)
      ·
        refine ⟨5430974981310311910675689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14482599950160831761801837 5430974981310311910675689)
        ·
          refine ⟨4073231235982733933006767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5430974981310311910675689 4073231235982733933006767)
          ·
            refine ⟨6109846853974100899510151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073231235982733933006767 6109846853974100899510151)
            ·
              refine ⟨9164770280961151349265227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6109846853974100899510151 9164770280961151349265227)
              ·
                refine ⟨13747155421441727023897841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9164770280961151349265227 13747155421441727023897841)
                ·
                  refine ⟨10310366566081295267923381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13747155421441727023897841 10310366566081295267923381)
                  ·
                    refine ⟨966596865570121431367817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10310366566081295267923381 966596865570121431367817)
                    ·
                      rfl

theorem cell22_2823661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_2823661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823661 prefixEnd_2823661 := by exact prefixLift 2823661
  have htrace : WordTrace (prefixWord ++ tailWord_2823661) baseStart_2823661 baseEnd_2823661 := by
    simpa [prefixWord, tailWord_2823661, baseEnd_2823661] using wordTrace_append hprefix tailTrace_2823661
  have hstable : (prefixWord ++ tailWord_2823661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823661).length < 2 ^ (prefixWord ++ tailWord_2823661).sum := by decide
  have hdescent : baseEnd_2823661 < baseStart_2823661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823689 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 4, 3]
def baseStart_2823689 : Nat := 118140960795 + 2823689 * 2 ^ 59
def prefixEnd_2823689 : Nat := 4983230072969 + 3 ^ 40 * 2823689 * 2
def baseEnd_2823689 : Nat := 966606450542338691667731

theorem tailTrace_2823689 : CollatzResearch.WordTrace tailWord_2823689 prefixEnd_2823689 966606450542338691667731 := by
  unfold tailWord_2823689
  simp only [CollatzResearch.WordTrace]
  refine ⟨102988398667264475532610121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68658932444842983688406747 102988398667264475532610121)
  ·
    refine ⟨77241299000448356649457591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102988398667264475532610121 77241299000448356649457591)
    ·
      refine ⟨115861948500672534974186387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77241299000448356649457591 115861948500672534974186387)
      ·
        refine ⟨173792922751008802461279581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115861948500672534974186387 173792922751008802461279581)
        ·
          refine ⟨65172346031628300922979843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173792922751008802461279581 65172346031628300922979843)
          ·
            refine ⟨97758519047442451384469765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65172346031628300922979843 97758519047442451384469765)
            ·
              refine ⟨18329722321395459634588081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97758519047442451384469765 18329722321395459634588081)
              ·
                refine ⟨13747291741046594725941061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18329722321395459634588081 13747291741046594725941061)
                ·
                  refine ⟨2577617201446236511113949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13747291741046594725941061 2577617201446236511113949)
                  ·
                    refine ⟨966606450542338691667731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577617201446236511113949 966606450542338691667731)
                    ·
                      rfl

theorem cell22_2823689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_2823689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823689 prefixEnd_2823689 := by exact prefixLift 2823689
  have htrace : WordTrace (prefixWord ++ tailWord_2823689) baseStart_2823689 baseEnd_2823689 := by
    simpa [prefixWord, tailWord_2823689, baseEnd_2823689] using wordTrace_append hprefix tailTrace_2823689
  have hstable : (prefixWord ++ tailWord_2823689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823689).length < 2 ^ (prefixWord ++ tailWord_2823689).sum := by decide
  have hdescent : baseEnd_2823689 < baseStart_2823689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823736 : List Nat := [2, 1, 2, 1, 4, 4, 2, 6]
def baseStart_2823736 : Nat := 118140960795 + 2823736 * 2 ^ 59
def prefixEnd_2823736 : Nat := 4983230072969 + 3 ^ 40 * 2823736 * 2
def baseEnd_2823736 : Nat := 107402504400316248415843

theorem tailTrace_2823736 : CollatzResearch.WordTrace tailWord_2823736 prefixEnd_2823736 107402504400316248415843 := by
  unfold tailWord_2823736
  simp only [CollatzResearch.WordTrace]
  refine ⟨51495056449047101279785531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68660075265396135039714041 51495056449047101279785531)
  ·
    refine ⟨77242584673570651919678297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51495056449047101279785531 77242584673570651919678297)
    ·
      refine ⟨57931938505177988939758723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77242584673570651919678297 57931938505177988939758723)
      ·
        refine ⟨86897907757766983409638085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57931938505177988939758723 86897907757766983409638085)
        ·
          refine ⟨16293357704581309389307141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86897907757766983409638085 16293357704581309389307141)
          ·
            refine ⟨3055004569608995510495089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16293357704581309389307141 3055004569608995510495089)
            ·
              refine ⟨2291253427206746632871317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055004569608995510495089 2291253427206746632871317)
              ·
                refine ⟨107402504400316248415843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2291253427206746632871317 107402504400316248415843)
                ·
                  rfl

theorem cell22_2823736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 6].length) (baseStart_2823736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823736 prefixEnd_2823736 := by exact prefixLift 2823736
  have htrace : WordTrace (prefixWord ++ tailWord_2823736) baseStart_2823736 baseEnd_2823736 := by
    simpa [prefixWord, tailWord_2823736, baseEnd_2823736] using wordTrace_append hprefix tailTrace_2823736
  have hstable : (prefixWord ++ tailWord_2823736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823736).length < 2 ^ (prefixWord ++ tailWord_2823736).sum := by decide
  have hdescent : baseEnd_2823736 < baseStart_2823736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823764 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2823764 : Nat := 118140960795 + 2823764 * 2 ^ 59
def prefixEnd_2823764 : Nat := 4983230072969 + 3 ^ 40 * 2823764 * 2
def baseEnd_2823764 : Nat := 322210708191687832014167

theorem tailTrace_2823764 : CollatzResearch.WordTrace tailWord_2823764 prefixEnd_2823764 322210708191687832014167 := by
  unfold tailWord_2823764
  simp only [CollatzResearch.WordTrace]
  refine ⟨51495567070996381670795173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68660756094661842227726897 51495567070996381670795173)
  ·
    refine ⟨9655418825811821563274095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51495567070996381670795173 9655418825811821563274095)
    ·
      refine ⟨14483128238717732344911143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9655418825811821563274095 14483128238717732344911143)
      ·
        refine ⟨21724692358076598517366715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14483128238717732344911143 21724692358076598517366715)
        ·
          refine ⟨32587038537114897776050073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21724692358076598517366715 32587038537114897776050073)
          ·
            refine ⟨24440278902836173332037555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32587038537114897776050073 24440278902836173332037555)
            ·
              refine ⟨36660418354254259998056333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24440278902836173332037555 36660418354254259998056333)
              ·
                refine ⟨13747656882845347499271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36660418354254259998056333 13747656882845347499271125)
                ·
                  refine ⟨322210708191687832014167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13747656882845347499271125 322210708191687832014167)
                  ·
                    rfl

theorem cell22_2823764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2823764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823764 prefixEnd_2823764 := by exact prefixLift 2823764
  have htrace : WordTrace (prefixWord ++ tailWord_2823764) baseStart_2823764 baseEnd_2823764 := by
    simpa [prefixWord, tailWord_2823764, baseEnd_2823764] using wordTrace_append hprefix tailTrace_2823764
  have hstable : (prefixWord ++ tailWord_2823764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823764).length < 2 ^ (prefixWord ++ tailWord_2823764).sum := by decide
  have hdescent : baseEnd_2823764 < baseStart_2823764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823781 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 5]
def baseStart_2823781 : Nat := 118140960795 + 2823781 * 2 ^ 59
def prefixEnd_2823781 : Nat := 4983230072969 + 3 ^ 40 * 2823781 * 2
def baseEnd_2823781 : Nat := 322212648007493706122483

theorem tailTrace_2823781 : CollatzResearch.WordTrace tailWord_2823781 prefixEnd_2823781 322212648007493706122483 := by
  unfold tailWord_2823781
  simp only [CollatzResearch.WordTrace]
  refine ⟨102991754182931175244959197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68661169455287450163306131 102991754182931175244959197)
  ·
    refine ⟨38621907818599190716859699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102991754182931175244959197 38621907818599190716859699)
    ·
      refine ⟨57932861727898786075289549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38621907818599190716859699 57932861727898786075289549)
      ·
        refine ⟨21724823147962044778233581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57932861727898786075289549 21724823147962044778233581)
        ·
          refine ⟨8146808680485766791837593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21724823147962044778233581 8146808680485766791837593)
          ·
            refine ⟨6110106510364325093878195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8146808680485766791837593 6110106510364325093878195)
            ·
              refine ⟨9165159765546487640817293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110106510364325093878195 9165159765546487640817293)
              ·
                refine ⟨3436934912079932865306485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9165159765546487640817293 3436934912079932865306485)
                ·
                  refine ⟨322212648007493706122483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3436934912079932865306485 322212648007493706122483)
                  ·
                    rfl

theorem cell22_2823781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_2823781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823781 prefixEnd_2823781 := by exact prefixLift 2823781
  have htrace : WordTrace (prefixWord ++ tailWord_2823781) baseStart_2823781 baseEnd_2823781 := by
    simpa [prefixWord, tailWord_2823781, baseEnd_2823781] using wordTrace_append hprefix tailTrace_2823781
  have hstable : (prefixWord ++ tailWord_2823781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823781).length < 2 ^ (prefixWord ++ tailWord_2823781).sum := by decide
  have hdescent : baseEnd_2823781 < baseStart_2823781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823841 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2823841 : Nat := 118140960795 + 2823841 * 2 ^ 59
def prefixEnd_2823841 : Nat := 4983230072969 + 3 ^ 40 * 2823841 * 2
def baseEnd_2823841 : Nat := 966658483248660961867265

theorem tailTrace_2823841 : CollatzResearch.WordTrace tailWord_2823841 prefixEnd_2823841 966658483248660961867265 := by
  unfold tailWord_2823841
  simp only [CollatzResearch.WordTrace]
  refine ⟨102993942562713805492143377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68662628375142536994762251 102993942562713805492143377)
  ·
    refine ⟨77245456922035354119107533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102993942562713805492143377 77245456922035354119107533)
    ·
      refine ⟨28967046345763257794665325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77245456922035354119107533 28967046345763257794665325)
      ·
        refine ⟨10862642379661221672999497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28967046345763257794665325 10862642379661221672999497)
        ·
          refine ⟨8146981784745916254749623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10862642379661221672999497 8146981784745916254749623)
          ·
            refine ⟨12220472677118874382124435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8146981784745916254749623 12220472677118874382124435)
            ·
              refine ⟨18330709015678311573186653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12220472677118874382124435 18330709015678311573186653)
              ·
                refine ⟨6874015880879366839944995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18330709015678311573186653 6874015880879366839944995)
                ·
                  refine ⟨10311023821319050259917493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6874015880879366839944995 10311023821319050259917493)
                  ·
                    refine ⟨966658483248660961867265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10311023821319050259917493 966658483248660961867265)
                    ·
                      rfl

theorem cell22_2823841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2823841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823841 prefixEnd_2823841 := by exact prefixLift 2823841
  have htrace : WordTrace (prefixWord ++ tailWord_2823841) baseStart_2823841 baseEnd_2823841 := by
    simpa [prefixWord, tailWord_2823841, baseEnd_2823841] using wordTrace_append hprefix tailTrace_2823841
  have hstable : (prefixWord ++ tailWord_2823841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823841).length < 2 ^ (prefixWord ++ tailWord_2823841).sum := by decide
  have hdescent : baseEnd_2823841 < baseStart_2823841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823856 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_2823856 : Nat := 118140960795 + 2823856 * 2 ^ 59
def prefixEnd_2823856 : Nat := 4983230072969 + 3 ^ 40 * 2823856 * 2
def baseEnd_2823856 : Nat := 966663618055205922742219

theorem tailTrace_2823856 : CollatzResearch.WordTrace tailWord_2823856 prefixEnd_2823856 966663618055205922742219 := by
  unfold tailWord_2823856
  simp only [CollatzResearch.WordTrace]
  refine ⟨51497244828829731526969711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68662993105106308702626281 51497244828829731526969711)
  ·
    refine ⟨77245867243244597290454567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51497244828829731526969711 77245867243244597290454567)
    ·
      refine ⟨115868800864866895935681851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77245867243244597290454567 115868800864866895935681851)
      ·
        refine ⟨173803201297300343903522777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115868800864866895935681851 173803201297300343903522777)
        ·
          refine ⟨130352400972975257927642083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173803201297300343903522777 130352400972975257927642083)
          ·
            refine ⟨195528601459462886891463125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130352400972975257927642083 195528601459462886891463125)
            ·
              refine ⟨4582701596706161411518667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 195528601459462886891463125 4582701596706161411518667)
              ·
                refine ⟨6874052395059242117278001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4582701596706161411518667 6874052395059242117278001)
                ·
                  refine ⟨5155539296294431587958501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6874052395059242117278001 5155539296294431587958501)
                  ·
                    refine ⟨966663618055205922742219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155539296294431587958501 966663618055205922742219)
                    ·
                      rfl

theorem cell22_2823856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_2823856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823856 prefixEnd_2823856 := by exact prefixLift 2823856
  have htrace : WordTrace (prefixWord ++ tailWord_2823856) baseStart_2823856 baseEnd_2823856 := by
    simpa [prefixWord, tailWord_2823856, baseEnd_2823856] using wordTrace_append hprefix tailTrace_2823856
  have hstable : (prefixWord ++ tailWord_2823856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823856).length < 2 ^ (prefixWord ++ tailWord_2823856).sum := by decide
  have hdescent : baseEnd_2823856 < baseStart_2823856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823862 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2823862 : Nat := 118140960795 + 2823862 * 2 ^ 59
def prefixEnd_2823862 : Nat := 4983230072969 + 3 ^ 40 * 2823862 * 2
def baseEnd_2823862 : Nat := 966665671977823907092201

theorem tailTrace_2823862 : CollatzResearch.WordTrace tailWord_2823862 prefixEnd_2823862 966665671977823907092201 := by
  unfold tailWord_2823862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437169280977357879916115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68663138997091817385771893 6437169280977357879916115)
  ·
    refine ⟨9655753921466036819874173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6437169280977357879916115 9655753921466036819874173)
    ·
      refine ⟨3620907720549763807452815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9655753921466036819874173 3620907720549763807452815)
      ·
        refine ⟨5431361580824645711179223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3620907720549763807452815 5431361580824645711179223)
        ·
          refine ⟨8147042371236968566768835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5431361580824645711179223 8147042371236968566768835)
          ·
            refine ⟨12220563556855452850153253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8147042371236968566768835 12220563556855452850153253)
            ·
              refine ⟨2291355666910397409403735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12220563556855452850153253 2291355666910397409403735)
              ·
                refine ⟨3437033500365596114105603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291355666910397409403735 3437033500365596114105603)
                ·
                  refine ⟨5155550250548394171158405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437033500365596114105603 5155550250548394171158405)
                  ·
                    refine ⟨966665671977823907092201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155550250548394171158405 966665671977823907092201)
                    ·
                      rfl

theorem cell22_2823862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2823862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823862 prefixEnd_2823862 := by exact prefixLift 2823862
  have htrace : WordTrace (prefixWord ++ tailWord_2823862) baseStart_2823862 baseEnd_2823862 := by
    simpa [prefixWord, tailWord_2823862, baseEnd_2823862] using wordTrace_append hprefix tailTrace_2823862
  have hstable : (prefixWord ++ tailWord_2823862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823862).length < 2 ^ (prefixWord ++ tailWord_2823862).sum := by decide
  have hdescent : baseEnd_2823862 < baseStart_2823862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823892 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_2823892 : Nat := 118140960795 + 2823892 * 2 ^ 59
def prefixEnd_2823892 : Nat := 4983230072969 + 3 ^ 40 * 2823892 * 2
def baseEnd_2823892 : Nat := 966675941590913828842109

theorem tailTrace_2823892 : CollatzResearch.WordTrace tailWord_2823892 prefixEnd_2823892 966675941590913828842109 := by
  unfold tailWord_2823892
  simp only [CollatzResearch.WordTrace]
  refine ⟨51497901342764520601124965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68663868457019360801499953 51497901342764520601124965)
  ·
    refine ⟨9655856501768347612710931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51497901342764520601124965 9655856501768347612710931)
    ·
      refine ⟨14483784752652521419066397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9655856501768347612710931 14483784752652521419066397)
      ·
        refine ⟨5431419282244695532149899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14483784752652521419066397 5431419282244695532149899)
        ·
          refine ⟨8147128923367043298224849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5431419282244695532149899 8147128923367043298224849)
          ·
            refine ⟨6110346692525282473668637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8147128923367043298224849 6110346692525282473668637)
            ·
              refine ⟨2291380009696980927625739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6110346692525282473668637 2291380009696980927625739)
              ·
                refine ⟨3437070014545471391438609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291380009696980927625739 3437070014545471391438609)
                ·
                  refine ⟨2577802510909103543578957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3437070014545471391438609 2577802510909103543578957)
                  ·
                    refine ⟨966675941590913828842109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2577802510909103543578957 966675941590913828842109)
                    ·
                      rfl

theorem cell22_2823892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_2823892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823892 prefixEnd_2823892 := by exact prefixLift 2823892
  have htrace : WordTrace (prefixWord ++ tailWord_2823892) baseStart_2823892 baseEnd_2823892 := by
    simpa [prefixWord, tailWord_2823892, baseEnd_2823892] using wordTrace_append hprefix tailTrace_2823892
  have hstable : (prefixWord ++ tailWord_2823892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823892).length < 2 ^ (prefixWord ++ tailWord_2823892).sum := by decide
  have hdescent : baseEnd_2823892 < baseStart_2823892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823905 : List Nat := [1, 2, 3, 1, 6, 1, 2, 6]
def baseStart_2823905 : Nat := 118140960795 + 2823905 * 2 ^ 59
def prefixEnd_2823905 : Nat := 4983230072969 + 3 ^ 40 * 2823905 * 2
def baseEnd_2823905 : Nat := 107408932417398458696341

theorem tailTrace_2823905 : CollatzResearch.WordTrace tailWord_2823905 prefixEnd_2823905 107408932417398458696341 := by
  unfold tailWord_2823905
  simp only [CollatzResearch.WordTrace]
  refine ⟨102996276834481944422473169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68664184556321296281648779 102996276834481944422473169)
  ·
    refine ⟨77247207625861458316854877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102996276834481944422473169 77247207625861458316854877)
    ·
      refine ⟨28967702859698046868820579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77247207625861458316854877 28967702859698046868820579)
      ·
        refine ⟨43451554289547070303230869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28967702859698046868820579 43451554289547070303230869)
        ·
          refine ⟨2036791607322518920463947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43451554289547070303230869 2036791607322518920463947)
          ·
            refine ⟨3055187410983778380695921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036791607322518920463947 3055187410983778380695921)
            ·
              refine ⟨2291390558237833785521941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055187410983778380695921 2291390558237833785521941)
              ·
                refine ⟨107408932417398458696341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2291390558237833785521941 107408932417398458696341)
                ·
                  rfl

theorem cell22_2823905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 6].length) (baseStart_2823905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823905 prefixEnd_2823905 := by exact prefixLift 2823905
  have htrace : WordTrace (prefixWord ++ tailWord_2823905) baseStart_2823905 baseEnd_2823905 := by
    simpa [prefixWord, tailWord_2823905, baseEnd_2823905] using wordTrace_append hprefix tailTrace_2823905
  have hstable : (prefixWord ++ tailWord_2823905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823905).length < 2 ^ (prefixWord ++ tailWord_2823905).sum := by decide
  have hdescent : baseEnd_2823905 < baseStart_2823905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823980 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_2823980 : Nat := 118140960795 + 2823980 * 2 ^ 59
def prefixEnd_2823980 : Nat := 4983230072969 + 3 ^ 40 * 2823980 * 2
def baseEnd_2823980 : Nat := 966706065789310932641839

theorem tailTrace_2823980 : CollatzResearch.WordTrace tailWord_2823980 prefixEnd_2823980 966706065789310932641839 := by
  unfold tailWord_2823980
  simp only [CollatzResearch.WordTrace]
  refine ⟨51499506154605116115726697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68666008206140154820968929 51499506154605116115726697)
  ·
    refine ⟨38624629615953837086795023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51499506154605116115726697 38624629615953837086795023)
    ·
      refine ⟨57936944423930755630192535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38624629615953837086795023 57936944423930755630192535)
      ·
        refine ⟨86905416635896133445288803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57936944423930755630192535 86905416635896133445288803)
        ·
          refine ⟨130358124953844200167933205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86905416635896133445288803 130358124953844200167933205)
          ·
            refine ⟨6110537107211446882871869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130358124953844200167933205 6110537107211446882871869)
            ·
              refine ⟨2291451415204292581076951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6110537107211446882871869 2291451415204292581076951)
              ·
                refine ⟨3437177122806438871615427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291451415204292581076951 3437177122806438871615427)
                ·
                  refine ⟨5155765684209658307423141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437177122806438871615427 5155765684209658307423141)
                  ·
                    refine ⟨966706065789310932641839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155765684209658307423141 966706065789310932641839)
                    ·
                      rfl

theorem cell22_2823980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_2823980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823980 prefixEnd_2823980 := by exact prefixLift 2823980
  have htrace : WordTrace (prefixWord ++ tailWord_2823980) baseStart_2823980 baseEnd_2823980 := by
    simpa [prefixWord, tailWord_2823980, baseEnd_2823980] using wordTrace_append hprefix tailTrace_2823980
  have hstable : (prefixWord ++ tailWord_2823980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823980).length < 2 ^ (prefixWord ++ tailWord_2823980).sum := by decide
  have hdescent : baseEnd_2823980 < baseStart_2823980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823991 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 4, 4]
def baseStart_2823991 : Nat := 118140960795 + 2823991 * 2 ^ 59
def prefixEnd_2823991 : Nat := 4983230072969 + 3 ^ 40 * 2823991 * 2
def baseEnd_2823991 : Nat := 966709831314110570616805

theorem tailTrace_2823991 : CollatzResearch.WordTrace tailWord_2823991 prefixEnd_2823991 966709831314110570616805 := by
  unfold tailWord_2823991
  simp only [CollatzResearch.WordTrace]
  refine ⟨102999413512170381110103827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68666275674780254073402551 102999413512170381110103827)
  ·
    refine ⟨154499120268255571665155741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102999413512170381110103827 154499120268255571665155741)
    ·
      refine ⟨57937170100595839374433403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154499120268255571665155741 57937170100595839374433403)
      ·
        refine ⟨86905755150893759061650105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57937170100595839374433403 86905755150893759061650105)
        ·
          refine ⟨65179316363170319296237579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86905755150893759061650105 65179316363170319296237579)
          ·
            refine ⟨97768974544755478944356369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65179316363170319296237579 97768974544755478944356369)
            ·
              refine ⟨73326730908566609208267277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97768974544755478944356369 73326730908566609208267277)
              ·
                refine ⟨27497524090712478453100229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73326730908566609208267277 27497524090712478453100229)
                ·
                  refine ⟨5155785767008589709956293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27497524090712478453100229 5155785767008589709956293)
                  ·
                    refine ⟨966709831314110570616805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5155785767008589709956293 966709831314110570616805)
                    ·
                      rfl

theorem cell22_2823991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_2823991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2823991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2823991 prefixEnd_2823991 := by exact prefixLift 2823991
  have htrace : WordTrace (prefixWord ++ tailWord_2823991) baseStart_2823991 baseEnd_2823991 := by
    simpa [prefixWord, tailWord_2823991, baseEnd_2823991] using wordTrace_append hprefix tailTrace_2823991
  have hstable : (prefixWord ++ tailWord_2823991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823991).length < 2 ^ (prefixWord ++ tailWord_2823991).sum := by decide
  have hdescent : baseEnd_2823991 < baseStart_2823991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824068 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 5]
def baseStart_2824068 : Nat := 118140960795 + 2824068 * 2 ^ 59
def prefixEnd_2824068 : Nat := 4983230072969 + 3 ^ 40 * 2824068 * 2
def baseEnd_2824068 : Nat := 322245396662569345480523

theorem tailTrace_2824068 : CollatzResearch.WordTrace tailWord_2824068 prefixEnd_2824068 322245396662569345480523 := by
  unfold tailWord_2824068
  simp only [CollatzResearch.WordTrace]
  refine ⟨51501110966445711630328429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68668147955260948840437905 51501110966445711630328429)
  ·
    refine ⟨19312916612417141861373161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51501110966445711630328429 19312916612417141861373161)
    ·
      refine ⟨14484687459312856396029871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19312916612417141861373161 14484687459312856396029871)
      ·
        refine ⟨21727031188969284594044807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14484687459312856396029871 21727031188969284594044807)
        ·
          refine ⟨32590546783453926891067211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21727031188969284594044807 32590546783453926891067211)
          ·
            refine ⟨48885820175180890336600817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32590546783453926891067211 48885820175180890336600817)
            ·
              refine ⟨36664365131385667752450613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48885820175180890336600817 36664365131385667752450613)
              ·
                refine ⟨3437284231067406351792245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36664365131385667752450613 3437284231067406351792245)
                ·
                  refine ⟨322245396662569345480523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3437284231067406351792245 322245396662569345480523)
                  ·
                    rfl

theorem cell22_2824068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_2824068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824068 prefixEnd_2824068 := by exact prefixLift 2824068
  have htrace : WordTrace (prefixWord ++ tailWord_2824068) baseStart_2824068 baseEnd_2824068 := by
    simpa [prefixWord, tailWord_2824068, baseEnd_2824068] using wordTrace_append hprefix tailTrace_2824068
  have hstable : (prefixWord ++ tailWord_2824068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824068).length < 2 ^ (prefixWord ++ tailWord_2824068).sum := by decide
  have hdescent : baseEnd_2824068 < baseStart_2824068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824128 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_2824128 : Nat := 118140960795 + 2824128 * 2 ^ 59
def prefixEnd_2824128 : Nat := 4983230072969 + 3 ^ 40 * 2824128 * 2
def baseEnd_2824128 : Nat := 966756729213887879941385

theorem tailTrace_2824128 : CollatzResearch.WordTrace tailWord_2824128 prefixEnd_2824128 966756729213887879941385 := by
  unfold tailWord_2824128
  simp only [CollatzResearch.WordTrace]
  refine ⟨51502205156337026753920519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68669606875116035671894025 51502205156337026753920519)
  ·
    refine ⟨77253307734505540130880779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51502205156337026753920519 77253307734505540130880779)
    ·
      refine ⟨115879961601758310196321169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77253307734505540130880779 115879961601758310196321169)
      ·
        refine ⟨86909971201318732647240877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115879961601758310196321169 86909971201318732647240877)
        ·
          refine ⟨32591239200494524742715329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86909971201318732647240877 32591239200494524742715329)
          ·
            refine ⟨24443429400370893557036497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32591239200494524742715329 24443429400370893557036497)
            ·
              refine ⟨18332572050278170167777373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24443429400370893557036497 18332572050278170167777373)
              ·
                refine ⟨6874714518854313812916515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18332572050278170167777373 6874714518854313812916515)
                ·
                  refine ⟨10312071778281470719374773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6874714518854313812916515 10312071778281470719374773)
                  ·
                    refine ⟨966756729213887879941385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10312071778281470719374773 966756729213887879941385)
                    ·
                      rfl

theorem cell22_2824128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_2824128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824128 prefixEnd_2824128 := by exact prefixLift 2824128
  have htrace : WordTrace (prefixWord ++ tailWord_2824128) baseStart_2824128 baseEnd_2824128 := by
    simpa [prefixWord, tailWord_2824128, baseEnd_2824128] using wordTrace_append hprefix tailTrace_2824128
  have hstable : (prefixWord ++ tailWord_2824128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824128).length < 2 ^ (prefixWord ++ tailWord_2824128).sum := by decide
  have hdescent : baseEnd_2824128 < baseStart_2824128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824188 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_2824188 : Nat := 118140960795 + 2824188 * 2 ^ 59
def prefixEnd_2824188 : Nat := 4983230072969 + 3 ^ 40 * 2824188 * 2
def baseEnd_2824188 : Nat := 966777268440067723441201

theorem tailTrace_2824188 : CollatzResearch.WordTrace tailWord_2824188 prefixEnd_2824188 966777268440067723441201 := by
  unfold tailWord_2824188
  simp only [CollatzResearch.WordTrace]
  refine ⟨51503299346228341877512609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68671065794971122503350145 51503299346228341877512609)
  ·
    refine ⟨38627474509671256408134457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51503299346228341877512609 38627474509671256408134457)
    ·
      refine ⟨28970605882253442306100843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38627474509671256408134457 28970605882253442306100843)
      ·
        refine ⟨43455908823380163459151265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28970605882253442306100843 43455908823380163459151265)
        ·
          refine ⟨32591931617535122594363449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43455908823380163459151265 32591931617535122594363449)
          ·
            refine ⟨24443948713151341945772587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32591931617535122594363449 24443948713151341945772587)
            ·
              refine ⟨36665923069727012918658881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24443948713151341945772587 36665923069727012918658881)
              ·
                refine ⟨27499442302295259688994161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36665923069727012918658881 27499442302295259688994161)
                ·
                  refine ⟨20624581726721444766745621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27499442302295259688994161 20624581726721444766745621)
                  ·
                    refine ⟨966777268440067723441201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20624581726721444766745621 966777268440067723441201)
                    ·
                      rfl

theorem cell22_2824188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_2824188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824188 prefixEnd_2824188 := by exact prefixLift 2824188
  have htrace : WordTrace (prefixWord ++ tailWord_2824188) baseStart_2824188 baseEnd_2824188 := by
    simpa [prefixWord, tailWord_2824188, baseEnd_2824188] using wordTrace_append hprefix tailTrace_2824188
  have hstable : (prefixWord ++ tailWord_2824188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824188).length < 2 ^ (prefixWord ++ tailWord_2824188).sum := by decide
  have hdescent : baseEnd_2824188 < baseStart_2824188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824203 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 7]
def baseStart_2824203 : Nat := 118140960795 + 2824203 * 2 ^ 59
def prefixEnd_2824203 : Nat := 4983230072969 + 3 ^ 40 * 2824203 * 2
def baseEnd_2824203 : Nat := 322260801082204228105385

theorem tailTrace_2824203 : CollatzResearch.WordTrace tailWord_2824203 prefixEnd_2824203 322260801082204228105385 := by
  unfold tailWord_2824203
  simp only [CollatzResearch.WordTrace]
  refine ⟨103007145787402341316821263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68671430524934894211214175 103007145787402341316821263)
  ·
    refine ⟨154510718681103511975231895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103007145787402341316821263 154510718681103511975231895)
    ·
      refine ⟨231766078021655267962847843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154510718681103511975231895 231766078021655267962847843)
      ·
        refine ⟨347649117032482901944271765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231766078021655267962847843 347649117032482901944271765)
        ·
          refine ⟨16296052360897636028637739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 347649117032482901944271765 16296052360897636028637739)
          ·
            refine ⟨24444078541346454042956609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16296052360897636028637739 24444078541346454042956609)
            ·
              refine ⟨18333058906009840532217457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24444078541346454042956609 18333058906009840532217457)
              ·
                refine ⟨13749794179507380399163093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18333058906009840532217457 13749794179507380399163093)
                ·
                  refine ⟨322260801082204228105385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13749794179507380399163093 322260801082204228105385)
                  ·
                    rfl

theorem cell22_2824203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 7].length) (baseStart_2824203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824203 prefixEnd_2824203 := by exact prefixLift 2824203
  have htrace : WordTrace (prefixWord ++ tailWord_2824203) baseStart_2824203 baseEnd_2824203 := by
    simpa [prefixWord, tailWord_2824203, baseEnd_2824203] using wordTrace_append hprefix tailTrace_2824203
  have hstable : (prefixWord ++ tailWord_2824203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824203).length < 2 ^ (prefixWord ++ tailWord_2824203).sum := by decide
  have hdescent : baseEnd_2824203 < baseStart_2824203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824220 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 7]
def baseStart_2824220 : Nat := 118140960795 + 2824220 * 2 ^ 59
def prefixEnd_2824220 : Nat := 4983230072969 + 3 ^ 40 * 2824220 * 2
def baseEnd_2824220 : Nat := 322262740898010102213701

theorem tailTrace_2824220 : CollatzResearch.WordTrace tailWord_2824220 prefixEnd_2824220 322262740898010102213701 := by
  unfold tailWord_2824220
  simp only [CollatzResearch.WordTrace]
  refine ⟨51503882914170376610095057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68671843885560502146793409 51503882914170376610095057)
  ·
    refine ⟨38627912185627782457571293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51503882914170376610095057 38627912185627782457571293)
    ·
      refine ⟨14485467069610418421589235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38627912185627782457571293 14485467069610418421589235)
      ·
        refine ⟨21728200604415627632383853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14485467069610418421589235 21728200604415627632383853)
        ·
          refine ⟨8148075226655860362143945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21728200604415627632383853 8148075226655860362143945)
          ·
            refine ⟨6111056419991895271607959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8148075226655860362143945 6111056419991895271607959)
            ·
              refine ⟨9166584629987842907411939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111056419991895271607959 9166584629987842907411939)
              ·
                refine ⟨13749876944981764361117909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9166584629987842907411939 13749876944981764361117909)
                ·
                  refine ⟨322262740898010102213701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13749876944981764361117909 322262740898010102213701)
                  ·
                    rfl

theorem cell22_2824220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_2824220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824220 prefixEnd_2824220 := by exact prefixLift 2824220
  have htrace : WordTrace (prefixWord ++ tailWord_2824220) baseStart_2824220 baseEnd_2824220 := by
    simpa [prefixWord, tailWord_2824220, baseEnd_2824220] using wordTrace_append hprefix tailTrace_2824220
  have hstable : (prefixWord ++ tailWord_2824220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824220).length < 2 ^ (prefixWord ++ tailWord_2824220).sum := by decide
  have hdescent : baseEnd_2824220 < baseStart_2824220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824295 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2824295 : Nat := 118140960795 + 2824295 * 2 ^ 59
def prefixEnd_2824295 : Nat := 4983230072969 + 3 ^ 40 * 2824295 * 2
def baseEnd_2824295 : Nat := 966813896726755111015873

theorem tailTrace_2824295 : CollatzResearch.WordTrace tailWord_2824295 prefixEnd_2824295 966813896726755111015873 := by
  unfold tailWord_2824295
  simp only [CollatzResearch.WordTrace]
  refine ⟨103010501303069041029170339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68673667535379360686113559 103010501303069041029170339)
  ·
    refine ⟨154515751954603561543755509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103010501303069041029170339 154515751954603561543755509)
    ·
      refine ⟨14485851745744083894727079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154515751954603561543755509 14485851745744083894727079)
      ·
        refine ⟨21728777618616125842090619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14485851745744083894727079 21728777618616125842090619)
        ·
          refine ⟨32593166427924188763135929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21728777618616125842090619 32593166427924188763135929)
          ·
            refine ⟨24444874820943141572351947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32593166427924188763135929 24444874820943141572351947)
            ·
              refine ⟨36667312231414712358527921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24444874820943141572351947 36667312231414712358527921)
              ·
                refine ⟨27500484173561034268895941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36667312231414712358527921 27500484173561034268895941)
                ·
                  refine ⟨5156340782542693925417989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27500484173561034268895941 5156340782542693925417989)
                  ·
                    refine ⟨966813896726755111015873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156340782542693925417989 966813896726755111015873)
                    ·
                      rfl

theorem cell22_2824295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2824295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824295 prefixEnd_2824295 := by exact prefixLift 2824295
  have htrace : WordTrace (prefixWord ++ tailWord_2824295) baseStart_2824295 baseEnd_2824295 := by
    simpa [prefixWord, tailWord_2824295, baseEnd_2824295] using wordTrace_append hprefix tailTrace_2824295
  have hstable : (prefixWord ++ tailWord_2824295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824295).length < 2 ^ (prefixWord ++ tailWord_2824295).sum := by decide
  have hdescent : baseEnd_2824295 < baseStart_2824295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824297 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 2, 3]
def baseStart_2824297 : Nat := 118140960795 + 2824297 * 2 ^ 59
def prefixEnd_2824297 : Nat := 4983230072969 + 3 ^ 40 * 2824297 * 2
def baseEnd_2824297 : Nat := 966814581367627772465867

theorem tailTrace_2824297 : CollatzResearch.WordTrace tailWord_2824297 prefixEnd_2824297 966814581367627772465867 := by
  unfold tailWord_2824297
  simp only [CollatzResearch.WordTrace]
  refine ⟨103010574249061795370743145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68673716166041196913828763 103010574249061795370743145)
  ·
    refine ⟨77257930686796346528057359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103010574249061795370743145 77257930686796346528057359)
    ·
      refine ⟨115886896030194519792086039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77257930686796346528057359 115886896030194519792086039)
      ·
        refine ⟨173830344045291779688129059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115886896030194519792086039 173830344045291779688129059)
        ·
          refine ⟨260745516067937669532193589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173830344045291779688129059 260745516067937669532193589)
          ·
            refine ⟨24444892131369156518643149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260745516067937669532193589 24444892131369156518643149)
            ·
              refine ⟨9166834549263433694491181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24444892131369156518643149 9166834549263433694491181)
              ·
                refine ⟨3437562955973787635434193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9166834549263433694491181 3437562955973787635434193)
                ·
                  refine ⟨2578172216980340726575645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3437562955973787635434193 2578172216980340726575645)
                  ·
                    refine ⟨966814581367627772465867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578172216980340726575645 966814581367627772465867)
                    ·
                      rfl

theorem cell22_2824297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_2824297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824297 prefixEnd_2824297 := by exact prefixLift 2824297
  have htrace : WordTrace (prefixWord ++ tailWord_2824297) baseStart_2824297 baseEnd_2824297 := by
    simpa [prefixWord, tailWord_2824297, baseEnd_2824297] using wordTrace_append hprefix tailTrace_2824297
  have hstable : (prefixWord ++ tailWord_2824297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824297).length < 2 ^ (prefixWord ++ tailWord_2824297).sum := by decide
  have hdescent : baseEnd_2824297 < baseStart_2824297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824344 : List Nat := [2, 1, 2, 4, 4, 1, 1, 7]
def baseStart_2824344 : Nat := 118140960795 + 2824344 * 2 ^ 59
def prefixEnd_2824344 : Nat := 4983230072969 + 3 ^ 40 * 2824344 * 2
def baseEnd_2824344 : Nat := 107425630047570590726747

theorem tailTrace_2824344 : CollatzResearch.WordTrace tailWord_2824344 prefixEnd_2824344 107425630047570590726747 := by
  unfold tailWord_2824344
  simp only [CollatzResearch.WordTrace]
  refine ⟨51506144239945761198852043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68674858986594348265136057 51506144239945761198852043)
  ·
    refine ⟨77259216359918641798278065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51506144239945761198852043 77259216359918641798278065)
    ·
      refine ⟨57944412269938981348708549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77259216359918641798278065 57944412269938981348708549)
      ·
        refine ⟨10864577300613559002882853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57944412269938981348708549 10864577300613559002882853)
        ·
          refine ⟨2037108243865042313040535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10864577300613559002882853 2037108243865042313040535)
          ·
            refine ⟨3055662365797563469560803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037108243865042313040535 3055662365797563469560803)
            ·
              refine ⟨4583493548696345204341205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055662365797563469560803 4583493548696345204341205)
              ·
                refine ⟨107425630047570590726747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4583493548696345204341205 107425630047570590726747)
                ·
                  rfl

theorem cell22_2824344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 7].length) (baseStart_2824344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824344 prefixEnd_2824344 := by exact prefixLift 2824344
  have htrace : WordTrace (prefixWord ++ tailWord_2824344) baseStart_2824344 baseEnd_2824344 := by
    simpa [prefixWord, tailWord_2824344, baseEnd_2824344] using wordTrace_append hprefix tailTrace_2824344
  have hstable : (prefixWord ++ tailWord_2824344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824344).length < 2 ^ (prefixWord ++ tailWord_2824344).sum := by decide
  have hdescent : baseEnd_2824344 < baseStart_2824344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824370 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2824370 : Nat := 118140960795 + 2824370 * 2 ^ 59
def prefixEnd_2824370 : Nat := 4983230072969 + 3 ^ 40 * 2824370 * 2
def baseEnd_2824370 : Nat := 966839570759479915390643

theorem tailTrace_2824370 : CollatzResearch.WordTrace tailWord_2824370 prefixEnd_2824370 966839570759479915390643 := by
  unfold tailWord_2824370
  simp only [CollatzResearch.WordTrace]
  refine ⟨25753309194449332209537641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68675491185198219225433709 25753309194449332209537641)
  ·
    refine ⟨19314981895836999157153231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25753309194449332209537641 19314981895836999157153231)
    ·
      refine ⟨28972472843755498735729847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19314981895836999157153231 28972472843755498735729847)
      ·
        refine ⟨43458709265633248103594771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28972472843755498735729847 43458709265633248103594771)
        ·
          refine ⟨65188063898449872155392157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43458709265633248103594771 65188063898449872155392157)
          ·
            refine ⟨24445523961918702058272059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65188063898449872155392157 24445523961918702058272059)
            ·
              refine ⟨36668285942878053087408089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24445523961918702058272059 36668285942878053087408089)
              ·
                refine ⟨27501214457158539815556067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36668285942878053087408089 27501214457158539815556067)
                ·
                  refine ⟨41251821685737809723334101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27501214457158539815556067 41251821685737809723334101)
                  ·
                    refine ⟨966839570759479915390643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41251821685737809723334101 966839570759479915390643)
                    ·
                      rfl

theorem cell22_2824370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2824370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824370 prefixEnd_2824370 := by exact prefixLift 2824370
  have htrace : WordTrace (prefixWord ++ tailWord_2824370) baseStart_2824370 baseEnd_2824370 := by
    simpa [prefixWord, tailWord_2824370, baseEnd_2824370] using wordTrace_append hprefix tailTrace_2824370
  have hstable : (prefixWord ++ tailWord_2824370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824370).length < 2 ^ (prefixWord ++ tailWord_2824370).sum := by decide
  have hdescent : baseEnd_2824370 < baseStart_2824370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824447 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 2, 4]
def baseStart_2824447 : Nat := 118140960795 + 2824447 * 2 ^ 59
def prefixEnd_2824447 : Nat := 4983230072969 + 3 ^ 40 * 2824447 * 2
def baseEnd_2824447 : Nat := 966865929433077381215407

theorem tailTrace_2824447 : CollatzResearch.WordTrace tailWord_2824447 prefixEnd_2824447 966865929433077381215407 := by
  unfold tailWord_2824447
  simp only [CollatzResearch.WordTrace]
  refine ⟨103016045198518370988703595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68677363465678913992469063 103016045198518370988703595)
  ·
    refine ⟨154524067797777556483055393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103016045198518370988703595 154524067797777556483055393)
    ·
      refine ⟨115893050848333167362291545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154524067797777556483055393 115893050848333167362291545)
      ·
        refine ⟨86919788136249875521718659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115893050848333167362291545 86919788136249875521718659)
        ·
          refine ⟨130379682204374813282577989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86919788136249875521718659 130379682204374813282577989)
          ·
            refine ⟨24446190413320277490483373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130379682204374813282577989 24446190413320277490483373)
            ·
              refine ⟨9167321404995104058931265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24446190413320277490483373 9167321404995104058931265)
              ·
                refine ⟨6875491053746328044198449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9167321404995104058931265 6875491053746328044198449)
                ·
                  refine ⟨5156618290309746033148837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6875491053746328044198449 5156618290309746033148837)
                  ·
                    refine ⟨966865929433077381215407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156618290309746033148837 966865929433077381215407)
                    ·
                      rfl

theorem cell22_2824447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_2824447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824447 prefixEnd_2824447 := by exact prefixLift 2824447
  have htrace : WordTrace (prefixWord ++ tailWord_2824447) baseStart_2824447 baseEnd_2824447 := by
    simpa [prefixWord, tailWord_2824447, baseEnd_2824447] using wordTrace_append hprefix tailTrace_2824447
  have hstable : (prefixWord ++ tailWord_2824447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824447).length < 2 ^ (prefixWord ++ tailWord_2824447).sum := by decide
  have hdescent : baseEnd_2824447 < baseStart_2824447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824449 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2824449 : Nat := 118140960795 + 2824449 * 2 ^ 59
def prefixEnd_2824449 : Nat := 4983230072969 + 3 ^ 40 * 2824449 * 2
def baseEnd_2824449 : Nat := 966866614073950042665401

theorem tailTrace_2824449 : CollatzResearch.WordTrace tailWord_2824449 prefixEnd_2824449 966866614073950042665401 := by
  unfold tailWord_2824449
  simp only [CollatzResearch.WordTrace]
  refine ⟨103016118144511125330276401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68677412096340750220184267 103016118144511125330276401)
  ·
    refine ⟨77262088608383343997707301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103016118144511125330276401 77262088608383343997707301)
    ·
      refine ⟨14486641614071876999570119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77262088608383343997707301 14486641614071876999570119)
      ·
        refine ⟨21729962421107815499355179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14486641614071876999570119 21729962421107815499355179)
        ·
          refine ⟨32594943631661723249032769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21729962421107815499355179 32594943631661723249032769)
          ·
            refine ⟨24446207723746292436774577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32594943631661723249032769 24446207723746292436774577)
            ·
              refine ⟨18334655792809719327580933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24446207723746292436774577 18334655792809719327580933)
              ·
                refine ⟨3437747961151822373921425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18334655792809719327580933 3437747961151822373921425)
                ·
                  refine ⟨2578310970863866780441069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3437747961151822373921425 2578310970863866780441069)
                  ·
                    refine ⟨966866614073950042665401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578310970863866780441069 966866614073950042665401)
                    ·
                      rfl

theorem cell22_2824449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2824449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824449 prefixEnd_2824449 := by exact prefixLift 2824449
  have htrace : WordTrace (prefixWord ++ tailWord_2824449) baseStart_2824449 baseEnd_2824449 := by
    simpa [prefixWord, tailWord_2824449, baseEnd_2824449] using wordTrace_append hprefix tailTrace_2824449
  have hstable : (prefixWord ++ tailWord_2824449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824449).length < 2 ^ (prefixWord ++ tailWord_2824449).sum := by decide
  have hdescent : baseEnd_2824449 < baseStart_2824449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824462 : List Nat := [4, 1, 1, 2, 1, 2, 4, 7]
def baseStart_2824462 : Nat := 118140960795 + 2824462 * 2 ^ 59
def prefixEnd_2824462 : Nat := 4983230072969 + 3 ^ 40 * 2824462 * 2
def baseEnd_2824462 : Nat := 107430118248846926898929

theorem tailTrace_2824462 : CollatzResearch.WordTrace tailWord_2824462 prefixEnd_2824462 107430118248846926898929 := by
  unfold tailWord_2824462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12877074036683003568812455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68677728195642685700333093 12877074036683003568812455)
  ·
    refine ⟨19315611055024505353218683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12877074036683003568812455 19315611055024505353218683)
    ·
      refine ⟨28973416582536758029828025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19315611055024505353218683 28973416582536758029828025)
      ·
        refine ⟨21730062436902568522371019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28973416582536758029828025 21730062436902568522371019)
        ·
          refine ⟨32595093655353852783556529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21730062436902568522371019 32595093655353852783556529)
          ·
            refine ⟨24446320241515389587667397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32595093655353852783556529 24446320241515389587667397)
            ·
              refine ⟨4583685045284135547687637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24446320241515389587667397 4583685045284135547687637)
              ·
                refine ⟨107430118248846926898929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4583685045284135547687637 107430118248846926898929)
                ·
                  rfl

theorem cell22_2824462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_2824462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824462 prefixEnd_2824462 := by exact prefixLift 2824462
  have htrace : WordTrace (prefixWord ++ tailWord_2824462) baseStart_2824462 baseEnd_2824462 := by
    simpa [prefixWord, tailWord_2824462, baseEnd_2824462] using wordTrace_append hprefix tailTrace_2824462
  have hstable : (prefixWord ++ tailWord_2824462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824462).length < 2 ^ (prefixWord ++ tailWord_2824462).sum := by decide
  have hdescent : baseEnd_2824462 < baseStart_2824462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824511 : List Nat := [1, 1, 2, 2, 4, 1, 3, 4, 1, 3]
def baseStart_2824511 : Nat := 118140960795 + 2824511 * 2 ^ 59
def prefixEnd_2824511 : Nat := 4983230072969 + 3 ^ 40 * 2824511 * 2
def baseEnd_2824511 : Nat := 966887837941002547615211

theorem tailTrace_2824511 : CollatzResearch.WordTrace tailWord_2824511 prefixEnd_2824511 966887837941002547615211 := by
  unfold tailWord_2824511
  simp only [CollatzResearch.WordTrace]
  refine ⟨103018379470286509919033387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68678919646857673279355591 103018379470286509919033387)
  ·
    refine ⟨154527569205429764878550081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103018379470286509919033387 154527569205429764878550081)
    ·
      refine ⟨115895676904072323658912561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154527569205429764878550081 115895676904072323658912561)
      ·
        refine ⟨86921757678054242744184421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115895676904072323658912561 86921757678054242744184421)
        ·
          refine ⟨16297829564635170514534579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86921757678054242744184421 16297829564635170514534579)
          ·
            refine ⟨24446744346952755771801869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16297829564635170514534579 24446744346952755771801869)
            ·
              refine ⟨9167529130107283414425701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24446744346952755771801869 9167529130107283414425701)
              ·
                refine ⟨1718911711895115640204819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9167529130107283414425701 1718911711895115640204819)
                ·
                  refine ⟨2578367567842673460307229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718911711895115640204819 2578367567842673460307229)
                  ·
                    refine ⟨966887837941002547615211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578367567842673460307229 966887837941002547615211)
                    ·
                      rfl

theorem cell22_2824511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 3].length) (baseStart_2824511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824511 prefixEnd_2824511 := by exact prefixLift 2824511
  have htrace : WordTrace (prefixWord ++ tailWord_2824511) baseStart_2824511 baseEnd_2824511 := by
    simpa [prefixWord, tailWord_2824511, baseEnd_2824511] using wordTrace_append hprefix tailTrace_2824511
  have hstable : (prefixWord ++ tailWord_2824511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824511).length < 2 ^ (prefixWord ++ tailWord_2824511).sum := by decide
  have hdescent : baseEnd_2824511 < baseStart_2824511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824616 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2824616 : Nat := 118140960795 + 2824616 * 2 ^ 59
def prefixEnd_2824616 : Nat := 4983230072969 + 3 ^ 40 * 2824616 * 2
def baseEnd_2824616 : Nat := 966923781586817273739889

theorem tailTrace_2824616 : CollatzResearch.WordTrace tailWord_2824616 prefixEnd_2824616 966923781586817273739889 := by
  unfold tailWord_2824616
  simp only [CollatzResearch.WordTrace]
  refine ⟨51511104567453056425802851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68681472756604075234403801 51511104567453056425802851)
  ·
    refine ⟨77266656851179584638704277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51511104567453056425802851 77266656851179584638704277)
    ·
      refine ⟨3621874539899043029939263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77266656851179584638704277 3621874539899043029939263)
      ·
        refine ⟨5432811809848564544908895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621874539899043029939263 5432811809848564544908895)
        ·
          refine ⟨8149217714772846817363343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432811809848564544908895 8149217714772846817363343)
          ·
            refine ⟨12223826572159270226045015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149217714772846817363343 12223826572159270226045015)
            ·
              refine ⟨18335739858238905339067523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12223826572159270226045015 18335739858238905339067523)
              ·
                refine ⟨27503609787358358008601285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18335739858238905339067523 27503609787358358008601285)
                ·
                  refine ⟨5156926835129692126612741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27503609787358358008601285 5156926835129692126612741)
                  ·
                    refine ⟨966923781586817273739889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156926835129692126612741 966923781586817273739889)
                    ·
                      rfl

theorem cell22_2824616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2824616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824616 prefixEnd_2824616 := by exact prefixLift 2824616
  have htrace : WordTrace (prefixWord ++ tailWord_2824616) baseStart_2824616 baseEnd_2824616 := by
    simpa [prefixWord, tailWord_2824616, baseEnd_2824616] using wordTrace_append hprefix tailTrace_2824616
  have hstable : (prefixWord ++ tailWord_2824616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824616).length < 2 ^ (prefixWord ++ tailWord_2824616).sum := by decide
  have hdescent : baseEnd_2824616 < baseStart_2824616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824680 : List Nat := [2, 1, 4, 1, 1, 3, 4, 2, 1, 3]
def baseStart_2824680 : Nat := 118140960795 + 2824680 * 2 ^ 59
def prefixEnd_2824680 : Nat := 4983230072969 + 3 ^ 40 * 2824680 * 2
def baseEnd_2824680 : Nat := 966945690094742440139693

theorem tailTrace_2824680 : CollatzResearch.WordTrace tailWord_2824680 prefixEnd_2824680 966945690094742440139693 := by
  unfold tailWord_2824680
  simp only [CollatzResearch.WordTrace]
  refine ⟨51512271703337125890967747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68683028937782834521290329 51512271703337125890967747)
  ·
    refine ⟨77268407555005688836451621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51512271703337125890967747 77268407555005688836451621)
    ·
      refine ⟨14487826416563566656834679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77268407555005688836451621 14487826416563566656834679)
      ·
        refine ⟨21731739624845349985252019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14487826416563566656834679 21731739624845349985252019)
        ·
          refine ⟨32597609437268024977878029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21731739624845349985252019 32597609437268024977878029)
          ·
            refine ⟨12224103538975509366704261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32597609437268024977878029 12224103538975509366704261)
            ·
              refine ⟨2292019413557908006257049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12224103538975509366704261 2292019413557908006257049)
              ·
                refine ⟨1719014560168431004692787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292019413557908006257049 1719014560168431004692787)
                ·
                  refine ⟨2578521840252646507039181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719014560168431004692787 2578521840252646507039181)
                  ·
                    refine ⟨966945690094742440139693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578521840252646507039181 966945690094742440139693)
                    ·
                      rfl

theorem cell22_2824680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_2824680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824680 prefixEnd_2824680 := by exact prefixLift 2824680
  have htrace : WordTrace (prefixWord ++ tailWord_2824680) baseStart_2824680 baseEnd_2824680 := by
    simpa [prefixWord, tailWord_2824680, baseEnd_2824680] using wordTrace_append hprefix tailTrace_2824680
  have hstable : (prefixWord ++ tailWord_2824680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824680).length < 2 ^ (prefixWord ++ tailWord_2824680).sum := by decide
  have hdescent : baseEnd_2824680 < baseStart_2824680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824689 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_2824689 : Nat := 118140960795 + 2824689 * 2 ^ 59
def prefixEnd_2824689 : Nat := 4983230072969 + 3 ^ 40 * 2824689 * 2
def baseEnd_2824689 : Nat := 966948770978669416664665

theorem tailTrace_2824689 : CollatzResearch.WordTrace tailWord_2824689 prefixEnd_2824689 966948770978669416664665 := by
  unfold tailWord_2824689
  simp only [CollatzResearch.WordTrace]
  refine ⟨103024871663641646319013121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68683247775761097546008747 103024871663641646319013121)
  ·
    refine ⟨77268653747731234739259841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103024871663641646319013121 77268653747731234739259841)
    ·
      refine ⟨57951490310798426054444881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77268653747731234739259841 57951490310798426054444881)
      ·
        refine ⟨43463617733098819540833661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57951490310798426054444881 43463617733098819540833661)
        ·
          refine ⟨16298856649912057327812623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43463617733098819540833661 16298856649912057327812623)
          ·
            refine ⟨24448284974868085991718935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16298856649912057327812623 24448284974868085991718935)
            ·
              refine ⟨36672427462302128987578403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24448284974868085991718935 36672427462302128987578403)
              ·
                refine ⟨55008641193453193481367605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36672427462302128987578403 55008641193453193481367605)
                ·
                  refine ⟨5157060111886236888878213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55008641193453193481367605 5157060111886236888878213)
                  ·
                    refine ⟨966948770978669416664665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157060111886236888878213 966948770978669416664665)
                    ·
                      rfl

theorem cell22_2824689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_2824689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824689 prefixEnd_2824689 := by exact prefixLift 2824689
  have htrace : WordTrace (prefixWord ++ tailWord_2824689) baseStart_2824689 baseEnd_2824689 := by
    simpa [prefixWord, tailWord_2824689, baseEnd_2824689] using wordTrace_append hprefix tailTrace_2824689
  have hstable : (prefixWord ++ tailWord_2824689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824689).length < 2 ^ (prefixWord ++ tailWord_2824689).sum := by decide
  have hdescent : baseEnd_2824689 < baseStart_2824689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824809 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_2824809 : Nat := 118140960795 + 2824809 * 2 ^ 59
def prefixEnd_2824809 : Nat := 4983230072969 + 3 ^ 40 * 2824809 * 2
def baseEnd_2824809 : Nat := 966989849431029103664297

theorem tailTrace_2824809 : CollatzResearch.WordTrace tailWord_2824809 prefixEnd_2824809 966989849431029103664297 := by
  unfold tailWord_2824809
  simp only [CollatzResearch.WordTrace]
  refine ⟨103029248423206906813381481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68686165615471271208920987 103029248423206906813381481)
  ·
    refine ⟨77271936317405180110036111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103029248423206906813381481 77271936317405180110036111)
    ·
      refine ⟨115907904476107770165054167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77271936317405180110036111 115907904476107770165054167)
      ·
        refine ⟨173861856714161655247581251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115907904476107770165054167 173861856714161655247581251)
        ·
          refine ⟨260792785071242482871371877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173861856714161655247581251 260792785071242482871371877)
          ·
            refine ⟨48898647200857965538382227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260792785071242482871371877 48898647200857965538382227)
            ·
              refine ⟨73347970801286948307573341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48898647200857965538382227 73347970801286948307573341)
              ·
                refine ⟨27505489050482605615340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73347970801286948307573341 27505489050482605615340003)
                ·
                  refine ⟨41258233575723908423010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27505489050482605615340003 41258233575723908423010005)
                  ·
                    refine ⟨966989849431029103664297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41258233575723908423010005 966989849431029103664297)
                    ·
                      rfl

theorem cell22_2824809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_2824809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824809 prefixEnd_2824809 := by exact prefixLift 2824809
  have htrace : WordTrace (prefixWord ++ tailWord_2824809) baseStart_2824809 baseEnd_2824809 := by
    simpa [prefixWord, tailWord_2824809, baseEnd_2824809] using wordTrace_append hprefix tailTrace_2824809
  have hstable : (prefixWord ++ tailWord_2824809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824809).length < 2 ^ (prefixWord ++ tailWord_2824809).sum := by decide
  have hdescent : baseEnd_2824809 < baseStart_2824809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824824 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_2824824 : Nat := 118140960795 + 2824824 * 2 ^ 59
def prefixEnd_2824824 : Nat := 4983230072969 + 3 ^ 40 * 2824824 * 2
def baseEnd_2824824 : Nat := 966994984237574064539251

theorem tailTrace_2824824 : CollatzResearch.WordTrace tailWord_2824824 prefixEnd_2824824 966994984237574064539251 := by
  unfold tailWord_2824824
  simp only [CollatzResearch.WordTrace]
  refine ⟨51514897759076282187588763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68686530345435042916785017 51514897759076282187588763)
  ·
    refine ⟨77272346638614423281383145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51514897759076282187588763 77272346638614423281383145)
    ·
      refine ⟨57954259978960817461037359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77272346638614423281383145 57954259978960817461037359)
      ·
        refine ⟨86931389968441226191556039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57954259978960817461037359 86931389968441226191556039)
        ·
          refine ⟨130397084952661839287334059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86931389968441226191556039 130397084952661839287334059)
          ·
            refine ⟨195595627428992758931001089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130397084952661839287334059 195595627428992758931001089)
            ·
              refine ⟨146696720571744569198250817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195595627428992758931001089 146696720571744569198250817)
              ·
                refine ⟨110022540428808426898688113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146696720571744569198250817 110022540428808426898688113)
                ·
                  refine ⟨82516905321606320174016085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110022540428808426898688113 82516905321606320174016085)
                  ·
                    refine ⟨966994984237574064539251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82516905321606320174016085 966994984237574064539251)
                    ·
                      rfl

theorem cell22_2824824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_2824824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824824 prefixEnd_2824824 := by exact prefixLift 2824824
  have htrace : WordTrace (prefixWord ++ tailWord_2824824) baseStart_2824824 baseEnd_2824824 := by
    simpa [prefixWord, tailWord_2824824, baseEnd_2824824] using wordTrace_append hprefix tailTrace_2824824
  have hstable : (prefixWord ++ tailWord_2824824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824824).length < 2 ^ (prefixWord ++ tailWord_2824824).sum := by decide
  have hdescent : baseEnd_2824824 < baseStart_2824824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824856 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 6]
def baseStart_2824856 : Nat := 118140960795 + 2824856 * 2 ^ 59
def prefixEnd_2824856 : Nat := 4983230072969 + 3 ^ 40 * 2824856 * 2
def baseEnd_2824856 : Nat := 322335312830512215913051

theorem tailTrace_2824856 : CollatzResearch.WordTrace tailWord_2824856 prefixEnd_2824856 322335312830512215913051 := by
  unfold tailWord_2824856
  simp only [CollatzResearch.WordTrace]
  refine ⟨51515481327018316920171211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68687308436024422560228281 51515481327018316920171211)
  ·
    refine ⟨77273221990527475380256817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51515481327018316920171211 77273221990527475380256817)
    ·
      refine ⟨57954916492895606535192613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77273221990527475380256817 57954916492895606535192613)
      ·
        refine ⟨10866546842417926225348615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57954916492895606535192613 10866546842417926225348615)
        ·
          refine ⟨16299820263626889338022923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10866546842417926225348615 16299820263626889338022923)
          ·
            refine ⟨24449730395440334007034385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16299820263626889338022923 24449730395440334007034385)
            ·
              refine ⟨18337297796580250505275789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24449730395440334007034385 18337297796580250505275789)
              ·
                refine ⟨6876486673717593939478421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18337297796580250505275789 6876486673717593939478421)
                ·
                  refine ⟨322335312830512215913051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6876486673717593939478421 322335312830512215913051)
                  ·
                    rfl

theorem cell22_2824856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_2824856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824856 prefixEnd_2824856 := by exact prefixLift 2824856
  have htrace : WordTrace (prefixWord ++ tailWord_2824856) baseStart_2824856 baseEnd_2824856 := by
    simpa [prefixWord, tailWord_2824856, baseEnd_2824856] using wordTrace_append hprefix tailTrace_2824856
  have hstable : (prefixWord ++ tailWord_2824856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824856).length < 2 ^ (prefixWord ++ tailWord_2824856).sum := by decide
  have hdescent : baseEnd_2824856 < baseStart_2824856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824967 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 3, 3]
def baseStart_2824967 : Nat := 118140960795 + 2824967 * 2 ^ 59
def prefixEnd_2824967 : Nat := 4983230072969 + 3 ^ 40 * 2824967 * 2
def baseEnd_2824967 : Nat := 967043936059969358213813

theorem tailTrace_2824967 : CollatzResearch.WordTrace tailWord_2824967 prefixEnd_2824967 967043936059969358213813 := by
  unfold tailWord_2824967
  simp only [CollatzResearch.WordTrace]
  refine ⟨103035011156634499797633155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68690007437756333198422103 103035011156634499797633155)
  ·
    refine ⟨154552516734951749696449733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103035011156634499797633155 154552516734951749696449733)
    ·
      refine ⟨28978596887803453068084325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154552516734951749696449733 28978596887803453068084325)
      ·
        refine ⟨5433486916463147450265811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28978596887803453068084325 5433486916463147450265811)
        ·
          refine ⟨8150230374694721175398717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433486916463147450265811 8150230374694721175398717)
          ·
            refine ⟨3056336390510520440774519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8150230374694721175398717 3056336390510520440774519)
            ·
              refine ⟨4584504585765780661161779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056336390510520440774519 4584504585765780661161779)
              ·
                refine ⟨6876756878648670991742669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584504585765780661161779 6876756878648670991742669)
                ·
                  refine ⟨2578783829493251621903501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6876756878648670991742669 2578783829493251621903501)
                  ·
                    refine ⟨967043936059969358213813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578783829493251621903501 967043936059969358213813)
                    ·
                      rfl

theorem cell22_2824967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_2824967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824967 prefixEnd_2824967 := by exact prefixLift 2824967
  have htrace : WordTrace (prefixWord ++ tailWord_2824967) baseStart_2824967 baseEnd_2824967 := by
    simpa [prefixWord, tailWord_2824967, baseEnd_2824967] using wordTrace_append hprefix tailTrace_2824967
  have hstable : (prefixWord ++ tailWord_2824967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824967).length < 2 ^ (prefixWord ++ tailWord_2824967).sum := by decide
  have hdescent : baseEnd_2824967 < baseStart_2824967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824993 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2824993 : Nat := 118140960795 + 2824993 * 2 ^ 59
def prefixEnd_2824993 : Nat := 4983230072969 + 3 ^ 40 * 2824993 * 2
def baseEnd_2824993 : Nat := 967052836391313957063733

theorem tailTrace_2824993 : CollatzResearch.WordTrace tailWord_2824993 prefixEnd_2824993 967052836391313957063733 := by
  unfold tailWord_2824993
  simp only [CollatzResearch.WordTrace]
  refine ⟨103035959454540306238079633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68690639636360204158719755 103035959454540306238079633)
  ·
    refine ⟨77276969590905229678559725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103035959454540306238079633 77276969590905229678559725)
    ·
      refine ⟨28978863596589461129459897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77276969590905229678559725 28978863596589461129459897)
      ·
        refine ⟨21734147697442095847094923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28978863596589461129459897 21734147697442095847094923)
        ·
          refine ⟨32601221546163143770642385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21734147697442095847094923 32601221546163143770642385)
          ·
            refine ⟨24450916159622357827981789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32601221546163143770642385 24450916159622357827981789)
            ·
              refine ⟨9169093559858384185493171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24450916159622357827981789 9169093559858384185493171)
              ·
                refine ⟨13753640339787576278239757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9169093559858384185493171 13753640339787576278239757)
                ·
                  refine ⟨5157615127420341104339909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13753640339787576278239757 5157615127420341104339909)
                  ·
                    refine ⟨967052836391313957063733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157615127420341104339909 967052836391313957063733)
                    ·
                      rfl

theorem cell22_2824993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2824993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2824993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2824993 prefixEnd_2824993 := by exact prefixLift 2824993
  have htrace : WordTrace (prefixWord ++ tailWord_2824993) baseStart_2824993 baseEnd_2824993 := by
    simpa [prefixWord, tailWord_2824993, baseEnd_2824993] using wordTrace_append hprefix tailTrace_2824993
  have hstable : (prefixWord ++ tailWord_2824993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824993).length < 2 ^ (prefixWord ++ tailWord_2824993).sum := by decide
  have hdescent : baseEnd_2824993 < baseStart_2824993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825038 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2825038 : Nat := 118140960795 + 2825038 * 2 ^ 59
def prefixEnd_2825038 : Nat := 4983230072969 + 3 ^ 40 * 2825038 * 2
def baseEnd_2825038 : Nat := 967068240810948839688595

theorem tailTrace_2825038 : CollatzResearch.WordTrace tailWord_2825038 prefixEnd_2825038 967068240810948839688595 := by
  unfold tailWord_2825038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879700092422159865433471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68691733826251519282311845 12879700092422159865433471)
  ·
    refine ⟨19319550138633239798150207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12879700092422159865433471 19319550138633239798150207)
    ·
      refine ⟨28979325207949859697225311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19319550138633239798150207 28979325207949859697225311)
      ·
        refine ⟨43468987811924789545837967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28979325207949859697225311 43468987811924789545837967)
        ·
          refine ⟨65203481717887184318756951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43468987811924789545837967 65203481717887184318756951)
          ·
            refine ⟨97805222576830776478135427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65203481717887184318756951 97805222576830776478135427)
            ·
              refine ⟨146707833865246164717203141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97805222576830776478135427 146707833865246164717203141)
              ·
                refine ⟨27507718849733655884475589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146707833865246164717203141 27507718849733655884475589)
                ·
                  refine ⟨5157697284325060478339173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27507718849733655884475589 5157697284325060478339173)
                  ·
                    refine ⟨967068240810948839688595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157697284325060478339173 967068240810948839688595)
                    ·
                      rfl

theorem cell22_2825038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2825038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825038 prefixEnd_2825038 := by exact prefixLift 2825038
  have htrace : WordTrace (prefixWord ++ tailWord_2825038) baseStart_2825038 baseEnd_2825038 := by
    simpa [prefixWord, tailWord_2825038, baseEnd_2825038] using wordTrace_append hprefix tailTrace_2825038
  have hstable : (prefixWord ++ tailWord_2825038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825038).length < 2 ^ (prefixWord ++ tailWord_2825038).sum := by decide
  have hdescent : baseEnd_2825038 < baseStart_2825038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825040 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 2, 3]
def baseStart_2825040 : Nat := 118140960795 + 2825040 * 2 ^ 59
def prefixEnd_2825040 : Nat := 4983230072969 + 3 ^ 40 * 2825040 * 2
def baseEnd_2825040 : Nat := 967068925451821501138589

theorem tailTrace_2825040 : CollatzResearch.WordTrace tailWord_2825040 prefixEnd_2825040 967068925451821501138589 := by
  unfold tailWord_2825040
  simp only [CollatzResearch.WordTrace]
  refine ⟨51518836842685016632520287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68691782456913355510027049 51518836842685016632520287)
  ·
    refine ⟨77278255264027524948780431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51518836842685016632520287 77278255264027524948780431)
    ·
      refine ⟨115917382896041287423170647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77278255264027524948780431 115917382896041287423170647)
      ·
        refine ⟨173876074344061931134755971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115917382896041287423170647 173876074344061931134755971)
        ·
          refine ⟨260814111516092896702133957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173876074344061931134755971 260814111516092896702133957)
          ·
            refine ⟨48902645909267418131650117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260814111516092896702133957 48902645909267418131650117)
            ·
              refine ⟨9169246107987640899684397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48902645909267418131650117 9169246107987640899684397)
              ·
                refine ⟨3438467290495365337381649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9169246107987640899684397 3438467290495365337381649)
                ·
                  refine ⟨2578850467871524003036237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3438467290495365337381649 2578850467871524003036237)
                  ·
                    refine ⟨967068925451821501138589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578850467871524003036237 967068925451821501138589)
                    ·
                      rfl

theorem cell22_2825040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_2825040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825040 prefixEnd_2825040 := by exact prefixLift 2825040
  have htrace : WordTrace (prefixWord ++ tailWord_2825040) baseStart_2825040 baseEnd_2825040 := by
    simpa [prefixWord, tailWord_2825040, baseEnd_2825040] using wordTrace_append hprefix tailTrace_2825040
  have hstable : (prefixWord ++ tailWord_2825040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825040).length < 2 ^ (prefixWord ++ tailWord_2825040).sum := by decide
  have hdescent : baseEnd_2825040 < baseStart_2825040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825070 : List Nat := [4, 1, 2, 3, 2, 1, 9]
def baseStart_2825070 : Nat := 118140960795 + 2825070 * 2 ^ 59
def prefixEnd_2825070 : Nat := 4983230072969 + 3 ^ 40 * 2825070 * 2
def baseEnd_2825070 : Nat := 35817747965367089736611

theorem tailTrace_2825070 : CollatzResearch.WordTrace tailWord_2825070 prefixEnd_2825070 35817747965367089736611 := by
  unfold tailWord_2825070
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879845984407668548579083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68692511916840898925755109 12879845984407668548579083)
  ·
    refine ⟨19319768976611502822868625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12879845984407668548579083 19319768976611502822868625)
    ·
      refine ⟨14489826732458627117151469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19319768976611502822868625 14489826732458627117151469)
      ·
        refine ⟨5433685024671985168931801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14489826732458627117151469 5433685024671985168931801)
        ·
          refine ⟨4075263768503988876698851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5433685024671985168931801 4075263768503988876698851)
          ·
            refine ⟨6112895652755983315048277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075263768503988876698851 6112895652755983315048277)
            ·
              refine ⟨35817747965367089736611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6112895652755983315048277 35817747965367089736611)
              ·
                rfl

theorem cell22_2825070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 9].length) (baseStart_2825070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825070 prefixEnd_2825070 := by exact prefixLift 2825070
  have htrace : WordTrace (prefixWord ++ tailWord_2825070) baseStart_2825070 baseEnd_2825070 := by
    simpa [prefixWord, tailWord_2825070, baseEnd_2825070] using wordTrace_append hprefix tailTrace_2825070
  have hstable : (prefixWord ++ tailWord_2825070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825070).length < 2 ^ (prefixWord ++ tailWord_2825070).sum := by decide
  have hdescent : baseEnd_2825070 < baseStart_2825070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825085 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2825085 : Nat := 118140960795 + 2825085 * 2 ^ 59
def prefixEnd_2825085 : Nat := 4983230072969 + 3 ^ 40 * 2825085 * 2
def baseEnd_2825085 : Nat := 967084329871456383763451

theorem tailTrace_2825085 : CollatzResearch.WordTrace tailWord_2825085 prefixEnd_2825085 967084329871456383763451 := by
  unfold tailWord_2825085
  simp only [CollatzResearch.WordTrace]
  refine ⟨103039314970207005950428709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68692876646804670633619139 103039314970207005950428709)
  ·
    refine ⟨19319871556913813615705383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103039314970207005950428709 19319871556913813615705383)
    ·
      refine ⟨28979807335370720423558075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19319871556913813615705383 28979807335370720423558075)
      ·
        refine ⟨43469711003056080635337113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28979807335370720423558075 43469711003056080635337113)
        ·
          refine ⟨32602283252292060476502835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43469711003056080635337113 32602283252292060476502835)
          ·
            refine ⟨48903424878438090714754253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32602283252292060476502835 48903424878438090714754253)
            ·
              refine ⟨18338784329414284018032845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48903424878438090714754253 18338784329414284018032845)
              ·
                refine ⟨6877044123530356506762317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18338784329414284018032845 6877044123530356506762317)
                ·
                  refine ⟨2578891546323883690035869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6877044123530356506762317 2578891546323883690035869)
                  ·
                    refine ⟨967084329871456383763451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578891546323883690035869 967084329871456383763451)
                    ·
                      rfl

theorem cell22_2825085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2825085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825085 prefixEnd_2825085 := by exact prefixLift 2825085
  have htrace : WordTrace (prefixWord ++ tailWord_2825085) baseStart_2825085 baseEnd_2825085 := by
    simpa [prefixWord, tailWord_2825085, baseEnd_2825085] using wordTrace_append hprefix tailTrace_2825085
  have hstable : (prefixWord ++ tailWord_2825085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825085).length < 2 ^ (prefixWord ++ tailWord_2825085).sum := by decide
  have hdescent : baseEnd_2825085 < baseStart_2825085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825119 : List Nat := [1, 1, 2, 5, 2, 1, 3, 3, 1, 3]
def baseStart_2825119 : Nat := 118140960795 + 2825119 * 2 ^ 59
def prefixEnd_2825119 : Nat := 4983230072969 + 3 ^ 40 * 2825119 * 2
def baseEnd_2825119 : Nat := 967095968766291628413347

theorem tailTrace_2825119 : CollatzResearch.WordTrace tailWord_2825119 prefixEnd_2825119 967095968766291628413347 := by
  unfold tailWord_2825119
  simp only [CollatzResearch.WordTrace]
  refine ⟨103040555052083829757166411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68693703368055886504777607 103040555052083829757166411)
  ·
    refine ⟨154560832578125744635749617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103040555052083829757166411 154560832578125744635749617)
    ·
      refine ⟨115920624433594308476812213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154560832578125744635749617 115920624433594308476812213)
      ·
        refine ⟨10867558540649466419701145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115920624433594308476812213 10867558540649466419701145)
        ·
          refine ⟨8150668905487099814775859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10867558540649466419701145 8150668905487099814775859)
          ·
            refine ⟨12226003358230649722163789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8150668905487099814775859 12226003358230649722163789)
            ·
              refine ⟨4584751259336493645811421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12226003358230649722163789 4584751259336493645811421)
              ·
                refine ⟨1719281722251185117179283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4584751259336493645811421 1719281722251185117179283)
                ·
                  refine ⟨2578922583376777675768925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719281722251185117179283 2578922583376777675768925)
                  ·
                    refine ⟨967095968766291628413347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578922583376777675768925 967095968766291628413347)
                    ·
                      rfl

theorem cell22_2825119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 1, 3].length) (baseStart_2825119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825119 prefixEnd_2825119 := by exact prefixLift 2825119
  have htrace : WordTrace (prefixWord ++ tailWord_2825119) baseStart_2825119 baseEnd_2825119 := by
    simpa [prefixWord, tailWord_2825119, baseEnd_2825119] using wordTrace_append hprefix tailTrace_2825119
  have hstable : (prefixWord ++ tailWord_2825119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825119).length < 2 ^ (prefixWord ++ tailWord_2825119).sum := by decide
  have hdescent : baseEnd_2825119 < baseStart_2825119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825142 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2825142 : Nat := 118140960795 + 2825142 * 2 ^ 59
def prefixEnd_2825142 : Nat := 4983230072969 + 3 ^ 40 * 2825142 * 2
def baseEnd_2825142 : Nat := 967103842136327235088277

theorem tailTrace_2825142 : CollatzResearch.WordTrace tailWord_2825142 prefixEnd_2825142 967103842136327235088277 := by
  unfold tailWord_2825142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6440087120687531542828355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68694262620667003123502453 6440087120687531542828355)
  ·
    refine ⟨9660130681031297314242533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6440087120687531542828355 9660130681031297314242533)
    ·
      refine ⟨1811274502693368246420475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9660130681031297314242533 1811274502693368246420475)
      ·
        refine ⟨2716911754040052369630713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811274502693368246420475 2716911754040052369630713)
        ·
          refine ⟨2037683815530039277223035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716911754040052369630713 2037683815530039277223035)
          ·
            refine ⟨3056525723295058915834553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037683815530039277223035 3056525723295058915834553)
            ·
              refine ⟨2292394292471294186875915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056525723295058915834553 2292394292471294186875915)
              ·
                refine ⟨3438591438706941280313873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292394292471294186875915 3438591438706941280313873)
                ·
                  refine ⟨2578943579030205960235405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3438591438706941280313873 2578943579030205960235405)
                  ·
                    refine ⟨967103842136327235088277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578943579030205960235405 967103842136327235088277)
                    ·
                      rfl

theorem cell22_2825142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2825142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825142 prefixEnd_2825142 := by exact prefixLift 2825142
  have htrace : WordTrace (prefixWord ++ tailWord_2825142) baseStart_2825142 baseEnd_2825142 := by
    simpa [prefixWord, tailWord_2825142, baseEnd_2825142] using wordTrace_append hprefix tailTrace_2825142
  have hstable : (prefixWord ++ tailWord_2825142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825142).length < 2 ^ (prefixWord ++ tailWord_2825142).sum := by decide
  have hdescent : baseEnd_2825142 < baseStart_2825142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825149 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 5]
def baseStart_2825149 : Nat := 118140960795 + 2825149 * 2 ^ 59
def prefixEnd_2825149 : Nat := 4983230072969 + 3 ^ 40 * 2825149 * 2
def baseEnd_2825149 : Nat := 322368746126460516721085

theorem tailTrace_2825149 : CollatzResearch.WordTrace tailWord_2825149 prefixEnd_2825149 322368746126460516721085 := by
  unfold tailWord_2825149
  simp only [CollatzResearch.WordTrace]
  refine ⟨103041649241975144880758501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68694432827983429920505667 103041649241975144880758501)
  ·
    refine ⟨19320309232870339665142219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103041649241975144880758501 19320309232870339665142219)
    ·
      refine ⟨28980463849305509497713329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19320309232870339665142219 28980463849305509497713329)
      ·
        refine ⟨21735347886979132123284997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28980463849305509497713329 21735347886979132123284997)
        ·
          refine ⟨4075377728808587273115937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21735347886979132123284997 4075377728808587273115937)
          ·
            refine ⟨3056533296606440454836953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4075377728808587273115937 3056533296606440454836953)
            ·
              refine ⟨2292399972454830341127715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056533296606440454836953 2292399972454830341127715)
              ·
                refine ⟨3438599958682245511691573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292399972454830341127715 3438599958682245511691573)
                ·
                  refine ⟨322368746126460516721085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3438599958682245511691573 322368746126460516721085)
                  ·
                    rfl

theorem cell22_2825149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_2825149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825149 prefixEnd_2825149 := by exact prefixLift 2825149
  have htrace : WordTrace (prefixWord ++ tailWord_2825149) baseStart_2825149 baseEnd_2825149 := by
    simpa [prefixWord, tailWord_2825149, baseEnd_2825149] using wordTrace_append hprefix tailTrace_2825149
  have hstable : (prefixWord ++ tailWord_2825149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825149).length < 2 ^ (prefixWord ++ tailWord_2825149).sum := by decide
  have hdescent : baseEnd_2825149 < baseStart_2825149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825175 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 4, 3]
def baseStart_2825175 : Nat := 118140960795 + 2825175 * 2 ^ 59
def prefixEnd_2825175 : Nat := 4983230072969 + 3 ^ 40 * 2825175 * 2
def baseEnd_2825175 : Nat := 967115138710726149013175

theorem tailTrace_2825175 : CollatzResearch.WordTrace tailWord_2825175 prefixEnd_2825175 967115138710726149013175 := by
  unfold tailWord_2825175
  simp only [CollatzResearch.WordTrace]
  refine ⟨103042597539880951321204979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68695065026587300880803319 103042597539880951321204979)
  ·
    refine ⟨154563896309821426981807469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103042597539880951321204979 154563896309821426981807469)
    ·
      refine ⟨57961461116183035118177801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154563896309821426981807469 57961461116183035118177801)
      ·
        refine ⟨43471095837137276338633351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57961461116183035118177801 43471095837137276338633351)
        ·
          refine ⟨65206643755705914507950027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43471095837137276338633351 65206643755705914507950027)
          ·
            refine ⟨97809965633558871761925041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65206643755705914507950027 97809965633558871761925041)
            ·
              refine ⟨73357474225169153821443781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97809965633558871761925041 73357474225169153821443781)
              ·
                refine ⟨13754526417219216341520709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73357474225169153821443781 13754526417219216341520709)
                ·
                  refine ⟨2578973703228603064035133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13754526417219216341520709 2578973703228603064035133)
                  ·
                    refine ⟨967115138710726149013175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578973703228603064035133 967115138710726149013175)
                    ·
                      rfl

theorem cell22_2825175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_2825175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825175 prefixEnd_2825175 := by exact prefixLift 2825175
  have htrace : WordTrace (prefixWord ++ tailWord_2825175) baseStart_2825175 baseEnd_2825175 := by
    simpa [prefixWord, tailWord_2825175, baseEnd_2825175] using wordTrace_append hprefix tailTrace_2825175
  have hstable : (prefixWord ++ tailWord_2825175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825175).length < 2 ^ (prefixWord ++ tailWord_2825175).sum := by decide
  have hdescent : baseEnd_2825175 < baseStart_2825175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825192 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2825192 : Nat := 118140960795 + 2825192 * 2 ^ 59
def prefixEnd_2825192 : Nat := 4983230072969 + 3 ^ 40 * 2825192 * 2
def baseEnd_2825192 : Nat := 967120958158143771338123

theorem tailTrace_2825192 : CollatzResearch.WordTrace tailWord_2825192 prefixEnd_2825192 967120958158143771338123 := by
  unfold tailWord_2825192
  simp only [CollatzResearch.WordTrace]
  refine ⟨51521608790409681612286915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68695478387212908816382553 51521608790409681612286915)
  ·
    refine ⟨77282413185614522418430373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51521608790409681612286915 77282413185614522418430373)
    ·
      refine ⟨14490452472302722953455695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77282413185614522418430373 14490452472302722953455695)
      ·
        refine ⟨21735678708454084430183543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14490452472302722953455695 21735678708454084430183543)
        ·
          refine ⟨32603518062681126645275315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21735678708454084430183543 32603518062681126645275315)
          ·
            refine ⟨48905277094021689967912973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32603518062681126645275315 48905277094021689967912973)
            ·
              refine ⟨18339478910258133737967365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48905277094021689967912973 18339478910258133737967365)
              ·
                refine ⟨3438652295673400075868881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18339478910258133737967365 3438652295673400075868881)
                ·
                  refine ⟨2578989221755050056901661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3438652295673400075868881 2578989221755050056901661)
                  ·
                    refine ⟨967120958158143771338123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2578989221755050056901661 967120958158143771338123)
                    ·
                      rfl

theorem cell22_2825192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2825192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825192 prefixEnd_2825192 := by exact prefixLift 2825192
  have htrace : WordTrace (prefixWord ++ tailWord_2825192) baseStart_2825192 baseEnd_2825192 := by
    simpa [prefixWord, tailWord_2825192, baseEnd_2825192] using wordTrace_append hprefix tailTrace_2825192
  have hstable : (prefixWord ++ tailWord_2825192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825192).length < 2 ^ (prefixWord ++ tailWord_2825192).sum := by decide
  have hdescent : baseEnd_2825192 < baseStart_2825192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825194 : List Nat := [3, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_2825194 : Nat := 118140960795 + 2825194 * 2 ^ 59
def prefixEnd_2825194 : Nat := 4983230072969 + 3 ^ 40 * 2825194 * 2
def baseEnd_2825194 : Nat := 322373880933005477596039

theorem tailTrace_2825194 : CollatzResearch.WordTrace tailWord_2825194 prefixEnd_2825194 322373880933005477596039 := by
  unfold tailWord_2825194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25760822631703029391536659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68695527017874745044097757 25760822631703029391536659)
  ·
    refine ⟨38641233947554544087304989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25760822631703029391536659 38641233947554544087304989)
    ·
      refine ⟨14490462730332954032739371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38641233947554544087304989 14490462730332954032739371)
      ·
        refine ⟨21735694095499431049109057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14490462730332954032739371 21735694095499431049109057)
        ·
          refine ⟨16301770571624573286831793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21735694095499431049109057 16301770571624573286831793)
          ·
            refine ⟨12226327928718429965123845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16301770571624573286831793 12226327928718429965123845)
            ·
              refine ⟨2292436486634705618460721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12226327928718429965123845 2292436486634705618460721)
              ·
                refine ⟨1719327364976029213845541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292436486634705618460721 1719327364976029213845541)
                ·
                  refine ⟨322373880933005477596039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719327364976029213845541 322373880933005477596039)
                  ·
                    rfl

theorem cell22_2825194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_2825194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825194 prefixEnd_2825194 := by exact prefixLift 2825194
  have htrace : WordTrace (prefixWord ++ tailWord_2825194) baseStart_2825194 baseEnd_2825194 := by
    simpa [prefixWord, tailWord_2825194, baseEnd_2825194] using wordTrace_append hprefix tailTrace_2825194
  have hstable : (prefixWord ++ tailWord_2825194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825194).length < 2 ^ (prefixWord ++ tailWord_2825194).sum := by decide
  have hdescent : baseEnd_2825194 < baseStart_2825194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825203 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 4, 7]
def baseStart_2825203 : Nat := 118140960795 + 2825203 * 2 ^ 59
def prefixEnd_2825203 : Nat := 4983230072969 + 3 ^ 40 * 2825203 * 2
def baseEnd_2825203 : Nat := 967124723682943409313089

theorem tailTrace_2825203 : CollatzResearch.WordTrace tailWord_2825203 prefixEnd_2825203 967124723682943409313089 := by
  unfold tailWord_2825203
  simp only [CollatzResearch.WordTrace]
  refine ⟨103043618783779512103224263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68695745855853008068816175 103043618783779512103224263)
  ·
    refine ⟨154565428175669268154836395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103043618783779512103224263 154565428175669268154836395)
    ·
      refine ⟨231848142263503902232254593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154565428175669268154836395 231848142263503902232254593)
      ·
        refine ⟨173886106697627926674190945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231848142263503902232254593 173886106697627926674190945)
        ·
          refine ⟨130414580023220945005643209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173886106697627926674190945 130414580023220945005643209)
          ·
            refine ⟨97810935017415708754232407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130414580023220945005643209 97810935017415708754232407)
            ·
              refine ⟨146716402526123563131348611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97810935017415708754232407 146716402526123563131348611)
              ·
                refine ⟨220074603789185344697022917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146716402526123563131348611 220074603789185344697022917)
                ·
                  refine ⟨41263988210472252130691797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220074603789185344697022917 41263988210472252130691797)
                  ·
                    refine ⟨967124723682943409313089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41263988210472252130691797 967124723682943409313089)
                    ·
                      rfl

theorem cell22_2825203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_2825203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825203 prefixEnd_2825203 := by exact prefixLift 2825203
  have htrace : WordTrace (prefixWord ++ tailWord_2825203) baseStart_2825203 baseEnd_2825203 := by
    simpa [prefixWord, tailWord_2825203, baseEnd_2825203] using wordTrace_append hprefix tailTrace_2825203
  have hstable : (prefixWord ++ tailWord_2825203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825203).length < 2 ^ (prefixWord ++ tailWord_2825203).sum := by decide
  have hdescent : baseEnd_2825203 < baseStart_2825203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825265 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2825265 : Nat := 118140960795 + 2825265 * 2 ^ 59
def prefixEnd_2825265 : Nat := 4983230072969 + 3 ^ 40 * 2825265 * 2
def baseEnd_2825265 : Nat := 967145947549995914262899

theorem tailTrace_2825265 : CollatzResearch.WordTrace tailWord_2825265 prefixEnd_2825265 967145947549995914262899 := by
  unfold tailWord_2825265
  simp only [CollatzResearch.WordTrace]
  refine ⟨103045880109554896691981249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68697253406369931127987499 103045880109554896691981249)
  ·
    refine ⟨77284410082166172518985937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103045880109554896691981249 77284410082166172518985937)
    ·
      refine ⟨57963307561624629389239453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77284410082166172518985937 57963307561624629389239453)
      ·
        refine ⟨21736240335609236020964795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57963307561624629389239453 21736240335609236020964795)
        ·
          refine ⟨32604360503413854031447193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21736240335609236020964795 32604360503413854031447193)
          ·
            refine ⟨24453270377560390523585395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32604360503413854031447193 24453270377560390523585395)
            ·
              refine ⟨36679905566340585785378093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24453270377560390523585395 36679905566340585785378093)
              ·
                refine ⟨13754964587377719669516785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36679905566340585785378093 13754964587377719669516785)
                ·
                  refine ⟨10316223440533289752137589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13754964587377719669516785 10316223440533289752137589)
                  ·
                    refine ⟨967145947549995914262899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10316223440533289752137589 967145947549995914262899)
                    ·
                      rfl

theorem cell22_2825265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2825265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825265 prefixEnd_2825265 := by exact prefixLift 2825265
  have htrace : WordTrace (prefixWord ++ tailWord_2825265) baseStart_2825265 baseEnd_2825265 := by
    simpa [prefixWord, tailWord_2825265, baseEnd_2825265] using wordTrace_append hprefix tailTrace_2825265
  have hstable : (prefixWord ++ tailWord_2825265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825265).length < 2 ^ (prefixWord ++ tailWord_2825265).sum := by decide
  have hdescent : baseEnd_2825265 < baseStart_2825265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825297 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_2825297 : Nat := 118140960795 + 2825297 * 2 ^ 59
def prefixEnd_2825297 : Nat := 4983230072969 + 3 ^ 40 * 2825297 * 2
def baseEnd_2825297 : Nat := 967156901803958497462801

theorem tailTrace_2825297 : CollatzResearch.WordTrace tailWord_2825297 prefixEnd_2825297 967156901803958497462801 := by
  unfold tailWord_2825297
  simp only [CollatzResearch.WordTrace]
  refine ⟨103047047245438966157146145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68698031496959310771430763 103047047245438966157146145)
  ·
    refine ⟨77285285434079224617859609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103047047245438966157146145 77285285434079224617859609)
    ·
      refine ⟨57963964075559418463394707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77285285434079224617859609 57963964075559418463394707)
      ·
        refine ⟨86945946113339127695092061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57963964075559418463394707 86945946113339127695092061)
        ·
          refine ⟨32604729792502172885659523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86945946113339127695092061 32604729792502172885659523)
          ·
            refine ⟨48907094688753259328489285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32604729792502172885659523 48907094688753259328489285)
            ·
              refine ⟨9170080254141236124091741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48907094688753259328489285 9170080254141236124091741)
              ·
                refine ⟨3438780095302963546534403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9170080254141236124091741 3438780095302963546534403)
                ·
                  refine ⟨5158170142954445319801605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438780095302963546534403 5158170142954445319801605)
                  ·
                    refine ⟨967156901803958497462801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5158170142954445319801605 967156901803958497462801)
                    ·
                      rfl

theorem cell22_2825297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_2825297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825297 prefixEnd_2825297 := by exact prefixLift 2825297
  have htrace : WordTrace (prefixWord ++ tailWord_2825297) baseStart_2825297 baseEnd_2825297 := by
    simpa [prefixWord, tailWord_2825297, baseEnd_2825297] using wordTrace_append hprefix tailTrace_2825297
  have hstable : (prefixWord ++ tailWord_2825297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825297).length < 2 ^ (prefixWord ++ tailWord_2825297).sum := by decide
  have hdescent : baseEnd_2825297 < baseStart_2825297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825340 : List Nat := [2, 2, 2, 1, 1, 3, 1, 10]
def baseStart_2825340 : Nat := 118140960795 + 2825340 * 2 ^ 59
def prefixEnd_2825340 : Nat := 4983230072969 + 3 ^ 40 * 2825340 * 2
def baseEnd_2825340 : Nat := 107463513509191190959741

theorem tailTrace_2825340 : CollatzResearch.WordTrace tailWord_2825340 prefixEnd_2825340 107463513509191190959741 := by
  unfold tailWord_2825340
  simp only [CollatzResearch.WordTrace]
  refine ⟨51524307792141592250480737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68699077056188789667307649 51524307792141592250480737)
  ·
    refine ⟨38643230844106194187860553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51524307792141592250480737 38643230844106194187860553)
    ·
      refine ⟨28982423133079645640895415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38643230844106194187860553 28982423133079645640895415)
      ·
        refine ⟨43473634699619468461343123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28982423133079645640895415 43473634699619468461343123)
        ·
          refine ⟨65210452049429202692014685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43473634699619468461343123 65210452049429202692014685)
          ·
            refine ⟨24453919518535951009505507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65210452049429202692014685 24453919518535951009505507)
            ·
              refine ⟨36680879277803926514258261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24453919518535951009505507 36680879277803926514258261)
              ·
                refine ⟨107463513509191190959741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36680879277803926514258261 107463513509191190959741)
                ·
                  rfl

theorem cell22_2825340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 10].length) (baseStart_2825340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825340 prefixEnd_2825340 := by exact prefixLift 2825340
  have htrace : WordTrace (prefixWord ++ tailWord_2825340) baseStart_2825340 baseEnd_2825340 := by
    simpa [prefixWord, tailWord_2825340, baseEnd_2825340] using wordTrace_append hprefix tailTrace_2825340
  have hstable : (prefixWord ++ tailWord_2825340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825340).length < 2 ^ (prefixWord ++ tailWord_2825340).sum := by decide
  have hdescent : baseEnd_2825340 < baseStart_2825340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825374 : List Nat := [4, 3, 1, 1, 2, 1, 3, 7]
def baseStart_2825374 : Nat := 118140960795 + 2825374 * 2 ^ 59
def prefixEnd_2825374 : Nat := 4983230072969 + 3 ^ 40 * 2825374 * 2
def baseEnd_2825374 : Nat := 107464806719728440365285

theorem tailTrace_2825374 : CollatzResearch.WordTrace tailWord_2825374 prefixEnd_2825374 107464806719728440365285 := by
  unfold tailWord_2825374
  simp only [CollatzResearch.WordTrace]
  refine ⟨12881231958270001038462397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68699903777440005538466117 12881231958270001038462397)
  ·
    refine ⟨4830461984351250389423399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12881231958270001038462397 4830461984351250389423399)
    ·
      refine ⟨7245692976526875584135099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830461984351250389423399 7245692976526875584135099)
      ·
        refine ⟨10868539464790313376202649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7245692976526875584135099 10868539464790313376202649)
        ·
          refine ⟨8151404598592735032151987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10868539464790313376202649 8151404598592735032151987)
          ·
            refine ⟨12227106897889102548227981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151404598592735032151987 12227106897889102548227981)
            ·
              refine ⟨4585165086708413455585493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12227106897889102548227981 4585165086708413455585493)
              ·
                refine ⟨107464806719728440365285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4585165086708413455585493 107464806719728440365285)
                ·
                  rfl

theorem cell22_2825374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_2825374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825374 prefixEnd_2825374 := by exact prefixLift 2825374
  have htrace : WordTrace (prefixWord ++ tailWord_2825374) baseStart_2825374 baseEnd_2825374 := by
    simpa [prefixWord, tailWord_2825374, baseEnd_2825374] using wordTrace_append hprefix tailTrace_2825374
  have hstable : (prefixWord ++ tailWord_2825374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825374).length < 2 ^ (prefixWord ++ tailWord_2825374).sum := by decide
  have hdescent : baseEnd_2825374 < baseStart_2825374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825481 : List Nat := [1, 2, 1, 1, 3, 3, 5, 2, 4]
def baseStart_2825481 : Nat := 118140960795 + 2825481 * 2 ^ 59
def prefixEnd_2825481 : Nat := 4983230072969 + 3 ^ 40 * 2825481 * 2
def baseEnd_2825481 : Nat := 322406629588081116954079

theorem tailTrace_2825481 : CollatzResearch.WordTrace tailWord_2825481 prefixEnd_2825481 322406629588081116954079 := by
  unfold tailWord_2825481
  simp only [CollatzResearch.WordTrace]
  refine ⟨103053758276772365581844297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68702505517848243721229531 103053758276772365581844297)
  ·
    refine ⟨77290318707579274186383223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103053758276772365581844297 77290318707579274186383223)
    ·
      refine ⟨115935478061368911279574835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77290318707579274186383223 115935478061368911279574835)
      ·
        refine ⟨173903217092053366919362253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115935478061368911279574835 173903217092053366919362253)
        ·
          refine ⟨65213706409520012594760845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173903217092053366919362253 65213706409520012594760845)
          ·
            refine ⟨24455139903570004723035317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65213706409520012594760845 24455139903570004723035317)
            ·
              refine ⟨2292669365959687942784561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24455139903570004723035317 2292669365959687942784561)
              ·
                refine ⟨1719502024469765957088421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292669365959687942784561 1719502024469765957088421)
                ·
                  refine ⟨322406629588081116954079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719502024469765957088421 322406629588081116954079)
                  ·
                    rfl

theorem cell22_2825481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_2825481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825481 prefixEnd_2825481 := by exact prefixLift 2825481
  have htrace : WordTrace (prefixWord ++ tailWord_2825481) baseStart_2825481 baseEnd_2825481 := by
    simpa [prefixWord, tailWord_2825481, baseEnd_2825481] using wordTrace_append hprefix tailTrace_2825481
  have hstable : (prefixWord ++ tailWord_2825481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825481).length < 2 ^ (prefixWord ++ tailWord_2825481).sum := by decide
  have hdescent : baseEnd_2825481 < baseStart_2825481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825496 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 2, 3]
def baseStart_2825496 : Nat := 118140960795 + 2825496 * 2 ^ 59
def prefixEnd_2825496 : Nat := 4983230072969 + 3 ^ 40 * 2825496 * 2
def baseEnd_2825496 : Nat := 967225023570788311737191

theorem tailTrace_2825496 : CollatzResearch.WordTrace tailWord_2825496 prefixEnd_2825496 967225023570788311737191 := by
  unfold tailWord_2825496
  simp only [CollatzResearch.WordTrace]
  refine ⟨51527152685859011571820171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68702870247812015429093561 51527152685859011571820171)
  ·
    refine ⟨77290729028788517357730257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51527152685859011571820171 77290729028788517357730257)
    ·
      refine ⟨57968046771591388018297693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77290729028788517357730257 57968046771591388018297693)
      ·
        refine ⟨21738017539346770506861635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57968046771591388018297693 21738017539346770506861635)
        ·
          refine ⟨32607026309020155760292453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21738017539346770506861635 32607026309020155760292453)
          ·
            refine ⟨6113817432941279205054835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32607026309020155760292453 6113817432941279205054835)
            ·
              refine ⟨9170726149411918807582253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113817432941279205054835 9170726149411918807582253)
              ·
                refine ⟨3439022306029469552843345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9170726149411918807582253 3439022306029469552843345)
                ·
                  refine ⟨2579266729522102164632509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3439022306029469552843345 2579266729522102164632509)
                  ·
                    refine ⟨967225023570788311737191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579266729522102164632509 967225023570788311737191)
                    ·
                      rfl

theorem cell22_2825496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_2825496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825496 prefixEnd_2825496 := by exact prefixLift 2825496
  have htrace : WordTrace (prefixWord ++ tailWord_2825496) baseStart_2825496 baseEnd_2825496 := by
    simpa [prefixWord, tailWord_2825496, baseEnd_2825496] using wordTrace_append hprefix tailTrace_2825496
  have hstable : (prefixWord ++ tailWord_2825496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825496).length < 2 ^ (prefixWord ++ tailWord_2825496).sum := by decide
  have hdescent : baseEnd_2825496 < baseStart_2825496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825526 : List Nat := [5, 1, 2, 3, 1, 10]
def baseStart_2825526 : Nat := 118140960795 + 2825526 * 2 ^ 59
def prefixEnd_2825526 : Nat := 4983230072969 + 3 ^ 40 * 2825526 * 2
def baseEnd_2825526 : Nat := 11941176459060225104779

theorem tailTrace_2825526 : CollatzResearch.WordTrace tailWord_2825526 prefixEnd_2825526 11941176459060225104779 := by
  unfold tailWord_2825526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6440962472600583641702027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68703599707739558844821621 6440962472600583641702027)
  ·
    refine ⟨9661443708900875462553041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6440962472600583641702027 9661443708900875462553041)
    ·
      refine ⟨7246082781675656596914781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9661443708900875462553041 7246082781675656596914781)
      ·
        refine ⟨2717281043128371223843043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7246082781675656596914781 2717281043128371223843043)
        ·
          refine ⟨4075921564692556835764565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717281043128371223843043 4075921564692556835764565)
          ·
            refine ⟨11941176459060225104779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4075921564692556835764565 11941176459060225104779)
            ·
              rfl

theorem cell22_2825526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 10].length) (baseStart_2825526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825526 prefixEnd_2825526 := by exact prefixLift 2825526
  have htrace : WordTrace (prefixWord ++ tailWord_2825526) baseStart_2825526 baseEnd_2825526 := by
    simpa [prefixWord, tailWord_2825526, baseEnd_2825526] using wordTrace_append hprefix tailTrace_2825526
  have hstable : (prefixWord ++ tailWord_2825526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825526).length < 2 ^ (prefixWord ++ tailWord_2825526).sum := by decide
  have hdescent : baseEnd_2825526 < baseStart_2825526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825575 : List Nat := [1, 1, 5, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2825575 : Nat := 118140960795 + 2825575 * 2 ^ 59
def prefixEnd_2825575 : Nat := 4983230072969 + 3 ^ 40 * 2825575 * 2
def baseEnd_2825575 : Nat := 967252066885258439011949

theorem tailTrace_2825575 : CollatzResearch.WordTrace tailWord_2825575 prefixEnd_2825575 967252066885258439011949 := by
  unfold tailWord_2825575
  simp only [CollatzResearch.WordTrace]
  refine ⟨103057186738431819635766179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68704791158954546423844119 103057186738431819635766179)
  ·
    refine ⟨154585780107647729453649269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103057186738431819635766179 154585780107647729453649269)
    ·
      refine ⟨14492416885091974636279619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154585780107647729453649269 14492416885091974636279619)
      ·
        refine ⟨21738625327637961954419429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14492416885091974636279619 21738625327637961954419429)
        ·
          refine ⟨4075992248932117866453643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21738625327637961954419429 4075992248932117866453643)
          ·
            refine ⟨6113988373398176799680465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075992248932117866453643 6113988373398176799680465)
            ·
              refine ⟨4585491280048632599760349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6113988373398176799680465 4585491280048632599760349)
              ·
                refine ⟨1719559230018237224910131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4585491280048632599760349 1719559230018237224910131)
                ·
                  refine ⟨2579338845027355837365197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719559230018237224910131 2579338845027355837365197)
                  ·
                    refine ⟨967252066885258439011949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579338845027355837365197 967252066885258439011949)
                    ·
                      rfl

theorem cell22_2825575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2825575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825575 prefixEnd_2825575 := by exact prefixLift 2825575
  have htrace : WordTrace (prefixWord ++ tailWord_2825575) baseStart_2825575 baseEnd_2825575 := by
    simpa [prefixWord, tailWord_2825575, baseEnd_2825575] using wordTrace_append hprefix tailTrace_2825575
  have hstable : (prefixWord ++ tailWord_2825575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825575).length < 2 ^ (prefixWord ++ tailWord_2825575).sum := by decide
  have hdescent : baseEnd_2825575 < baseStart_2825575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825631 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 4, 3]
def baseStart_2825631 : Nat := 118140960795 + 2825631 * 2 ^ 59
def prefixEnd_2825631 : Nat := 4983230072969 + 3 ^ 40 * 2825631 * 2
def baseEnd_2825631 : Nat := 967271236829692959611777

theorem tailTrace_2825631 : CollatzResearch.WordTrace tailWord_2825631 prefixEnd_2825631 967271236829692959611777 := by
  unfold tailWord_2825631
  simp only [CollatzResearch.WordTrace]
  refine ⟨103059229226228941199804747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68706152817485960799869831 103059229226228941199804747)
  ·
    refine ⟨154588843839343411799707121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103059229226228941199804747 154588843839343411799707121)
    ·
      refine ⟨115941632879507558849780341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154588843839343411799707121 115941632879507558849780341)
      ·
        refine ⟨10869528082453833642166907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115941632879507558849780341 10869528082453833642166907)
        ·
          refine ⟨16304292123680750463250361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10869528082453833642166907 16304292123680750463250361)
          ·
            refine ⟨12228219092760562847437771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16304292123680750463250361 12228219092760562847437771)
            ·
              refine ⟨18342328639140844271156657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12228219092760562847437771 18342328639140844271156657)
              ·
                refine ⟨13756746479355633203367493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18342328639140844271156657 13756746479355633203367493)
                ·
                  refine ⟨2579389964879181225631405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13756746479355633203367493 2579389964879181225631405)
                  ·
                    refine ⟨967271236829692959611777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579389964879181225631405 967271236829692959611777)
                    ·
                      rfl

theorem cell22_2825631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_2825631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825631 prefixEnd_2825631 := by exact prefixLift 2825631
  have htrace : WordTrace (prefixWord ++ tailWord_2825631) baseStart_2825631 baseEnd_2825631 := by
    simpa [prefixWord, tailWord_2825631, baseEnd_2825631] using wordTrace_append hprefix tailTrace_2825631
  have hstable : (prefixWord ++ tailWord_2825631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825631).length < 2 ^ (prefixWord ++ tailWord_2825631).sum := by decide
  have hdescent : baseEnd_2825631 < baseStart_2825631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825710 : List Nat := [4, 1, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_2825710 : Nat := 118140960795 + 2825710 * 2 ^ 59
def prefixEnd_2825710 : Nat := 4983230072969 + 3 ^ 40 * 2825710 * 2
def baseEnd_2825710 : Nat := 967298280144163086886535

theorem tailTrace_2825710 : CollatzResearch.WordTrace tailWord_2825710 prefixEnd_2825710 967298280144163086886535 := by
  unfold tailWord_2825710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12882763824117842211491323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68708073728628491794620389 12882763824117842211491323)
  ·
    refine ⟨19324145736176763317236985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12882763824117842211491323 19324145736176763317236985)
    ·
      refine ⟨14493109302132572487927739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19324145736176763317236985 14493109302132572487927739)
      ·
        refine ⟨21739663953198858731891609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493109302132572487927739 21739663953198858731891609)
        ·
          refine ⟨16304747964899144048918707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21739663953198858731891609 16304747964899144048918707)
          ·
            refine ⟨24457121947348716073378061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16304747964899144048918707 24457121947348716073378061)
            ·
              refine ⟨9171420730255768527516773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24457121947348716073378061 9171420730255768527516773)
              ·
                refine ⟨1719641386922956598909395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9171420730255768527516773 1719641386922956598909395)
                ·
                  refine ⟨2579462080384434898364093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719641386922956598909395 2579462080384434898364093)
                  ·
                    refine ⟨967298280144163086886535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579462080384434898364093 967298280144163086886535)
                    ·
                      rfl

theorem cell22_2825710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_2825710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825710 prefixEnd_2825710 := by exact prefixLift 2825710
  have htrace : WordTrace (prefixWord ++ tailWord_2825710) baseStart_2825710 baseEnd_2825710 := by
    simpa [prefixWord, tailWord_2825710, baseEnd_2825710] using wordTrace_append hprefix tailTrace_2825710
  have hstable : (prefixWord ++ tailWord_2825710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825710).length < 2 ^ (prefixWord ++ tailWord_2825710).sum := by decide
  have hdescent : baseEnd_2825710 < baseStart_2825710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825736 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_2825736 : Nat := 118140960795 + 2825736 * 2 ^ 59
def prefixEnd_2825736 : Nat := 4983230072969 + 3 ^ 40 * 2825736 * 2
def baseEnd_2825736 : Nat := 967307180475507685736455

theorem tailTrace_2825736 : CollatzResearch.WordTrace tailWord_2825736 prefixEnd_2825736 967307180475507685736455 := by
  unfold tailWord_2825736
  simp only [CollatzResearch.WordTrace]
  refine ⟨51531529445424272066188531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68708705927232362754918041 51531529445424272066188531)
  ·
    refine ⟨77297294168136408099282797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51531529445424272066188531 77297294168136408099282797)
    ·
      refine ⟨28986485313051153037231049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77297294168136408099282797 28986485313051153037231049)
      ·
        refine ⟨21739863984788364777923287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28986485313051153037231049 21739863984788364777923287)
        ·
          refine ⟨32609795977182547166884931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21739863984788364777923287 32609795977182547166884931)
          ·
            refine ⟨48914693965773820750327397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32609795977182547166884931 48914693965773820750327397)
            ·
              refine ⟨9171505118582591390686387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48914693965773820750327397 9171505118582591390686387)
              ·
                refine ⟨13757257677873887086029581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9171505118582591390686387 13757257677873887086029581)
                ·
                  refine ⟨5158971629202707657261093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13757257677873887086029581 5158971629202707657261093)
                  ·
                    refine ⟨967307180475507685736455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5158971629202707657261093 967307180475507685736455)
                    ·
                      rfl

theorem cell22_2825736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_2825736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825736 prefixEnd_2825736 := by exact prefixLift 2825736
  have htrace : WordTrace (prefixWord ++ tailWord_2825736) baseStart_2825736 baseEnd_2825736 := by
    simpa [prefixWord, tailWord_2825736, baseEnd_2825736] using wordTrace_append hprefix tailTrace_2825736
  have hstable : (prefixWord ++ tailWord_2825736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825736).length < 2 ^ (prefixWord ++ tailWord_2825736).sum := by decide
  have hdescent : baseEnd_2825736 < baseStart_2825736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825781 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2825781 : Nat := 118140960795 + 2825781 * 2 ^ 59
def prefixEnd_2825781 : Nat := 4983230072969 + 3 ^ 40 * 2825781 * 2
def baseEnd_2825781 : Nat := 967322584895142568361317

theorem tailTrace_2825781 : CollatzResearch.WordTrace tailWord_2825781 prefixEnd_2825781 967322584895142568361317 := by
  unfold tailWord_2825781
  simp only [CollatzResearch.WordTrace]
  refine ⟨103064700175685516817765197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68709800117123677878510131 103064700175685516817765197)
  ·
    refine ⟨38649262565882068806661949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103064700175685516817765197 38649262565882068806661949)
    ·
      refine ⟨14493473462205775802498231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38649262565882068806661949 14493473462205775802498231)
      ·
        refine ⟨21740210193308663703747347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493473462205775802498231 21740210193308663703747347)
        ·
          refine ⟨32610315289962995555621021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21740210193308663703747347 32610315289962995555621021)
          ·
            refine ⟨12228868233736123333357883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32610315289962995555621021 12228868233736123333357883)
            ·
              refine ⟨18343302350604185000036825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12228868233736123333357883 18343302350604185000036825)
              ·
                refine ⟨13757476762953138750027619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18343302350604185000036825 13757476762953138750027619)
                ·
                  refine ⟨20636215144429708125041429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13757476762953138750027619 20636215144429708125041429)
                  ·
                    refine ⟨967322584895142568361317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20636215144429708125041429 967322584895142568361317)
                    ·
                      rfl

theorem cell22_2825781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2825781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825781 prefixEnd_2825781 := by exact prefixLift 2825781
  have htrace : WordTrace (prefixWord ++ tailWord_2825781) baseStart_2825781 baseEnd_2825781 := by
    simpa [prefixWord, tailWord_2825781, baseEnd_2825781] using wordTrace_append hprefix tailTrace_2825781
  have hstable : (prefixWord ++ tailWord_2825781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825781).length < 2 ^ (prefixWord ++ tailWord_2825781).sum := by decide
  have hdescent : baseEnd_2825781 < baseStart_2825781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825783 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 1, 5]
def baseStart_2825783 : Nat := 118140960795 + 2825783 * 2 ^ 59
def prefixEnd_2825783 : Nat := 4983230072969 + 3 ^ 40 * 2825783 * 2
def baseEnd_2825783 : Nat := 967323269536015229811311

theorem tailTrace_2825783 : CollatzResearch.WordTrace tailWord_2825783 prefixEnd_2825783 967323269536015229811311 := by
  unfold tailWord_2825783
  simp only [CollatzResearch.WordTrace]
  refine ⟨103064773121678271159338003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68709848747785514106225335 103064773121678271159338003)
  ·
    refine ⟨154597159682517406739007005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103064773121678271159338003 154597159682517406739007005)
    ·
      refine ⟨57973934880944027527127627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154597159682517406739007005 57973934880944027527127627)
      ·
        refine ⟨86960902321416041290691441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57973934880944027527127627 86960902321416041290691441)
        ·
          refine ⟨65220676741062030968018581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86960902321416041290691441 65220676741062030968018581)
          ·
            refine ⟨3057219222237282701625871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65220676741062030968018581 3057219222237282701625871)
            ·
              refine ⟨4585828833355924052438807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057219222237282701625871 4585828833355924052438807)
              ·
                refine ⟨6878743250033886078658211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4585828833355924052438807 6878743250033886078658211)
                ·
                  refine ⟨10318114875050829117987317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6878743250033886078658211 10318114875050829117987317)
                  ·
                    refine ⟨967323269536015229811311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10318114875050829117987317 967323269536015229811311)
                    ·
                      rfl

theorem cell22_2825783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_2825783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825783 prefixEnd_2825783 := by exact prefixLift 2825783
  have htrace : WordTrace (prefixWord ++ tailWord_2825783) baseStart_2825783 baseEnd_2825783 := by
    simpa [prefixWord, tailWord_2825783, baseEnd_2825783] using wordTrace_append hprefix tailTrace_2825783
  have hstable : (prefixWord ++ tailWord_2825783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825783).length < 2 ^ (prefixWord ++ tailWord_2825783).sum := by decide
  have hdescent : baseEnd_2825783 < baseStart_2825783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825871 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 7, 4]
def baseStart_2825871 : Nat := 118140960795 + 2825871 * 2 ^ 59
def prefixEnd_2825871 : Nat := 4983230072969 + 3 ^ 40 * 2825871 * 2
def baseEnd_2825871 : Nat := 967353393734412333611041

theorem tailTrace_2825871 : CollatzResearch.WordTrace tailWord_2825871 prefixEnd_2825871 967353393734412333611041 := by
  unfold tailWord_2825871
  simp only [CollatzResearch.WordTrace]
  refine ⟨103067982745359462188541467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68711988496906308125694311 103067982745359462188541467)
  ·
    refine ⟨154601974118039193282812201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103067982745359462188541467 154601974118039193282812201)
    ·
      refine ⟨115951480588529394962109151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154601974118039193282812201 115951480588529394962109151)
      ·
        refine ⟨173927220882794092443163727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115951480588529394962109151 173927220882794092443163727)
        ·
          refine ⟨260890831324191138664745591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173927220882794092443163727 260890831324191138664745591)
          ·
            refine ⟨391336246986286707997118387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260890831324191138664745591 391336246986286707997118387)
            ·
              refine ⟨587004370479430061995677581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391336246986286707997118387 587004370479430061995677581)
              ·
                refine ⟨220126638929786273248379093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587004370479430061995677581 220126638929786273248379093)
                ·
                  refine ⟨5159218099916865779258885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 220126638929786273248379093 5159218099916865779258885)
                  ·
                    refine ⟨967353393734412333611041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5159218099916865779258885 967353393734412333611041)
                    ·
                      rfl

theorem cell22_2825871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_2825871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825871 prefixEnd_2825871 := by exact prefixLift 2825871
  have htrace : WordTrace (prefixWord ++ tailWord_2825871) baseStart_2825871 baseEnd_2825871 := by
    simpa [prefixWord, tailWord_2825871, baseEnd_2825871] using wordTrace_append hprefix tailTrace_2825871
  have hstable : (prefixWord ++ tailWord_2825871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825871).length < 2 ^ (prefixWord ++ tailWord_2825871).sum := by decide
  have hdescent : baseEnd_2825871 < baseStart_2825871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825879 : List Nat := [1, 1, 3, 3, 2, 4, 2, 2, 1, 3]
def baseStart_2825879 : Nat := 118140960795 + 2825879 * 2 ^ 59
def prefixEnd_2825879 : Nat := 4983230072969 + 3 ^ 40 * 2825879 * 2
def baseEnd_2825879 : Nat := 967356132297902979411017

theorem tailTrace_2825879 : CollatzResearch.WordTrace tailWord_2825879 prefixEnd_2825879 967356132297902979411017 := by
  unfold tailWord_2825879
  simp only [CollatzResearch.WordTrace]
  refine ⟨103068274529330479554832691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68712183019553653036555127 103068274529330479554832691)
  ·
    refine ⟨154602411793995719332249037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103068274529330479554832691 154602411793995719332249037)
    ·
      refine ⟨57975904422748394749593389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154602411793995719332249037 57975904422748394749593389)
      ·
        refine ⟨21740964158530648031097521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57975904422748394749593389 21740964158530648031097521)
        ·
          refine ⟨16305723118897986023323141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21740964158530648031097521 16305723118897986023323141)
          ·
            refine ⟨3057323084793372379373089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16305723118897986023323141 3057323084793372379373089)
            ·
              refine ⟨2292992313595029284529817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057323084793372379373089 2292992313595029284529817)
              ·
                refine ⟨1719744235196271963397363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292992313595029284529817 1719744235196271963397363)
                ·
                  refine ⟨2579616352794407945096045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719744235196271963397363 2579616352794407945096045)
                  ·
                    refine ⟨967356132297902979411017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579616352794407945096045 967356132297902979411017)
                    ·
                      rfl

theorem cell22_2825879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_2825879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825879 prefixEnd_2825879 := by exact prefixLift 2825879
  have htrace : WordTrace (prefixWord ++ tailWord_2825879) baseStart_2825879 baseEnd_2825879 := by
    simpa [prefixWord, tailWord_2825879, baseEnd_2825879] using wordTrace_append hprefix tailTrace_2825879
  have hstable : (prefixWord ++ tailWord_2825879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825879).length < 2 ^ (prefixWord ++ tailWord_2825879).sum := by decide
  have hdescent : baseEnd_2825879 < baseStart_2825879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825888 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_2825888 : Nat := 118140960795 + 2825888 * 2 ^ 59
def prefixEnd_2825888 : Nat := 4983230072969 + 3 ^ 40 * 2825888 * 2
def baseEnd_2825888 : Nat := 967359213181829955935989

theorem tailTrace_2825888 : CollatzResearch.WordTrace tailWord_2825888 prefixEnd_2825888 967359213181829955935989 := by
  unfold tailWord_2825888
  simp only [CollatzResearch.WordTrace]
  refine ⟨51534301393148937045955159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68712401857531916061273545 51534301393148937045955159)
  ·
    refine ⟨77301452089723405568932739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51534301393148937045955159 77301452089723405568932739)
    ·
      refine ⟨115952178134585108353399109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77301452089723405568932739 115952178134585108353399109)
      ·
        refine ⟨21741033400234707816262333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115952178134585108353399109 21741033400234707816262333)
        ·
          refine ⟨8152887525088015431098375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21741033400234707816262333 8152887525088015431098375)
          ·
            refine ⟨12229331287632023146647563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8152887525088015431098375 12229331287632023146647563)
            ·
              refine ⟨18343996931448034719971345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12229331287632023146647563 18343996931448034719971345)
              ·
                refine ⟨13757997698586026039978509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18343996931448034719971345 13757997698586026039978509)
                ·
                  refine ⟨5159249136969759764991941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13757997698586026039978509 5159249136969759764991941)
                  ·
                    refine ⟨967359213181829955935989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5159249136969759764991941 967359213181829955935989)
                    ·
                      rfl

theorem cell22_2825888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_2825888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825888 prefixEnd_2825888 := by exact prefixLift 2825888
  have htrace : WordTrace (prefixWord ++ tailWord_2825888) baseStart_2825888 baseEnd_2825888 := by
    simpa [prefixWord, tailWord_2825888, baseEnd_2825888] using wordTrace_append hprefix tailTrace_2825888
  have hstable : (prefixWord ++ tailWord_2825888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825888).length < 2 ^ (prefixWord ++ tailWord_2825888).sum := by decide
  have hdescent : baseEnd_2825888 < baseStart_2825888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825920 : List Nat := [2, 1, 1, 2, 4, 1, 4, 3, 4]
def baseStart_2825920 : Nat := 118140960795 + 2825920 * 2 ^ 59
def prefixEnd_2825920 : Nat := 4983230072969 + 3 ^ 40 * 2825920 * 2
def baseEnd_2825920 : Nat := 322456722478597513045297

theorem tailTrace_2825920 : CollatzResearch.WordTrace tailWord_2825920 prefixEnd_2825920 322456722478597513045297 := by
  unfold tailWord_2825920
  simp only [CollatzResearch.WordTrace]
  refine ⟨51534884961090971778537607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68713179948121295704716809 51534884961090971778537607)
  ·
    refine ⟨77302327441636457667806411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51534884961090971778537607 77302327441636457667806411)
    ·
      refine ⟨115953491162454686501709617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77302327441636457667806411 115953491162454686501709617)
      ·
        refine ⟨86965118371841014876282213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115953491162454686501709617 86965118371841014876282213)
        ·
          refine ⟨16305959694720190289302915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86965118371841014876282213 16305959694720190289302915)
          ·
            refine ⟨24458939542080285433954373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16305959694720190289302915 24458939542080285433954373)
            ·
              refine ⟨4586051164140053518866445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24458939542080285433954373 4586051164140053518866445)
              ·
                refine ⟨1719769186552520069574917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4586051164140053518866445 1719769186552520069574917)
                ·
                  refine ⟨322456722478597513045297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719769186552520069574917 322456722478597513045297)
                  ·
                    rfl

theorem cell22_2825920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_2825920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825920 prefixEnd_2825920 := by exact prefixLift 2825920
  have htrace : WordTrace (prefixWord ++ tailWord_2825920) baseStart_2825920 baseEnd_2825920 := by
    simpa [prefixWord, tailWord_2825920, baseEnd_2825920] using wordTrace_append hprefix tailTrace_2825920
  have hstable : (prefixWord ++ tailWord_2825920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825920).length < 2 ^ (prefixWord ++ tailWord_2825920).sum := by decide
  have hdescent : baseEnd_2825920 < baseStart_2825920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825965 : List Nat := [1, 5, 1, 2, 1, 2, 4, 6]
def baseStart_2825965 : Nat := 118140960795 + 2825965 * 2 ^ 59
def prefixEnd_2825965 : Nat := 4983230072969 + 3 ^ 40 * 2825965 * 2
def baseEnd_2825965 : Nat := 107487285761714157973417

theorem tailTrace_2825965 : CollatzResearch.WordTrace tailWord_2825965 prefixEnd_2825965 107487285761714157973417 := by
  unfold tailWord_2825965
  simp only [CollatzResearch.WordTrace]
  refine ⟨103071411207018916242463349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68714274138012610828308899 103071411207018916242463349)
  ·
    refine ⟨9662944800658023397730939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103071411207018916242463349 9662944800658023397730939)
    ·
      refine ⟨14494417200987035096596409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9662944800658023397730939 14494417200987035096596409)
      ·
        refine ⟨10870812900740276322447307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14494417200987035096596409 10870812900740276322447307)
        ·
          refine ⟨16306219351110414483670961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10870812900740276322447307 16306219351110414483670961)
          ·
            refine ⟨12229664513332810862753221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16306219351110414483670961 12229664513332810862753221)
            ·
              refine ⟨2293062096249902036766229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12229664513332810862753221 2293062096249902036766229)
              ·
                refine ⟨107487285761714157973417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2293062096249902036766229 107487285761714157973417)
                ·
                  rfl

theorem cell22_2825965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 6].length) (baseStart_2825965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825965 prefixEnd_2825965 := by exact prefixLift 2825965
  have htrace : WordTrace (prefixWord ++ tailWord_2825965) baseStart_2825965 baseEnd_2825965 := by
    simpa [prefixWord, tailWord_2825965, baseEnd_2825965] using wordTrace_append hprefix tailTrace_2825965
  have hstable : (prefixWord ++ tailWord_2825965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825965).length < 2 ^ (prefixWord ++ tailWord_2825965).sum := by decide
  have hdescent : baseEnd_2825965 < baseStart_2825965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825982 : List Nat := [4, 2, 2, 1, 4, 1, 8]
def baseStart_2825982 : Nat := 118140960795 + 2825982 * 2 ^ 59
def prefixEnd_2825982 : Nat := 4983230072969 + 3 ^ 40 * 2825982 * 2
def baseEnd_2825982 : Nat := 35829310788994260892063

theorem tailTrace_2825982 : CollatzResearch.WordTrace tailWord_2825982 prefixEnd_2825982 35829310788994260892063 := by
  unfold tailWord_2825982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12884003905994666018229025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68714687498638218763888133 12884003905994666018229025)
  ·
    refine ⟨9663002929495999513671769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12884003905994666018229025 9663002929495999513671769)
    ·
      refine ⟨7247252197121999635253827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9663002929495999513671769 7247252197121999635253827)
      ·
        refine ⟨10870878295682999452880741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7247252197121999635253827 10870878295682999452880741)
        ·
          refine ⟨2038289680440562397415139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10870878295682999452880741 2038289680440562397415139)
          ·
            refine ⟨3057434520660843596122709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038289680440562397415139 3057434520660843596122709)
            ·
              refine ⟨35829310788994260892063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3057434520660843596122709 35829310788994260892063)
              ·
                rfl

theorem cell22_2825982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 8].length) (baseStart_2825982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825982 prefixEnd_2825982 := by exact prefixLift 2825982
  have htrace : WordTrace (prefixWord ++ tailWord_2825982) baseStart_2825982 baseEnd_2825982 := by
    simpa [prefixWord, tailWord_2825982, baseEnd_2825982] using wordTrace_append hprefix tailTrace_2825982
  have hstable : (prefixWord ++ tailWord_2825982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825982).length < 2 ^ (prefixWord ++ tailWord_2825982).sum := by decide
  have hdescent : baseEnd_2825982 < baseStart_2825982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825993 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 5]
def baseStart_2825993 : Nat := 118140960795 + 2825993 * 2 ^ 59
def prefixEnd_2825993 : Nat := 4983230072969 + 3 ^ 40 * 2825993 * 2
def baseEnd_2825993 : Nat := 322465052275881560686889

theorem tailTrace_2825993 : CollatzResearch.WordTrace tailWord_2825993 prefixEnd_2825993 322465052275881560686889 := by
  unfold tailWord_2825993
  simp only [CollatzResearch.WordTrace]
  refine ⟨103072432450917477024482633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68714954967278318016321755 103072432450917477024482633)
  ·
    refine ⟨77304324338188107768361975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103072432450917477024482633 77304324338188107768361975)
    ·
      refine ⟨115956486507282161652542963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77304324338188107768361975 115956486507282161652542963)
      ·
        refine ⟨173934729760923242478814445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115956486507282161652542963 173934729760923242478814445)
        ·
          refine ⟨65225523660346215929555417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173934729760923242478814445 65225523660346215929555417)
          ·
            refine ⟨48919142745259661947166563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65225523660346215929555417 48919142745259661947166563)
            ·
              refine ⟨73378714117889492920749845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48919142745259661947166563 73378714117889492920749845)
              ·
                refine ⟨3439627224276069980660149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73378714117889492920749845 3439627224276069980660149)
                ·
                  refine ⟨322465052275881560686889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3439627224276069980660149 322465052275881560686889)
                  ·
                    rfl

theorem cell22_2825993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_2825993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2825993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2825993 prefixEnd_2825993 := by exact prefixLift 2825993
  have htrace : WordTrace (prefixWord ++ tailWord_2825993) baseStart_2825993 baseEnd_2825993 := by
    simpa [prefixWord, tailWord_2825993, baseEnd_2825993] using wordTrace_append hprefix tailTrace_2825993
  have hstable : (prefixWord ++ tailWord_2825993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825993).length < 2 ^ (prefixWord ++ tailWord_2825993).sum := by decide
  have hdescent : baseEnd_2825993 < baseStart_2825993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826008 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_2826008 : Nat := 118140960795 + 2826008 * 2 ^ 59
def prefixEnd_2826008 : Nat := 4983230072969 + 3 ^ 40 * 2826008 * 2
def baseEnd_2826008 : Nat := 967400291634189642935621

theorem tailTrace_2826008 : CollatzResearch.WordTrace tailWord_2826008 prefixEnd_2826008 967400291634189642935621 := by
  unfold tailWord_2826008
  simp only [CollatzResearch.WordTrace]
  refine ⟨51536489772931567293139339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68715319697242089724185785 51536489772931567293139339)
  ·
    refine ⟨77304734659397350939709009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51536489772931567293139339 77304734659397350939709009)
    ·
      refine ⟨57978550994548013204781757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77304734659397350939709009 57978550994548013204781757)
      ·
        refine ⟨21741956622955504951793159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57978550994548013204781757 21741956622955504951793159)
        ·
          refine ⟨32612934934433257427689739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21741956622955504951793159 32612934934433257427689739)
          ·
            refine ⟨48919402401649886141534609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32612934934433257427689739 48919402401649886141534609)
            ·
              refine ⟨36689551801237414606150957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48919402401649886141534609 36689551801237414606150957)
              ·
                refine ⟨13758581925464030477306609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36689551801237414606150957 13758581925464030477306609)
                ·
                  refine ⟨10318936444098022857979957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13758581925464030477306609 10318936444098022857979957)
                  ·
                    refine ⟨967400291634189642935621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10318936444098022857979957 967400291634189642935621)
                    ·
                      rfl

theorem cell22_2826008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_2826008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826008 prefixEnd_2826008 := by exact prefixLift 2826008
  have htrace : WordTrace (prefixWord ++ tailWord_2826008) baseStart_2826008 baseEnd_2826008 := by
    simpa [prefixWord, tailWord_2826008, baseEnd_2826008] using wordTrace_append hprefix tailTrace_2826008
  have hstable : (prefixWord ++ tailWord_2826008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826008).length < 2 ^ (prefixWord ++ tailWord_2826008).sum := by decide
  have hdescent : baseEnd_2826008 < baseStart_2826008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826010 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_2826010 : Nat := 118140960795 + 2826010 * 2 ^ 59
def prefixEnd_2826010 : Nat := 4983230072969 + 3 ^ 40 * 2826010 * 2
def baseEnd_2826010 : Nat := 322466992091687434795205

theorem tailTrace_2826010 : CollatzResearch.WordTrace tailWord_2826010 prefixEnd_2826010 322466992091687434795205 := by
  unfold tailWord_2826010
  simp only [CollatzResearch.WordTrace]
  refine ⟨25768263122963972231962871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68715368327903925951900989 25768263122963972231962871)
  ·
    refine ⟨38652394684445958347944307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25768263122963972231962871 38652394684445958347944307)
    ·
      refine ⟨57978592026668937521916461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38652394684445958347944307 57978592026668937521916461)
      ·
        refine ⟨21741972010000851570718673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57978592026668937521916461 21741972010000851570718673)
        ·
          refine ⟨16306479007500638678039005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21741972010000851570718673 16306479007500638678039005)
          ·
            refine ⟨6114929627812739504264627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16306479007500638678039005 6114929627812739504264627)
            ·
              refine ⟨9172394441719109256396941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6114929627812739504264627 9172394441719109256396941)
              ·
                refine ⟨3439647915644665971148853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9172394441719109256396941 3439647915644665971148853)
                ·
                  refine ⟨322466992091687434795205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3439647915644665971148853 322466992091687434795205)
                  ·
                    rfl

theorem cell22_2826010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_2826010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826010 prefixEnd_2826010 := by exact prefixLift 2826010
  have htrace : WordTrace (prefixWord ++ tailWord_2826010) baseStart_2826010 baseEnd_2826010 := by
    simpa [prefixWord, tailWord_2826010, baseEnd_2826010] using wordTrace_append hprefix tailTrace_2826010
  have hstable : (prefixWord ++ tailWord_2826010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826010).length < 2 ^ (prefixWord ++ tailWord_2826010).sum := by decide
  have hdescent : baseEnd_2826010 < baseStart_2826010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826053 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_2826053 : Nat := 118140960795 + 2826053 * 2 ^ 59
def prefixEnd_2826053 : Nat := 4983230072969 + 3 ^ 40 * 2826053 * 2
def baseEnd_2826053 : Nat := 967415696053824525560483

theorem tailTrace_2826053 : CollatzResearch.WordTrace tailWord_2826053 prefixEnd_2826053 967415696053824525560483 := by
  unfold tailWord_2826053
  simp only [CollatzResearch.WordTrace]
  refine ⟨103074620830700107271666813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68716413887133404847777875 103074620830700107271666813)
  ·
    refine ⟨38652982811512540226875055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103074620830700107271666813 38652982811512540226875055)
    ·
      refine ⟨57979474217268810340312583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38652982811512540226875055 57979474217268810340312583)
      ·
        refine ⟨86969211325903215510468875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57979474217268810340312583 86969211325903215510468875)
        ·
          refine ⟨130453816988854823265703313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86969211325903215510468875 130453816988854823265703313)
          ·
            refine ⟨97840362741641117449277485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130453816988854823265703313 97840362741641117449277485)
            ·
              refine ⟨36690136028115419043479057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97840362741641117449277485 36690136028115419043479057)
              ·
                refine ⟨27517602021086564282609293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36690136028115419043479057 27517602021086564282609293)
                ·
                  refine ⟨10319100757907461605978485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27517602021086564282609293 10319100757907461605978485)
                  ·
                    refine ⟨967415696053824525560483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10319100757907461605978485 967415696053824525560483)
                    ·
                      rfl

theorem cell22_2826053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_2826053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826053 prefixEnd_2826053 := by exact prefixLift 2826053
  have htrace : WordTrace (prefixWord ++ tailWord_2826053) baseStart_2826053 baseEnd_2826053 := by
    simpa [prefixWord, tailWord_2826053, baseEnd_2826053] using wordTrace_append hprefix tailTrace_2826053
  have hstable : (prefixWord ++ tailWord_2826053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826053).length < 2 ^ (prefixWord ++ tailWord_2826053).sum := by decide
  have hdescent : baseEnd_2826053 < baseStart_2826053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826128 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 9]
def baseStart_2826128 : Nat := 118140960795 + 2826128 * 2 ^ 59
def prefixEnd_2826128 : Nat := 4983230072969 + 3 ^ 40 * 2826128 * 2
def baseEnd_2826128 : Nat := 322480456695516443311751

theorem tailTrace_2826128 : CollatzResearch.WordTrace tailWord_2826128 prefixEnd_2826128 322480456695516443311751 := by
  unfold tailWord_2826128
  simp only [CollatzResearch.WordTrace]
  refine ⟨51538678152714197540323519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68718237536952263387098025 51538678152714197540323519)
  ·
    refine ⟨77308017229071296310485279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51538678152714197540323519 77308017229071296310485279)
    ·
      refine ⟨115962025843606944465727919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77308017229071296310485279 115962025843606944465727919)
      ·
        refine ⟨173943038765410416698591879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115962025843606944465727919 173943038765410416698591879)
        ·
          refine ⟨260914558148115625047887819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173943038765410416698591879 260914558148115625047887819)
          ·
            refine ⟨391371837222173437571831729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260914558148115625047887819 391371837222173437571831729)
            ·
              refine ⟨293528877916630078178873797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391371837222173437571831729 293528877916630078178873797)
              ·
                refine ⟨55036664609368139658538837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293528877916630078178873797 55036664609368139658538837)
                ·
                  refine ⟨322480456695516443311751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55036664609368139658538837 322480456695516443311751)
                  ·
                    rfl

theorem cell22_2826128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_2826128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826128 prefixEnd_2826128 := by exact prefixLift 2826128
  have htrace : WordTrace (prefixWord ++ tailWord_2826128) baseStart_2826128 baseEnd_2826128 := by
    simpa [prefixWord, tailWord_2826128, baseEnd_2826128] using wordTrace_append hprefix tailTrace_2826128
  have hstable : (prefixWord ++ tailWord_2826128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826128).length < 2 ^ (prefixWord ++ tailWord_2826128).sum := by decide
  have hdescent : baseEnd_2826128 < baseStart_2826128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826175 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 3, 4]
def baseStart_2826175 : Nat := 118140960795 + 2826175 * 2 ^ 59
def prefixEnd_2826175 : Nat := 4983230072969 + 3 ^ 40 * 2826175 * 2
def baseEnd_2826175 : Nat := 967457459147056874010109

theorem tailTrace_2826175 : CollatzResearch.WordTrace tailWord_2826175 prefixEnd_2826175 967457459147056874010109 := by
  unfold tailWord_2826175
  simp only [CollatzResearch.WordTrace]
  refine ⟨103079070536258122107607979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68719380357505414738405319 103079070536258122107607979)
  ·
    refine ⟨154618605804387183161411969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103079070536258122107607979 154618605804387183161411969)
    ·
      refine ⟨115963954353290387371058977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154618605804387183161411969 115963954353290387371058977)
      ·
        refine ⟨86972965764967790528294233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115963954353290387371058977 86972965764967790528294233)
        ·
          refine ⟨65229724323725842896220675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86972965764967790528294233 65229724323725842896220675)
          ·
            refine ⟨97844586485588764344331013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65229724323725842896220675 97844586485588764344331013)
            ·
              refine ⟨18345859966047893314562065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97844586485588764344331013 18345859966047893314562065)
              ·
                refine ⟨13759394974535919985921549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18345859966047893314562065 13759394974535919985921549)
                ·
                  refine ⟨5159773115450969994720581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13759394974535919985921549 5159773115450969994720581)
                  ·
                    refine ⟨967457459147056874010109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5159773115450969994720581 967457459147056874010109)
                    ·
                      rfl

theorem cell22_2826175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_2826175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826175 prefixEnd_2826175 := by exact prefixLift 2826175
  have htrace : WordTrace (prefixWord ++ tailWord_2826175) baseStart_2826175 baseEnd_2826175 := by
    simpa [prefixWord, tailWord_2826175, baseEnd_2826175] using wordTrace_append hprefix tailTrace_2826175
  have hstable : (prefixWord ++ tailWord_2826175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826175).length < 2 ^ (prefixWord ++ tailWord_2826175).sum := by decide
  have hdescent : baseEnd_2826175 < baseStart_2826175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826190 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_2826190 : Nat := 118140960795 + 2826190 * 2 ^ 59
def prefixEnd_2826190 : Nat := 4983230072969 + 3 ^ 40 * 2826190 * 2
def baseEnd_2826190 : Nat := 322487531317867278295021

theorem tailTrace_2826190 : CollatzResearch.WordTrace tailWord_2826190 prefixEnd_2826190 322487531317867278295021 := by
  unfold tailWord_2826190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12884952203900472458675503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68719745087469186446269349 12884952203900472458675503)
  ·
    refine ⟨19327428305850708688013255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12884952203900472458675503 19327428305850708688013255)
    ·
      refine ⟨28991142458776063032019883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19327428305850708688013255 28991142458776063032019883)
      ·
        refine ⟨43486713688164094548029825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28991142458776063032019883 43486713688164094548029825)
        ·
          refine ⟨32615035266123070911022369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43486713688164094548029825 32615035266123070911022369)
          ·
            refine ⟨24461276449592303183266777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32615035266123070911022369 24461276449592303183266777)
            ·
              refine ⟨18345957337194227387450083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24461276449592303183266777 18345957337194227387450083)
              ·
                refine ⟨27518936005791341081175125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18345957337194227387450083 27518936005791341081175125)
                ·
                  refine ⟨322487531317867278295021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27518936005791341081175125 322487531317867278295021)
                  ·
                    rfl

theorem cell22_2826190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_2826190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826190 prefixEnd_2826190 := by exact prefixLift 2826190
  have htrace : WordTrace (prefixWord ++ tailWord_2826190) baseStart_2826190 baseEnd_2826190 := by
    simpa [prefixWord, tailWord_2826190, baseEnd_2826190] using wordTrace_append hprefix tailTrace_2826190
  have hstable : (prefixWord ++ tailWord_2826190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826190).length < 2 ^ (prefixWord ++ tailWord_2826190).sum := by decide
  have hdescent : baseEnd_2826190 < baseStart_2826190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826192 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_2826192 : Nat := 118140960795 + 2826192 * 2 ^ 59
def prefixEnd_2826192 : Nat := 4983230072969 + 3 ^ 40 * 2826192 * 2
def baseEnd_2826192 : Nat := 967463278594474496335057

theorem tailTrace_2826192 : CollatzResearch.WordTrace tailWord_2826192 prefixEnd_2826192 967463278594474496335057 := by
  unfold tailWord_2826192
  simp only [CollatzResearch.WordTrace]
  refine ⟨51539845288598267005488415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68719793718131022673984553 51539845288598267005488415)
  ·
    refine ⟨77309767932897400508232623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51539845288598267005488415 77309767932897400508232623)
    ·
      refine ⟨115964651899346100762348935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77309767932897400508232623 115964651899346100762348935)
      ·
        refine ⟨173946977849019151143523403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115964651899346100762348935 173946977849019151143523403)
        ·
          refine ⟨260920466773528726715285105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173946977849019151143523403 260920466773528726715285105)
          ·
            refine ⟨195690350080146545036463829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260920466773528726715285105 195690350080146545036463829)
            ·
              refine ⟨4586492580003434649292121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 195690350080146545036463829 4586492580003434649292121)
              ·
                refine ⟨3439869435002575986969091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4586492580003434649292121 3439869435002575986969091)
                ·
                  refine ⟨5159804152503863980453637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439869435002575986969091 5159804152503863980453637)
                  ·
                    refine ⟨967463278594474496335057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5159804152503863980453637 967463278594474496335057)
                    ·
                      rfl

theorem cell22_2826192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_2826192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826192 prefixEnd_2826192 := by exact prefixLift 2826192
  have htrace : WordTrace (prefixWord ++ tailWord_2826192) baseStart_2826192 baseEnd_2826192 := by
    simpa [prefixWord, tailWord_2826192, baseEnd_2826192] using wordTrace_append hprefix tailTrace_2826192
  have hstable : (prefixWord ++ tailWord_2826192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826192).length < 2 ^ (prefixWord ++ tailWord_2826192).sum := by decide
  have hdescent : baseEnd_2826192 < baseStart_2826192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826224 : List Nat := [2, 1, 1, 1, 3, 2, 6, 2, 4]
def baseStart_2826224 : Nat := 118140960795 + 2826224 * 2 ^ 59
def prefixEnd_2826224 : Nat := 4983230072969 + 3 ^ 40 * 2826224 * 2
def baseEnd_2826224 : Nat := 322491410949479026511653

theorem tailTrace_2826224 : CollatzResearch.WordTrace tailWord_2826224 prefixEnd_2826224 322491410949479026511653 := by
  unfold tailWord_2826224
  simp only [CollatzResearch.WordTrace]
  refine ⟨51540428856540301738070863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68720571808720402317427817 51540428856540301738070863)
  ·
    refine ⟨77310643284810452607106295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51540428856540301738070863 77310643284810452607106295)
    ·
      refine ⟨115965964927215678910659443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77310643284810452607106295 115965964927215678910659443)
      ·
        refine ⟨173948947390823518365989165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115965964927215678910659443 173948947390823518365989165)
        ·
          refine ⟨65230855271558819387245937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173948947390823518365989165 65230855271558819387245937)
          ·
            refine ⟨48923141453669114540434453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65230855271558819387245937 48923141453669114540434453)
            ·
              refine ⟨2293272255640739744082865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48923141453669114540434453 2293272255640739744082865)
              ·
                refine ⟨1719954191730554808062149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293272255640739744082865 1719954191730554808062149)
                ·
                  refine ⟨322491410949479026511653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719954191730554808062149 322491410949479026511653)
                  ·
                    rfl

theorem cell22_2826224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 4].length) (baseStart_2826224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826224 prefixEnd_2826224 := by exact prefixLift 2826224
  have htrace : WordTrace (prefixWord ++ tailWord_2826224) baseStart_2826224 baseEnd_2826224 := by
    simpa [prefixWord, tailWord_2826224, baseEnd_2826224] using wordTrace_append hprefix tailTrace_2826224
  have hstable : (prefixWord ++ tailWord_2826224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826224).length < 2 ^ (prefixWord ++ tailWord_2826224).sum := by decide
  have hdescent : baseEnd_2826224 < baseStart_2826224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826235 : List Nat := [1, 1, 1, 1, 1, 3, 7, 7]
def baseStart_2826235 : Nat := 118140960795 + 2826235 * 2 ^ 59
def prefixEnd_2826235 : Nat := 4983230072969 + 3 ^ 40 * 2826235 * 2
def baseEnd_2826235 : Nat := 107497555374804079723325

theorem tailTrace_2826235 : CollatzResearch.WordTrace tailWord_2826235 prefixEnd_2826235 107497555374804079723325 := by
  unfold tailWord_2826235
  simp only [CollatzResearch.WordTrace]
  refine ⟨103081258916040752354792159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68720839277360501569861439 103081258916040752354792159)
  ·
    refine ⟨154621888374061128532188239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103081258916040752354792159 154621888374061128532188239)
    ·
      refine ⟨231932832561091692798282359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154621888374061128532188239 231932832561091692798282359)
      ·
        refine ⟨347899248841637539197423539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231932832561091692798282359 347899248841637539197423539)
        ·
          refine ⟨521848873262456308796135309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347899248841637539197423539 521848873262456308796135309)
          ·
            refine ⟨195693327473421115798550741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 521848873262456308796135309 195693327473421115798550741)
            ·
              refine ⟨4586562362658307401528533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 195693327473421115798550741 4586562362658307401528533)
              ·
                refine ⟨107497555374804079723325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4586562362658307401528533 107497555374804079723325)
                ·
                  rfl

theorem cell22_2826235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 7].length) (baseStart_2826235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826235 prefixEnd_2826235 := by exact prefixLift 2826235
  have htrace : WordTrace (prefixWord ++ tailWord_2826235) baseStart_2826235 baseEnd_2826235 := by
    simpa [prefixWord, tailWord_2826235, baseEnd_2826235] using wordTrace_append hprefix tailTrace_2826235
  have hstable : (prefixWord ++ tailWord_2826235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826235).length < 2 ^ (prefixWord ++ tailWord_2826235).sum := by decide
  have hdescent : baseEnd_2826235 < baseStart_2826235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826252 : List Nat := [2, 2, 1, 2, 3, 1, 5, 6]
def baseStart_2826252 : Nat := 118140960795 + 2826252 * 2 ^ 59
def prefixEnd_2826252 : Nat := 4983230072969 + 3 ^ 40 * 2826252 * 2
def baseEnd_2826252 : Nat := 107498201980072704426097

theorem tailTrace_2826252 : CollatzResearch.WordTrace tailWord_2826252 prefixEnd_2826252 107498201980072704426097 := by
  unfold tailWord_2826252
  simp only [CollatzResearch.WordTrace]
  refine ⟨51540939478489582129080505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68721252637986109505440673 51540939478489582129080505)
  ·
    refine ⟨38655704608867186596810379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51540939478489582129080505 38655704608867186596810379)
    ·
      refine ⟨57983556913300779895215569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38655704608867186596810379 57983556913300779895215569)
      ·
        refine ⟨43487667684975584921411677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57983556913300779895215569 43487667684975584921411677)
        ·
          refine ⟨16307875381865844345529379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43487667684975584921411677 16307875381865844345529379)
          ·
            refine ⟨24461813072798766518294069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16307875381865844345529379 24461813072798766518294069)
            ·
              refine ⟨2293294975574884361090069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24461813072798766518294069 2293294975574884361090069)
              ·
                refine ⟨107498201980072704426097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2293294975574884361090069 107498201980072704426097)
                ·
                  rfl

theorem cell22_2826252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 6].length) (baseStart_2826252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826252 prefixEnd_2826252 := by exact prefixLift 2826252
  have htrace : WordTrace (prefixWord ++ tailWord_2826252) baseStart_2826252 baseEnd_2826252 := by
    simpa [prefixWord, tailWord_2826252, baseEnd_2826252] using wordTrace_append hprefix tailTrace_2826252
  have hstable : (prefixWord ++ tailWord_2826252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826252).length < 2 ^ (prefixWord ++ tailWord_2826252).sum := by decide
  have hdescent : baseEnd_2826252 < baseStart_2826252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826260 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2826260 : Nat := 118140960795 + 2826260 * 2 ^ 59
def prefixEnd_2826260 : Nat := 4983230072969 + 3 ^ 40 * 2826260 * 2
def baseEnd_2826260 : Nat := 967486556384144985634849

theorem tailTrace_2826260 : CollatzResearch.WordTrace tailWord_2826260 prefixEnd_2826260 967486556384144985634849 := by
  unfold tailWord_2826260
  simp only [CollatzResearch.WordTrace]
  refine ⟨51541085370475090812226117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68721447160633454416301489 51541085370475090812226117)
  ·
    refine ⟨9663953506964079527292397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51541085370475090812226117 9663953506964079527292397)
    ·
      refine ⟨3623982565111529822734649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9663953506964079527292397 3623982565111529822734649)
      ·
        refine ⟨2717986923833647367050987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3623982565111529822734649 2717986923833647367050987)
        ·
          refine ⟨4076980385750471050576481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717986923833647367050987 4076980385750471050576481)
          ·
            refine ⟨3057735289312853287932361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4076980385750471050576481 3057735289312853287932361)
            ·
              refine ⟨2293301466984639965949271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057735289312853287932361 2293301466984639965949271)
              ·
                refine ⟨3439952200476959948923907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293301466984639965949271 3439952200476959948923907)
                ·
                  refine ⟨5159928300715439923385861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439952200476959948923907 5159928300715439923385861)
                  ·
                    refine ⟨967486556384144985634849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5159928300715439923385861 967486556384144985634849)
                    ·
                      rfl

theorem cell22_2826260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2826260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826260 prefixEnd_2826260 := by exact prefixLift 2826260
  have htrace : WordTrace (prefixWord ++ tailWord_2826260) baseStart_2826260 baseEnd_2826260 := by
    simpa [prefixWord, tailWord_2826260, baseEnd_2826260] using wordTrace_append hprefix tailTrace_2826260
  have hstable : (prefixWord ++ tailWord_2826260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826260).length < 2 ^ (prefixWord ++ tailWord_2826260).sum := by decide
  have hdescent : baseEnd_2826260 < baseStart_2826260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826273 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 2, 3]
def baseStart_2826273 : Nat := 118140960795 + 2826273 * 2 ^ 59
def prefixEnd_2826273 : Nat := 4983230072969 + 3 ^ 40 * 2826273 * 2
def baseEnd_2826273 : Nat := 967491006549817285059809

theorem tailTrace_2826273 : CollatzResearch.WordTrace tailWord_2826273 prefixEnd_2826273 967491006549817285059809 := by
  unfold tailWord_2826273
  simp only [CollatzResearch.WordTrace]
  refine ⟨103082644889903084844675473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68721763259935389896450315 103082644889903084844675473)
  ·
    refine ⟨77311983667427313633506605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103082644889903084844675473 77311983667427313633506605)
    ·
      refine ⟨28991993875285242612564977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77311983667427313633506605 28991993875285242612564977)
      ·
        refine ⟨21743995406463931959423733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28991993875285242612564977 21743995406463931959423733)
        ·
          refine ⟨2038499569355993621195975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21743995406463931959423733 2038499569355993621195975)
          ·
            refine ⟨3057749354033990431793963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038499569355993621195975 3057749354033990431793963)
            ·
              refine ⟨4586624031050985647690945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057749354033990431793963 4586624031050985647690945)
              ·
                refine ⟨3439968023288239235768209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4586624031050985647690945 3439968023288239235768209)
                ·
                  refine ⟨2579976017466179426826157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3439968023288239235768209 2579976017466179426826157)
                  ·
                    refine ⟨967491006549817285059809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2579976017466179426826157 967491006549817285059809)
                    ·
                      rfl

theorem cell22_2826273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_2826273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826273 prefixEnd_2826273 := by exact prefixLift 2826273
  have htrace : WordTrace (prefixWord ++ tailWord_2826273) baseStart_2826273 baseEnd_2826273 := by
    simpa [prefixWord, tailWord_2826273, baseEnd_2826273] using wordTrace_append hprefix tailTrace_2826273
  have hstable : (prefixWord ++ tailWord_2826273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826273).length < 2 ^ (prefixWord ++ tailWord_2826273).sum := by decide
  have hdescent : baseEnd_2826273 < baseStart_2826273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826318 : List Nat := [4, 1, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_2826318 : Nat := 118140960795 + 2826318 * 2 ^ 59
def prefixEnd_2826318 : Nat := 4983230072969 + 3 ^ 40 * 2826318 * 2
def baseEnd_2826318 : Nat := 967506410969452167684671

theorem tailTrace_2826318 : CollatzResearch.WordTrace tailWord_2826318 prefixEnd_2826318 967506410969452167684671 := by
  unfold tailWord_2826318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12885535771842507191257951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68722857449826705020042405 12885535771842507191257951)
  ·
    refine ⟨19328303657763760786886927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12885535771842507191257951 19328303657763760786886927)
    ·
      refine ⟨28992455486645641180330391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19328303657763760786886927 28992455486645641180330391)
      ·
        refine ⟨43488683229968461770495587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28992455486645641180330391 43488683229968461770495587)
        ·
          refine ⟨65233024844952692655743381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43488683229968461770495587 65233024844952692655743381)
          ·
            refine ⟨3057798039607157468237971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65233024844952692655743381 3057798039607157468237971)
            ·
              refine ⟨4586697059410736202356957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057798039607157468237971 4586697059410736202356957)
              ·
                refine ⟨1720011397279026075883859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4586697059410736202356957 1720011397279026075883859)
                ·
                  refine ⟨2580017095918539113825789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720011397279026075883859 2580017095918539113825789)
                  ·
                    refine ⟨967506410969452167684671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580017095918539113825789 967506410969452167684671)
                    ·
                      rfl

theorem cell22_2826318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_2826318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826318 prefixEnd_2826318 := by exact prefixLift 2826318
  have htrace : WordTrace (prefixWord ++ tailWord_2826318) baseStart_2826318 baseEnd_2826318 := by
    simpa [prefixWord, tailWord_2826318, baseEnd_2826318] using wordTrace_append hprefix tailTrace_2826318
  have hstable : (prefixWord ++ tailWord_2826318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826318).length < 2 ^ (prefixWord ++ tailWord_2826318).sum := by decide
  have hdescent : baseEnd_2826318 < baseStart_2826318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826361 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 1, 4]
def baseStart_2826361 : Nat := 118140960795 + 2826361 * 2 ^ 59
def prefixEnd_2826361 : Nat := 4983230072969 + 3 ^ 40 * 2826361 * 2
def baseEnd_2826361 : Nat := 967521130748214388859539

theorem tailTrace_2826361 : CollatzResearch.WordTrace tailWord_2826361 prefixEnd_2826361 967521130748214388859539 := by
  unfold tailWord_2826361
  simp only [CollatzResearch.WordTrace]
  refine ⟨103085854513584275873878937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68723903009056183915919291 103085854513584275873878937)
  ·
    refine ⟨77314390885188206905409203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103085854513584275873878937 77314390885188206905409203)
    ·
      refine ⟨115971586327782310358113805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77314390885188206905409203 115971586327782310358113805)
      ·
        refine ⟨43489344872918366384292677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115971586327782310358113805 43489344872918366384292677)
        ·
          refine ⟨8154252163672193697054877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43489344872918366384292677 8154252163672193697054877)
          ·
            refine ⟨3057844561377072636395579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8154252163672193697054877 3057844561377072636395579)
            ·
              refine ⟨4586766842065608954593369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057844561377072636395579 4586766842065608954593369)
              ·
                refine ⟨3440075131549206715945027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4586766842065608954593369 3440075131549206715945027)
                ·
                  refine ⟨5160112697323810073917541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440075131549206715945027 5160112697323810073917541)
                  ·
                    refine ⟨967521130748214388859539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5160112697323810073917541 967521130748214388859539)
                    ·
                      rfl

theorem cell22_2826361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_2826361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826361 prefixEnd_2826361 := by exact prefixLift 2826361
  have htrace : WordTrace (prefixWord ++ tailWord_2826361) baseStart_2826361 baseEnd_2826361 := by
    simpa [prefixWord, tailWord_2826361, baseEnd_2826361] using wordTrace_append hprefix tailTrace_2826361
  have hstable : (prefixWord ++ tailWord_2826361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826361).length < 2 ^ (prefixWord ++ tailWord_2826361).sum := by decide
  have hdescent : baseEnd_2826361 < baseStart_2826361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826447 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 4, 5]
def baseStart_2826447 : Nat := 118140960795 + 2826447 * 2 ^ 59
def prefixEnd_2826447 : Nat := 4983230072969 + 3 ^ 40 * 2826447 * 2
def baseEnd_2826447 : Nat := 967550570305738831209275

theorem tailTrace_2826447 : CollatzResearch.WordTrace tailWord_2826447 prefixEnd_2826447 967550570305738831209275 := by
  unfold tailWord_2826447
  simp only [CollatzResearch.WordTrace]
  refine ⟨103088991191272712561509595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68725994127515141707673063 103088991191272712561509595)
  ·
    refine ⟨154633486786909068842264393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103088991191272712561509595 154633486786909068842264393)
    ·
      refine ⟨115975115090181801631698295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154633486786909068842264393 115975115090181801631698295)
      ·
        refine ⟨173962672635272702447547443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115975115090181801631698295 173962672635272702447547443)
        ·
          refine ⟨260944008952909053671321165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173962672635272702447547443 260944008952909053671321165)
          ·
            refine ⟨97854003357340895126745437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260944008952909053671321165 97854003357340895126745437)
            ·
              refine ⟨36695251259002835672529539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97854003357340895126745437 36695251259002835672529539)
              ·
                refine ⟨55042876888504253508794309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36695251259002835672529539 55042876888504253508794309)
                ·
                  refine ⟨10320539416594547532898933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55042876888504253508794309 10320539416594547532898933)
                  ·
                    refine ⟨967550570305738831209275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10320539416594547532898933 967550570305738831209275)
                    ·
                      rfl

theorem cell22_2826447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_2826447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826447 prefixEnd_2826447 := by exact prefixLift 2826447
  have htrace : WordTrace (prefixWord ++ tailWord_2826447) baseStart_2826447 baseEnd_2826447 := by
    simpa [prefixWord, tailWord_2826447, baseEnd_2826447] using wordTrace_append hprefix tailTrace_2826447
  have hstable : (prefixWord ++ tailWord_2826447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826447).length < 2 ^ (prefixWord ++ tailWord_2826447).sum := by decide
  have hdescent : baseEnd_2826447 < baseStart_2826447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826449 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 5]
def baseStart_2826449 : Nat := 118140960795 + 2826449 * 2 ^ 59
def prefixEnd_2826449 : Nat := 4983230072969 + 3 ^ 40 * 2826449 * 2
def baseEnd_2826449 : Nat := 322517084982203830886423

theorem tailTrace_2826449 : CollatzResearch.WordTrace tailWord_2826449 prefixEnd_2826449 322517084982203830886423 := by
  unfold tailWord_2826449
  simp only [CollatzResearch.WordTrace]
  refine ⟨103089064137265466903082401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68726042758176977935388267 103089064137265466903082401)
  ·
    refine ⟨77316798102949100177311801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103089064137265466903082401 77316798102949100177311801)
    ·
      refine ⟨57987598577211825132983851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77316798102949100177311801 57987598577211825132983851)
      ·
        refine ⟨86981397865817737699475777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57987598577211825132983851 86981397865817737699475777)
        ·
          refine ⟨65236048399363303274606833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86981397865817737699475777 65236048399363303274606833)
          ·
            refine ⟨48927036299522477455955125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65236048399363303274606833 48927036299522477455955125)
            ·
              refine ⟨4586909653080232261495793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48927036299522477455955125 4586909653080232261495793)
              ·
                refine ⟨3440182239810174196121845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4586909653080232261495793 3440182239810174196121845)
                ·
                  refine ⟨322517084982203830886423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3440182239810174196121845 322517084982203830886423)
                  ·
                    rfl

theorem cell22_2826449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_2826449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826449 prefixEnd_2826449 := by exact prefixLift 2826449
  have htrace : WordTrace (prefixWord ++ tailWord_2826449) baseStart_2826449 baseEnd_2826449 := by
    simpa [prefixWord, tailWord_2826449, baseEnd_2826449] using wordTrace_append hprefix tailTrace_2826449
  have hstable : (prefixWord ++ tailWord_2826449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826449).length < 2 ^ (prefixWord ++ tailWord_2826449).sum := by decide
  have hdescent : baseEnd_2826449 < baseStart_2826449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826453 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_2826453 : Nat := 118140960795 + 2826453 * 2 ^ 59
def prefixEnd_2826453 : Nat := 4983230072969 + 3 ^ 40 * 2826453 * 2
def baseEnd_2826453 : Nat := 967552624228356815559257

theorem tailTrace_2826453 : CollatzResearch.WordTrace tailWord_2826453 prefixEnd_2826453 967552624228356815559257 := by
  unfold tailWord_2826453
  simp only [CollatzResearch.WordTrace]
  refine ⟨103089210029250975586228013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68726140019500650390818675 103089210029250975586228013)
  ·
    refine ⟨38658453760969115844835505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103089210029250975586228013 38658453760969115844835505)
    ·
      refine ⟨28993840320726836883626629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38658453760969115844835505 28993840320726836883626629)
      ·
        refine ⟨5436345060136281915679993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28993840320726836883626629 5436345060136281915679993)
        ·
          refine ⟨4077258795102211436759995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5436345060136281915679993 4077258795102211436759995)
          ·
            refine ⟨6115888192653317155139993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077258795102211436759995 6115888192653317155139993)
            ·
              refine ⟨4586916144489987866354995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6115888192653317155139993 4586916144489987866354995)
              ·
                refine ⟨6880374216734981799532493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586916144489987866354995 6880374216734981799532493)
                ·
                  refine ⟨2580140331275618174824685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6880374216734981799532493 2580140331275618174824685)
                  ·
                    refine ⟨967552624228356815559257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580140331275618174824685 967552624228356815559257)
                    ·
                      rfl

theorem cell22_2826453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_2826453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826453 prefixEnd_2826453 := by exact prefixLift 2826453
  have htrace : WordTrace (prefixWord ++ tailWord_2826453) baseStart_2826453 baseEnd_2826453 := by
    simpa [prefixWord, tailWord_2826453, baseEnd_2826453] using wordTrace_append hprefix tailTrace_2826453
  have hstable : (prefixWord ++ tailWord_2826453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826453).length < 2 ^ (prefixWord ++ tailWord_2826453).sum := by decide
  have hdescent : baseEnd_2826453 < baseStart_2826453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826524 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2826524 : Nat := 118140960795 + 2826524 * 2 ^ 59
def prefixEnd_2826524 : Nat := 4983230072969 + 3 ^ 40 * 2826524 * 2
def baseEnd_2826524 : Nat := 967576928979336297034039

theorem tailTrace_2826524 : CollatzResearch.WordTrace tailWord_2826524 prefixEnd_2826524 967576928979336297034039 := by
  unfold tailWord_2826524
  simp only [CollatzResearch.WordTrace]
  refine ⟨51545899805996877356031313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68727866407995836474708417 51545899805996877356031313)
  ·
    refine ⟨38659424854497658017023485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51545899805996877356031313 38659424854497658017023485)
    ·
      refine ⟨14497284320436621756383807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38659424854497658017023485 14497284320436621756383807)
      ·
        refine ⟨21745926480654932634575711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14497284320436621756383807 21745926480654932634575711)
        ·
          refine ⟨32618889720982398951863567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21745926480654932634575711 32618889720982398951863567)
          ·
            refine ⟨48928334581473598427795351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32618889720982398951863567 48928334581473598427795351)
            ·
              refine ⟨73392501872210397641693027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48928334581473598427795351 73392501872210397641693027)
              ·
                refine ⟨110088752808315596462539541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73392501872210397641693027 110088752808315596462539541)
                ·
                  refine ⟨5160410287889793584181541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110088752808315596462539541 5160410287889793584181541)
                  ·
                    refine ⟨967576928979336297034039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5160410287889793584181541 967576928979336297034039)
                    ·
                      rfl

theorem cell22_2826524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2826524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826524 prefixEnd_2826524 := by exact prefixLift 2826524
  have htrace : WordTrace (prefixWord ++ tailWord_2826524) baseStart_2826524 baseEnd_2826524 := by
    simpa [prefixWord, tailWord_2826524, baseEnd_2826524] using wordTrace_append hprefix tailTrace_2826524
  have hstable : (prefixWord ++ tailWord_2826524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826524).length < 2 ^ (prefixWord ++ tailWord_2826524).sum := by decide
  have hdescent : baseEnd_2826524 < baseStart_2826524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826605 : List Nat := [1, 5, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_2826605 : Nat := 118140960795 + 2826605 * 2 ^ 59
def prefixEnd_2826605 : Nat := 4983230072969 + 3 ^ 40 * 2826605 * 2
def baseEnd_2826605 : Nat := 967604656934679085758791

theorem tailTrace_2826605 : CollatzResearch.WordTrace tailWord_2826605 prefixEnd_2826605 967604656934679085758791 := by
  unfold tailWord_2826605
  simp only [CollatzResearch.WordTrace]
  refine ⟨103094753924700305545761269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68729835949800203697174179 103094753924700305545761269)
  ·
    refine ⟨9665133180440653644915119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103094753924700305545761269 9665133180440653644915119)
    ·
      refine ⟨14497699770660980467372679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9665133180440653644915119 14497699770660980467372679)
      ·
        refine ⟨21746549655991470701059019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14497699770660980467372679 21746549655991470701059019)
        ·
          refine ⟨32619824483987206051588529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21746549655991470701059019 32619824483987206051588529)
          ·
            refine ⟨24464868362990404538691397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32619824483987206051588529 24464868362990404538691397)
            ·
              refine ⟨4587162818060700851004637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24464868362990404538691397 4587162818060700851004637)
              ·
                refine ⟨1720186056772762819126739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4587162818060700851004637 1720186056772762819126739)
                ·
                  refine ⟨2580279085159144228690109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720186056772762819126739 2580279085159144228690109)
                  ·
                    refine ⟨967604656934679085758791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580279085159144228690109 967604656934679085758791)
                    ·
                      rfl

theorem cell22_2826605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_2826605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826605 prefixEnd_2826605 := by exact prefixLift 2826605
  have htrace : WordTrace (prefixWord ++ tailWord_2826605) baseStart_2826605 baseEnd_2826605 := by
    simpa [prefixWord, tailWord_2826605, baseEnd_2826605] using wordTrace_append hprefix tailTrace_2826605
  have hstable : (prefixWord ++ tailWord_2826605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826605).length < 2 ^ (prefixWord ++ tailWord_2826605).sum := by decide
  have hdescent : baseEnd_2826605 < baseStart_2826605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826648 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 1, 4]
def baseStart_2826648 : Nat := 118140960795 + 2826648 * 2 ^ 59
def prefixEnd_2826648 : Nat := 4983230072969 + 3 ^ 40 * 2826648 * 2
def baseEnd_2826648 : Nat := 967619376713441306933659

theorem tailTrace_2826648 : CollatzResearch.WordTrace tailWord_2826648 prefixEnd_2826648 967619376713441306933659 := by
  unfold tailWord_2826648
  simp only [CollatzResearch.WordTrace]
  refine ⟨51548161131772261944788299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68730881509029682593051065 51548161131772261944788299)
  ·
    refine ⟨77322241697658392917182449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51548161131772261944788299 77322241697658392917182449)
    ·
      refine ⟨57991681273243794687886837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77322241697658392917182449 57991681273243794687886837)
      ·
        refine ⟨5436720119366605751989391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57991681273243794687886837 5436720119366605751989391)
        ·
          refine ⟨8155080179049908627984087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436720119366605751989391 8155080179049908627984087)
          ·
            refine ⟨12232620268574862941976131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155080179049908627984087 12232620268574862941976131)
            ·
              refine ⟨18348930402862294412964197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12232620268574862941976131 18348930402862294412964197)
              ·
                refine ⟨3440424450536680202430787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18348930402862294412964197 3440424450536680202430787)
                ·
                  refine ⟨5160636675805020303646181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440424450536680202430787 5160636675805020303646181)
                  ·
                    refine ⟨967619376713441306933659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5160636675805020303646181 967619376713441306933659)
                    ·
                      rfl

theorem cell22_2826648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_2826648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826648 prefixEnd_2826648 := by exact prefixLift 2826648
  have htrace : WordTrace (prefixWord ++ tailWord_2826648) baseStart_2826648 baseEnd_2826648 := by
    simpa [prefixWord, tailWord_2826648, baseEnd_2826648] using wordTrace_append hprefix tailTrace_2826648
  have hstable : (prefixWord ++ tailWord_2826648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826648).length < 2 ^ (prefixWord ++ tailWord_2826648).sum := by decide
  have hdescent : baseEnd_2826648 < baseStart_2826648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826661 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_2826661 : Nat := 118140960795 + 2826661 * 2 ^ 59
def prefixEnd_2826661 : Nat := 4983230072969 + 3 ^ 40 * 2826661 * 2
def baseEnd_2826661 : Nat := 967623826879113606358619

theorem tailTrace_2826661 : CollatzResearch.WordTrace tailWord_2826661 prefixEnd_2826661 967623826879113606358619 := by
  unfold tailWord_2826661
  simp only [CollatzResearch.WordTrace]
  refine ⟨103096796412497427109799837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68731197608331618073199891 103096796412497427109799837)
  ·
    refine ⟨38661298654686535166174939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103096796412497427109799837 38661298654686535166174939)
    ·
      refine ⟨57991947982029802749262409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38661298654686535166174939 57991947982029802749262409)
      ·
        refine ⟨43493960986522352061946807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57991947982029802749262409 43493960986522352061946807)
        ·
          refine ⟨65240941479783528092920211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43493960986522352061946807 65240941479783528092920211)
          ·
            refine ⟨97861412219675292139380317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65240941479783528092920211 97861412219675292139380317)
            ·
              refine ⟨36698029582378234552267619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97861412219675292139380317 36698029582378234552267619)
              ·
                refine ⟨55047044373567351828401429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36698029582378234552267619 55047044373567351828401429)
                ·
                  refine ⟨2580330205010969616956317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55047044373567351828401429 2580330205010969616956317)
                  ·
                    refine ⟨967623826879113606358619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580330205010969616956317 967623826879113606358619)
                    ·
                      rfl

theorem cell22_2826661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_2826661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826661 prefixEnd_2826661 := by exact prefixLift 2826661
  have htrace : WordTrace (prefixWord ++ tailWord_2826661) baseStart_2826661 baseEnd_2826661 := by
    simpa [prefixWord, tailWord_2826661, baseEnd_2826661] using wordTrace_append hprefix tailTrace_2826661
  have hstable : (prefixWord ++ tailWord_2826661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826661).length < 2 ^ (prefixWord ++ tailWord_2826661).sum := by decide
  have hdescent : baseEnd_2826661 < baseStart_2826661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826695 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 2, 3]
def baseStart_2826695 : Nat := 118140960795 + 2826695 * 2 ^ 59
def prefixEnd_2826695 : Nat := 4983230072969 + 3 ^ 40 * 2826695 * 2
def baseEnd_2826695 : Nat := 967635465773948851008515

theorem tailTrace_2826695 : CollatzResearch.WordTrace tailWord_2826695 prefixEnd_2826695 967635465773948851008515 := by
  unfold tailWord_2826695
  simp only [CollatzResearch.WordTrace]
  refine ⟨103098036494374250916537539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68732024329582833944358359 103098036494374250916537539)
  ·
    refine ⟨154647054741561376374806309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103098036494374250916537539 154647054741561376374806309)
    ·
      refine ⟨28996322764042758070276183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154647054741561376374806309 28996322764042758070276183)
      ·
        refine ⟨43494484146064137105414275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28996322764042758070276183 43494484146064137105414275)
        ·
          refine ⟨65241726219096205658121413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43494484146064137105414275 65241726219096205658121413)
          ·
            refine ⟨12232823666080538560897765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65241726219096205658121413 12232823666080538560897765)
            ·
              refine ⟨2293654437390100980168331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12232823666080538560897765 2293654437390100980168331)
              ·
                refine ⟨3440481656085151470252497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293654437390100980168331 3440481656085151470252497)
                ·
                  refine ⟨2580361242063863602689373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3440481656085151470252497 2580361242063863602689373)
                  ·
                    refine ⟨967635465773948851008515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580361242063863602689373 967635465773948851008515)
                    ·
                      rfl

theorem cell22_2826695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_2826695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826695 prefixEnd_2826695 := by exact prefixLift 2826695
  have htrace : WordTrace (prefixWord ++ tailWord_2826695) baseStart_2826695 baseEnd_2826695 := by
    simpa [prefixWord, tailWord_2826695, baseEnd_2826695] using wordTrace_append hprefix tailTrace_2826695
  have hstable : (prefixWord ++ tailWord_2826695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826695).length < 2 ^ (prefixWord ++ tailWord_2826695).sum := by decide
  have hdescent : baseEnd_2826695 < baseStart_2826695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826710 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2826710 : Nat := 118140960795 + 2826710 * 2 ^ 59
def prefixEnd_2826710 : Nat := 4983230072969 + 3 ^ 40 * 2826710 * 2
def baseEnd_2826710 : Nat := 967640600580493811883469

theorem tailTrace_2826710 : CollatzResearch.WordTrace tailWord_2826710 prefixEnd_2826710 967640600580493811883469 := by
  unfold tailWord_2826710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443661474332494279895849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68732389059546605652222389 6443661474332494279895849)
  ·
    refine ⟨4832746105749370709921887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6443661474332494279895849 4832746105749370709921887)
    ·
      refine ⟨7249119158624056064882831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832746105749370709921887 7249119158624056064882831)
      ·
        refine ⟨10873678737936084097324247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7249119158624056064882831 10873678737936084097324247)
        ·
          refine ⟨16310518106904126145986371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10873678737936084097324247 16310518106904126145986371)
          ·
            refine ⟨24465777160356189218979557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16310518106904126145986371 24465777160356189218979557)
            ·
              refine ⟨4587333217566785478558667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24465777160356189218979557 4587333217566785478558667)
              ·
                refine ⟨6880999826350178217838001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587333217566785478558667 6880999826350178217838001)
                ·
                  refine ⟨5160749869762633663378501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6880999826350178217838001 5160749869762633663378501)
                  ·
                    refine ⟨967640600580493811883469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5160749869762633663378501 967640600580493811883469)
                    ·
                      rfl

theorem cell22_2826710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2826710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826710 prefixEnd_2826710 := by exact prefixLift 2826710
  have htrace : WordTrace (prefixWord ++ tailWord_2826710) baseStart_2826710 baseEnd_2826710 := by
    simpa [prefixWord, tailWord_2826710, baseEnd_2826710] using wordTrace_append hprefix tailTrace_2826710
  have hstable : (prefixWord ++ tailWord_2826710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826710).length < 2 ^ (prefixWord ++ tailWord_2826710).sum := by decide
  have hdescent : baseEnd_2826710 < baseStart_2826710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826751 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 2, 5]
def baseStart_2826751 : Nat := 118140960795 + 2826751 * 2 ^ 59
def prefixEnd_2826751 : Nat := 4983230072969 + 3 ^ 40 * 2826751 * 2
def baseEnd_2826751 : Nat := 967654635718383371608343

theorem tailTrace_2826751 : CollatzResearch.WordTrace tailWord_2826751 prefixEnd_2826751 967654635718383371608343 := by
  unfold tailWord_2826751
  simp only [CollatzResearch.WordTrace]
  refine ⟨103100078982171372480576107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68733385988114248320384071 103100078982171372480576107)
  ·
    refine ⟨154650118473257058720864161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103100078982171372480576107 154650118473257058720864161)
    ·
      refine ⟨115987588854942794040648121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154650118473257058720864161 115987588854942794040648121)
      ·
        refine ⟨86990691641207095530486091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115987588854942794040648121 86990691641207095530486091)
        ·
          refine ⟨130486037461810643295729137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86990691641207095530486091 130486037461810643295729137)
          ·
            refine ⟨97864528096357982471796853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130486037461810643295729137 97864528096357982471796853)
            ·
              refine ⟨9174799509033560856730955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97864528096357982471796853 9174799509033560856730955)
              ·
                refine ⟨13762199263550341285096433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9174799509033560856730955 13762199263550341285096433)
                ·
                  refine ⟨10321649447662755963822325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13762199263550341285096433 10321649447662755963822325)
                  ·
                    refine ⟨967654635718383371608343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10321649447662755963822325 967654635718383371608343)
                    ·
                      rfl

theorem cell22_2826751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_2826751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826751 prefixEnd_2826751 := by exact prefixLift 2826751
  have htrace : WordTrace (prefixWord ++ tailWord_2826751) baseStart_2826751 baseEnd_2826751 := by
    simpa [prefixWord, tailWord_2826751, baseEnd_2826751] using wordTrace_append hprefix tailTrace_2826751
  have hstable : (prefixWord ++ tailWord_2826751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826751).length < 2 ^ (prefixWord ++ tailWord_2826751).sum := by decide
  have hdescent : baseEnd_2826751 < baseStart_2826751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826753 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 5]
def baseStart_2826753 : Nat := 118140960795 + 2826753 * 2 ^ 59
def prefixEnd_2826753 : Nat := 4983230072969 + 3 ^ 40 * 2826753 * 2
def baseEnd_2826753 : Nat := 322551773453085344352779

theorem tailTrace_2826753 : CollatzResearch.WordTrace tailWord_2826753 prefixEnd_2826753 322551773453085344352779 := by
  unfold tailWord_2826753
  simp only [CollatzResearch.WordTrace]
  refine ⟨103100151928164126822148913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68733434618776084548099275 103100151928164126822148913)
  ·
    refine ⟨77325113946123095116611685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103100151928164126822148913 77325113946123095116611685)
    ·
      refine ⟨14498458864898080334364691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77325113946123095116611685 14498458864898080334364691)
      ·
        refine ⟨21747688297347120501547037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14498458864898080334364691 21747688297347120501547037)
        ·
          refine ⟨8155383111505170188080139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21747688297347120501547037 8155383111505170188080139)
          ·
            refine ⟨12233074667257755282120209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155383111505170188080139 12233074667257755282120209)
            ·
              refine ⟨9174806000443316461590157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12233074667257755282120209 9174806000443316461590157)
              ·
                refine ⟨3440552250166243673096309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9174806000443316461590157 3440552250166243673096309)
                ·
                  refine ⟨322551773453085344352779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3440552250166243673096309 322551773453085344352779)
                  ·
                    rfl

theorem cell22_2826753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_2826753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826753 prefixEnd_2826753 := by exact prefixLift 2826753
  have htrace : WordTrace (prefixWord ++ tailWord_2826753) baseStart_2826753 baseEnd_2826753 := by
    simpa [prefixWord, tailWord_2826753, baseEnd_2826753] using wordTrace_append hprefix tailTrace_2826753
  have hstable : (prefixWord ++ tailWord_2826753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826753).length < 2 ^ (prefixWord ++ tailWord_2826753).sum := by decide
  have hdescent : baseEnd_2826753 < baseStart_2826753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826796 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_2826796 : Nat := 118140960795 + 2826796 * 2 ^ 59
def prefixEnd_2826796 : Nat := 4983230072969 + 3 ^ 40 * 2826796 * 2
def baseEnd_2826796 : Nat := 967670040138018254233205

theorem tailTrace_2826796 : CollatzResearch.WordTrace tailWord_2826796 prefixEnd_2826796 967670040138018254233205 := by
  unfold tailWord_2826796
  simp only [CollatzResearch.WordTrace]
  refine ⟨51550860133504172582982121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68734480178005563443976161 51550860133504172582982121)
  ·
    refine ⟨38663145100128129437236591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51550860133504172582982121 38663145100128129437236591)
    ·
      refine ⟨57994717650192194155854887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38663145100128129437236591 57994717650192194155854887)
      ·
        refine ⟨86992076475288291233782331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57994717650192194155854887 86992076475288291233782331)
        ·
          refine ⟨130488114712932436850673497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86992076475288291233782331 130488114712932436850673497)
          ·
            refine ⟨97866086034699327638005123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130488114712932436850673497 97866086034699327638005123)
            ·
              refine ⟨146799129052048991457007685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97866086034699327638005123 146799129052048991457007685)
              ·
                refine ⟨27524836697259185898188941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146799129052048991457007685 27524836697259185898188941)
                ·
                  refine ⟨10321813761472194711820853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27524836697259185898188941 10321813761472194711820853)
                  ·
                    refine ⟨967670040138018254233205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10321813761472194711820853 967670040138018254233205)
                    ·
                      rfl

theorem cell22_2826796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_2826796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826796 prefixEnd_2826796 := by exact prefixLift 2826796
  have htrace : WordTrace (prefixWord ++ tailWord_2826796) baseStart_2826796 baseEnd_2826796 := by
    simpa [prefixWord, tailWord_2826796, baseEnd_2826796] using wordTrace_append hprefix tailTrace_2826796
  have hstable : (prefixWord ++ tailWord_2826796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826796).length < 2 ^ (prefixWord ++ tailWord_2826796).sum := by decide
  have hdescent : baseEnd_2826796 < baseStart_2826796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826804 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2826804 : Nat := 118140960795 + 2826804 * 2 ^ 59
def prefixEnd_2826804 : Nat := 4983230072969 + 3 ^ 40 * 2826804 * 2
def baseEnd_2826804 : Nat := 322557592900502966677727

theorem tailTrace_2826804 : CollatzResearch.WordTrace tailWord_2826804 prefixEnd_2826804 322557592900502966677727 := by
  unfold tailWord_2826804
  simp only [CollatzResearch.WordTrace]
  refine ⟨51551006025489681266127733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68734674700652908354836977 51551006025489681266127733)
  ·
    refine ⟨4832906814889657618699475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51551006025489681266127733 4832906814889657618699475)
    ·
      refine ⟨7249360222334486428049213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832906814889657618699475 7249360222334486428049213)
      ·
        refine ⟨2718510083375432410518455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7249360222334486428049213 2718510083375432410518455)
        ·
          refine ⟨4077765125063148615777683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718510083375432410518455 4077765125063148615777683)
          ·
            refine ⟨6116647687594722923666525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077765125063148615777683 6116647687594722923666525)
            ·
              refine ⟨2293742882848021096374947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6116647687594722923666525 2293742882848021096374947)
              ·
                refine ⟨3440614324272031644562421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293742882848021096374947 3440614324272031644562421)
                ·
                  refine ⟨322557592900502966677727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3440614324272031644562421 322557592900502966677727)
                  ·
                    rfl

theorem cell22_2826804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2826804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826804 prefixEnd_2826804 := by exact prefixLift 2826804
  have htrace : WordTrace (prefixWord ++ tailWord_2826804) baseStart_2826804 baseEnd_2826804 := by
    simpa [prefixWord, tailWord_2826804, baseEnd_2826804] using wordTrace_append hprefix tailTrace_2826804
  have hstable : (prefixWord ++ tailWord_2826804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826804).length < 2 ^ (prefixWord ++ tailWord_2826804).sum := by decide
  have hdescent : baseEnd_2826804 < baseStart_2826804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826828 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_2826828 : Nat := 118140960795 + 2826828 * 2 ^ 59
def prefixEnd_2826828 : Nat := 4983230072969 + 3 ^ 40 * 2826828 * 2
def baseEnd_2826828 : Nat := 967680994391980837433107

theorem tailTrace_2826828 : CollatzResearch.WordTrace tailWord_2826828 prefixEnd_2826828 967680994391980837433107 := by
  unfold tailWord_2826828
  simp only [CollatzResearch.WordTrace]
  refine ⟨51551443701446207315564569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68735258268594943087419425 51551443701446207315564569)
  ·
    refine ⟨38663582776084655486673427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51551443701446207315564569 38663582776084655486673427)
    ·
      refine ⟨57995374164126983230010141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38663582776084655486673427 57995374164126983230010141)
      ·
        refine ⟨21748265311547618711253803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57995374164126983230010141 21748265311547618711253803)
        ·
          refine ⟨32622397967321428066880705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21748265311547618711253803 32622397967321428066880705)
          ·
            refine ⟨24466798475491071050160529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32622397967321428066880705 24466798475491071050160529)
            ·
              refine ⟨18350098856618303287620397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24466798475491071050160529 18350098856618303287620397)
              ·
                refine ⟨6881287071231863732857649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18350098856618303287620397 6881287071231863732857649)
                ·
                  refine ⟨5160965303423897799643237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6881287071231863732857649 5160965303423897799643237)
                  ·
                    refine ⟨967680994391980837433107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5160965303423897799643237 967680994391980837433107)
                    ·
                      rfl

theorem cell22_2826828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_2826828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826828 prefixEnd_2826828 := by exact prefixLift 2826828
  have htrace : WordTrace (prefixWord ++ tailWord_2826828) baseStart_2826828 baseEnd_2826828 := by
    simpa [prefixWord, tailWord_2826828, baseEnd_2826828] using wordTrace_append hprefix tailTrace_2826828
  have hstable : (prefixWord ++ tailWord_2826828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826828).length < 2 ^ (prefixWord ++ tailWord_2826828).sum := by decide
  have hdescent : baseEnd_2826828 < baseStart_2826828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826864 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 2, 3]
def baseStart_2826864 : Nat := 118140960795 + 2826864 * 2 ^ 59
def prefixEnd_2826864 : Nat := 4983230072969 + 3 ^ 40 * 2826864 * 2
def baseEnd_2826864 : Nat := 967693317927688743532997

theorem tailTrace_2826864 : CollatzResearch.WordTrace tailWord_2826864 prefixEnd_2826864 967693317927688743532997 := by
  unfold tailWord_2826864
  simp only [CollatzResearch.WordTrace]
  refine ⟨51552100215380996389719823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68736133620507995186293097 51552100215380996389719823)
  ·
    refine ⟨77328150323071494584579735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51552100215380996389719823 77328150323071494584579735)
    ·
      refine ⟨115992225484607241876869603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77328150323071494584579735 115992225484607241876869603)
      ·
        refine ⟨173988338226910862815304405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115992225484607241876869603 173988338226910862815304405)
        ·
          refine ⟨4077851677193223347233697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 173988338226910862815304405 4077851677193223347233697)
          ·
            refine ⟨3058388757894917510425273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4077851677193223347233697 3058388757894917510425273)
            ·
              refine ⟨2293791568421188132818955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058388757894917510425273 2293791568421188132818955)
              ·
                refine ⟨3440687352631782199228433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293791568421188132818955 3440687352631782199228433)
                ·
                  refine ⟨2580515514473836649421325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3440687352631782199228433 2580515514473836649421325)
                  ·
                    refine ⟨967693317927688743532997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580515514473836649421325 967693317927688743532997)
                    ·
                      rfl

theorem cell22_2826864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_2826864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826864 prefixEnd_2826864 := by exact prefixLift 2826864
  have htrace : WordTrace (prefixWord ++ tailWord_2826864) baseStart_2826864 baseEnd_2826864 := by
    simpa [prefixWord, tailWord_2826864, baseEnd_2826864] using wordTrace_append hprefix tailTrace_2826864
  have hstable : (prefixWord ++ tailWord_2826864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826864).length < 2 ^ (prefixWord ++ tailWord_2826864).sum := by decide
  have hdescent : baseEnd_2826864 < baseStart_2826864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826903 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 2, 5]
def baseStart_2826903 : Nat := 118140960795 + 2826903 * 2 ^ 59
def prefixEnd_2826903 : Nat := 4983230072969 + 3 ^ 40 * 2826903 * 2
def baseEnd_2826903 : Nat := 967706668424705641807877

theorem tailTrace_2826903 : CollatzResearch.WordTrace tailWord_2826903 prefixEnd_2826903 967706668424705641807877 := by
  unfold tailWord_2826903
  simp only [CollatzResearch.WordTrace]
  refine ⟨103105622877620702440109363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68737081918413801626739575 103105622877620702440109363)
  ·
    refine ⟨154658434316431053660164045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103105622877620702440109363 154658434316431053660164045)
    ·
      refine ⟨57996912868661645122561517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154658434316431053660164045 57996912868661645122561517)
      ·
        refine ⟨21748842325748116920960569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57996912868661645122561517 21748842325748116920960569)
        ·
          refine ⟨16311631744311087690720427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21748842325748116920960569 16311631744311087690720427)
          ·
            refine ⟨24467447616466631536080641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16311631744311087690720427 24467447616466631536080641)
            ·
              refine ⟨18350585712349973652060481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24467447616466631536080641 18350585712349973652060481)
              ·
                refine ⟨13762939284262480239045361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18350585712349973652060481 13762939284262480239045361)
                ·
                  refine ⟨10322204463196860179284021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13762939284262480239045361 10322204463196860179284021)
                  ·
                    refine ⟨967706668424705641807877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10322204463196860179284021 967706668424705641807877)
                    ·
                      rfl

theorem cell22_2826903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_2826903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826903 prefixEnd_2826903 := by exact prefixLift 2826903
  have htrace : WordTrace (prefixWord ++ tailWord_2826903) baseStart_2826903 baseEnd_2826903 := by
    simpa [prefixWord, tailWord_2826903, baseEnd_2826903] using wordTrace_append hprefix tailTrace_2826903
  have hstable : (prefixWord ++ tailWord_2826903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826903).length < 2 ^ (prefixWord ++ tailWord_2826903).sum := by decide
  have hdescent : baseEnd_2826903 < baseStart_2826903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826909 : List Nat := [1, 4, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2826909 : Nat := 118140960795 + 2826909 * 2 ^ 59
def prefixEnd_2826909 : Nat := 4983230072969 + 3 ^ 40 * 2826909 * 2
def baseEnd_2826909 : Nat := 967708722347323626157859

theorem tailTrace_2826909 : CollatzResearch.WordTrace tailWord_2826909 prefixEnd_2826909 967708722347323626157859 := by
  unfold tailWord_2826909
  simp only [CollatzResearch.WordTrace]
  refine ⟨103105841715598965464827781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68737227810399310309885187 103105841715598965464827781)
  ·
    refine ⟨19332345321674806024655209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103105841715598965464827781 19332345321674806024655209)
    ·
      refine ⟨14499258991256104518491407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19332345321674806024655209 14499258991256104518491407)
      ·
        refine ⟨21748888486884156777737111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14499258991256104518491407 21748888486884156777737111)
        ·
          refine ⟨32623332730326235166605667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21748888486884156777737111 32623332730326235166605667)
          ·
            refine ⟨48934999095489352749908501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32623332730326235166605667 48934999095489352749908501)
            ·
              refine ⟨2293828082601063410151961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48934999095489352749908501 2293828082601063410151961)
              ·
                refine ⟨1720371061950797557613971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293828082601063410151961 1720371061950797557613971)
                ·
                  refine ⟨2580556592926196336420957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720371061950797557613971 2580556592926196336420957)
                  ·
                    refine ⟨967708722347323626157859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580556592926196336420957 967708722347323626157859)
                    ·
                      rfl

theorem cell22_2826909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2826909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826909 prefixEnd_2826909 := by exact prefixLift 2826909
  have htrace : WordTrace (prefixWord ++ tailWord_2826909) baseStart_2826909 baseEnd_2826909 := by
    simpa [prefixWord, tailWord_2826909, baseEnd_2826909] using wordTrace_append hprefix tailTrace_2826909
  have hstable : (prefixWord ++ tailWord_2826909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826909).length < 2 ^ (prefixWord ++ tailWord_2826909).sum := by decide
  have hdescent : baseEnd_2826909 < baseStart_2826909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826952 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 1, 4]
def baseStart_2826952 : Nat := 118140960795 + 2826952 * 2 ^ 59
def prefixEnd_2826952 : Nat := 4983230072969 + 3 ^ 40 * 2826952 * 2
def baseEnd_2826952 : Nat := 967723442126085847332727

theorem tailTrace_2826952 : CollatzResearch.WordTrace tailWord_2826952 prefixEnd_2826952 967723442126085847332727 := by
  unfold tailWord_2826952
  simp only [CollatzResearch.WordTrace]
  refine ⟨51553705027221591904321555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68738273369628789205762073 51553705027221591904321555)
  ·
    refine ⟨77330557540832387856482333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51553705027221591904321555 77330557540832387856482333)
    ·
      refine ⟨28998959077812145446180875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77330557540832387856482333 28998959077812145446180875)
      ·
        refine ⟨43498438616718218169271313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28998959077812145446180875 43498438616718218169271313)
        ·
          refine ⟨32623828962538663626953485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43498438616718218169271313 32623828962538663626953485)
          ·
            refine ⟨12233935860951998860107557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32623828962538663626953485 12233935860951998860107557)
            ·
              refine ⟨2293862973928499786270167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12233935860951998860107557 2293862973928499786270167)
              ·
                refine ⟨3440794460892749679405251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293862973928499786270167 3440794460892749679405251)
                ·
                  refine ⟨5161191691339124519107877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440794460892749679405251 5161191691339124519107877)
                  ·
                    refine ⟨967723442126085847332727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5161191691339124519107877 967723442126085847332727)
                    ·
                      rfl

theorem cell22_2826952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_2826952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826952 prefixEnd_2826952 := by exact prefixLift 2826952
  have htrace : WordTrace (prefixWord ++ tailWord_2826952) baseStart_2826952 baseEnd_2826952 := by
    simpa [prefixWord, tailWord_2826952, baseEnd_2826952] using wordTrace_append hprefix tailTrace_2826952
  have hstable : (prefixWord ++ tailWord_2826952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826952).length < 2 ^ (prefixWord ++ tailWord_2826952).sum := by decide
  have hdescent : baseEnd_2826952 < baseStart_2826952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826993 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2826993 : Nat := 118140960795 + 2826993 * 2 ^ 59
def prefixEnd_2826993 : Nat := 4983230072969 + 3 ^ 40 * 2826993 * 2
def baseEnd_2826993 : Nat := 967737477263975407057601

theorem tailTrace_2826993 : CollatzResearch.WordTrace tailWord_2826993 prefixEnd_2826993 967737477263975407057601 := by
  unfold tailWord_2826993
  simp only [CollatzResearch.WordTrace]
  refine ⟨103108905447294647810885633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68739270298196431873923755 103108905447294647810885633)
  ·
    refine ⟨77331679085470985858164225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103108905447294647810885633 77331679085470985858164225)
    ·
      refine ⟨57998759314103239393623169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77331679085470985858164225 57998759314103239393623169)
      ·
        refine ⟨43499069485577429545217377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57998759314103239393623169 43499069485577429545217377)
        ·
          refine ⟨32624302114183072158913033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43499069485577429545217377 32624302114183072158913033)
          ·
            refine ⟨24468226585637304119184775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32624302114183072158913033 24468226585637304119184775)
            ·
              refine ⟨36702339878455956178777163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24468226585637304119184775 36702339878455956178777163)
              ·
                refine ⟨55053509817683934268165745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36702339878455956178777163 55053509817683934268165745)
                ·
                  refine ⟨41290132363262950701124309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55053509817683934268165745 41290132363262950701124309)
                  ·
                    refine ⟨967737477263975407057601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41290132363262950701124309 967737477263975407057601)
                    ·
                      rfl

theorem cell22_2826993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2826993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2826993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2826993 prefixEnd_2826993 := by exact prefixLift 2826993
  have htrace : WordTrace (prefixWord ++ tailWord_2826993) baseStart_2826993 baseEnd_2826993 := by
    simpa [prefixWord, tailWord_2826993, baseEnd_2826993] using wordTrace_append hprefix tailTrace_2826993
  have hstable : (prefixWord ++ tailWord_2826993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826993).length < 2 ^ (prefixWord ++ tailWord_2826993).sum := by decide
  have hdescent : baseEnd_2826993 < baseStart_2826993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827023 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 7]
def baseStart_2827023 : Nat := 118140960795 + 2827023 * 2 ^ 59
def prefixEnd_2827023 : Nat := 4983230072969 + 3 ^ 40 * 2827023 * 2
def baseEnd_2827023 : Nat := 322582582292355109602503

theorem tailTrace_2827023 : CollatzResearch.WordTrace tailWord_2827023 prefixEnd_2827023 322582582292355109602503 := by
  unfold tailWord_2827023
  simp only [CollatzResearch.WordTrace]
  refine ⟨103109999637185962934477723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68739999758123975289651815 103109999637185962934477723)
  ·
    refine ⟨154664999455778944401716585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103109999637185962934477723 154664999455778944401716585)
    ·
      refine ⟨115998749591834208301287439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154664999455778944401716585 115998749591834208301287439)
      ·
        refine ⟨173998124387751312451931159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115998749591834208301287439 173998124387751312451931159)
        ·
          refine ⟨260997186581626968677896739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173998124387751312451931159 260997186581626968677896739)
          ·
            refine ⟨391495779872440453016845109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260997186581626968677896739 391495779872440453016845109)
            ·
              refine ⟨36702729363041292470329229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 391495779872440453016845109 36702729363041292470329229)
              ·
                refine ⟨13763523511140484676373461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36702729363041292470329229 13763523511140484676373461)
                ·
                  refine ⟨322582582292355109602503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13763523511140484676373461 322582582292355109602503)
                  ·
                    rfl

theorem cell22_2827023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 7].length) (baseStart_2827023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827023 prefixEnd_2827023 := by exact prefixLift 2827023
  have htrace : WordTrace (prefixWord ++ tailWord_2827023) baseStart_2827023 baseEnd_2827023 := by
    simpa [prefixWord, tailWord_2827023, baseEnd_2827023] using wordTrace_append hprefix tailTrace_2827023
  have hstable : (prefixWord ++ tailWord_2827023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827023).length < 2 ^ (prefixWord ++ tailWord_2827023).sum := by decide
  have hdescent : baseEnd_2827023 < baseStart_2827023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827117 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_2827117 : Nat := 118140960795 + 2827117 * 2 ^ 59
def prefixEnd_2827117 : Nat := 4983230072969 + 3 ^ 40 * 2827117 * 2
def baseEnd_2827117 : Nat := 967779924998080416957221

theorem tailTrace_2827117 : CollatzResearch.WordTrace tailWord_2827117 prefixEnd_2827117 967779924998080416957221 := by
  unfold tailWord_2827117
  simp only [CollatzResearch.WordTrace]
  refine ⟨103113428098845416988399605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68742285399230277992266403 103113428098845416988399605)
  ·
    refine ⟨9666883884266757842662463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103113428098845416988399605 9666883884266757842662463)
    ·
      refine ⟨14500325826400136763993695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9666883884266757842662463 14500325826400136763993695)
      ·
        refine ⟨21750488739600205145990543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14500325826400136763993695 21750488739600205145990543)
        ·
          refine ⟨32625733109400307718985815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21750488739600205145990543 32625733109400307718985815)
          ·
            refine ⟨48938599664100461578478723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32625733109400307718985815 48938599664100461578478723)
            ·
              refine ⟨73407899496150692367718085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48938599664100461578478723 73407899496150692367718085)
              ·
                refine ⟨13763981155528254818947141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73407899496150692367718085 13763981155528254818947141)
                ·
                  refine ⟨2580746466661547778552589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13763981155528254818947141 2580746466661547778552589)
                  ·
                    refine ⟨967779924998080416957221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580746466661547778552589 967779924998080416957221)
                    ·
                      rfl

theorem cell22_2827117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_2827117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827117 prefixEnd_2827117 := by exact prefixLift 2827117
  have htrace : WordTrace (prefixWord ++ tailWord_2827117) baseStart_2827117 baseEnd_2827117 := by
    simpa [prefixWord, tailWord_2827117, baseEnd_2827117] using wordTrace_append hprefix tailTrace_2827117
  have hstable : (prefixWord ++ tailWord_2827117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827117).length < 2 ^ (prefixWord ++ tailWord_2827117).sum := by decide
  have hdescent : baseEnd_2827117 < baseStart_2827117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827181 : List Nat := [1, 5, 2, 3, 2, 1, 8]
def baseStart_2827181 : Nat := 118140960795 + 2827181 * 2 ^ 59
def prefixEnd_2827181 : Nat := 4983230072969 + 3 ^ 40 * 2827181 * 2
def baseEnd_2827181 : Nat := 35844512352074280865075

theorem tailTrace_2827181 : CollatzResearch.WordTrace tailWord_2827181 prefixEnd_2827181 35844512352074280865075 := by
  unfold tailWord_2827181
  simp only [CollatzResearch.WordTrace]
  refine ⟨103115762370613555918729397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68743841580409037279152931 103115762370613555918729397)
  ·
    refine ⟨9667102722245020867380881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103115762370613555918729397 9667102722245020867380881)
    ·
      refine ⟨7250327041683765650535661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9667102722245020867380881 7250327041683765650535661)
      ·
        refine ⟨2718872640631412118950873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7250327041683765650535661 2718872640631412118950873)
        ·
          refine ⟨2039154480473559089213155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718872640631412118950873 2039154480473559089213155)
          ·
            refine ⟨3058731720710338633819733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039154480473559089213155 3058731720710338633819733)
            ·
              refine ⟨35844512352074280865075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3058731720710338633819733 35844512352074280865075)
              ·
                rfl

theorem cell22_2827181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 8].length) (baseStart_2827181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827181 prefixEnd_2827181 := by exact prefixLift 2827181
  have htrace : WordTrace (prefixWord ++ tailWord_2827181) baseStart_2827181 baseEnd_2827181 := by
    simpa [prefixWord, tailWord_2827181, baseEnd_2827181] using wordTrace_append hprefix tailTrace_2827181
  have hstable : (prefixWord ++ tailWord_2827181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827181).length < 2 ^ (prefixWord ++ tailWord_2827181).sum := by decide
  have hdescent : baseEnd_2827181 < baseStart_2827181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827269 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_2827269 : Nat := 118140960795 + 2827269 * 2 ^ 59
def prefixEnd_2827269 : Nat := 4983230072969 + 3 ^ 40 * 2827269 * 2
def baseEnd_2827269 : Nat := 967831957704402687156755

theorem tailTrace_2827269 : CollatzResearch.WordTrace tailWord_2827269 prefixEnd_2827269 967831957704402687156755 := by
  unfold tailWord_2827269
  simp only [CollatzResearch.WordTrace]
  refine ⟨103118971994294746947932861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68745981329529831298621907 103118971994294746947932861)
  ·
    refine ⟨38669614497860530105474823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103118971994294746947932861 38669614497860530105474823)
    ·
      refine ⟨58004421746790795158212235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38669614497860530105474823 58004421746790795158212235)
      ·
        refine ⟨87006632620186192737318353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58004421746790795158212235 87006632620186192737318353)
        ·
          refine ⟨65254974465139644552988765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87006632620186192737318353 65254974465139644552988765)
          ·
            refine ⟨24470615424427366707370787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65254974465139644552988765 24470615424427366707370787)
            ·
              refine ⟨36705923136641050061056181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24470615424427366707370787 36705923136641050061056181)
              ·
                refine ⟨3441180294060098443224017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36705923136641050061056181 3441180294060098443224017)
                ·
                  refine ⟨2580885220545073832418013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3441180294060098443224017 2580885220545073832418013)
                  ·
                    refine ⟨967831957704402687156755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580885220545073832418013 967831957704402687156755)
                    ·
                      rfl

theorem cell22_2827269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_2827269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827269 prefixEnd_2827269 := by exact prefixLift 2827269
  have htrace : WordTrace (prefixWord ++ tailWord_2827269) baseStart_2827269 baseEnd_2827269 := by
    simpa [prefixWord, tailWord_2827269, baseEnd_2827269] using wordTrace_append hprefix tailTrace_2827269
  have hstable : (prefixWord ++ tailWord_2827269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827269).length < 2 ^ (prefixWord ++ tailWord_2827269).sum := by decide
  have hdescent : baseEnd_2827269 < baseStart_2827269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827303 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2827303 : Nat := 118140960795 + 2827303 * 2 ^ 59
def prefixEnd_2827303 : Nat := 4983230072969 + 3 ^ 40 * 2827303 * 2
def baseEnd_2827303 : Nat := 967843596599237931806651

theorem tailTrace_2827303 : CollatzResearch.WordTrace tailWord_2827303 prefixEnd_2827303 967843596599237931806651 := by
  unfold tailWord_2827303
  simp only [CollatzResearch.WordTrace]
  refine ⟨103120212076171570754670563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68746808050781047169780375 103120212076171570754670563)
  ·
    refine ⟨154680318114257356132005845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103120212076171570754670563 154680318114257356132005845)
    ·
      refine ⟨3625319955802906784343887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 154680318114257356132005845 3625319955802906784343887)
      ·
        refine ⟨5437979933704360176515831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625319955802906784343887 5437979933704360176515831)
        ·
          refine ⟨8156969900556540264773747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437979933704360176515831 8156969900556540264773747)
          ·
            refine ⟨12235454850834810397160621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156969900556540264773747 12235454850834810397160621)
            ·
              refine ⟨4588295569063053898935233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12235454850834810397160621 4588295569063053898935233)
              ·
                refine ⟨3441221676797290424201425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4588295569063053898935233 3441221676797290424201425)
                ·
                  refine ⟨2580916257597967818151069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3441221676797290424201425 2580916257597967818151069)
                  ·
                    refine ⟨967843596599237931806651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580916257597967818151069 967843596599237931806651)
                    ·
                      rfl

theorem cell22_2827303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2827303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827303 prefixEnd_2827303 := by exact prefixLift 2827303
  have htrace : WordTrace (prefixWord ++ tailWord_2827303) baseStart_2827303 baseEnd_2827303 := by
    simpa [prefixWord, tailWord_2827303, baseEnd_2827303] using wordTrace_append hprefix tailTrace_2827303
  have hstable : (prefixWord ++ tailWord_2827303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827303).length < 2 ^ (prefixWord ++ tailWord_2827303).sum := by decide
  have hdescent : baseEnd_2827303 < baseStart_2827303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827348 : List Nat := [2, 4, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_2827348 : Nat := 118140960795 + 2827348 * 2 ^ 59
def prefixEnd_2827348 : Nat := 4983230072969 + 3 ^ 40 * 2827348 * 2
def baseEnd_2827348 : Nat := 967859001018872814431513

theorem tailTrace_2827348 : CollatzResearch.WordTrace tailWord_2827348 prefixEnd_2827348 967859001018872814431513 := by
  unfold tailWord_2827348
  simp only [CollatzResearch.WordTrace]
  refine ⟨51560926680504271720029349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68747902240672362293372465 51560926680504271720029349)
  ·
    refine ⟨9667673752594550947505503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51560926680504271720029349 9667673752594550947505503)
    ·
      refine ⟨14501510628891826421258255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9667673752594550947505503 14501510628891826421258255)
      ·
        refine ⟨21752265943337739631887383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14501510628891826421258255 21752265943337739631887383)
        ·
          refine ⟨32628398915006609447831075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21752265943337739631887383 32628398915006609447831075)
          ·
            refine ⟨48942598372509914171746613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32628398915006609447831075 48942598372509914171746613)
            ·
              refine ⟨4588368597422804453601245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48942598372509914171746613 4588368597422804453601245)
              ·
                refine ⟨1720638224033551670100467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4588368597422804453601245 1720638224033551670100467)
                ·
                  refine ⟨2580957336050327505150701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720638224033551670100467 2580957336050327505150701)
                  ·
                    refine ⟨967859001018872814431513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2580957336050327505150701 967859001018872814431513)
                    ·
                      rfl

theorem cell22_2827348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_2827348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827348 prefixEnd_2827348 := by exact prefixLift 2827348
  have htrace : WordTrace (prefixWord ++ tailWord_2827348) baseStart_2827348 baseEnd_2827348 := by
    simpa [prefixWord, tailWord_2827348, baseEnd_2827348] using wordTrace_append hprefix tailTrace_2827348
  have hstable : (prefixWord ++ tailWord_2827348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827348).length < 2 ^ (prefixWord ++ tailWord_2827348).sum := by decide
  have hdescent : baseEnd_2827348 < baseStart_2827348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827387 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 5, 5]
def baseStart_2827387 : Nat := 118140960795 + 2827387 * 2 ^ 59
def prefixEnd_2827387 : Nat := 4983230072969 + 3 ^ 40 * 2827387 * 2
def baseEnd_2827387 : Nat := 967872351515889712706393

theorem tailTrace_2827387 : CollatzResearch.WordTrace tailWord_2827387 prefixEnd_2827387 967872351515889712706393 := by
  unfold tailWord_2827387
  simp only [CollatzResearch.WordTrace]
  refine ⟨103123275807867253100728415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68748850538578168733818943 103123275807867253100728415)
  ·
    refine ⟨154684913711800879651092623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103123275807867253100728415 154684913711800879651092623)
    ·
      refine ⟨232027370567701319476638935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154684913711800879651092623 232027370567701319476638935)
      ·
        refine ⟨348041055851551979214958403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232027370567701319476638935 348041055851551979214958403)
        ·
          refine ⟨522061583777327968822437605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348041055851551979214958403 522061583777327968822437605)
          ·
            refine ⟨97886546958248994154207051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 522061583777327968822437605 97886546958248994154207051)
            ·
              refine ⟨146829820437373491231310577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97886546958248994154207051 146829820437373491231310577)
              ·
                refine ⟨110122365328030118423482933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146829820437373491231310577 110122365328030118423482933)
                ·
                  refine ⟨10323971749502823602201525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110122365328030118423482933 10323971749502823602201525)
                  ·
                    refine ⟨967872351515889712706393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10323971749502823602201525 967872351515889712706393)
                    ·
                      rfl

theorem cell22_2827387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_2827387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827387 prefixEnd_2827387 := by exact prefixLift 2827387
  have htrace : WordTrace (prefixWord ++ tailWord_2827387) baseStart_2827387 baseEnd_2827387 := by
    simpa [prefixWord, tailWord_2827387, baseEnd_2827387] using wordTrace_append hprefix tailTrace_2827387
  have hstable : (prefixWord ++ tailWord_2827387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827387).length < 2 ^ (prefixWord ++ tailWord_2827387).sum := by decide
  have hdescent : baseEnd_2827387 < baseStart_2827387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827404 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_2827404 : Nat := 118140960795 + 2827404 * 2 ^ 59
def prefixEnd_2827404 : Nat := 4983230072969 + 3 ^ 40 * 2827404 * 2
def baseEnd_2827404 : Nat := 967878170963307335031341

theorem tailTrace_2827404 : CollatzResearch.WordTrace tailWord_2827404 prefixEnd_2827404 967878170963307335031341 := by
  unfold tailWord_2827404
  simp only [CollatzResearch.WordTrace]
  refine ⟨51561947924402832502048633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68749263899203776669398177 51561947924402832502048633)
  ·
    refine ⟨38671460943302124376536475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51561947924402832502048633 38671460943302124376536475)
    ·
      refine ⟨58007191414953186564804713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38671460943302124376536475 58007191414953186564804713)
      ·
        refine ⟨43505393561214889923603535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58007191414953186564804713 43505393561214889923603535)
        ·
          refine ⟨65258090341822334885405303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43505393561214889923603535 65258090341822334885405303)
          ·
            refine ⟨97887135512733502328107955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65258090341822334885405303 97887135512733502328107955)
            ·
              refine ⟨146830703269100253492161933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97887135512733502328107955 146830703269100253492161933)
              ·
                refine ⟨55061513725912595059560725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146830703269100253492161933 55061513725912595059560725)
                ·
                  refine ⟨2581008455902152893416909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55061513725912595059560725 2581008455902152893416909)
                  ·
                    refine ⟨967878170963307335031341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581008455902152893416909 967878170963307335031341)
                    ·
                      rfl

theorem cell22_2827404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_2827404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827404 prefixEnd_2827404 := by exact prefixLift 2827404
  have htrace : WordTrace (prefixWord ++ tailWord_2827404) baseStart_2827404 baseEnd_2827404 := by
    simpa [prefixWord, tailWord_2827404, baseEnd_2827404] using wordTrace_append hprefix tailTrace_2827404
  have hstable : (prefixWord ++ tailWord_2827404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827404).length < 2 ^ (prefixWord ++ tailWord_2827404).sum := by decide
  have hdescent : baseEnd_2827404 < baseStart_2827404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827423 : List Nat := [1, 1, 2, 6, 2, 1, 1, 4, 4]
def baseStart_2827423 : Nat := 118140960795 + 2827423 * 2 ^ 59
def prefixEnd_2827423 : Nat := 4983230072969 + 3 ^ 40 * 2827423 * 2
def baseEnd_2827423 : Nat := 322628225017199206268761

theorem tailTrace_2827423 : CollatzResearch.WordTrace tailWord_2827423 prefixEnd_2827423 322628225017199206268761 := by
  unfold tailWord_2827423
  simp only [CollatzResearch.WordTrace]
  refine ⟨103124588835736831249038923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68749725890491220832692615 103124588835736831249038923)
  ·
    refine ⟨154686883253605246873558385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103124588835736831249038923 154686883253605246873558385)
    ·
      refine ⟨116015162440203935155168789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154686883253605246873558385 116015162440203935155168789)
      ·
        refine ⟨5438210739384559460398537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116015162440203935155168789 5438210739384559460398537)
        ·
          refine ⟨4078658054538419595298903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5438210739384559460398537 4078658054538419595298903)
          ·
            refine ⟨6117987081807629392948355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078658054538419595298903 6117987081807629392948355)
            ·
              refine ⟨9176980622711444089422533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6117987081807629392948355 9176980622711444089422533)
              ·
                refine ⟨1720683866758395766766725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9176980622711444089422533 1720683866758395766766725)
                ·
                  refine ⟨322628225017199206268761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1720683866758395766766725 322628225017199206268761)
                  ·
                    rfl

theorem cell22_2827423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 4].length) (baseStart_2827423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827423 prefixEnd_2827423 := by exact prefixLift 2827423
  have htrace : WordTrace (prefixWord ++ tailWord_2827423) baseStart_2827423 baseEnd_2827423 := by
    simpa [prefixWord, tailWord_2827423, baseEnd_2827423] using wordTrace_append hprefix tailTrace_2827423
  have hstable : (prefixWord ++ tailWord_2827423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827423).length < 2 ^ (prefixWord ++ tailWord_2827423).sum := by decide
  have hdescent : baseEnd_2827423 < baseStart_2827423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827556 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2827556 : Nat := 118140960795 + 2827556 * 2 ^ 59
def prefixEnd_2827556 : Nat := 4983230072969 + 3 ^ 40 * 2827556 * 2
def baseEnd_2827556 : Nat := 967930203669629605230875

theorem tailTrace_2827556 : CollatzResearch.WordTrace tailWord_2827556 prefixEnd_2827556 967930203669629605230875 := by
  unfold tailWord_2827556
  simp only [CollatzResearch.WordTrace]
  refine ⟨51564719872127497481815261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68752959829503329975753681 51564719872127497481815261)
  ·
    refine ⟨19336769952047811555680723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51564719872127497481815261 19336769952047811555680723)
    ·
      refine ⟨29005154928071717333521085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19336769952047811555680723 29005154928071717333521085)
      ·
        refine ⟨10876933098026894000070407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29005154928071717333521085 10876933098026894000070407)
        ·
          refine ⟨16315399647040341000105611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10876933098026894000070407 16315399647040341000105611)
          ·
            refine ⟨24473099470560511500158417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16315399647040341000105611 24473099470560511500158417)
            ·
              refine ⟨18354824602920383625118813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24473099470560511500158417 18354824602920383625118813)
              ·
                refine ⟨6883059226095143859419555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18354824602920383625118813 6883059226095143859419555)
                ·
                  refine ⟨10324588839142715789129333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6883059226095143859419555 10324588839142715789129333)
                  ·
                    refine ⟨967930203669629605230875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10324588839142715789129333 967930203669629605230875)
                    ·
                      rfl

theorem cell22_2827556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2827556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827556 prefixEnd_2827556 := by exact prefixLift 2827556
  have htrace : WordTrace (prefixWord ++ tailWord_2827556) baseStart_2827556 baseEnd_2827556 := by
    simpa [prefixWord, tailWord_2827556, baseEnd_2827556] using wordTrace_append hprefix tailTrace_2827556
  have hstable : (prefixWord ++ tailWord_2827556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827556).length < 2 ^ (prefixWord ++ tailWord_2827556).sum := by decide
  have hdescent : baseEnd_2827556 < baseStart_2827556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827560 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2827560 : Nat := 118140960795 + 2827560 * 2 ^ 59
def prefixEnd_2827560 : Nat := 4983230072969 + 3 ^ 40 * 2827560 * 2
def baseEnd_2827560 : Nat := 967931572951374928130863

theorem tailTrace_2827560 : CollatzResearch.WordTrace tailWord_2827560 prefixEnd_2827560 967931572951374928130863 := by
  unfold tailWord_2827560
  simp only [CollatzResearch.WordTrace]
  refine ⟨51564792818120251823388067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68753057090827002431184089 51564792818120251823388067)
  ·
    refine ⟨77347189227180377735082101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51564792818120251823388067 77347189227180377735082101)
    ·
      refine ⟨7251298990048160412663947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77347189227180377735082101 7251298990048160412663947)
      ·
        refine ⟨10876948485072240618995921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7251298990048160412663947 10876948485072240618995921)
        ·
          refine ⟨8157711363804180464246941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10876948485072240618995921 8157711363804180464246941)
          ·
            refine ⟨3059141761426567674092603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8157711363804180464246941 3059141761426567674092603)
            ·
              refine ⟨4588712642139851511138905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059141761426567674092603 4588712642139851511138905)
              ·
                refine ⟨3441534481604888633354179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4588712642139851511138905 3441534481604888633354179)
                ·
                  refine ⟨5162301722407332950031269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441534481604888633354179 5162301722407332950031269)
                  ·
                    refine ⟨967931572951374928130863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5162301722407332950031269 967931572951374928130863)
                    ·
                      rfl

theorem cell22_2827560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2827560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827560 prefixEnd_2827560 := by exact prefixLift 2827560
  have htrace : WordTrace (prefixWord ++ tailWord_2827560) baseStart_2827560 baseEnd_2827560 := by
    simpa [prefixWord, tailWord_2827560, baseEnd_2827560] using wordTrace_append hprefix tailTrace_2827560
  have hstable : (prefixWord ++ tailWord_2827560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827560).length < 2 ^ (prefixWord ++ tailWord_2827560).sum := by decide
  have hdescent : baseEnd_2827560 < baseStart_2827560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827571 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 2, 4]
def baseStart_2827571 : Nat := 118140960795 + 2827571 * 2 ^ 59
def prefixEnd_2827571 : Nat := 4983230072969 + 3 ^ 40 * 2827571 * 2
def baseEnd_2827571 : Nat := 967935338476174566105829

theorem tailTrace_2827571 : CollatzResearch.WordTrace tailWord_2827571 prefixEnd_2827571 967935338476174566105829 := by
  unfold tailWord_2827571
  simp only [CollatzResearch.WordTrace]
  refine ⟨103129986839200652525426567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68753324559467101683617711 103129986839200652525426567)
  ·
    refine ⟨154694980258800978788139851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103129986839200652525426567 154694980258800978788139851)
    ·
      refine ⟨232042470388201468182209777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154694980258800978788139851 232042470388201468182209777)
      ·
        refine ⟨174031852791151101136657333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232042470388201468182209777 174031852791151101136657333)
        ·
          refine ⟨16315486199170415731561625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174031852791151101136657333 16315486199170415731561625)
          ·
            refine ⟨12236614649377811798671219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16315486199170415731561625 12236614649377811798671219)
            ·
              refine ⟨18354921974066717698006829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12236614649377811798671219 18354921974066717698006829)
              ·
                refine ⟨6883095740275019136752561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18354921974066717698006829 6883095740275019136752561)
                ·
                  refine ⟨5162321805206264352564421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6883095740275019136752561 5162321805206264352564421)
                  ·
                    refine ⟨967935338476174566105829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5162321805206264352564421 967935338476174566105829)
                    ·
                      rfl

theorem cell22_2827571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_2827571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827571 prefixEnd_2827571 := by exact prefixLift 2827571
  have htrace : WordTrace (prefixWord ++ tailWord_2827571) baseStart_2827571 baseEnd_2827571 := by
    simpa [prefixWord, tailWord_2827571, baseEnd_2827571] using wordTrace_append hprefix tailTrace_2827571
  have hstable : (prefixWord ++ tailWord_2827571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827571).length < 2 ^ (prefixWord ++ tailWord_2827571).sum := by decide
  have hdescent : baseEnd_2827571 < baseStart_2827571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827736 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 2, 7]
def baseStart_2827736 : Nat := 118140960795 + 2827736 * 2 ^ 59
def prefixEnd_2827736 : Nat := 4983230072969 + 3 ^ 40 * 2827736 * 2
def baseEnd_2827736 : Nat := 967991821348169135730323

theorem tailTrace_2827736 : CollatzResearch.WordTrace tailWord_2827736 prefixEnd_2827736 967991821348169135730323 := by
  unfold tailWord_2827736
  simp only [CollatzResearch.WordTrace]
  refine ⟨51568002441801442852591531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68757336589068590470122041 51568002441801442852591531)
  ·
    refine ⟨77352003662702164278887297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51568002441801442852591531 77352003662702164278887297)
    ·
      refine ⟨58014002747026623209165473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77352003662702164278887297 58014002747026623209165473)
      ·
        refine ⟨43510502060269967406874105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58014002747026623209165473 43510502060269967406874105)
        ·
          refine ⟨32632876545202475555155579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43510502060269967406874105 32632876545202475555155579)
          ·
            refine ⟨48949314817803713332733369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32632876545202475555155579 48949314817803713332733369)
            ·
              refine ⟨36711986113352784999550027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48949314817803713332733369 36711986113352784999550027)
              ·
                refine ⟨55067979170029177499325041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36711986113352784999550027 55067979170029177499325041)
                ·
                  refine ⟨41300984377521883124493781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55067979170029177499325041 41300984377521883124493781)
                  ·
                    refine ⟨967991821348169135730323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41300984377521883124493781 967991821348169135730323)
                    ·
                      rfl

theorem cell22_2827736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_2827736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827736 prefixEnd_2827736 := by exact prefixLift 2827736
  have htrace : WordTrace (prefixWord ++ tailWord_2827736) baseStart_2827736 baseEnd_2827736 := by
    simpa [prefixWord, tailWord_2827736, baseEnd_2827736] using wordTrace_append hprefix tailTrace_2827736
  have hstable : (prefixWord ++ tailWord_2827736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827736).length < 2 ^ (prefixWord ++ tailWord_2827736).sum := by decide
  have hdescent : baseEnd_2827736 < baseStart_2827736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827789 : List Nat := [1, 7, 1, 1, 2, 1, 3, 6]
def baseStart_2827789 : Nat := 118140960795 + 2827789 * 2 ^ 59
def prefixEnd_2827789 : Nat := 4983230072969 + 3 ^ 40 * 2827789 * 2
def baseEnd_2827789 : Nat := 107556662703477184906129

theorem tailTrace_2827789 : CollatzResearch.WordTrace tailWord_2827789 prefixEnd_2827789 107556662703477184906129 := by
  unfold tailWord_2827789
  simp only [CollatzResearch.WordTrace]
  refine ⟨103137937952410875756862421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68758625301607250504574947 103137937952410875756862421)
  ·
    refine ⟨2417295420759629900551463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 103137937952410875756862421 2417295420759629900551463)
    ·
      refine ⟨3625943131139444850827195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417295420759629900551463 3625943131139444850827195)
      ·
        refine ⟨5438914696709167276240793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625943131139444850827195 5438914696709167276240793)
        ·
          refine ⟨4079186022531875457180595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5438914696709167276240793 4079186022531875457180595)
          ·
            refine ⟨6118779033797813185770893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079186022531875457180595 6118779033797813185770893)
            ·
              refine ⟨2294542137674179944664085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6118779033797813185770893 2294542137674179944664085)
              ·
                refine ⟨107556662703477184906129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2294542137674179944664085 107556662703477184906129)
                ·
                  rfl

theorem cell22_2827789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 6].length) (baseStart_2827789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827789 prefixEnd_2827789 := by exact prefixLift 2827789
  have htrace : WordTrace (prefixWord ++ tailWord_2827789) baseStart_2827789 baseEnd_2827789 := by
    simpa [prefixWord, tailWord_2827789, baseEnd_2827789] using wordTrace_append hprefix tailTrace_2827789
  have hstable : (prefixWord ++ tailWord_2827789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827789).length < 2 ^ (prefixWord ++ tailWord_2827789).sum := by decide
  have hdescent : baseEnd_2827789 < baseStart_2827789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827847 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 1, 4]
def baseStart_2827847 : Nat := 118140960795 + 2827847 * 2 ^ 59
def prefixEnd_2827847 : Nat := 4983230072969 + 3 ^ 40 * 2827847 * 2
def baseEnd_2827847 : Nat := 968029818916601846204983

theorem tailTrace_2827847 : CollatzResearch.WordTrace tailWord_2827847 prefixEnd_2827847 968029818916601846204983 := by
  unfold tailWord_2827847
  simp only [CollatzResearch.WordTrace]
  refine ⟨103140053386200751662473795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68760035590800501108315863 103140053386200751662473795)
  ·
    refine ⟨154710080079301127493710693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103140053386200751662473795 154710080079301127493710693)
    ·
      refine ⟨29008140014868961405070755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154710080079301127493710693 29008140014868961405070755)
      ·
        refine ⟨43512210022303442107606133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29008140014868961405070755 43512210022303442107606133)
        ·
          refine ⟨4079269689590947697588075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43512210022303442107606133 4079269689590947697588075)
          ·
            refine ⟨6118904534386421546382113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079269689590947697588075 6118904534386421546382113)
            ·
              refine ⟨4589178400789816159786585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6118904534386421546382113 4589178400789816159786585)
              ·
                refine ⟨3441883800592362119839939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4589178400789816159786585 3441883800592362119839939)
                ·
                  refine ⟨5162825700888543179759909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441883800592362119839939 5162825700888543179759909)
                  ·
                    refine ⟨968029818916601846204983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5162825700888543179759909 968029818916601846204983)
                    ·
                      rfl

theorem cell22_2827847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_2827847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827847 prefixEnd_2827847 := by exact prefixLift 2827847
  have htrace : WordTrace (prefixWord ++ tailWord_2827847) baseStart_2827847 baseEnd_2827847 := by
    simpa [prefixWord, tailWord_2827847, baseEnd_2827847] using wordTrace_append hprefix tailTrace_2827847
  have hstable : (prefixWord ++ tailWord_2827847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827847).length < 2 ^ (prefixWord ++ tailWord_2827847).sum := by decide
  have hdescent : baseEnd_2827847 < baseStart_2827847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827860 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_2827860 : Nat := 118140960795 + 2827860 * 2 ^ 59
def prefixEnd_2827860 : Nat := 4983230072969 + 3 ^ 40 * 2827860 * 2
def baseEnd_2827860 : Nat := 968034269082274145629943

theorem tailTrace_2827860 : CollatzResearch.WordTrace tailWord_2827860 prefixEnd_2827860 968034269082274145629943 := by
  unfold tailWord_2827860
  simp only [CollatzResearch.WordTrace]
  refine ⟨51570263767576827441348517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68760351690102436588464689 51570263767576827441348517)
  ·
    refine ⟨9669424456420655145252847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51570263767576827441348517 9669424456420655145252847)
    ·
      refine ⟨14504136684630982717879271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9669424456420655145252847 14504136684630982717879271)
      ·
        refine ⟨21756205026946474076818907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14504136684630982717879271 21756205026946474076818907)
        ·
          refine ⟨32634307540419711115228361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21756205026946474076818907 32634307540419711115228361)
          ·
            refine ⟨24475730655314783336421271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32634307540419711115228361 24475730655314783336421271)
            ·
              refine ⟨36713595982972175004631907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24475730655314783336421271 36713595982972175004631907)
              ·
                refine ⟨55070393974458262506947861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36713595982972175004631907 55070393974458262506947861)
                ·
                  refine ⟨2581424717552731055013181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55070393974458262506947861 2581424717552731055013181)
                  ·
                    refine ⟨968034269082274145629943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581424717552731055013181 968034269082274145629943)
                    ·
                      rfl

theorem cell22_2827860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_2827860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827860 prefixEnd_2827860 := by exact prefixLift 2827860
  have htrace : WordTrace (prefixWord ++ tailWord_2827860) baseStart_2827860 baseEnd_2827860 := by
    simpa [prefixWord, tailWord_2827860, baseEnd_2827860] using wordTrace_append hprefix tailTrace_2827860
  have hstable : (prefixWord ++ tailWord_2827860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827860).length < 2 ^ (prefixWord ++ tailWord_2827860).sum := by decide
  have hdescent : baseEnd_2827860 < baseStart_2827860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827875 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 2, 4]
def baseStart_2827875 : Nat := 118140960795 + 2827875 * 2 ^ 59
def prefixEnd_2827875 : Nat := 4983230072969 + 3 ^ 40 * 2827875 * 2
def baseEnd_2827875 : Nat := 968039403888819106504897

theorem tailTrace_2827875 : CollatzResearch.WordTrace tailWord_2827875 prefixEnd_2827875 968039403888819106504897 := by
  unfold tailWord_2827875
  simp only [CollatzResearch.WordTrace]
  refine ⟨103141074630099312444493079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68760716420066208296328719 103141074630099312444493079)
  ·
    refine ⟨154711611945148968666739619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103141074630099312444493079 154711611945148968666739619)
    ·
      refine ⟨232067417917723453000109429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154711611945148968666739619 232067417917723453000109429)
      ·
        refine ⟨21756320429786573718760259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232067417917723453000109429 21756320429786573718760259)
        ·
          refine ⟨32634480644679860578140389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21756320429786573718760259 32634480644679860578140389)
          ·
            refine ⟨6118965120877473858401323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32634480644679860578140389 6118965120877473858401323)
            ·
              refine ⟨9178447681316210787601985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6118965120877473858401323 9178447681316210787601985)
              ·
                refine ⟨6883835760987158090701489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9178447681316210787601985 6883835760987158090701489)
                ·
                  refine ⟨5162876820740368568026117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6883835760987158090701489 5162876820740368568026117)
                  ·
                    refine ⟨968039403888819106504897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5162876820740368568026117 968039403888819106504897)
                    ·
                      rfl

theorem cell22_2827875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_2827875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827875 prefixEnd_2827875 := by exact prefixLift 2827875
  have htrace : WordTrace (prefixWord ++ tailWord_2827875) baseStart_2827875 baseEnd_2827875 := by
    simpa [prefixWord, tailWord_2827875, baseEnd_2827875] using wordTrace_append hprefix tailTrace_2827875
  have hstable : (prefixWord ++ tailWord_2827875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827875).length < 2 ^ (prefixWord ++ tailWord_2827875).sum := by decide
  have hdescent : baseEnd_2827875 < baseStart_2827875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827890 : List Nat := [3, 2, 1, 2, 3, 2, 2, 7]
def baseStart_2827890 : Nat := 118140960795 + 2827890 * 2 ^ 59
def prefixEnd_2827890 : Nat := 4983230072969 + 3 ^ 40 * 2827890 * 2
def baseEnd_2827890 : Nat := 107560504299484896375539

theorem tailTrace_2827890 : CollatzResearch.WordTrace tailWord_2827890 prefixEnd_2827890 107560504299484896375539 := by
  unfold tailWord_2827890
  simp only [CollatzResearch.WordTrace]
  refine ⟨25785405431261242501572281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68761081150029980004192749 25785405431261242501572281)
  ·
    refine ⟨19339054073445931876179211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25785405431261242501572281 19339054073445931876179211)
    ·
      refine ⟨29008581110168897814268817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19339054073445931876179211 29008581110168897814268817)
      ·
        refine ⟨21756435832626673360701613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29008581110168897814268817 21756435832626673360701613)
        ·
          refine ⟨8158663437235002510263105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21756435832626673360701613 8158663437235002510263105)
          ·
            refine ⟨6118997577926251882697329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8158663437235002510263105 6118997577926251882697329)
            ·
              refine ⟨4589248183444688912022997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6118997577926251882697329 4589248183444688912022997)
              ·
                refine ⟨107560504299484896375539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4589248183444688912022997 107560504299484896375539)
                ·
                  rfl

theorem cell22_2827890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_2827890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827890 prefixEnd_2827890 := by exact prefixLift 2827890
  have htrace : WordTrace (prefixWord ++ tailWord_2827890) baseStart_2827890 baseEnd_2827890 := by
    simpa [prefixWord, tailWord_2827890, baseEnd_2827890] using wordTrace_append hprefix tailTrace_2827890
  have hstable : (prefixWord ++ tailWord_2827890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827890).length < 2 ^ (prefixWord ++ tailWord_2827890).sum := by decide
  have hdescent : baseEnd_2827890 < baseStart_2827890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827894 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_2827894 : Nat := 118140960795 + 2827894 * 2 ^ 59
def prefixEnd_2827894 : Nat := 4983230072969 + 3 ^ 40 * 2827894 * 2
def baseEnd_2827894 : Nat := 968045907977109390279839

theorem tailTrace_2827894 : CollatzResearch.WordTrace tailWord_2827894 prefixEnd_2827894 968045907977109390279839 := by
  unfold tailWord_2827894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446360476064404918089671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68761178411353652459623157 6446360476064404918089671)
  ·
    refine ⟨9669540714096607377134507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6446360476064404918089671 9669540714096607377134507)
    ·
      refine ⟨14504311071144911065701761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9669540714096607377134507 14504311071144911065701761)
      ·
        refine ⟨10878233303358683299276321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14504311071144911065701761 10878233303358683299276321)
        ·
          refine ⟨8158674977519012474457241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10878233303358683299276321 8158674977519012474457241)
          ·
            refine ⟨6119006233139259355842931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8158674977519012474457241 6119006233139259355842931)
            ·
              refine ⟨9178509349708889033764397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119006233139259355842931 9178509349708889033764397)
              ·
                refine ⟨3441941006140833387661649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9178509349708889033764397 3441941006140833387661649)
                ·
                  refine ⟨2581455754605625040746237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3441941006140833387661649 2581455754605625040746237)
                  ·
                    refine ⟨968045907977109390279839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581455754605625040746237 968045907977109390279839)
                    ·
                      rfl

theorem cell22_2827894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_2827894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827894 prefixEnd_2827894 := by exact prefixLift 2827894
  have htrace : WordTrace (prefixWord ++ tailWord_2827894) baseStart_2827894 baseEnd_2827894 := by
    simpa [prefixWord, tailWord_2827894, baseEnd_2827894] using wordTrace_append hprefix tailTrace_2827894
  have hstable : (prefixWord ++ tailWord_2827894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827894).length < 2 ^ (prefixWord ++ tailWord_2827894).sum := by decide
  have hdescent : baseEnd_2827894 < baseStart_2827894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827965 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2827965 : Nat := 118140960795 + 2827965 * 2 ^ 59
def prefixEnd_2827965 : Nat := 4983230072969 + 3 ^ 40 * 2827965 * 2
def baseEnd_2827965 : Nat := 968070212728088871754621

theorem tailTrace_2827965 : CollatzResearch.WordTrace tailWord_2827965 prefixEnd_2827965 968070212728088871754621 := by
  unfold tailWord_2827965
  simp only [CollatzResearch.WordTrace]
  refine ⟨103144357199773257815269349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68762904799848838543512899 103144357199773257815269349)
  ·
    refine ⟨19339566974957485840363003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103144357199773257815269349 19339566974957485840363003)
    ·
      refine ⟨29009350462436228760544505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19339566974957485840363003 29009350462436228760544505)
      ·
        refine ⟨21757012846827171570408379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29009350462436228760544505 21757012846827171570408379)
        ·
          refine ⟨32635519270240757355612569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21757012846827171570408379 32635519270240757355612569)
          ·
            refine ⟨24476639452680568016709427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32635519270240757355612569 24476639452680568016709427)
            ·
              refine ⟨36714959179020852025064141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24476639452680568016709427 36714959179020852025064141)
              ·
                refine ⟨13768109692132819509399053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36714959179020852025064141 13768109692132819509399053)
                ·
                  refine ⟨5163041134549807316024645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13768109692132819509399053 5163041134549807316024645)
                  ·
                    refine ⟨968070212728088871754621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163041134549807316024645 968070212728088871754621)
                    ·
                      rfl

theorem cell22_2827965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2827965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827965 prefixEnd_2827965 := by exact prefixLift 2827965
  have htrace : WordTrace (prefixWord ++ tailWord_2827965) baseStart_2827965 baseEnd_2827965 := by
    simpa [prefixWord, tailWord_2827965, baseEnd_2827965] using wordTrace_append hprefix tailTrace_2827965
  have hstable : (prefixWord ++ tailWord_2827965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827965).length < 2 ^ (prefixWord ++ tailWord_2827965).sum := by decide
  have hdescent : baseEnd_2827965 < baseStart_2827965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2827982 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_2827982 : Nat := 118140960795 + 2827982 * 2 ^ 59
def prefixEnd_2827982 : Nat := 4983230072969 + 3 ^ 40 * 2827982 * 2
def baseEnd_2827982 : Nat := 968076032175506494079569

theorem tailTrace_2827982 : CollatzResearch.WordTrace tailWord_2827982 prefixEnd_2827982 968076032175506494079569 := by
  unfold tailWord_2827982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12893122155088958714829775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68763318160474446479092133 12893122155088958714829775)
  ·
    refine ⟨19339683232633438072244663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12893122155088958714829775 19339683232633438072244663)
    ·
      refine ⟨29009524848950157108366995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19339683232633438072244663 29009524848950157108366995)
      ·
        refine ⟨43514287273425235662550493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29009524848950157108366995 43514287273425235662550493)
        ·
          refine ⟨16317857727534463373456435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43514287273425235662550493 16317857727534463373456435)
          ·
            refine ⟨24476786591301695060184653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16317857727534463373456435 24476786591301695060184653)
            ·
              refine ⟨9178794971738135647569245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24476786591301695060184653 9178794971738135647569245)
              ·
                refine ⟨3442048114401800867838467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9178794971738135647569245 3442048114401800867838467)
                ·
                  refine ⟨5163072171602701301757701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442048114401800867838467 5163072171602701301757701)
                  ·
                    refine ⟨968076032175506494079569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163072171602701301757701 968076032175506494079569)
                    ·
                      rfl

theorem cell22_2827982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_2827982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2827982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2827982 prefixEnd_2827982 := by exact prefixLift 2827982
  have htrace : WordTrace (prefixWord ++ tailWord_2827982) baseStart_2827982 baseEnd_2827982 := by
    simpa [prefixWord, tailWord_2827982, baseEnd_2827982] using wordTrace_append hprefix tailTrace_2827982
  have hstable : (prefixWord ++ tailWord_2827982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2827982).length < 2 ^ (prefixWord ++ tailWord_2827982).sum := by decide
  have hdescent : baseEnd_2827982 < baseStart_2827982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2827982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828010 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2828010 : Nat := 118140960795 + 2828010 * 2 ^ 59
def prefixEnd_2828010 : Nat := 4983230072969 + 3 ^ 40 * 2828010 * 2
def baseEnd_2828010 : Nat := 968085617147723754379483

theorem tailTrace_2828010 : CollatzResearch.WordTrace tailWord_2828010 prefixEnd_2828010 968085617147723754379483 := by
  unfold tailWord_2828010
  simp only [CollatzResearch.WordTrace]
  refine ⟨25786499621152557625164371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68763998989740153667104989 25786499621152557625164371)
  ·
    refine ⟨38679749431728836437746557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25786499621152557625164371 38679749431728836437746557)
    ·
      refine ⟨14504906036898313664154959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38679749431728836437746557 14504906036898313664154959)
      ·
        refine ⟨21757359055347470496232439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14504906036898313664154959 21757359055347470496232439)
        ·
          refine ⟨32636038583021205744348659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21757359055347470496232439 32636038583021205744348659)
          ·
            refine ⟨48954057874531808616522989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32636038583021205744348659 48954057874531808616522989)
            ·
              refine ⟨18357771702949428231196121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48954057874531808616522989 18357771702949428231196121)
              ·
                refine ⟨13768328777212071173397091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18357771702949428231196121 13768328777212071173397091)
                ·
                  refine ⟨20652493165818106760095637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13768328777212071173397091 20652493165818106760095637)
                  ·
                    refine ⟨968085617147723754379483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20652493165818106760095637 968085617147723754379483)
                    ·
                      rfl

theorem cell22_2828010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2828010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828010 prefixEnd_2828010 := by exact prefixLift 2828010
  have htrace : WordTrace (prefixWord ++ tailWord_2828010) baseStart_2828010 baseEnd_2828010 := by
    simpa [prefixWord, tailWord_2828010, baseEnd_2828010] using wordTrace_append hprefix tailTrace_2828010
  have hstable : (prefixWord ++ tailWord_2828010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828010).length < 2 ^ (prefixWord ++ tailWord_2828010).sum := by decide
  have hdescent : baseEnd_2828010 < baseStart_2828010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828012 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_2828012 : Nat := 118140960795 + 2828012 * 2 ^ 59
def prefixEnd_2828012 : Nat := 4983230072969 + 3 ^ 40 * 2828012 * 2
def baseEnd_2828012 : Nat := 968086301788596415829477

theorem tailTrace_2828012 : CollatzResearch.WordTrace tailWord_2828012 prefixEnd_2828012 968086301788596415829477 := by
  unfold tailWord_2828012
  simp only [CollatzResearch.WordTrace]
  refine ⟨51573035715301492421115145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68764047620401989894820193 51573035715301492421115145)
  ·
    refine ⟨38679776786476119315836359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51573035715301492421115145 38679776786476119315836359)
    ·
      refine ⟨58019665179714178973754539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38679776786476119315836359 58019665179714178973754539)
      ·
        refine ⟨87029497769571268460631809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58019665179714178973754539 87029497769571268460631809)
        ·
          refine ⟨65272123327178451345473857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87029497769571268460631809 65272123327178451345473857)
          ·
            refine ⟨48954092495383838509105393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65272123327178451345473857 48954092495383838509105393)
            ·
              refine ⟨36715569371537878881829045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48954092495383838509105393 36715569371537878881829045)
              ·
                refine ⟨3442084628581676145171473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36715569371537878881829045 3442084628581676145171473)
                ·
                  refine ⟨2581563471436257108878605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442084628581676145171473 2581563471436257108878605)
                  ·
                    refine ⟨968086301788596415829477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581563471436257108878605 968086301788596415829477)
                    ·
                      rfl

theorem cell22_2828012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_2828012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828012 prefixEnd_2828012 := by exact prefixLift 2828012
  have htrace : WordTrace (prefixWord ++ tailWord_2828012) baseStart_2828012 baseEnd_2828012 := by
    simpa [prefixWord, tailWord_2828012, baseEnd_2828012] using wordTrace_append hprefix tailTrace_2828012
  have hstable : (prefixWord ++ tailWord_2828012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828012).length < 2 ^ (prefixWord ++ tailWord_2828012).sum := by decide
  have hdescent : baseEnd_2828012 < baseStart_2828012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828117 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2828117 : Nat := 118140960795 + 2828117 * 2 ^ 59
def prefixEnd_2828117 : Nat := 4983230072969 + 3 ^ 40 * 2828117 * 2
def baseEnd_2828117 : Nat := 968122245434411141954155

theorem tailTrace_2828117 : CollatzResearch.WordTrace tailWord_2828117 prefixEnd_2828117 968122245434411141954155 := by
  unfold tailWord_2828117
  simp only [CollatzResearch.WordTrace]
  refine ⟨103149901095222587774802605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68766600730148391849868403 103149901095222587774802605)
  ·
    refine ⟨38681212910708470415550977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103149901095222587774802605 38681212910708470415550977)
    ·
      refine ⟨29010909683031352811663233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38681212910708470415550977 29010909683031352811663233)
      ·
        refine ⟨21758182262273514608747425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29010909683031352811663233 21758182262273514608747425)
        ·
          refine ⟨16318636696705135956560569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21758182262273514608747425 16318636696705135956560569)
          ·
            refine ⟨12238977522528851967420427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16318636696705135956560569 12238977522528851967420427)
            ·
              refine ⟨18358466283793277951130641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12238977522528851967420427 18358466283793277951130641)
              ·
                refine ⟨13768849712844958463347981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18358466283793277951130641 13768849712844958463347981)
                ·
                  refine ⟨5163318642316859423755493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13768849712844958463347981 5163318642316859423755493)
                  ·
                    refine ⟨968122245434411141954155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163318642316859423755493 968122245434411141954155)
                    ·
                      rfl

theorem cell22_2828117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2828117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828117 prefixEnd_2828117 := by exact prefixLift 2828117
  have htrace : WordTrace (prefixWord ++ tailWord_2828117) baseStart_2828117 baseEnd_2828117 := by
    simpa [prefixWord, tailWord_2828117, baseEnd_2828117] using wordTrace_append hprefix tailTrace_2828117
  have hstable : (prefixWord ++ tailWord_2828117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828117).length < 2 ^ (prefixWord ++ tailWord_2828117).sum := by decide
  have hdescent : baseEnd_2828117 < baseStart_2828117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828147 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 4, 3]
def baseStart_2828147 : Nat := 118140960795 + 2828147 * 2 ^ 59
def prefixEnd_2828147 : Nat := 4983230072969 + 3 ^ 40 * 2828147 * 2
def baseEnd_2828147 : Nat := 968132515047501063704063

theorem tailTrace_2828147 : CollatzResearch.WordTrace tailWord_2828147 prefixEnd_2828147 968132515047501063704063 := by
  unfold tailWord_2828147
  simp only [CollatzResearch.WordTrace]
  refine ⟨103150995285113902898394695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68767330190075935265596463 103150995285113902898394695)
  ·
    refine ⟨154726492927670854347592043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103150995285113902898394695 154726492927670854347592043)
    ·
      refine ⟨232089739391506281521388065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154726492927670854347592043 232089739391506281521388065)
      ·
        refine ⟨174067304543629711141041049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232089739391506281521388065 174067304543629711141041049)
        ·
          refine ⟨130550478407722283355780787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174067304543629711141041049 130550478407722283355780787)
          ·
            refine ⟨195825717611583425033671181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130550478407722283355780787 195825717611583425033671181)
            ·
              refine ⟨73434644104343784387626693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195825717611583425033671181 73434644104343784387626693)
              ·
                refine ⟨13768995769564459572680005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73434644104343784387626693 13768995769564459572680005)
                ·
                  refine ⟨2581686706793336169877501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13768995769564459572680005 2581686706793336169877501)
                  ·
                    refine ⟨968132515047501063704063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581686706793336169877501 968132515047501063704063)
                    ·
                      rfl

theorem cell22_2828147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 3].length) (baseStart_2828147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828147 prefixEnd_2828147 := by exact prefixLift 2828147
  have htrace : WordTrace (prefixWord ++ tailWord_2828147) baseStart_2828147 baseEnd_2828147 := by
    simpa [prefixWord, tailWord_2828147, baseEnd_2828147] using wordTrace_append hprefix tailTrace_2828147
  have hstable : (prefixWord ++ tailWord_2828147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828147).length < 2 ^ (prefixWord ++ tailWord_2828147).sum := by decide
  have hdescent : baseEnd_2828147 < baseStart_2828147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828160 : List Nat := [2, 1, 1, 2, 1, 2, 13]
def baseStart_2828160 : Nat := 118140960795 + 2828160 * 2 ^ 59
def prefixEnd_2828160 : Nat := 4983230072969 + 3 ^ 40 * 2828160 * 2
def baseEnd_2828160 : Nat := 35856924637524939375149

theorem tailTrace_2828160 : CollatzResearch.WordTrace tailWord_2828160 prefixEnd_2828160 35856924637524939375149 := by
  unfold tailWord_2828160
  simp only [CollatzResearch.WordTrace]
  refine ⟨51575734717033403059308967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68767646289377870745745289 51575734717033403059308967)
  ·
    refine ⟨77363602075550104588963451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51575734717033403059308967 77363602075550104588963451)
    ·
      refine ⟨116045403113325156883445177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77363602075550104588963451 116045403113325156883445177)
      ·
        refine ⟨87034052334993867662583883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116045403113325156883445177 87034052334993867662583883)
        ·
          refine ⟨130551078502490801493875825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87034052334993867662583883 130551078502490801493875825)
          ·
            refine ⟨97913308876868101120406869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130551078502490801493875825 97913308876868101120406869)
            ·
              refine ⟨35856924637524939375149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 97913308876868101120406869 35856924637524939375149)
              ·
                rfl

theorem cell22_2828160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 13].length) (baseStart_2828160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828160 prefixEnd_2828160 := by exact prefixLift 2828160
  have htrace : WordTrace (prefixWord ++ tailWord_2828160) baseStart_2828160 baseEnd_2828160 := by
    simpa [prefixWord, tailWord_2828160, baseEnd_2828160] using wordTrace_append hprefix tailTrace_2828160
  have hstable : (prefixWord ++ tailWord_2828160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828160).length < 2 ^ (prefixWord ++ tailWord_2828160).sum := by decide
  have hdescent : baseEnd_2828160 < baseStart_2828160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828181 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_2828181 : Nat := 118140960795 + 2828181 * 2 ^ 59
def prefixEnd_2828181 : Nat := 4983230072969 + 3 ^ 40 * 2828181 * 2
def baseEnd_2828181 : Nat := 968144153942336308353959

theorem tailTrace_2828181 : CollatzResearch.WordTrace tailWord_2828181 prefixEnd_2828181 968144153942336308353959 := by
  unfold tailWord_2828181
  simp only [CollatzResearch.WordTrace]
  refine ⟨103152235366990726705132397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68768156911327151136754931 103152235366990726705132397)
  ·
    refine ⟨38682088262621522514424649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103152235366990726705132397 38682088262621522514424649)
    ·
      refine ⟨29011566196966141885818487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38682088262621522514424649 29011566196966141885818487)
      ·
        refine ⟨43517349295449212828727731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29011566196966141885818487 43517349295449212828727731)
        ·
          refine ⟨65276023943173819243091597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43517349295449212828727731 65276023943173819243091597)
          ·
            refine ⟨24478508978690182216159349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65276023943173819243091597 24478508978690182216159349)
            ·
              refine ⟨2294860216752204582764939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24478508978690182216159349 2294860216752204582764939)
              ·
                refine ⟨3442290325128306874147409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294860216752204582764939 3442290325128306874147409)
                ·
                  refine ⟨2581717743846230155610557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442290325128306874147409 2581717743846230155610557)
                  ·
                    refine ⟨968144153942336308353959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581717743846230155610557 968144153942336308353959)
                    ·
                      rfl

theorem cell22_2828181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_2828181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828181 prefixEnd_2828181 := by exact prefixLift 2828181
  have htrace : WordTrace (prefixWord ++ tailWord_2828181) baseStart_2828181 baseEnd_2828181 := by
    simpa [prefixWord, tailWord_2828181, baseEnd_2828181] using wordTrace_append hprefix tailTrace_2828181
  have hstable : (prefixWord ++ tailWord_2828181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828181).length < 2 ^ (prefixWord ++ tailWord_2828181).sum := by decide
  have hdescent : baseEnd_2828181 < baseStart_2828181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
